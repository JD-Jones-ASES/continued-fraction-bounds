#!/usr/bin/env python3
"""Finite, exact, independently written regression checks for the extension formulas.

No Lean calls, network access, or third-party dependencies. Every decision
uses Fraction/Quad arithmetic. This supplements, not replaces, quantified proofs.
Run normally and with python -O: no mathematical checks use assert.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction as Q
from itertools import product
import json
import platform
from pathlib import Path
import sys
from cf_bounds import (Quad, metallic_data, envelopes, run_cell, constant_cell,
                       run_bounds, rectangle_optima, tail_iter, fiber_profiles,
                       window_thresholds, prepend_word, actual_triple, serial)

counts = Counter()


def check(condition, group, detail=""):
    if not condition:
        raise RuntimeError(f"FAILED {group}: {detail}")
    counts[group] += 1


def finite_digits(x):
    """Positive literal word for a rational [0;word] in (0,1]."""
    if not Q(0) < x <= Q(1):
        raise ValueError("rational past must be in (0,1]")
    word = []
    while x:
        t = 1/x
        b = t.numerator // t.denominator
        word.append(b)
        x = t-b
    return word


def bad_future_example(a, r, objective, scale=10**9):
    """Irrational witness just outside K_r; returns actual triple and cutoff."""
    data = window_thresholds(a, r)
    L, U = data["L"], data["U"]
    beta, _, _, _ = metallic_data(a)
    idx = 0 if objective == "F" else 1
    vals = [(t, fiber_profiles(a, t)[idx]) for t in (L, U)]
    t, cutoff = (max if objective == "F" else min)(vals, key=lambda z: z[1])
    if objective == "F":
        x = Q(1) if t <= Q(1, a+1) else (1/t-a if t <= beta else 1/(a+t))
    else:
        x = 1/(a+t) if t <= beta else (1/t-a if t <= Q(1, a) else Q(0))
    # For these tested r>=1,a>=2 optima x is positive. The abstract proof also
    # covers a zero past optimizer by approximating it with positive rationals.
    if x == 0:
        x = Q(1, scale)
    sign = -1 if t == L else 1
    eta = Q(1, scale*(L.denominator*U.denominator)**2)
    y = t + sign*Quad(0, eta, beta.d)
    check(0 < y < 1 and (y < L or y > U), "bad_future_outside_cylinder")
    past_word = finite_digits(x)
    alpha = prepend_word(list(reversed(past_word)) + [a], y)
    actual = actual_triple(alpha, len(past_word)-1)
    check(actual["x"] == x and actual["y"] == y and actual["a"] == a,
          "bad_future_actual_realization")
    n = len(past_word)-1
    extended = actual_triple(alpha, n+r)
    check(any(extended["digits"][n+3+i] != a for i in range(r)),
          "actual_bad_window_literal_digit")
    theta = (min if objective == "F" else max)(actual["theta"])
    return actual, theta, cutoff


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    for d in (2, 5, 8, 13, 20):
        root = Quad(0, 1, d)
        check(root*root == d and root > 0, "field_sanity")
        for u, v in product(range(-3, 4), repeat=2):
            z = Quad(Q(u, 3), Q(v, 7), d)
            check(z+(-z) == 0 and z*z == Quad(z.u*z.u+d*z.v*z.v, 2*z.u*z.v, d),
                  "field_arithmetic")
            if z != 0:
                check(z/z == 1, "field_inverse")
            floor = z.floor()
            check(floor <= z < floor+1, "exact_floor")

    # Check both inverse inequalities on exact rational grids.
    for a in range(2, 11):
        beta, c, kap, lam = metallic_data(a)
        check(beta*(a+beta) == 1 and c == beta/(1+beta*beta), "metallic_identities")
        check(lam == c*a/(1+(a+beta)**2), "upper_constant_identity")
        for i, j in product(range(17), repeat=2):
            x, y = Q(i, 16), Q(j, 16)
            F, G = envelopes(a, x, y)
            radius = max(abs(x-beta), abs(y-beta))
            check(F < c < G, "classical_strict_grid")
            check(c-F >= kap*radius, "existing_minimum_stability")
            check(G-c > lam*radius, "maximum_stability_strict_grid")
        for x, y in ((Q(1), Q(1, a+1)), (Q(1, a+1), Q(1))):
            F, _ = envelopes(a, x, y)
            check(c-F == kap*max(abs(x-beta), abs(y-beta)), "existing_equality_points")
        check(envelopes(a, beta, beta) == (c, c), "metallic_equality")
        f = lambda z: z/(1+z*z)
        for j in range(5):
            t = Q(j, 4*(a+1))
            lhs = f(a+t)-c-lam*(beta-t)
            rhs = c*(beta-t)**2*(a*(a+t)-2)/((1+(a+t)**2)*(1+(a+beta)**2))
            check(lhs == rhs and rhs > 0, "upper_stability_remainder_identity")

    # Compare the special four-corner theorem with a different finite-candidate
    # evaluator, and test interior rational points of each rectangle.
    for a, r, s, e, f in product(range(2, 8), range(5), range(5), "LH", "LH"):
        data = run_bounds(a, r, s, e, f)
        lx, ux = data["past_cell"]; ly, uy = data["future_cell"]
        oracle = rectangle_optima(a, lx, ux, ly, uy)
        C, U = data["minimum_supremum"], data["maximum_infimum"]
        check((C, U) == (oracle["minimum_supremum"], oracle["maximum_infimum"]),
              "run_corner_vs_switching_candidates", (a, r, s, e, f))
        for i, j in product(range(3), repeat=2):
            F, G = envelopes(a, lx+(ux-lx)*Q(i, 2), ly+(uy-ly)*Q(j, 2))
            check(F <= C and G >= U, "run_interior_grid")

    # Thin rectangles cover all three branches of each new fiber formula.
    for a in (Q(1), Q(3, 2), Q(2), Q(5, 2), Q(3), Q(7)):
        for i in range(41):
            t = Q(i, 40)
            oracle = rectangle_optima(a, t, t, 0, 1)
            check(fiber_profiles(a, t) ==
                  (oracle["minimum_supremum"], oracle["maximum_infimum"]),
                  "fiber_profiles_vs_rectangle_candidates")

    # Full closed/degenerate rectangles, with a=1 and noninteger a included.
    intervals = [(Q(i, 4), Q(j, 4)) for i in range(5) for j in range(i, 5)]
    for a in (Q(1), Q(3, 2), Q(2), Q(7, 2)):
        for (lx, ux), (ly, uy) in product(intervals, repeat=2):
            data = rectangle_optima(a, lx, ux, ly, uy)
            for i, j in product(range(3), repeat=2):
                F, G = envelopes(a, lx+(ux-lx)*Q(i, 2), ly+(uy-ly)*Q(j, 2))
                check(F <= data["minimum_supremum"] and G >= data["maximum_infimum"],
                      "general_rectangle_grid")

    # Independent actual floor/fraction extraction, not an assumed coordinate bridge.
    for a, length, endpoint in product(range(2, 7), range(1, 5), ("ordinary", "terminal_one")):
        beta, c, kap, lam = metallic_data(a)
        past_word = ([a]*length if endpoint == "ordinary" else [1, a-1]+[a]*length)
        for future_word in ([a+1, 17], [a-1, 1, 31], [a, a, a+1, 11]):
            y = prepend_word(future_word, beta)
            alpha = prepend_word(past_word+[a], y)
            n = len(past_word)-1
            out = actual_triple(alpha, n)
            x = prepend_word(past_word[::-1], Q(0))
            check(out["a"] == a and out["x"] == x and out["y"] == y,
                  "actual_coordinate_recovery")
            D = a+x+y
            check(out["theta"] == [x*(a+y)/D, 1/D, y*(a+x)/D], "actual_three_error_identities")
            F, G = min(out["theta"]), max(out["theta"])
            rad = max(abs(x-beta), abs(y-beta))
            check(c-F > kap*rad and G-c > lam*rad, "actual_both_strict_stabilities")

    # Sharp localization cutoffs and explicit BAD actual digit-window witnesses.
    windows = []
    for a in range(2, 8):
        beta, c, kap, lam = metallic_data(a)
        for r in range(1, 6):
            w = window_thresholds(a, r)
            L, U = w["L"], w["U"]
            B, A = w["F_must_exceed"], w["G_must_be_below"]
            check(B < c < A, "window_strict_gaps")
            delta = min(beta-L, U-beta)
            check(c-B >= kap*delta and A-c >= lam*delta, "window_vs_global_thresholds")
            for i, j in product(range(9), repeat=2):
                x, y = Q(i, 8), Q(j, 8)
                if not (L < x < U and L < y < U):
                    F, G = envelopes(a, x, y)
                    check(F <= B and G >= A, "window_bad_region_grid")
            for obj in ("F", "G"):
                _, theta, cutoff = bad_future_example(a, r, obj)
                check(abs(theta-cutoff) < Q(1, 10**6), "actual_bad_window_sharpness_approach")
                check((theta < cutoff if obj == "F" else theta > cutoff),
                      "actual_bad_window_side")
            if a == 2:
                windows.append({**w, "old_sufficient_deficit": kap*delta,
                                "sharp_deficit": c-B, "sharp_maximum_excess": A-c})

    # The optimal G coefficient is approached, not attained away from the center.
    sharpness = []
    for a in range(2, 7):
        beta, c, _, lam = metallic_data(a)
        ratios = []
        for j in range(1, 7):
            x = tail_iter(a, 2*j, Q(0))
            eta = Q(1, 100*x.denominator**4)
            y = 1/(a+x) + Quad(0, eta, beta.d)
            alpha = prepend_word([a]*(2*j+1), y)
            out = actual_triple(alpha, 2*j-1)
            rad = max(abs(x-beta), abs(y-beta))
            ratio = (max(out["theta"])-c)/rad
            check(ratio > lam, "upper_actual_sharpness_strict")
            if ratios:
                check(ratio < ratios[-1], "upper_actual_sharpness_decreasing_samples")
            ratios.append(ratio)
        check(ratios[-1] < lam*Q(1001, 1000), "upper_actual_sharpness_close")
        sharpness.append({"a": a, "lambda": lam,
                          "ratios_j_1_to_6": ratios})

    # Exact convergence identity and stronger two-sided gap estimates.
    for a, r, e in product(range(2, 8), range(9), "LH"):
        beta, _, _, _ = metallic_data(a)
        pprev, p = Q(1), Q(0)
        for _ in range(r):
            pprev, p = p, a*p+pprev
        pnext = a*p+pprev
        for t in (Q(0), Q(1, a+1), Q(1, a), Q(1)):
            image = tail_iter(a, r, t)
            check(image == (pprev*t+p)/(p*t+pnext), "continuant_iteration_identity")
            check(abs(image-beta) == abs(t-beta)/((p*t+pnext)*(p*beta+pnext)),
                  "exact_convergence_identity")
    for a, r, s, e, f in product(range(2, 6), range(4), range(4), "LH", "LH"):
        beta, c, kap, lam = metallic_data(a)
        data = run_bounds(a, r, s, e, f)
        dx = [abs(t-beta) for t in data["past_cell"]]
        dy = [abs(t-beta) for t in data["future_cell"]]
        eps, dist = max(dx)+max(dy), max(min(dx), min(dy))
        check(kap*dist <= c-data["minimum_supremum"] <= eps,
              "sharper_two_sided_minimum_run_gaps")
        check(lam*dist <= data["maximum_infimum"]-c <= eps,
              "sharper_two_sided_maximum_run_gaps")

    # Wrong variants must demonstrably fail; tests survive python -O.
    beta, c, kap, lam = metallic_data(2)
    F, G = envelopes(2, Q(1, 2), Q(1, 2))
    corners = [envelopes(2, Q(i), Q(j)) for i, j in product((0, 1), repeat=2)]
    check(F > max(v[0] for v in corners), "negative_controls_rejected", "arbitrary F corners")
    check(G < min(v[1] for v in corners), "negative_controls_rejected", "arbitrary G corners")
    F, _ = envelopes(2, Q(1), Q(1, 3))
    check(c-F < kap*Q(101, 100)*(1-beta), "negative_controls_rejected", "inflated kappa")
    x = beta-Q(1, 10**6); y = 1/(2+x)
    check(envelopes(2, x, y)[1]-c < lam*Q(101, 100)*(beta-x),
          "negative_controls_rejected", "inflated lambda")
    b1, c1, _, lam1 = metallic_data(1)
    check(Q(1, 2)-c1 < lam1*b1, "negative_controls_rejected", "lambda formula at a=1")
    boundary = actual_triple(prepend_word([1, 1, 2], beta), 1)
    check(boundary["x"] == Q(1, 2) and boundary["digits"][2] != 2,
          "negative_controls_rejected", "canonicalization changes finite departure")
    _, theta, B = bad_future_example(2, 1, "F")
    check(theta > B-Q(1, 10**6), "negative_controls_rejected", "overstrong digit cutoff")
    check(window_thresholds(2, 1)["F_must_exceed"] == Q(10, 29) and
          window_thresholds(2, 1)["G_must_be_below"] == Q(21, 58), "silver_window_example")

    result = {"status": "PASS", "scope": "finite exact independent replay; not a Lean build",
              "python": platform.python_version(), "optimized_mode": bool(sys.flags.optimize),
              "arithmetic": "Fraction and exact real quadratic fields; standard library only",
              "checks": dict(sorted(counts.items())), "total_checks": sum(counts.values()),
              "silver_window_examples": serial(windows),
              "upper_actual_sharpness_examples": serial(sharpness)}
    text = json.dumps(result, indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text+"\n", encoding="utf-8")
    print(json.dumps({k:v for k,v in result.items() if not k.endswith("examples")}, indent=2))

if __name__ == "__main__":
    main()
