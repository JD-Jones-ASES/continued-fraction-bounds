"""Exact continued-fraction bound calculator, using exact rational and quadratic arithmetic.

Python >=3.10, standard library only. Public inputs use integers/Fraction.
The general-rectangle evaluator enumerates corners and switching-curve/edge
intersections (and the metallic point), rather than the formal clipping
implementation. It is an executable mathematical reference, not Lean-verified.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as Q
from itertools import product
from quadratic import Quad


def _parameter(a, lower=1):
    if not isinstance(a, (int, Q)) or isinstance(a, bool):
        raise TypeError("use int or fractions.Fraction, not float")
    a = Q(a)
    if a < lower:
        raise ValueError(f"a must be at least {lower}")
    return a


def _length(r):
    if not isinstance(r, int) or isinstance(r, bool) or r < 0:
        raise ValueError("run length must be a nonnegative integer")


def metallic_data(a):
    """Return beta,c,kappa,lambda; the stability assertions require a >= 2."""
    a = _parameter(a)
    p, q = a.numerator, a.denominator
    d = p*p + 4*q*q
    beta = Quad(Q(-p, 2*q), Q(1, 2*q), d)
    c = Quad(0, Q(q, d), d)
    kappa = c*(a+1-beta)/(1+(a+1)**2)
    lam = a*beta/(a*a+4)
    return beta, c, kappa, lam


def envelopes(a, x, y):
    a = _parameter(a)
    if any(not isinstance(t, (int, Q, Quad)) or isinstance(t, bool) for t in (x, y)):
        raise TypeError("coordinates must be exact rational/quadratic numbers")
    if not (0 <= x <= 1 and 0 <= y <= 1):
        raise ValueError("coordinates must be in [0,1]")
    den = a+x+y
    nums = (Q(1), x*(a+y), y*(a+x))
    return min(nums)/den, max(nums)/den


def tail_iter(a, r, t):
    a = _parameter(a)
    _length(r)
    if not isinstance(t, (int, Q, Quad)) or isinstance(t, bool):
        raise TypeError("tail must be an exact rational/quadratic number")
    if not 0 <= t <= 1:
        raise ValueError("tail must be in [0,1]")
    if isinstance(t, int):
        t = Q(t)
    for _ in range(r):
        t = 1/(a+t)
    return t


def constant_cell(a, r):
    return tuple(sorted((tail_iter(a, r, Q(0)), tail_iter(a, r, Q(1)))))


def run_cell(a, r, departure):
    a = _parameter(a)
    if a <= 1:
        raise ValueError("exact low/high run cells require a > 1")
    if departure == "L":
        endpoints = (1/a, Q(1))
    elif departure == "H":
        endpoints = (Q(0), 1/(a+1))
    else:
        raise ValueError("departure must be 'L' or 'H'")
    return tuple(sorted(tail_iter(a, r, t) for t in endpoints))


def run_bounds(a, r, s, e, f):
    xs, ys = run_cell(a, r, e), run_cell(a, s, f)
    rows = [(x, y, *envelopes(a, x, y)) for x, y in product(xs, ys)]
    lo, hi = max(rows, key=lambda z: z[2]), min(rows, key=lambda z: z[3])
    return {"minimum_supremum": lo[2], "maximum_infimum": hi[3],
            "minimum_optimizer": lo[:2], "maximum_optimizer": hi[:2],
            "past_cell": xs, "future_cell": ys,
            "corner_evaluations": [
                {"x": x, "y": y, "minimum": lower, "maximum": upper}
                for x, y, lower, upper in rows]}


def fiber_profiles(a, t):
    """Return max_y F(a,t,y) and min_y G(a,t,y), as exact Fractions."""
    a = _parameter(a)
    if not isinstance(t, (int, Q)) or isinstance(t, bool):
        raise TypeError("t must be int or Fraction")
    t = Q(t)
    if not 0 <= t <= 1:
        raise ValueError("t must be in [0,1]")
    f = lambda z: z/(1+z*z)
    below_beta = t*(a+t) <= 1
    if t <= 1/(a+1):
        phi = t*(a+1)/(a+1+t)
    elif below_beta:
        phi = f(t)
    else:
        phi = f(a+t)
    if below_beta:
        psi = f(a+t)
    elif t <= 1/a:
        psi = f(t)
    else:
        psi = a*t/(a+t)
    return phi, psi


def window_thresholds(a, r):
    """Exact sharp open-cylinder tests: F > B_F or G < B_G."""
    a = _parameter(a, 2)
    _length(r)
    if r == 0:
        raise ValueError("digit-window thresholds here use r >= 1")
    L, U = constant_cell(a, r)
    phiL, psiL = fiber_profiles(a, L)
    phiU, psiU = fiber_profiles(a, U)
    return {"a": a, "r": r, "L": L, "U": U,
            "F_must_exceed": max(phiL, phiU),
            "G_must_be_below": min(psiL, psiU)}


def rectangle_optima(a, lx, ux, ly, uy):
    """Exact extrema via a finite switching-edge candidate set.

    Values/coordinates are Fractions except possibly the metallic center.
    This evaluator includes degenerate rectangles and axes.
    """
    a = _parameter(a)
    if any(not isinstance(t, (int, Q)) or isinstance(t, bool) for t in (lx, ux, ly, uy)):
        raise TypeError("rectangle endpoints must be int or Fraction")
    lx, ux, ly, uy = map(Q, (lx, ux, ly, uy))
    if not (0 <= lx <= ux <= 1 and 0 <= ly <= uy <= 1):
        raise ValueError("invalid rectangle in the unit square")
    candidates = list(product((lx, ux), (ly, uy)))
    for t in (lx, ux):
        for u in ([1/(a+t)] + ([1/t-a] if t else [])):
            if ly <= u <= uy:
                candidates.append((t, u))
    for t in (ly, uy):
        for u in ([1/(a+t)] + ([1/t-a] if t else [])):
            if lx <= u <= ux:
                candidates.append((u, t))
    b, c, _, _ = metallic_data(a)
    if lx <= b <= ux and ly <= b <= uy:
        candidates.append((b, b))
    rows = [(x, y, *envelopes(a, x, y)) for x, y in candidates]
    frow, grow = max(rows, key=lambda z: z[2]), min(rows, key=lambda z: z[3])
    return {"minimum_supremum": frow[2], "maximum_infimum": grow[3],
            "minimum_optimizer": frow[:2], "maximum_optimizer": grow[:2],
            "candidate_count": len(candidates)}


def prepend_word(word, tail):
    if not isinstance(tail, (int, Q, Quad)) or isinstance(tail, bool):
        raise TypeError("tail must be an exact rational/quadratic number")
    if not 0 <= tail <= 1:
        raise ValueError("tail must be in [0,1]")
    if isinstance(tail, int):
        tail = Q(tail)
    for b in reversed(word):
        if not isinstance(b, int) or isinstance(b, bool) or b < 1:
            raise ValueError("positive integer digits required")
        tail = 1/(b+tail)
    return tail


def actual_triple(alpha: Quad, n: int):
    """Extract actual floor digits/convergents, then the chronological triple."""
    _length(n)
    if not isinstance(alpha, Quad) or alpha.v == 0:
        raise ValueError("provide a genuinely irrational quadratic input")
    z = alpha
    pm2, pm1, qm2, qm1 = 0, 1, 1, 0
    digits, ps, qs, complete = [], [], [], []
    for _ in range(n+3):
        complete.append(z)
        digit = z.floor()
        digits.append(digit)
        p, q = digit*pm1+pm2, digit*qm1+qm2
        ps.append(p); qs.append(q)
        pm2, pm1, qm2, qm1 = pm1, p, qm1, q
        z = 1/(z-digit)
    theta = [qs[i]*abs(qs[i]*alpha-ps[i]) for i in range(n, n+3)]
    x = Q(qs[n], qs[n+1])
    y = complete[n+2]-digits[n+2]
    return {"digits": digits, "theta": theta, "x": x, "y": y,
            "a": digits[n+2], "denominators": qs}


def serial(value):
    if isinstance(value, Quad):
        return {"exact": value.exact_string(), "decimal": str(value.decimal())}
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, dict):
        return {k: serial(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [serial(v) for v in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    run = sub.add_parser("run", help="four-corner bounds for exact terminated runs")
    run.add_argument("a", type=int); run.add_argument("r", type=int); run.add_argument("s", type=int)
    run.add_argument("e", choices=["L", "H"]); run.add_argument("f", choices=["L", "H"])
    window = sub.add_parser("window", help="sharp digit-window cutoffs")
    window.add_argument("a", type=int); window.add_argument("r", type=int)
    args = parser.parse_args()
    try:
        if args.command == "run":
            if args.a < 2:
                raise ValueError("ordinary exact-run API requires integer a >= 2")
            out = {"schema": "continued-fraction-run-bounds-v1",
                   "input": {"a": args.a, "r": args.r, "s": args.s,
                             "past_departure": args.e, "future_departure": args.f},
                   **run_bounds(args.a, args.r, args.s, args.e, args.f)}
        else:
            out = window_thresholds(args.a, args.r)
    except (TypeError, ValueError) as exc:
        parser.error(str(exc))
    print(json.dumps(serial(out), indent=2))

if __name__ == "__main__":
    main()
