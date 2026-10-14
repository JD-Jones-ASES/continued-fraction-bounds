#!/usr/bin/env python3
"""Independent exact continued-fraction and stability replay.

Run: python3 scripts/independent_replay.py

Uses only the Python standard library; imports no companion probe code.
Arithmetic is exact in Q(sqrt(2)). Finite checks replay formulas, actual
continued-fraction reconstruction, endpoint distinctions and selected
extremizing sequences. They are not a proof of the unrestricted theorems
or a novelty certificate. The unrestricted arguments are given in Proof.md.
"""

from dataclasses import dataclass
from fractions import Fraction as Q
from functools import total_ordering
from itertools import product
import json


@total_ordering
@dataclass(frozen=True)
class S:
    """An exact a + b sqrt(2), with a,b rational."""

    a: Q = Q(0)
    b: Q = Q(0)

    def __post_init__(self):
        object.__setattr__(self, "a", Q(self.a))
        object.__setattr__(self, "b", Q(self.b))

    @staticmethod
    def of(value):
        return value if isinstance(value, S) else S(value)

    def __add__(self, other):
        other = S.of(other)
        return S(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return S(-self.a, -self.b)

    def __sub__(self, other):
        return self + (-S.of(other))

    def __rsub__(self, other):
        return S.of(other) + (-self)

    def __mul__(self, other):
        other = S.of(other)
        return S(self.a * other.a + 2 * self.b * other.b,
                 self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = S.of(other)
        norm = other.a * other.a - 2 * other.b * other.b
        if norm == 0:
            raise ZeroDivisionError("zero quadratic-field denominator")
        return self * S(other.a / norm, -other.b / norm)

    def __rtruediv__(self, other):
        return S.of(other) / self

    def __pow__(self, exponent):
        if not isinstance(exponent, int):
            raise TypeError("only integer powers are supported")
        if exponent < 0:
            return (1 / self) ** (-exponent)
        answer, base = S(1), self
        while exponent:
            if exponent & 1:
                answer *= base
            base *= base
            exponent //= 2
        return answer

    def sign(self):
        if self.b == 0:
            return (self.a > 0) - (self.a < 0)
        if self.a == 0:
            return (self.b > 0) - (self.b < 0)
        if (self.a > 0) == (self.b > 0):
            return 1 if self.a > 0 else -1
        dominant = self.a if self.a * self.a > 2 * self.b * self.b else self.b
        return 1 if dominant > 0 else -1

    def __eq__(self, other):
        if not isinstance(other, (S, Q, int)):
            return NotImplemented
        other = S.of(other)
        return self.a == other.a and self.b == other.b

    def __lt__(self, other):
        return (self - other).sign() < 0

    def __abs__(self):
        return -self if self.sign() < 0 else self


SQRT2 = S(0, 1)
BETA = SQRT2 - 1
HURWITZ = SQRT2 / 4
KAPPA = (2 * SQRT2 - 1) / 20
COUNTS = {}


def check(category, condition, detail=""):
    if not condition:
        raise AssertionError(f"{category}: {detail}")
    COUNTS[category] = COUNTS.get(category, 0) + 1


def reject(name, false_claim):
    if false_claim:
        raise AssertionError(f"negative control unexpectedly survived: {name}")
    COUNTS["negative_controls_rejected"] = COUNTS.get("negative_controls_rejected", 0) + 1


def t_iter(value, count):
    for _ in range(count):
        value = 1 / (2 + value)
    return value


def coeffs(x, y):
    denominator = 2 + x + y
    return (x * (2 + y) / denominator, 1 / denominator,
            y * (2 + x) / denominator)


def cf_value(digits):
    value = Q(0)
    for digit in reversed(digits):
        value = 1 / (digit + value)
    return value


def finite_cf(value):
    digits = []
    while value:
        reciprocal = 1 / value
        digit = reciprocal.numerator // reciprocal.denominator
        digits.append(digit)
        value = reciprocal - digit
    return digits


def field_floor(value):
    if value < 0:
        raise ValueError("this replay only floors nonnegative values")
    low, high = 0, 1
    while value >= high:
        low, high = high, 2 * high
    while high - low > 1:
        middle = (low + high) // 2
        if value >= middle:
            low = middle
        else:
            high = middle
    return low


def cf_prefix(value, length):
    digits = []
    for _ in range(length):
        value = 1 / value
        digit = field_floor(value)
        digits.append(digit)
        value -= digit
    return digits


def past_class(digits):
    count = 0
    for digit in digits:
        if digit != 2:
            return ("below" if digit == 1 else "above", count)
        count += 1
    return ("exhausted", count)


def endpoints(kind):
    return (Q(1, 2), Q(1)) if kind == "below" else (Q(0), Q(1, 3))


def past_digits(run, kind, tail):
    # Retain the actual terminal (1,1), rather than canonicalizing to (2).
    tail_digits = [1, 1] if kind == "below" and tail == Q(1, 2) else finite_cf(tail)
    return [2] * run + tail_digits


def reconstruct(past, y):
    """Build alpha, then compute its errors directly from integer convergents."""
    initial = list(reversed(past))
    p_previous, p_current = 1, 0
    q_previous, q_current = 0, 1
    for digit in initial:
        p_previous, p_current = p_current, digit * p_current + p_previous
        q_previous, q_current = q_current, digit * q_current + q_previous
    alpha = (p_current * (2 + y) + p_previous) / (q_current * (2 + y) + q_previous)
    p_next, q_next = 2 * p_current + p_previous, 2 * q_current + q_previous
    denominators = (q_previous, q_current, q_next)
    numerators = (p_previous, p_current, p_next)
    errors = tuple(abs(q * alpha - p) for p, q in zip(numerators, denominators))
    theta = tuple(q * error for q, error in zip(denominators, errors))
    x = Q(q_previous, q_current)
    check("actual_cf", alpha.b != 0 and y.b != 0, "irrationality")
    check("actual_cf", cf_prefix(alpha, len(initial) + 1) == initial + [2], "initial digits")
    check("actual_cf", x == cf_value(past), "reversed finite past")
    check("actual_cf", errors[2] / errors[1] == y, "future error ratio")
    check("actual_cf", errors[0] == 2 * errors[1] + errors[2], "error recurrence")
    check("actual_cf", q_previous * errors[1] + q_current * errors[0] == 1, "cross identity")
    check("actual_cf", theta == tuple(S.of(z) for z in coeffs(x, y)), "all three theta formulas")
    u, v = x * theta[1], y * theta[1]
    check("deficit_identity", 2 * theta[1] * (theta[0] + theta[2]) + 4 * theta[1] ** 2 + (u - v) ** 2 == 1)
    return x, theta


def replay_endpoints():
    pell = [0, 1]
    for _ in range(12):
        pell.append(2 * pell[-1] + pell[-2])
    cells = []
    for run in range(9):
        previous = 1 if run == 0 else pell[run - 1]
        current, following = pell[run], pell[run + 1]
        expected = (Q(current, following), Q(previous + 3 * current, current + 3 * following),
                    Q(following, pell[run + 2]), Q(previous + current, current + following))
        actual = tuple(t_iter(z, run) for z in (Q(0), Q(1, 3), Q(1, 2), Q(1)))
        check("endpoint_formulas", actual == expected)
        a, b, c, d = actual
        check("run_parity", a < b < BETA < c < d if run % 2 == 0 else d < c < BETA < b < a)
        check("endpoint_alternatives", cf_value([2] * run + [1, 1]) == cf_value([2] * (run + 1)) == c)
        if run:
            check("endpoint_alternatives", cf_value([2] * run + [1]) == cf_value([2] * (run - 1) + [3]) == d)
        for kind in ("below", "above"):
            interval = tuple(sorted(t_iter(z, run) for z in endpoints(kind)))
            cells.append((run, kind, interval))
            shifted = tuple(sorted(t_iter(z, 1) for z in interval))
            check("shift_relation", shifted == tuple(sorted(t_iter(z, run + 1) for z in endpoints(kind))))
    for i, left in enumerate(cells):
        for right in cells[i + 1:]:
            check("disjoint_interiors", max(left[2][0], right[2][0]) >= min(left[2][1], right[2][1]))
    check("endpoint_class", past_class([1, 1]) == ("below", 0))
    reject("canonicalizing 1/2 preserves the below-2 class",
           past_class(finite_cf(Q(1, 2))) == ("below", 0))


def replay_sharpness():
    for r, s, past_kind, future_kind in product(range(5), range(5), ("below", "above"), ("below", "above")):
        corners = []
        for z, w in product(endpoints(past_kind), endpoints(future_kind)):
            x_star, y_star = t_iter(z, r), t_iter(w, s)
            theta = coeffs(x_star, y_star)
            corners.append((z, w, x_star, y_star, min(theta), max(theta)))
        upper = max(row[4] for row in corners)
        lower = min(row[5] for row in corners)
        selected = [row for row in corners if row[4] == upper or row[5] == lower]
        eta = (1 + BETA) / 2 if future_kind == "below" else BETA / 2
        for z_star, w_star, x_star, y_star, f_star, g_star in selected:
            distances = []
            for scale in (16, 64, 256, 1024):
                z = Q(1, scale + 3) if z_star == 0 else z_star
                w = (1 - Q(1, scale)) * w_star + eta / scale
                past = past_digits(r, past_kind, z)
                y = t_iter(w, s)
                check("symbolic_class", past_class(past) == (past_kind, r))
                future_digits = cf_prefix(y, s + 1)
                check("symbolic_class", future_digits[:s] == [2] * s)
                check("symbolic_class", future_digits[s] == 1 if future_kind == "below" else future_digits[s] >= 3)
                x, theta = reconstruct(past, y)
                check("strict_finite_future", min(theta) < upper and max(theta) > lower)
                distance = abs(S(x) - x_star) + abs(y - y_star)
                distances.append(distance)
                # Each coefficient is 1-Lipschitz in each coordinate on [0,1]^2.
                if f_star == upper:
                    check("extremizing_approach", 0 < upper - min(theta) <= distance)
                if g_star == lower:
                    check("extremizing_approach", 0 < max(theta) - lower <= distance)
            check("extremizing_approach", all(a > b for a, b in zip(distances, distances[1:])))


def replay_infinite_future():
    for run in range(9):
        for kind, past in (("below", [2] * run + [1, 1]), ("above", [2] * run + [3])):
            x, theta = reconstruct(past, BETA)
            expected = t_iter(Q(1, 2) if kind == "below" else Q(1, 3), run)
            check("infinite_future_equality", x == expected and past_class(past) == (kind, run))
            denominator = 2 + x + BETA
            f = x / (BETA * denominator) if x <= BETA else 1 / denominator
            g = 1 / denominator if x <= BETA else x / (BETA * denominator)
            check("infinite_future_equality", min(theta) == f and max(theta) == g)
        x, theta = reconstruct([2] * run, BETA)
        expected_f = (1 - BETA ** (2 * run + 2)) / (2 * SQRT2) if run % 2 else (1 - BETA ** (2 * run)) / (2 * SQRT2)
        expected_g = (1 + BETA ** (2 * run)) / (2 * SQRT2) if run % 2 else (1 + BETA ** (2 * run + 2)) / (2 * SQRT2)
        check("all_two_formulas", min(theta) == expected_f and max(theta) == expected_g)
        check("all_two_formulas", min(theta) < HURWITZ < max(theta))
        theta_n = (1 - (-1) ** (run + 1) * BETA ** (2 * run + 2)) / (2 * SQRT2)
        check("all_two_formulas", theta[1] == theta_n)
    reject("signless metallic coefficient formula at index zero",
           BETA == (1 - BETA ** 2) / (2 * SQRT2))


def replay_exhausted_past():
    for n, s, kind in product(range(9), range(5), ("below", "above")):
        past = [2] * n
        x = cf_value(past)
        lo, hi = sorted(t_iter(z, s) for z in endpoints(kind))
        clamp = lambda z: max(lo, min(hi, z))
        f_y = lo if n == 0 else clamp(max(1 / x - 2, 1 / (2 + x)))
        g_y = clamp(Q(1, 2) if n == 0 else min(1 / x - 2, 1 / (2 + x)))
        upper, lower = min(coeffs(x, f_y)), max(coeffs(x, g_y))
        eta = (1 + BETA) / 2 if kind == "below" else BETA / 2
        for target in (f_y, g_y):
            tail_target = target
            for _ in range(s):
                tail_target = 1 / tail_target - 2
            tail = Q(63, 64) * tail_target + eta / 64
            _, theta = reconstruct(past, t_iter(tail, s))
            check("exhausted_past", min(theta) == 0 if n == 0 else min(theta) < upper)
            check("exhausted_past", max(theta) > lower)


def replay_stability():
    equality_points = ((S(1), S(Q(1, 3))), (S(Q(1, 3)), S(1)), (BETA, BETA))
    for i, j in product(range(25), repeat=2):
        x, y = S(Q(i, 24)), S(Q(j, 24))
        radius = max(abs(x - BETA), abs(y - BETA))
        slack = HURWITZ - min(coeffs(x, y)) - KAPPA * radius
        check("stability_grid", slack >= 0)
        check("stability_grid", (slack == 0) == ((x, y) in equality_points))
    for x, y in equality_points:
        check("stability_equality", HURWITZ - min(coeffs(x, y)) == KAPPA * max(abs(x - BETA), abs(y - BETA)))
    x, y = equality_points[0]
    reject("strictly larger global stability constant",
           HURWITZ - min(coeffs(x, y)) >= (KAPPA + Q(1, 1000)) * max(abs(x - BETA), abs(y - BETA)))


def replay_missing_hypothesis():
    # Unimodular previous pairs and alpha between them do not enforce
    # the sign/error recursion for an arbitrarily chosen next digit.
    alpha = S(Q(5, 13)) + BETA / 1000
    partial_quotient = 10
    numerators, denominators = (1, 1, 11), (2, 3, 32)
    errors = tuple(abs(q * alpha - p) for p, q in zip(numerators, denominators))
    theta = tuple(q * error for q, error in zip(denominators, errors))
    check("missing_hypothesis_witness", Q(1, 3) < alpha < Q(1, 2))
    check("missing_hypothesis_witness", abs(numerators[1] * denominators[0] - numerators[0] * denominators[1]) == 1)
    check("missing_hypothesis_witness", numerators[2] == partial_quotient * numerators[1] + numerators[0]
          and denominators[2] == partial_quotient * denominators[1] + denominators[0])
    check("missing_hypothesis_witness", denominators[0] * errors[1] + denominators[1] * errors[0] == 1)
    check("missing_hypothesis_witness", (partial_quotient ** 2 + 4) * min(theta) ** 2 > 1)
    reject("bracketing alone supplies alternating error recurrence",
           errors[0] == partial_quotient * errors[1] + errors[2])
    reject("arbitrary unimodular step satisfies generalized Borel bound",
           (partial_quotient ** 2 + 4) * min(theta) ** 2 < 1)


def main():
    check("field_sanity", SQRT2 ** 2 == 2 and BETA * (2 + BETA) == 1)
    check("field_sanity", S(3, -2) > 0 and S(1, -1) < 0 and 1 / SQRT2 == SQRT2 / 2)
    replay_endpoints()
    replay_sharpness()
    replay_infinite_future()
    replay_exhausted_past()
    replay_stability()
    replay_missing_hypothesis()
    print(json.dumps({"status": "PASS", "arithmetic": "exact Q(sqrt(2)); standard library only",
                      "scope": "finite independent replay; see Verification.md for unrestricted formal coverage",
                      "checks": COUNTS, "total_checks": sum(COUNTS.values())}, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
