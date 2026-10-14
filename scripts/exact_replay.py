"""Exact finite audits of the unrestricted written cylinder theorems.

All arithmetic here is rational. The general rectangle optimizer enumerates
boundary crossings independently of the four-corner run-cell formula.
No finite grid is represented as a proof over all real tails/run lengths.
Checks remain active under python -O. No external data or solver is used.
"""

from __future__ import annotations

from fractions import Fraction as Q
from itertools import combinations_with_replacement, product


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def coefficients(a, x, y):
    """Return the actual three coefficient formulas, in chronological order."""
    a, x, y = Q(a), Q(x), Q(y)
    require(a >= 2 and 0 <= x <= 1 and 0 <= y <= 1, "invalid coordinate")
    denominator = a + x + y
    return (x * (a + y) / denominator, 1 / denominator,
            y * (a + x) / denominator)


def transform(a, x, count):
    require(count >= 0, "negative run")
    for _ in range(count):
        x = 1 / (Q(a) + x)
    return x


def continuants(a, count):
    """P_{-1},P_0,...,P_{count+1}, indexed by k+1."""
    values = [1, 0]
    for _ in range(count + 1):
        values.append(a * values[-1] + values[-2])
    return values


def run_cell(a, count, kind):
    require(a >= 2 and count >= 0 and kind in {"L", "H"}, "invalid cell")
    tails = (Q(1, a), Q(1)) if kind == "L" else (Q(0), Q(1, a + 1))
    return tuple(sorted(transform(a, x, count) for x in tails))


def cell_via_continuants(a, count, kind):
    p = continuants(a, count + 1)
    pm, pc, pp = p[count], p[count + 1], p[count + 2]
    tails = (Q(1, a), Q(1)) if kind == "L" else (Q(0), Q(1, a + 1))
    return tuple(sorted((pm * x + pc) / (pc * x + pp) for x in tails))


def validate_box(box):
    left, right = map(Q, box)
    require(0 <= left <= right <= 1, "invalid rectangle interval")
    return left, right


def contains_fixed_point(a, box):
    left, right = validate_box(box)
    return left * (a + left) <= 1 <= right * (a + right)


def boundary_candidates(a, first, second):
    """Corners and every boundary intersection with x=T(y) or y=T(x)."""
    left, right = validate_box(first)
    low, high = validate_box(second)
    points = set(product((left, right), (low, high)))
    for x in (left, right):
        candidates = [1 / (a + x)]
        if x:
            candidates.append(1 / x - a)
        points.update((x, y) for y in candidates if low <= y <= high)
    for y in (low, high):
        candidates = [1 / (a + y)]
        if y:
            candidates.append(1 / y - a)
        points.update((x, y) for x in candidates if left <= x <= right)
    return points


def finite_extrema(a, points):
    values = [(min(coefficients(a, x, y)), max(coefficients(a, x, y)), x, y)
              for x, y in points]
    upper = max(v[0] for v in values)
    lower = min(v[1] for v in values)
    return (upper, lower,
            {(v[2], v[3]) for v in values if v[0] == upper},
            {(v[2], v[3]) for v in values if v[1] == lower})


def rectangle_extrema(a, first, second):
    """For rational boxes excluding (beta,beta), every optimum is rational.

    None explicitly identifies the metallic case; it is never approximated
    by a rational or silently excluded from the theorem.
    """
    if contains_fixed_point(a, first) and contains_fixed_point(a, second):
        return None
    return finite_extrema(a, boundary_candidates(a, first, second))


def run_extrema(a, r, s, left_kind, right_kind):
    first, second = run_cell(a, r, left_kind), run_cell(a, s, right_kind)
    return finite_extrema(a, set(product(first, second)))


def rejects(thunk):
    try:
        thunk()
    except (RuntimeError, ValueError, ZeroDivisionError):
        return True
    return False


def main():
    counts = {"cell_identities": 0, "cell_disjointness": 0,
              "run_rectangles": 0, "grid_points": 0,
              "general_boxes": 0, "negative_controls": 0}
    # Every integer a=2..8, run length 0..12, and the two deviation types.
    for a in range(2, 9):
        cells = []
        for r, kind in product(range(13), ("L", "H")):
            cell = run_cell(a, r, kind)
            require(cell == cell_via_continuants(a, r, kind), "continuant endpoints")
            require(not contains_fixed_point(a, cell), "terminated cell contains beta")
            require(tuple(sorted(1 / (a + x) for x in cell)) ==
                    run_cell(a, r + 1, kind), "shift identity")
            cells.append(cell)
            counts["cell_identities"] += 1
        for i, first in enumerate(cells):
            for second in cells[i + 1:]:
                require(min(first[1], second[1]) <= max(first[0], second[0]),
                        "distinct run interiors overlap")
                counts["cell_disjointness"] += 1

        for r, s, left_kind, right_kind in product(range(13), range(13), "LH", "LH"):
            first = run_cell(a, r, left_kind)
            second = run_cell(a, s, right_kind)
            result = run_extrema(a, r, s, left_kind, right_kind)
            independent = rectangle_extrema(a, first, second)
            require(independent is not None and result == independent,
                    "four corners disagree with all boundary crossings")
            upper, lower, maximizers, minimizers = result
            require(len(maximizers) == len(minimizers) == 1, "nonunique extremizer")
            require((a*a+4)*upper*upper < 1 < (a*a+4)*lower*lower,
                    "no strict improvement over the classical constant")
            for i, j in product(range(3), repeat=2):
                x = first[0] + Q(i, 2) * (first[1] - first[0])
                y = second[0] + Q(j, 2) * (second[1] - second[0])
                triple = coefficients(a, x, y)
                require(min(triple) <= upper and max(triple) >= lower,
                        "rational run-grid violation")
                counts["grid_points"] += 1
            counts["run_rectangles"] += 1

    # Independent finite diagnostics on general boxes, including degeneracies
    # and boxes containing the irrational metallic optimum.
    intervals = list(combinations_with_replacement([Q(k, 6) for k in range(7)], 2))
    for a, first, second in product((2, 3), intervals, intervals):
        result = rectangle_extrema(a, first, second)
        for i, j in product(range(5), repeat=2):
            x = first[0] + Q(i, 4) * (first[1] - first[0])
            y = second[0] + Q(j, 4) * (second[1] - second[0])
            triple = coefficients(a, x, y)
            if result is None:
                require((a*a+4)*min(triple)**2 <= 1 <= (a*a+4)*max(triple)**2,
                        "classical metallic bound")
            else:
                require(min(triple) <= result[0] and max(triple) >= result[1],
                        "general rectangle grid violation")
        counts["general_boxes"] += 1

    # Hand-readable exact anchors, not inferred from the tested implementation.
    anchors = {
        (0, 0, "L", "L"): (Q(1, 3), Q(5, 12)),
        (0, 0, "L", "H"): (Q(3, 10), Q(2, 5)),
        (0, 0, "H", "H"): (Q(7, 24), Q(3, 8)),
        (1, 1, "L", "L"): (Q(12, 35), Q(5, 14)),
        (1, 1, "H", "H"): (Q(7, 20), Q(51, 140)),
        (2, 2, "H", "H"): (Q(287, 816), Q(17, 48)),
    }
    for args, values in anchors.items():
        require(run_extrema(2, *args)[:2] == values, "exact anchor mismatch")

    arbitrary_first = (Q(1, 4), Q(3, 8))
    arbitrary_second = (Q(1, 2), Q(3, 4))
    corner_only = finite_extrema(2, set(product(arbitrary_first, arbitrary_second)))
    full_rectangle = rectangle_extrema(2, arbitrary_first, arbitrary_second)
    controls = [
        rejects(lambda: run_cell(2, -1, "L")),
        rejects(lambda: run_cell(2, 1, "wrong")),
        rejects(lambda: coefficients(2, Q(-1, 3), Q(1, 2))),
        rejects(lambda: rectangle_extrema(2, (Q(3, 4), Q(1, 4)), (0, 1))),
        # Dropping parity changes the ordered endpoints.
        run_cell(2, 1, "L") != (Q(2, 5), Q(1, 3)),
        # General rectangles need crossing candidates: four corners alone fail.
        corner_only[0] < full_rectangle[0],
        # Prescribing only a minimum run length retains the fixed point.
        contains_fixed_point(2, tuple(sorted((transform(2, Q(0), 5),
                                             transform(2, Q(1), 5))))),
        # A wrong upper bound is rejected by an explicit rational witness.
        min(coefficients(2, Q(501, 1000), Q(501, 1000))) > Q(3, 10),
        # A corner in the relaxation is rational, hence not an infinite future.
        run_extrema(2, 0, 0, "L", "L")[2] == {(Q(1, 2), Q(1, 2))},
    ]
    for i, passed in enumerate(controls):
        require(passed, f"negative control {i} failed to detect false claim")
        counts["negative_controls"] += 1
    print("Exact rational audits:", counts)
    print("PASS: finite replay passed; unrestricted formal coverage is recorded in Verification.md.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
