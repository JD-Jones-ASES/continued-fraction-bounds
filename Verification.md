# Formal contract and verification

The authoritative contract is [Challenge.lean](Challenge.lean), selected
by [comparator.json](comparator.json). Its definitions use Mathlib's
continued fraction of the actual input real number. The Solution imports
the implementation; it never imports Challenge placeholders.

The compared statements cover the ordinary-convergent bridge, the unique
four-corner extrema and rational constants, strict actual-run bounds,
epsilon-sharpness in every exact digit class, global inverse stability,
its complete equality locus, and optimality both on the square and over
actual triples. Additional contracts give exact level-set regions,
near-extremizer localization, classical equality loci, and the silver
stability coefficient. The finite index may vary in run sharpness.

The written proof and applications include broader rectangle and boundary
statements. Only declarations explicitly present in the comparison
configuration constitute the recorded formal contract. Supporting Lean
theorems are checked by the package build and the namespace-wide axiom audit.

## Reproduction

The project pins Lean `v4.35.0-rc3` and canonical Mathlib commit
`a98628e16c11f5167f16124105ddce53efa9bfe5` in its committed manifest.

```bash
lake exe cache get
lake build
python3 scripts/check_sources.py
python3 scripts/audit_axioms.py
python3 scripts/check_negative_controls.py
python3 scripts/exact_replay.py
python3 -O scripts/exact_replay.py
python3 scripts/independent_replay.py
python3 -O scripts/independent_replay.py
```

The rational replay freshly evaluates 4,732 run rectangles, 1,568 general
rectangles, cell identities and disjointness, and nine negative controls.
The independent quadratic-field replay performs 10,525 exact checks,
including actual irrational continued fractions, endpoint alternatives,
stability equality configurations, and five rejected false claims.
These finite checks have their stated finite scope. The Lean proofs
establish the unrestricted quantified formal statements.

Four Lean controls compile their correct statements and require a proof
error for each corrupted version: a chronological coefficient index,
an increased stability coefficient, an incorrect mixed corner constant,
and the reversed finite endpoint `[0;1,1]`. The mathematical replays also
reject corner-only optimization for arbitrary rectangles and replacement
of exact runs by minimum-run information.

## Exact-commit Linux checks

The verification workflow checks the selected full commit SHA before
building. It runs the complete build, source checks, metadata validation,
all compared and public supporting theorem axiom audits, exact replays,
and corruption controls. Comparator checks the Challenge/Solution
statements and definitions; the solution closure is replayed with Lean,
NanoDa and con-ron. A separate fresh runner rebuilds the project.

```bash
python3 scripts/verify_kernels.py
```

This command requires Linux, the pinned checkers, and a clean committed
checkout. It invalidates stale success records before running and saves
the candidate SHA, tool hashes, manifests, logs and kernel outcomes in
`.lake/verification/`. CI preserves these as exact-commit artifacts.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Challenge statement placeholders are intentional; they are not allowed
in the implementation or its proved declarations.

The metadata workflow validates the official v0.4 schema, Palomar's
required fields and normalized provenance, and the submission form's
YAML parser. MSC codes are quoted strings. Verification does not imply
registry submission, registration, novelty, or specialist peer review.
