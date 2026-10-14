# Formal contract and verification

The authoritative contract is [Challenge.lean](Challenge.lean), selected
by [comparator.json](comparator.json). Its definitions use Mathlib's
continued fraction of the actual input real number. The Solution imports
the implementation; it never imports Challenge placeholders.

The compared statements cover:

- The actual ordinary-convergent bridge, rational finite past, and irrational future.
- Exact clipping formulas on every closed rectangle for real parameters at least one, including degenerate and zero-axis cases.
- Run-cell geometry at every length, unique four-corner extrema, strict actual-run bounds, and epsilon-sharpness in every exact digit class.
- Both global inverse inequalities for every real parameter at least two, their complete equality loci, and coefficient optimality over both the square and actual triples.
- Fixed-word future density, fixed-past sharp bounds, exhausted pasts, attained metallic-future boundary examples, and the exact alternating all-constant coefficients.
- Exact level-set regions, effective convergence and two-sided endpoint-distance bounds for the run gaps.
- Complete fiber profiles and sharp complement bounds for symmetric and asymmetric target rectangles; actual digit-window extraction, including the finite-past length condition.
- Optimal symmetric digit-window cutoffs over actual triples, with bad-future witnesses approaching each cutoff and the finite index allowed to vary.
- Executable rational Lean definitions proved equal to the real run constants and bounding actual triples.

For the two-sided exact-run sharpness the finite index may vary. When the entire finite past is prescribed, the index remains fixed. All declaration names and their independently compared definitions are listed in the comparison configuration. Supporting Lean theorems are checked by the complete build and the namespace-wide axiom audit. The optional empty-past convention and continuant closed forms in the written exposition are not separate compared contracts.

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
python3 scripts/extensions_replay.py
python3 -O scripts/extensions_replay.py
```

The rational replay freshly evaluates 4,732 run rectangles, 1,568 general
rectangles, cell identities and disjointness, and nine negative controls.
The independent quadratic-field replay performs 10,525 exact checks,
including actual irrational continued fractions, endpoint alternatives,
stability equality configurations, and five rejected false claims.
The extension replay performs 27,570 exact checks of the maximum inverse
estimate, fiber profiles, run gaps, window cutoffs, and actual bad-window
examples, including direct extraction of their violating future digits.
Its seven negative controls include an inflated maximum coefficient,
the invalid parameter-one extension, and a strengthened window cutoff.
All three replays are run normally and with Python optimizations enabled.
These finite checks have their stated finite scope. The Lean proofs
establish the unrestricted quantified formal statements.

Fifteen Lean controls compile their correct statements and require a proof error for each corrupted version. They cover chronological indexing, an increased stability coefficient, an incorrect mixed corner constant, the reversed finite endpoint `[0;1,1]`, exact versus minimum runs, a missing departure, rational-future nonattainment, both arbitrary-rectangle corner failures, and replacement of actual coordinates by disconnected variables. The additional controls corrupt the maximum coefficient, its parameter
hypothesis, its equality locus, a sharp silver window cutoff, and the
rational calculator's objective. The three exact replays add twenty-one
mathematical negative controls.

## Exact-commit Linux checks

The verification workflow runs on `main` and `codex/**` pushes, ordinary
pull requests, and explicit dispatch. It checks the selected full commit
SHA before building. Pull requests verify GitHub's proposed merge commit;
push runs verify the pushed commit itself. The workflow has read-only
repository permissions and does not use `pull_request_target`. It runs the complete build, source checks, metadata validation,
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
`.lake/verification/`. CI preserves these as exact-commit artifacts for 90 days. Completed
release evidence is also copied into the repository's
[verification evidence branch](https://github.com/JD-Jones-ASES/continued-fraction-bounds/tree/codex/verification-evidence),
under `commits/<full-source-sha>/`. Each directory includes the original
artifact ZIPs, their SHA-256 hashes, workflow/run identity, and a manifest.
This Git-tracked archive remains available independently of Actions
artifact expiry. Evidence is keyed to the source commit, rather than
claimed for the later archive commit.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Challenge statement placeholders are intentional; they are not allowed
in the implementation or its proved declarations.

The metadata workflow validates the official v0.4 schema, Palomar's
required fields and normalized provenance, and the submission form's
YAML parser. MSC codes are quoted strings. Verification does not imply
registry submission, registration, novelty, or specialist peer review.

## Calculator and formal API

`minimumTripleSupremum` and `maximumTripleInfimum` are descriptive aliases
for the existing real run-bound names. `rationalMinimumSupremum` and
`rationalMaximumInfimum` are executable over Lean rationals;
`rational_actual_run_bounds` connects their outputs to literal actual
run hypotheses. The cast theorems are included in the independently
compared contract.

`scripts/cf_bounds.py` is a standard-library exact arithmetic aid adapted
from the GPT-6 Pro review, credited in Disclosure.md. Its `run` command
returns the input, rational cells, all four evaluations, and the selected
extrema. Its `window` command returns the exact rational cutoffs. No
floating-point comparison selects a mathematical branch. The Python
implementation is not itself kernel-certified; the formal guarantee
belongs to the Lean definitions and theorems.
