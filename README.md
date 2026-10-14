# Exact-commit verification evidence

This branch preserves the original GitHub Actions artifacts for verified
source commits of [continued-fraction-bounds](https://github.com/JD-Jones-ASES/continued-fraction-bounds).
It is an evidence archive, not a Lean source checkout.

Each `commits/<full-source-sha>/` directory contains:

- A manifest linking the source commit and successful workflow run.
- The original formal-verification and fresh-project-build artifact ZIPs,
  checked against GitHub's artifact SHA-256 digests.
- Workflow run/job metadata and a checksum file covering the directory.

The formal artifact contains Comparator output, Lean/NanoDa/con-ron
results, axiom inventories, source/build logs, metadata and arithmetic
checks, and mathematical corruption controls. Contents vary with the
source version. The separate artifact records a fresh project build.
Use the manifest and embedded `candidate_sha` to match evidence to source.
An archive commit is not itself the verified source commit.

To verify a downloaded directory, run `shasum -a 256 -c SHA256SUMS` inside it.
These Git-tracked copies remain available independently of Actions artifact
expiry. They are not evidence of Palomar submission, registry acceptance,
worldwide priority, or independent human specialist review.
