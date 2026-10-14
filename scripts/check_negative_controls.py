#!/usr/bin/env python3
"""Compile valid contracts, then require rejection of specific corrupted contracts."""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / ".lake/verification/negative-controls"

PREFIX = """module
public import ContinuedFractionBounds.Applications
public import ContinuedFractionBounds.ContinuedFractionsWords
public import ContinuedFractionBounds.ActualRuns
public import ContinuedFractionBounds.RunChecks
public import ContinuedFractionBounds.RectangleOptimization
public section
open ContinuedFractionBounds
"""

CONTROLS = [
    ("chronological-center", """
example (α : ℝ) (hα : Irrational α) (n : ℕ) :
    theta α (n+1) = 1 / ((digit α (n+2) : ℝ)+past α n+future α n) := by
  exact (ordinary_convergent_triple hα n).2.1
""", "theta α (n+1) = 1 /", "theta α n = 1 /"),
    ("sharp-stability-coefficient", """
example {a x y : ℝ} (ha : 2 ≤ a) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    stabilityConstant a * max |x-metallic a| |y-metallic a| ≤ threshold a-lower a x y := by
  exact global_stability ha hx hx1 hy hy1
""", "stabilityConstant a *", "(stabilityConstant a+1) *"),
    ("silver-mixed-corner", """
example : lower 2 1 (1/3) = 3/10 := by norm_num [lower]
""", "= 3/10", "= 7/24"),
    ("reversed-finite-endpoint", """
example : prependWord [1,1] 0 = (1/2 : ℝ) := by
  norm_num [prependWord, prependDigit]
""", "= (1/2 : ℝ)", "= (1/3 : ℝ)"),
    ("exact-runs-not-minimum-runs", """
example {α : ℝ} {a : ℤ} (hα : Irrational α) (ha : 2 ≤ a)
    (n r s : ℕ) (e f : Departure) (hd : digit α (n+2) = a)
    (hp : ExactPastRun α n a r e) (hf : ExactFutureRun α n a s f) :
    minimumTriple α n < runLowerBound a r s e f := by
  exact (actual_run_bounds hα ha n r s e f hd hp hf).1
""", "(hp : ExactPastRun α n a r e) (hf : ExactFutureRun α n a s f)",
     "(hp : ∀ i < r, digit α (n+1-i) = a) (hf : ∀ i < s, digit α (n+3+i) = a)"),
    ("future-departure-cannot-be-deleted", """
example {α : ℝ} {a : ℤ} (hα : Irrational α) (ha : 2 ≤ a)
    (n r s : ℕ) (e f : Departure) (hd : digit α (n+2) = a)
    (hp : ExactPastRun α n a r e) (hf : ExactFutureRun α n a s f) :
    runUpperBound a r s e f < maximumTriple α n := by
  exact (actual_run_bounds hα ha n r s e f hd hp hf).2.2.2
""", "(hf : ExactFutureRun α n a s f)",
     "(hf : ∀ i < s, digit α (n+3+i) = a)"),
    ("rational-future-corner-is-not-actual", """
example {α : ℝ} (hα : Irrational α) (n : ℕ) :
    future α n ≠ (1/3 : ℝ) := by
  simpa using (future_irrational hα n).ne_rat (1/3)
""", "future α n ≠", "future α n ="),
    ("arbitrary-rectangle-lower-corners-fail", """
example :
    max (max (lower 2 0 0) (lower 2 0 1)) (max (lower 2 1 0) (lower 2 1 1)) <
      lower 2 (1/2) (1/2) := by
  exact arbitrary_rectangle_lower_corners_fail
""", ")) <\n      lower", ")) ≥\n      lower"),
    ("arbitrary-rectangle-upper-corners-fail", """
example :
    upper 2 (1/2) (1/2) <
      min (min (upper 2 0 0) (upper 2 0 1)) (min (upper 2 1 0) (upper 2 1 1)) := by
  exact arbitrary_rectangle_upper_corners_fail
""", "upper 2 (1/2) (1/2) <", "upper 2 (1/2) (1/2) ≥"),
    ("actual-bridge-not-arbitrary-coordinates", """
example {α : ℝ} (hα : Irrational α) (n : ℕ) (x y : ℝ) :
    minimumTriple α n = lower (digit α (n+2)) (past α n) (future α n) := by
  exact actual_minimum_eq hα n
""", "lower (digit α (n+2)) (past α n) (future α n)",
     "lower (digit α (n+2)) x y"),

]


def main() -> None:
    WORK.mkdir(parents=True, exist_ok=True)
    report = WORK.parent / "negative-controls.json"
    report.unlink(missing_ok=True)
    lake = os.environ.get("LAKE") or shutil.which("lake") or str(Path.home()/".elan/bin/lake")
    results = []
    for name, body, good, bad in CONTROLS:
        if body.count(good) != 1:
            raise SystemExit(f"Mutation anchor is not unique: {name}")
        for mutated in (False, True):
            stem = name + ("-mutant" if mutated else "-valid")
            source = WORK / (stem + ".lean")
            source.write_text(PREFIX + (body.replace(good, bad) if mutated else body))
            process = subprocess.run([lake, "env", "lean", str(source)], cwd=ROOT,
                                     text=True, capture_output=True, timeout=120)
            output = process.stdout + process.stderr
            (WORK / (stem + ".log")).write_text(output)
            if not mutated and process.returncode != 0:
                raise SystemExit(f"Valid control failed: {name}\n{output}")
            if mutated and (process.returncode == 0 or "error:" not in output
                            or "unknown module" in output.lower()
                            or "object file" in output.lower()):
                raise SystemExit(f"Mutant was not rejected for a proof error: {name}\n{output}")
        results.append({"name": name, "valid_compiles": True, "mutant_rejected": True})
    report.write_text(json.dumps({"status": "passed", "controls": results}, indent=2)+"\n")
    print(f"All {len(results)} valid Lean controls compiled and all corrupted contracts were rejected")


if __name__ == "__main__":
    main()
