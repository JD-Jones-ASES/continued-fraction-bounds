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
