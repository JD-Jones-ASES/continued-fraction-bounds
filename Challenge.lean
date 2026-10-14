module
public import Mathlib

/-!
# Sharp continued-fraction bounds from exact digit runs

Ordinary convergents are Mathlib's convergents of the actual irrational real
input. Index n denotes the first of the chronological triple n,n+1,n+2;
the central partial quotient has index n+2. Exact-run optimality permits
this finite index to vary. Rational future corners are limiting values.
-/

@[expose] public section
namespace ContinuedFractionBounds
open Filter

/-- Minimum of the three rational approximation-coefficient expressions. -/
noncomputable def lower (a x y : ℝ) : ℝ :=
  min 1 (min (x * (a + y)) (y * (a + x))) / (a + x + y)
/-- Maximum of the three rational approximation-coefficient expressions. -/
noncomputable def upper (a x y : ℝ) : ℝ :=
  max 1 (max (x * (a + y)) (y * (a + x))) / (a + x + y)
/-- Positive fixed point of t ↦ 1/(a+t). -/
noncomputable def metallic (a : ℝ) : ℝ := (Real.sqrt (a ^ 2 + 4) - a) / 2
/-- Classical metallic approximation threshold. -/
noncomputable def threshold (a : ℝ) : ℝ := 1 / Real.sqrt (a ^ 2 + 4)
/-- The proposed optimal coefficient in the uniform linear inverse estimate. -/
noncomputable def stabilityConstant (a : ℝ) : ℝ :=
  threshold a * (a + 1 - metallic a) / (1 + (a + 1) ^ 2)
/-- Complete quotients computed from the actual real input by the floor/fraction algorithm. -/
noncomputable def completeQuotient (α : ℝ) : ℕ → ℝ
  | 0 => α
  | n + 1 => (Int.fract (completeQuotient α n))⁻¹
/-- The actual ordinary partial quotient; index zero is the integer part. -/
noncomputable def digit (α : ℝ) (n : ℕ) : ℤ := ⌊completeQuotient α n⌋
/-- Ordinary convergent numerator from Mathlib’s continued fraction of the input. -/
noncomputable def numerator (α : ℝ) (n : ℕ) : ℝ := (GenContFract.of α).nums n
/-- Ordinary convergent denominator from Mathlib’s continued fraction of the input. -/
noncomputable def denominator (α : ℝ) (n : ℕ) : ℝ := (GenContFract.of α).dens n
/-- The actual approximation coefficient qₙ |qₙ α − pₙ|. -/
noncomputable def theta (α : ℝ) (n : ℕ) : ℝ :=
  denominator α n * |denominator α n * α - numerator α n|
/-- Reversed finite-past coordinate at the middle convergent n+1. -/
noncomputable def past (α : ℝ) (n : ℕ) : ℝ := denominator α n / denominator α (n+1)
/-- Irrational future coordinate after the actual central digit n+2. -/
noncomputable def future (α : ℝ) (n : ℕ) : ℝ := Int.fract (completeQuotient α (n+2))
/-- Minimum of the three chronological coefficients at n, n+1, n+2. -/
noncomputable def minimumTriple (α : ℝ) (n : ℕ) : ℝ :=
  min (theta α n) (min (theta α (n+1)) (theta α (n+2)))
/-- Maximum of the three chronological coefficients at n, n+1, n+2. -/
noncomputable def maximumTriple (α : ℝ) (n : ℕ) : ℝ :=
  max (theta α n) (max (theta α (n+1)) (theta α (n+2)))
/-- The inverse branch t ↦ 1/(a+t). -/
noncomputable def tailMap (a t : ℝ) : ℝ := 1 / (a + t)
/-- A finite constant-digit prefix of arbitrary natural length. -/
noncomputable def tailIter (a : ℝ) (r : ℕ) (t : ℝ) : ℝ := (tailMap a)^[r] t
/-- The first departing digit is strictly below or strictly above the central digit. -/
inductive Departure | low | high
  deriving DecidableEq, Repr
/-- Left endpoint of the closed departure interval. -/
noncomputable def departureLeft (a : ℝ) : Departure → ℝ
  | .low => 1 / a
  | .high => 0
/-- Right endpoint of the closed departure interval. -/
noncomputable def departureRight (a : ℝ) : Departure → ℝ
  | .low => 1
  | .high => 1 / (a + 1)
/-- Closed interval of departure tails; endpoints encode closure, not irrational attainment. -/
def departureInterval (a : ℝ) (e : Departure) : Set ℝ :=
  Set.Icc (departureLeft a e) (departureRight a e)
/-- The exact closed run cell, defined as the image of a departure interval. -/
def runCell (a : ℝ) (r : ℕ) (e : Departure) : Set ℝ :=
  tailIter a r '' departureInterval a e
/-- Either image endpoint, without choosing a parity or orientation. -/
def runEndpoint (a : ℝ) (r : ℕ) (e : Departure) (x : ℝ) : Prop :=
  x = tailIter a r (departureLeft a e) ∨ x = tailIter a r (departureRight a e)
/-- Smaller endpoint after the possibly orientation-reversing iterate. -/
noncomputable def runLower (a : ℝ) (r : ℕ) (e : Departure) : ℝ :=
  min (tailIter a r (departureLeft a e)) (tailIter a r (departureRight a e))
/-- Larger endpoint after the possibly orientation-reversing iterate. -/
noncomputable def runUpper (a : ℝ) (r : ℕ) (e : Departure) : ℝ :=
  max (tailIter a r (departureLeft a e)) (tailIter a r (departureRight a e))
/-- Maximum of the lower envelope over all four explicitly listed corners. -/
noncomputable def runLowerBound (a : ℝ) (r s : ℕ) (e f : Departure) : ℝ :=
  max (max (lower a (runLower a r e) (runLower a s f))
    (lower a (runLower a r e) (runUpper a s f)))
    (max (lower a (runUpper a r e) (runLower a s f))
      (lower a (runUpper a r e) (runUpper a s f)))
/-- Minimum of the upper envelope over all four explicitly listed corners. -/
noncomputable def runUpperBound (a : ℝ) (r s : ℕ) (e f : Departure) : ℝ :=
  min (min (upper a (runLower a r e) (runLower a s f))
    (upper a (runLower a r e) (runUpper a s f)))
    (min (upper a (runUpper a r e) (runLower a s f))
      (upper a (runUpper a r e) (runUpper a s f)))
/-- A literal positive partial quotient on the specified side of the central integer. -/
def DigitDeparture (a b : ℤ) : Departure → Prop
  | .low => 1 ≤ b ∧ b < a
  | .high => a < b
/-- Exactly r copies of a in the actual reversed past, then a departing digit; exhausted pasts are excluded. -/
def ExactPastRun (α : ℝ) (n : ℕ) (a : ℤ) (r : ℕ) (e : Departure) : Prop :=
  r ≤ n ∧ (∀ i < r, digit α (n+1-i) = a) ∧
    DigitDeparture a (digit α (n+1-r)) e
/-- Exactly s copies of a in the actual future, followed by the specified departure. -/
def ExactFutureRun (α : ℝ) (n : ℕ) (a : ℤ) (s : ℕ) (e : Departure) : Prop :=
  (∀ i < s, digit α (n+3+i) = a) ∧
    DigitDeparture a (digit α (n+3+s)) e
/-- Rational graph obtained by solving a side-coefficient level inequality. -/
noncomputable def levelBoundary (a t z : ℝ) : ℝ :=
  t * (a + z) / (a + z - t)
/-- Evaluate a single positive digit before its remaining tail. -/
noncomputable def prependDigit (b : ℤ) (t : ℝ) : ℝ := ((b : ℝ) + t)⁻¹
/-- Evaluate a finite literal digit word, retaining terminal one. -/
noncomputable def prependWord : List ℤ → ℝ → ℝ
  | [], t => t
  | b :: bs, t => prependDigit b (prependWord bs t)
/-- Every digit in the prescribed finite word is positive. -/
def PositiveWord (w : List ℤ) : Prop := ∀ b ∈ w, 1 ≤ b
/-- Closed cylinder for at least r constant digits. -/
def constantCell (a : ℝ) (r : ℕ) : Set ℝ := tailIter a r '' Set.Icc (0 : ℝ) 1
/-- Lower endpoint of the constant-prefix cylinder. -/
noncomputable def constantLower (a : ℝ) (r : ℕ) : ℝ :=
  min (tailIter a r 0) (tailIter a r 1)
/-- Upper endpoint of the constant-prefix cylinder. -/
noncomputable def constantUpper (a : ℝ) (r : ℕ) : ℝ :=
  max (tailIter a r 0) (tailIter a r 1)
/-- Lower-envelope switching involution on positive arguments. -/
noncomputable def lowerSwitch (a t : ℝ) : ℝ := max (1 / t - a) (1 / (a + t))
/-- Upper-envelope switching curve, extended by zero. -/
noncomputable def upperSwitch (a t : ℝ) : ℝ :=
  if t ≤ metallic a then 1 / (a + t) else max 0 (1 / t - a)
/-- Clip a proposed coordinate to a closed interval. -/
noncomputable def clip (z L U : ℝ) := min U (max L z)
/-- Lower end of the feasible lower switching segment. -/
noncomputable def lowerClipLeft (a lx uy : ℝ) := max lx (lowerSwitch a uy)
/-- Upper end of that segment, including a zero lower edge. -/
noncomputable def lowerClipRight (a ux ly : ℝ) :=
  if ly = 0 then ux else min ux (lowerSwitch a ly)
/-- Clip the metallic coordinate to the feasible lower switching segment. -/
noncomputable def lowerClipX (a lx ux ly uy : ℝ) :=
  clip (metallic a) (lowerClipLeft a lx uy) (lowerClipRight a ux ly)
/-- Matching second coordinate on the lower switching curve. -/
noncomputable def lowerClipY (a lx ux ly uy : ℝ) :=
  lowerSwitch a (lowerClipX a lx ux ly uy)
/-- Exhaustive maximizing first coordinate for every closed rectangle. -/
noncomputable def lowerRectangleX (a lx ux ly uy : ℝ) :=
  if ux * uy = 0 then ux
  else if min (ux * (a + uy)) (uy * (a + ux)) ≤ 1 then ux
  else if 1 ≤ min (lx * (a + ly)) (ly * (a + lx)) then lx
  else lowerClipX a lx ux ly uy
/-- Exhaustive maximizing second coordinate for every closed rectangle. -/
noncomputable def lowerRectangleY (a lx ux ly uy : ℝ) :=
  if ux * uy = 0 then uy
  else if min (ux * (a + uy)) (uy * (a + ux)) ≤ 1 then uy
  else if 1 ≤ min (lx * (a + ly)) (ly * (a + lx)) then ly
  else lowerClipY a lx ux ly uy
/-- Lower end of the feasible upper switching segment. -/
noncomputable def upperClipLeft (a lx uy : ℝ) := max lx (upperSwitch a uy)
/-- Upper end of the feasible upper switching segment. -/
noncomputable def upperClipRight (a ux ly : ℝ) := min ux (upperSwitch a ly)
/-- Clip the metallic coordinate to the feasible upper switching segment. -/
noncomputable def upperClipX (a lx ux ly uy : ℝ) :=
  clip (metallic a) (upperClipLeft a lx uy) (upperClipRight a ux ly)
/-- Matching second coordinate on the upper switching curve. -/
noncomputable def upperClipY (a lx ux ly uy : ℝ) :=
  upperSwitch a (upperClipX a lx ux ly uy)
/-- Exhaustive minimizing first coordinate for every closed rectangle. -/
noncomputable def upperRectangleX (a lx ux ly uy : ℝ) :=
  if max (ux * (a + uy)) (uy * (a + ux)) ≤ 1 then ux
  else if 1 ≤ max (lx * (a + ly)) (ly * (a + lx)) then lx
  else upperClipX a lx ux ly uy
/-- Exhaustive minimizing second coordinate for every closed rectangle. -/
noncomputable def upperRectangleY (a lx ux ly uy : ℝ) :=
  if max (ux * (a + uy)) (uy * (a + ux)) ≤ 1 then uy
  else if 1 ≤ max (lx * (a + ly)) (ly * (a + lx)) then ly
  else upperClipY a lx ux ly uy
/-- Explicit irrational with low departing finite past and constant infinite future. -/
noncomputable def metallicLowExample (a : ℤ) : ℝ :=
  prependWord [1,a-1] (metallic (a:ℝ))
/-- Explicit irrational with high departing finite past and constant infinite future. -/
noncomputable def metallicHighExample (a : ℤ) : ℝ :=
  prependWord [a+1] (metallic (a:ℝ))
/-- Departure endpoint nearest the metallic fixed point. -/
noncomputable def metallicNearestTail (a : ℝ) : Departure → ℝ
  | .low => 1/a
  | .high => 1/(a+1)
/-- The input has exactly the prescribed initial positive digit word. -/
def HasInitialWord (α : ℝ) (w : List ℤ) : Prop :=
  ∀ k, (hk : k < w.length) → digit α (k+1) = w[k]
/-- Finite reversed-past coordinate for the complete prescribed word. -/
noncomputable def wordPast (w : List ℤ) : ℝ := prependWord w.reverse 0
/-- Exact maximizing future coordinate for a prescribed entire past. -/
noncomputable def fixedPastLowerY (a : ℝ) (w : List ℤ) (s : ℕ) (e : Departure) : ℝ :=
  lowerRectangleY a (wordPast w) (wordPast w) (runLower a s e) (runUpper a s e)
/-- Exact minimizing future coordinate for a prescribed entire past. -/
noncomputable def fixedPastUpperY (a : ℝ) (w : List ℤ) (s : ℕ) (e : Departure) : ℝ :=
  upperRectangleY a (wordPast w) (wordPast w) (runLower a s e) (runUpper a s e)
/-- Sharp upper bound for the minimum with a fixed entire finite past. -/
noncomputable def fixedPastLowerBound (a : ℝ) (w : List ℤ) (s : ℕ) (e : Departure) : ℝ :=
  lower a (wordPast w) (fixedPastLowerY a w s e)
/-- Sharp lower bound for the maximum with a fixed entire finite past. -/
noncomputable def fixedPastUpperBound (a : ℝ) (w : List ℤ) (s : ℕ) (e : Departure) : ℝ :=
  upper a (wordPast w) (fixedPastUpperY a w s e)
/-- Optimal uniform inverse coefficient for the maximum envelope. -/
noncomputable def upperStabilityConstant (a : ℝ) : ℝ :=
  a * metallic a / (a ^ 2 + 4)
/-- Distance from the metallic point to the nearer run endpoint. -/
noncomputable def runDistanceNear (a : ℝ) (r : ℕ) (e : Departure) : ℝ :=
  min |runLower a r e-metallic a| |runUpper a r e-metallic a|
/-- Distance from the metallic point to the farther run endpoint. -/
noncomputable def runDistanceFar (a : ℝ) (r : ℕ) (e : Departure) : ℝ :=
  max |runLower a r e-metallic a| |runUpper a r e-metallic a|
/-- Exact one-coordinate maximum of the lower envelope. -/
noncomputable def lowerProfile (a t : ℝ) : ℝ :=
  if t ≤ 1 / (a + 1) then t * (a + 1) / (a + 1 + t)
  else if t ≤ metallic a then t / (1 + t ^ 2)
  else (a + t) / (1 + (a + t) ^ 2)
/-- A maximizing second coordinate, including the nonunique zero fiber. -/
noncomputable def lowerProfileWitness (a t : ℝ) : ℝ :=
  if t ≤ 1 / (a + 1) then 1 else if t ≤ metallic a then 1 / t - a else 1 / (a + t)
/-- Exact one-coordinate minimum of the upper envelope. -/
noncomputable def upperProfile (a t : ℝ) : ℝ :=
  if t ≤ metallic a then (a + t) / (1 + (a + t) ^ 2)
  else if t ≤ 1 / a then t / (1 + t ^ 2) else a * t / (a + t)
/-- The minimizing second coordinate. -/
noncomputable def upperProfileWitness (a t : ℝ) : ℝ :=
  if t ≤ metallic a then 1 / (a + t) else if t ≤ 1 / a then 1 / t - a else 0
/-- Sharp lower-envelope cutoff outside an open target square. -/
noncomputable def sharpLowerWindowThreshold (a L U : ℝ) : ℝ :=
  max (lowerProfile a L) (lowerProfile a U)
/-- Sharp upper-envelope cutoff outside an open target square. -/
noncomputable def sharpUpperWindowThreshold (a L U : ℝ) : ℝ :=
  min (upperProfile a L) (upperProfile a U)
/-- Four-endpoint lower cutoff outside an open target rectangle. -/
noncomputable def sharpLowerRectangleThreshold (a Lx Ux Ly Uy : ℝ) : ℝ :=
  max (sharpLowerWindowThreshold a Lx Ux) (sharpLowerWindowThreshold a Ly Uy)
/-- Four-endpoint upper cutoff outside an open target rectangle. -/
noncomputable def sharpUpperRectangleThreshold (a Lx Ux Ly Uy : ℝ) : ℝ :=
  min (sharpUpperWindowThreshold a Lx Ux) (sharpUpperWindowThreshold a Ly Uy)
/-- Lower cutoff for a specified constant-digit window. -/
noncomputable def sharpLowerDigitThreshold (a : ℝ) (r : ℕ) : ℝ :=
  sharpLowerWindowThreshold a (constantLower a r) (constantUpper a r)
/-- Upper cutoff for a specified constant-digit window. -/
noncomputable def sharpUpperDigitThreshold (a : ℝ) (r : ℕ) : ℝ :=
  sharpUpperWindowThreshold a (constantLower a r) (constantUpper a r)
/-- Descriptive alias for the exact-run minimum supremum. -/
noncomputable def minimumTripleSupremum := runLowerBound
/-- Descriptive alias for the exact-run maximum infimum. -/
noncomputable def maximumTripleInfimum := runUpperBound
/-- Executable rational inverse-branch iteration. -/
def rationalTailIter (a : ℚ) (r : ℕ) (t : ℚ) : ℚ :=
  (fun z : ℚ => 1 / (a + z))^[r] t
/-- Rational left departure endpoint. -/
def rationalDepartureLeft (a : ℚ) : Departure → ℚ
  | .low => 1/a
  | .high => 0
/-- Rational right departure endpoint. -/
def rationalDepartureRight (a : ℚ) : Departure → ℚ
  | .low => 1
  | .high => 1/(a+1)
/-- Exact rational lower run endpoint. -/
def rationalRunLower (a : ℚ) (r : ℕ) (e : Departure) : ℚ :=
  min (rationalTailIter a r (rationalDepartureLeft a e))
    (rationalTailIter a r (rationalDepartureRight a e))
/-- Exact rational upper run endpoint. -/
def rationalRunUpper (a : ℚ) (r : ℕ) (e : Departure) : ℚ :=
  max (rationalTailIter a r (rationalDepartureLeft a e))
    (rationalTailIter a r (rationalDepartureRight a e))
/-- Executable rational minimum envelope. -/
def rationalLower (a x y : ℚ) : ℚ :=
  min 1 (min (x*(a+y)) (y*(a+x))) / (a+x+y)
/-- Executable rational maximum envelope. -/
def rationalUpper (a x y : ℚ) : ℚ :=
  max 1 (max (x*(a+y)) (y*(a+x))) / (a+x+y)
/-- Executable four-corner rational minimum supremum. -/
def rationalMinimumSupremum (a : ℚ) (r s : ℕ) (e f : Departure) : ℚ :=
  max (max (rationalLower a (rationalRunLower a r e) (rationalRunLower a s f))
    (rationalLower a (rationalRunLower a r e) (rationalRunUpper a s f)))
    (max (rationalLower a (rationalRunUpper a r e) (rationalRunLower a s f))
      (rationalLower a (rationalRunUpper a r e) (rationalRunUpper a s f)))
/-- Executable four-corner rational maximum infimum. -/
def rationalMaximumInfimum (a : ℚ) (r s : ℕ) (e f : Departure) : ℚ :=
  min (min (rationalUpper a (rationalRunLower a r e) (rationalRunLower a s f))
    (rationalUpper a (rationalRunLower a r e) (rationalRunUpper a s f)))
    (min (rationalUpper a (rationalRunUpper a r e) (rationalRunLower a s f))
      (rationalUpper a (rationalRunUpper a r e) (rationalRunUpper a s f)))
theorem convergent_eq (α : ℝ) (n : ℕ) :
    numerator α n / denominator α n = (α.convergent n : ℝ) := by
  sorry
theorem ordinary_convergent_triple {α : ℝ} (hα : Irrational α) (n : ℕ) :
    let a := (digit α (n+2) : ℝ)
    let x := past α n
    let y := future α n
    theta α n = x*(a+y)/(a+x+y) ∧
    theta α (n+1) = 1/(a+x+y) ∧
    theta α (n+2) = y*(a+x)/(a+x+y) := by
  sorry
theorem runLowerBound_extremizer {a : ℝ} (ha : 1 < a) (r s : ℕ) (e f : Departure) :
    ∃ cx cy, runEndpoint a r e cx ∧ runEndpoint a s f cy ∧
      lower a cx cy = runLowerBound a r s e f ∧
      ∀ x ∈ runCell a r e, ∀ y ∈ runCell a s f,
        lower a x y ≤ runLowerBound a r s e f ∧
        (lower a x y = runLowerBound a r s e f ↔ x = cx ∧ y = cy) := by
  sorry
theorem runUpperBound_extremizer {a : ℝ} (ha : 1 < a) (r s : ℕ) (e f : Departure) :
    ∃ cx cy, runEndpoint a r e cx ∧ runEndpoint a s f cy ∧
      upper a cx cy = runUpperBound a r s e f ∧
      ∀ x ∈ runCell a r e, ∀ y ∈ runCell a s f,
        runUpperBound a r s e f ≤ upper a x y ∧
        (upper a x y = runUpperBound a r s e f ↔ x = cx ∧ y = cy) := by
  sorry
theorem runBounds_rational (a : ℚ) (r s : ℕ) (e f : Departure) :
    (∃ q : ℚ, (q : ℝ) = runLowerBound (a : ℝ) r s e f) ∧
      (∃ q : ℚ, (q : ℝ) = runUpperBound (a : ℝ) r s e f) := by
  sorry
theorem actual_run_bounds {α : ℝ} {a : ℤ} (hα : Irrational α) (ha : 2 ≤ a)
    (n r s : ℕ) (e f : Departure) (hd : digit α (n+2) = a)
    (hp : ExactPastRun α n a r e) (hf : ExactFutureRun α n a s f) :
    minimumTriple α n < runLowerBound a r s e f ∧
      runLowerBound a r s e f < threshold a ∧
      threshold a < runUpperBound a r s e f ∧
      runUpperBound a r s e f < maximumTriple α n := by
  sorry
theorem actual_run_lower_sharp {a : ℤ} (ha : 2 ≤ a) (r s : ℕ) (e f : Departure)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ α : ℝ, ∃ n : ℕ, Irrational α ∧ digit α (n+2) = a ∧
      ExactPastRun α n a r e ∧ ExactFutureRun α n a s f ∧
      runLowerBound a r s e f - ε < minimumTriple α n ∧
      minimumTriple α n < runLowerBound a r s e f := by
  sorry
theorem actual_run_upper_sharp {a : ℤ} (ha : 2 ≤ a) (r s : ℕ) (e f : Departure)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ α : ℝ, ∃ n : ℕ, Irrational α ∧ digit α (n+2) = a ∧
      ExactPastRun α n a r e ∧ ExactFutureRun α n a s f ∧
      runUpperBound a r s e f < maximumTriple α n ∧
      maximumTriple α n < runUpperBound a r s e f + ε := by
  sorry
theorem global_stability {a x y : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    stabilityConstant a * max |x - metallic a| |y - metallic a| ≤
      threshold a - lower a x y := by
  sorry
theorem global_stability_eq_iff {a x y : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    threshold a - lower a x y = stabilityConstant a * max |x - metallic a| |y - metallic a| ↔
      (x = metallic a ∧ y = metallic a) ∨
      (x = 1 ∧ y = 1 / (a + 1)) ∨ (x = 1 / (a + 1) ∧ y = 1) := by
  sorry
theorem stabilityConstant_optimal {a K : ℝ} (ha : 2 ≤ a)
    (hK : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      K * max |x - metallic a| |y - metallic a| ≤ threshold a - lower a x y) :
    K ≤ stabilityConstant a := by
  sorry
theorem stabilityConstant_two : stabilityConstant 2 = (2 * Real.sqrt 2 - 1) / 20 := by
  sorry
theorem actual_stability_strict {α : ℝ} {a : ℤ} (hα : Irrational α)
    (ha : 2 ≤ a) (n : ℕ) (hdigit : digit α (n+2) = a) :
    stabilityConstant a * max |past α n - metallic a| |future α n - metallic a| <
      threshold a - minimumTriple α n := by
  sorry
theorem actual_stabilityConstant_optimal {a : ℤ} {K : ℝ} (ha : 2 ≤ a)
    (hK : ∀ α : ℝ, Irrational α → ∀ n : ℕ, digit α (n+2) = a →
      K * max |past α n - metallic a| |future α n - metallic a| ≤
        threshold a - minimumTriple α n) : K ≤ stabilityConstant a := by
  sorry
theorem near_extremizer_radius {a x y ε : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hε : threshold a - ε ≤ lower a x y) :
    max |x-metallic a| |y-metallic a| ≤ ε / stabilityConstant a := by
  sorry
theorem small_deficit_in_interval {a x y L U : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hdef : threshold a - lower a x y <
      stabilityConstant a * min (metallic a-L) (U-metallic a)) :
    x ∈ Set.Ioo L U ∧ y ∈ Set.Ioo L U := by
  sorry
theorem lower_level_iff {a t x y : ℝ} (ht : 0 < t) (hta : t < a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    t ≤ lower a x y ↔
      x + y ≤ 1 / t - a ∧ levelBoundary a t y ≤ x ∧ levelBoundary a t x ≤ y := by
  sorry
theorem upper_level_iff {a t x y : ℝ} (ht : 0 < t) (hta : t < a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    upper a x y ≤ t ↔
      1 / t - a ≤ x + y ∧ x ≤ levelBoundary a t y ∧ y ≤ levelBoundary a t x := by
  sorry
theorem lower_eq_threshold_iff {a x y : ℝ} (ha : 1 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    lower a x y = threshold a ↔ x = metallic a ∧ y = metallic a := by
  sorry
theorem upper_eq_threshold_iff {a x y : ℝ} (ha : 1 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    upper a x y = threshold a ↔ x = metallic a ∧ y = metallic a := by
  sorry
theorem lower_rectangle_maximum {a lx ux ly uy : ℝ} (ha : 1 ≤ a)
    (hlx : 0 ≤ lx) (hlxu : lx ≤ ux) (hux : ux ≤ 1)
    (hly : 0 ≤ ly) (hlyu : ly ≤ uy) (huy : uy ≤ 1) :
    let t := lowerRectangleX a lx ux ly uy
    let u := lowerRectangleY a lx ux ly uy
    t ∈ Set.Icc lx ux ∧ u ∈ Set.Icc ly uy ∧
      ∀ x ∈ Set.Icc lx ux, ∀ y ∈ Set.Icc ly uy,
        lower a x y ≤ lower a t u ∧
        (lower a x y = lower a t u ↔ ux * uy = 0 ∨ (x = t ∧ y = u)) := by
  sorry
theorem upper_rectangle_minimum {a lx ux ly uy : ℝ} (ha : 1 ≤ a)
    (hlx : 0 ≤ lx) (hlxu : lx ≤ ux) (hux : ux ≤ 1)
    (hly : 0 ≤ ly) (hlyu : ly ≤ uy) (huy : uy ≤ 1) :
    let t := upperRectangleX a lx ux ly uy
    let u := upperRectangleY a lx ux ly uy
    t ∈ Set.Icc lx ux ∧ u ∈ Set.Icc ly uy ∧
      ∀ x ∈ Set.Icc lx ux, ∀ y ∈ Set.Icc ly uy,
        upper a t u ≤ upper a x y ∧
        (upper a x y = upper a t u ↔ x = t ∧ y = u) := by
  sorry
theorem lower_rectangle_threshold_iff {a lx ux ly uy : ℝ} (ha : 1 ≤ a)
    (hlx : 0 ≤ lx) (hlxu : lx ≤ ux) (hux : ux ≤ 1)
    (hly : 0 ≤ ly) (hlyu : ly ≤ uy) (huy : uy ≤ 1) :
    lower a (lowerRectangleX a lx ux ly uy) (lowerRectangleY a lx ux ly uy) = threshold a ↔
      metallic a ∈ Set.Icc lx ux ∧ metallic a ∈ Set.Icc ly uy := by
  sorry
theorem upper_rectangle_threshold_iff {a lx ux ly uy : ℝ} (ha : 1 ≤ a)
    (hlx : 0 ≤ lx) (hlxu : lx ≤ ux) (hux : ux ≤ 1)
    (hly : 0 ≤ ly) (hlyu : ly ≤ uy) (huy : uy ≤ 1) :
    upper a (upperRectangleX a lx ux ly uy) (upperRectangleY a lx ux ly uy) = threshold a ↔
      metallic a ∈ Set.Icc lx ux ∧ metallic a ∈ Set.Icc ly uy := by
  sorry
theorem fixed_word_future_sequences {w : List ℤ} (hw : PositiveWord w) (hwne : w ≠ [])
    {a : ℤ} (ha : 2 ≤ a) (s : ℕ) (e : Departure) {y : ℝ} (hy : y ∈ runCell a s e) :
    ∃ α : ℕ → ℝ,
      (∀ N, Irrational (α N) ∧
        (∀ k, (hk : k < w.length) → digit (α N) (k+1) = w[k]) ∧
        digit (α N) (w.length+1) = a ∧ ExactFutureRun (α N) (w.length-1) a s e ∧
        past (α N) (w.length-1) = prependWord w.reverse 0) ∧
      Tendsto (fun N => future (α N) (w.length-1)) atTop (nhds y) := by
  sorry
theorem exhausted_past {α : ℝ} (hα : Irrational α) {a : ℤ} (n : ℕ)
    (hd : ∀ k, 1 ≤ k → k ≤ n+1 → digit α k = a) :
    past α n = tailIter a (n+1) 0 := by
  sorry
theorem metallic_irrational {a : ℤ} (ha : 2 ≤ a) : Irrational (metallic (a : ℝ)) := by
  sorry
theorem metallic_digits {a : ℤ} (ha : 2 ≤ a) (n : ℕ) :
    digit (metallic (a:ℝ)) (n+1) = a := by
  sorry
theorem metallic_theta {a : ℤ} (ha : 2 ≤ a) (k : ℕ) :
    theta (metallic (a:ℝ)) k =
      (1 - (-1:ℝ)^(k+1)*(metallic a)^(2*k+2)) / Real.sqrt ((a:ℝ)^2+4) := by
  sorry
theorem metallic_triple_even {a : ℤ} (ha : 2 ≤ a) (j : ℕ) :
    minimumTriple (metallic (a:ℝ)) (2*j) =
      (1-(metallic a)^(4*j+4)) / Real.sqrt ((a:ℝ)^2+4) ∧
    maximumTriple (metallic (a:ℝ)) (2*j) =
      (1+(metallic a)^(4*j+2)) / Real.sqrt ((a:ℝ)^2+4) := by
  sorry
theorem metallic_triple_odd {a : ℤ} (ha : 2 ≤ a) (j : ℕ) :
    minimumTriple (metallic (a:ℝ)) (2*j+1) =
      (1-(metallic a)^(4*j+4)) / Real.sqrt ((a:ℝ)^2+4) ∧
    maximumTriple (metallic (a:ℝ)) (2*j+1) =
      (1+(metallic a)^(4*j+6)) / Real.sqrt ((a:ℝ)^2+4) := by
  sorry
theorem metallic_triples_tendsto {a : ℤ} (ha : 2 ≤ a) :
    Tendsto (minimumTriple (metallic (a:ℝ))) atTop (nhds (threshold (a:ℝ))) ∧
    Tendsto (maximumTriple (metallic (a:ℝ))) atTop (nhds (threshold (a:ℝ))) := by
  sorry
theorem metallic_future_run_extrema {a x : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure)
    (hx : x ∈ runCell a r e) :
    let z := tailIter a r (metallicNearestTail a e)
    lower a x (metallic a) ≤ lower a z (metallic a) ∧
    upper a z (metallic a) ≤ upper a x (metallic a) ∧
    (lower a x (metallic a) = lower a z (metallic a) ↔ x = z) ∧
    (upper a x (metallic a) = upper a z (metallic a) ↔ x = z) := by
  sorry
theorem metallic_low_example_states {a : ℤ} (ha : 2 ≤ a) (r : ℕ) :
    Irrational (metallicLowExample a) ∧
    digit (metallicLowExample a) (r+3) = a ∧
    ExactPastRun (metallicLowExample a) (r+1) a r .low ∧
    past (metallicLowExample a) (r+1) = tailIter a r (1/(a:ℝ)) ∧
    future (metallicLowExample a) (r+1) = metallic (a:ℝ) := by
  sorry
theorem metallic_high_example_states {a : ℤ} (ha : 2 ≤ a) (r : ℕ) :
    Irrational (metallicHighExample a) ∧
    digit (metallicHighExample a) (r+2) = a ∧
    ExactPastRun (metallicHighExample a) r a r .high ∧
    past (metallicHighExample a) r = tailIter a r (1/((a:ℝ)+1)) ∧
    future (metallicHighExample a) r = metallic (a:ℝ) := by
  sorry
theorem metallic_low_example_attains {a : ℤ} (ha : 2 ≤ a) (r : ℕ) :
    minimumTriple (metallicLowExample a) (r+1) =
      lower a (tailIter a r (1/(a:ℝ))) (metallic a) ∧
    maximumTriple (metallicLowExample a) (r+1) =
      upper a (tailIter a r (1/(a:ℝ))) (metallic a) := by
  sorry
theorem metallic_high_example_attains {a : ℤ} (ha : 2 ≤ a) (r : ℕ) :
    minimumTriple (metallicHighExample a) r =
      lower a (tailIter a r (1/((a:ℝ)+1))) (metallic a) ∧
    maximumTriple (metallicHighExample a) r =
      upper a (tailIter a r (1/((a:ℝ)+1))) (metallic a) := by
  sorry
theorem past_ne_metallic {a : ℤ} (ha : 2 ≤ a) (α : ℝ) (n : ℕ) :
    past α n ≠ metallic (a:ℝ) := by
  sorry
theorem infinite_future_iff_metallic {α : ℝ} (hα : Irrational α)
    {a : ℤ} (ha : 2 ≤ a) (n : ℕ) :
    (∀ i : ℕ, digit α (n+3+i) = a) ↔ future α n = metallic (a:ℝ) := by
  sorry
theorem envelopes_lipschitz {a x y u v : ℝ} (ha : 1 ≤ a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |lower a x y-lower a u v| ≤ |x-u|+|y-v| ∧
      |upper a x y-upper a u v| ≤ |x-u|+|y-v| := by
  sorry
theorem run_constants_convergence {a : ℝ} (ha : 1 < a) (r s : ℕ) (e f : Departure) :
    0 < threshold a-runLowerBound a r s e f ∧
      threshold a-runLowerBound a r s e f ≤ (1/a^2)^r+(1/a^2)^s ∧
      0 < runUpperBound a r s e f-threshold a ∧
      runUpperBound a r s e f-threshold a ≤ (1/a^2)^r+(1/a^2)^s := by
  sorry
theorem small_deficit_constant_cell {a x y : ℝ} (ha : 2 ≤ a) (r : ℕ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hd : threshold a-lower a x y < stabilityConstant a *
      min (metallic a-constantLower a r) (constantUpper a r-metallic a)) :
    x ∈ interior (constantCell a r) ∧ y ∈ interior (constantCell a r) := by
  sorry
theorem small_deficit_digit_window {α : ℝ} {a : ℤ} (hα : Irrational α)
    (ha : 2 ≤ a) (n r : ℕ) (hd : digit α (n+2)=a)
    (hdef : threshold a-minimumTriple α n < stabilityConstant a *
      min (metallic a-constantLower a r) (constantUpper a r-metallic a)) :
    r < n+1 ∧ (∀ i < r, digit α (n+1-i)=a) ∧
      (∀ i < r, digit α (n+3+i)=a) := by
  sorry
theorem silver_one_low_high :
    runLowerBound 2 1 1 .low .high = 10 / 29 ∧
      runUpperBound 2 1 1 .low .high = 21 / 58 := by
  sorry
theorem past_rational (α : ℝ) (n : ℕ) : ∃ r : ℚ, past α n = r := by
  sorry
theorem future_irrational {α : ℝ} (hα : Irrational α) (n : ℕ) :
    Irrational (future α n) := by
  sorry
theorem runCell_shift (a : ℝ) (r : ℕ) (e : Departure) :
    tailMap a '' runCell a r e = runCell a (r + 1) e := by
  sorry
theorem runCell_eq_Icc {a : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure) :
    runCell a r e = Set.Icc (runLower a r e) (runUpper a r e) := by
  sorry
theorem runCell_interiors_disjoint {a : ℝ} (ha : 1 < a) (r s : ℕ)
    (e f : Departure) (hdiff : r ≠ s ∨ e ≠ f) :
    Disjoint (interior (runCell a r e)) (interior (runCell a s f)) := by
  sorry
theorem metallic_not_mem_runCell {a : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure) :
    metallic a ∉ runCell a r e := by
  sorry
theorem fixedPastLower_extremum {a : ℝ} (ha : 1 < a) {w : List ℤ}
    (hw : PositiveWord w) (hwne : w ≠ []) (s : ℕ) (e : Departure) :
    fixedPastLowerY a w s e ∈ runCell a s e ∧
    ∀ y ∈ runCell a s e,
      lower a (wordPast w) y ≤ fixedPastLowerBound a w s e ∧
      (lower a (wordPast w) y = fixedPastLowerBound a w s e ↔ y = fixedPastLowerY a w s e) := by
  sorry
theorem fixedPastUpper_extremum {a : ℝ} (ha : 1 < a) {w : List ℤ}
    (hw : PositiveWord w) (hwne : w ≠ []) (s : ℕ) (e : Departure) :
    fixedPastUpperY a w s e ∈ runCell a s e ∧
    ∀ y ∈ runCell a s e,
      fixedPastUpperBound a w s e ≤ upper a (wordPast w) y ∧
      (upper a (wordPast w) y = fixedPastUpperBound a w s e ↔ y = fixedPastUpperY a w s e) := by
  sorry
theorem fixedPast_bounds_rational {a : ℤ} (ha : 2 ≤ a) {w : List ℤ}
    (hw : PositiveWord w) (hwne : w ≠ []) (s : ℕ) (e : Departure) :
    (∃ q : ℚ, fixedPastLowerBound a w s e = q) ∧
      (∃ q : ℚ, fixedPastUpperBound a w s e = q) := by
  sorry
theorem fixed_past_bounds {α : ℝ} (hα : Irrational α) {w : List ℤ}
    (hw : PositiveWord w) (hwne : w ≠ []) (hword : HasInitialWord α w)
    {a : ℤ} (ha : 2 ≤ a) (s : ℕ) (e : Departure)
    (hd : digit α (w.length+1) = a) (hf : ExactFutureRun α (w.length-1) a s e) :
    minimumTriple α (w.length-1) < fixedPastLowerBound a w s e ∧
      fixedPastUpperBound a w s e < maximumTriple α (w.length-1) := by
  sorry
theorem fixedPast_bounds_strict_threshold {a : ℤ} (ha : 2 ≤ a) {w : List ℤ}
    (hw : PositiveWord w) (hwne : w ≠ []) (s : ℕ) (e : Departure) :
    fixedPastLowerBound a w s e < threshold a ∧
      threshold a < fixedPastUpperBound a w s e := by
  sorry
theorem fixed_past_lower_sharp {w : List ℤ} (hw : PositiveWord w) (hwne : w ≠ [])
    {a : ℤ} (ha : 2 ≤ a) (s : ℕ) (e : Departure) (ε : ℝ) (hε : 0 < ε) :
    ∃ α : ℝ, Irrational α ∧ HasInitialWord α w ∧ digit α (w.length+1) = a ∧
      ExactFutureRun α (w.length-1) a s e ∧
      fixedPastLowerBound a w s e - ε < minimumTriple α (w.length-1) ∧
      minimumTriple α (w.length-1) < fixedPastLowerBound a w s e := by
  sorry
theorem fixed_past_upper_sharp {w : List ℤ} (hw : PositiveWord w) (hwne : w ≠ [])
    {a : ℤ} (ha : 2 ≤ a) (s : ℕ) (e : Departure) (ε : ℝ) (hε : 0 < ε) :
    ∃ α : ℝ, Irrational α ∧ HasInitialWord α w ∧ digit α (w.length+1) = a ∧
      ExactFutureRun α (w.length-1) a s e ∧
      fixedPastUpperBound a w s e < maximumTriple α (w.length-1) ∧
      maximumTriple α (w.length-1) < fixedPastUpperBound a w s e + ε := by
  sorry
theorem exhausted_fixed_past_bounds {α : ℝ} (hα : Irrational α) {a : ℤ} (ha : 2 ≤ a)
    (n s : ℕ) (e : Departure) (hp : ∀ k, 1 ≤ k → k ≤ n+1 → digit α k = a)
    (hd : digit α (n+2) = a) (hf : ExactFutureRun α n a s e) :
    minimumTriple α n < fixedPastLowerBound a (List.replicate (n+1) a) s e ∧
      fixedPastUpperBound a (List.replicate (n+1) a) s e < maximumTriple α n := by
  sorry
theorem fixed_word_metallic_realization {w : List ℤ} (hw : PositiveWord w) (hwne : w ≠ [])
    {a : ℤ} (ha : 2 ≤ a) :
    ∃ α : ℝ, Irrational α ∧ HasInitialWord α w ∧ digit α (w.length+1) = a ∧
      (∀ i : ℕ, digit α (w.length-1+3+i) = a) ∧
      minimumTriple α (w.length-1) = lower a (wordPast w) (metallic a) ∧
      maximumTriple α (w.length-1) = upper a (wordPast w) (metallic a) := by
  sorry
theorem terminal_one_endpoint (a : ℤ) :
    prependWord [a-1,1] 0 = 1/(a:ℝ) := by
  sorry
theorem exactFutureRun_iff_mem {α : ℝ} (hα : Irrational α) {a : ℤ} (ha : 2 ≤ a)
    (n s : ℕ) (e : Departure) :
    ExactFutureRun α n a s e ↔ future α n ∈ runCell a s e := by
  sorry
theorem fixed_word_irrational_future_realization {w : List ℤ}
    (hw : PositiveWord w) (hwne : w ≠ []) {a : ℤ} (ha : 2 ≤ a)
    (s : ℕ) (e : Departure) {y : ℝ} (hiy : Irrational y) (hy : y ∈ runCell a s e) :
    ∃ α : ℝ, Irrational α ∧
      (∀ k, (hk : k < w.length) → digit α (k+1) = w[k]) ∧
      digit α (w.length+1) = a ∧ ExactFutureRun α (w.length-1) a s e ∧
      past α (w.length-1) = prependWord w.reverse 0 ∧ future α (w.length-1) = y := by
  sorry
theorem global_upper_stability {a x y : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    upperStabilityConstant a * max |x-metallic a| |y-metallic a| ≤
      upper a x y-threshold a := by
  sorry
theorem global_upper_stability_eq_iff {a x y : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    upper a x y-threshold a =
        upperStabilityConstant a * max |x-metallic a| |y-metallic a| ↔
      x = metallic a ∧ y = metallic a := by
  sorry
theorem upperStabilityConstant_optimal {a K : ℝ} (ha : 2 ≤ a)
    (hK : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      K * max |x-metallic a| |y-metallic a| ≤ upper a x y-threshold a) :
    K ≤ upperStabilityConstant a := by
  sorry
theorem upperStabilityConstant_two :
    upperStabilityConstant 2 = (Real.sqrt 2-1)/4 := by
  sorry
theorem actual_upper_stability_strict {α : ℝ} {a : ℤ} (hα : Irrational α)
    (ha : 2 ≤ a) (n : ℕ) (hdigit : digit α (n+2) = a) :
    upperStabilityConstant a * max |past α n-metallic a| |future α n-metallic a| <
      maximumTriple α n-threshold a := by
  sorry
theorem actual_upperStabilityConstant_optimal {a : ℤ} {K : ℝ} (ha : 2 ≤ a)
    (hK : ∀ α : ℝ, Irrational α → ∀ n : ℕ, digit α (n+2) = a →
      K * max |past α n-metallic a| |future α n-metallic a| ≤
        maximumTriple α n-threshold a) : K ≤ upperStabilityConstant a := by
  sorry
theorem actual_upper_stability_sharp {a : ℤ} (ha : 2 ≤ a) {K : ℝ}
    (hK : upperStabilityConstant a < K) :
    ∃ α : ℝ, ∃ n : ℕ, Irrational α ∧ digit α (n+2) = a ∧
      maximumTriple α n-threshold a <
        K * max |past α n-metallic a| |future α n-metallic a| := by
  sorry
theorem rational_past_irrational_future_realization {a : ℤ} (ha : 1 ≤ a)
    (x : ℚ) (hx : 0 < x) (hx1 : x ≤ 1) {y : ℝ}
    (hiy : Irrational y) (hy : 0 < y) (hy1 : y < 1) :
    ∃ α : ℝ, ∃ n : ℕ, Irrational α ∧ digit α (n+2) = a ∧
      past α n = (x:ℝ) ∧ future α n = y := by
  sorry
theorem actual_coordinate_sequences {a : ℤ} (ha : 1 ≤ a) {x y : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    ∃ α : ℕ → ℝ, ∃ n : ℕ → ℕ,
      (∀ N, Irrational (α N) ∧ digit (α N) (n N+2) = a) ∧
      Tendsto (fun N => past (α N) (n N)) atTop (nhds x) ∧
      Tendsto (fun N => future (α N) (n N)) atTop (nhds y) := by
  sorry
theorem run_gap_bounds {a : ℝ} (ha : 2 ≤ a) (r s : ℕ) (e f : Departure) :
    stabilityConstant a * max (runDistanceNear a r e) (runDistanceNear a s f) ≤
        threshold a-runLowerBound a r s e f ∧
      threshold a-runLowerBound a r s e f ≤
        runDistanceFar a r e+runDistanceFar a s f ∧
      upperStabilityConstant a * max (runDistanceNear a r e) (runDistanceNear a s f) ≤
        runUpperBound a r s e f-threshold a ∧
      runUpperBound a r s e f-threshold a ≤
        runDistanceFar a r e+runDistanceFar a s f := by
  sorry
theorem lowerProfile_optimal {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    lowerProfileWitness a t ∈ Set.Icc (0 : ℝ) 1 ∧
      lower a t (lowerProfileWitness a t) = lowerProfile a t ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        lower a t u ≤ lowerProfile a t ∧
        (lower a t u = lowerProfile a t ↔ t = 0 ∨ u = lowerProfileWitness a t) := by
  sorry
theorem upperProfile_optimal {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    upperProfileWitness a t ∈ Set.Icc (0 : ℝ) 1 ∧
      upper a t (upperProfileWitness a t) = upperProfile a t ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        upperProfile a t ≤ upper a t u ∧
        (upper a t u = upperProfile a t ↔ u = upperProfileWitness a t) := by
  sorry
theorem sharp_window_complement_bounds {a L U x y : ℝ} (ha : 2 ≤ a)
    (hL : 0 ≤ L) (hLb : L ≤ metallic a) (hbU : metallic a ≤ U) (hU : U ≤ 1)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hout : ¬(x ∈ Set.Ioo L U ∧ y ∈ Set.Ioo L U)) :
    lower a x y ≤ sharpLowerWindowThreshold a L U ∧
      sharpUpperWindowThreshold a L U ≤ upper a x y := by
  sorry
theorem sharp_window_complement_attainment {a L U : ℝ} (ha : 2 ≤ a)
    (hL : L ∈ Set.Icc (0:ℝ) 1) (hU : U ∈ Set.Icc (0:ℝ) 1) :
    (∃ x ∈ Set.Icc (0:ℝ) 1, ∃ y ∈ Set.Icc (0:ℝ) 1,
      ¬(x ∈ Set.Ioo L U ∧ y ∈ Set.Ioo L U) ∧
      lower a x y = sharpLowerWindowThreshold a L U) ∧
    (∃ x ∈ Set.Icc (0:ℝ) 1, ∃ y ∈ Set.Icc (0:ℝ) 1,
      ¬(x ∈ Set.Ioo L U ∧ y ∈ Set.Ioo L U) ∧
      upper a x y = sharpUpperWindowThreshold a L U) := by
  sorry
theorem sharp_rectangle_complement_bounds {a Lx Ux Ly Uy x y : ℝ} (ha : 2 ≤ a)
    (hLx : 0 ≤ Lx) (hLxb : Lx ≤ metallic a) (hbUx : metallic a ≤ Ux) (hUx : Ux ≤ 1)
    (hLy : 0 ≤ Ly) (hLyb : Ly ≤ metallic a) (hbUy : metallic a ≤ Uy) (hUy : Uy ≤ 1)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hout : ¬(x ∈ Set.Ioo Lx Ux ∧ y ∈ Set.Ioo Ly Uy)) :
    lower a x y ≤ sharpLowerRectangleThreshold a Lx Ux Ly Uy ∧
      sharpUpperRectangleThreshold a Lx Ux Ly Uy ≤ upper a x y := by
  sorry
theorem sharp_rectangle_complement_attainment {a Lx Ux Ly Uy : ℝ} (ha : 2 ≤ a)
    (hLx : Lx ∈ Set.Icc (0:ℝ) 1) (hUx : Ux ∈ Set.Icc (0:ℝ) 1)
    (hLy : Ly ∈ Set.Icc (0:ℝ) 1) (hUy : Uy ∈ Set.Icc (0:ℝ) 1) :
    (∃ x ∈ Set.Icc (0:ℝ) 1, ∃ y ∈ Set.Icc (0:ℝ) 1,
      ¬(x ∈ Set.Ioo Lx Ux ∧ y ∈ Set.Ioo Ly Uy) ∧
      lower a x y = sharpLowerRectangleThreshold a Lx Ux Ly Uy) ∧
    (∃ x ∈ Set.Icc (0:ℝ) 1, ∃ y ∈ Set.Icc (0:ℝ) 1,
      ¬(x ∈ Set.Ioo Lx Ux ∧ y ∈ Set.Ioo Ly Uy) ∧
      upper a x y = sharpUpperRectangleThreshold a Lx Ux Ly Uy) := by
  sorry
theorem sharp_window_digit_window {α : ℝ} {a : ℤ} (hα : Irrational α)
    (ha : 2 ≤ a) (n r s : ℕ) (hd : digit α (n+2) = a)
    (hsharp : max (sharpLowerDigitThreshold a r) (sharpLowerDigitThreshold a s) <
        minimumTriple α n ∨
      maximumTriple α n < min (sharpUpperDigitThreshold a r) (sharpUpperDigitThreshold a s)) :
    r < n+1 ∧ (∀ i < r, digit α (n+1-i) = a) ∧
      (∀ i < s, digit α (n+3+i) = a) := by
  sorry
theorem sharp_symmetric_digit_window {α : ℝ} {a : ℤ} (hα : Irrational α)
    (ha : 2 ≤ a) (n r : ℕ) (hd : digit α (n+2) = a)
    (hsharp : sharpLowerDigitThreshold a r < minimumTriple α n ∨
      maximumTriple α n < sharpUpperDigitThreshold a r) :
    r < n+1 ∧ (∀ i < r, digit α (n+1-i) = a) ∧
      (∀ i < r, digit α (n+3+i) = a) := by
  sorry
theorem silver_sharp_window_one :
    sharpLowerDigitThreshold 2 1 = 10/29 ∧ sharpUpperDigitThreshold 2 1 = 21/58 := by
  sorry
theorem silver_sharp_window_two :
    sharpLowerDigitThreshold 2 2 = 119/338 ∧ sharpUpperDigitThreshold 2 2 = 60/169 := by
  sorry
theorem silver_sharp_window_three :
    sharpLowerDigitThreshold 2 3 = 348/985 ∧ sharpUpperDigitThreshold 2 3 = 697/1970 := by
  sorry
theorem actual_lower_window_sharp {a : ℤ} (ha : 2 ≤ a) (r : ℕ) (hr : 0 < r)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ α : ℝ, ∃ n : ℕ, Irrational α ∧ digit α (n+2) = a ∧
      ¬ (∀ i < r, digit α (n+3+i) = a) ∧
      sharpLowerWindowThreshold a (constantLower a r) (constantUpper a r)-ε <
        minimumTriple α n := by
  sorry
theorem actual_upper_window_sharp {a : ℤ} (ha : 2 ≤ a) (r : ℕ) (hr : 0 < r)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ α : ℝ, ∃ n : ℕ, Irrational α ∧ digit α (n+2) = a ∧
      ¬ (∀ i < r, digit α (n+3+i) = a) ∧
      maximumTriple α n <
        sharpUpperWindowThreshold a (constantLower a r) (constantUpper a r)+ε := by
  sorry
theorem actual_lower_window_threshold_optimal {a : ℤ} (ha : 2 ≤ a)
    (r : ℕ) (hr : 0 < r) {B : ℝ}
    (hB : ∀ α : ℝ, Irrational α → ∀ n : ℕ, digit α (n+2) = a →
      B < minimumTriple α n → ∀ i < r, digit α (n+3+i) = a) :
    sharpLowerWindowThreshold a (constantLower a r) (constantUpper a r) ≤ B := by
  sorry
theorem actual_upper_window_threshold_optimal {a : ℤ} (ha : 2 ≤ a)
    (r : ℕ) (hr : 0 < r) {B : ℝ}
    (hB : ∀ α : ℝ, Irrational α → ∀ n : ℕ, digit α (n+2) = a →
      maximumTriple α n < B → ∀ i < r, digit α (n+3+i) = a) :
    B ≤ sharpUpperWindowThreshold a (constantLower a r) (constantUpper a r) := by
  sorry
theorem rationalMinimumSupremum_cast (a : ℚ) (r s : ℕ) (e f : Departure) :
    (rationalMinimumSupremum a r s e f : ℝ) = minimumTripleSupremum a r s e f := by
  sorry
theorem rationalMaximumInfimum_cast (a : ℚ) (r s : ℕ) (e f : Departure) :
    (rationalMaximumInfimum a r s e f : ℝ) = maximumTripleInfimum a r s e f := by
  sorry
theorem rational_actual_run_bounds {α : ℝ} {a : ℤ} (hα : Irrational α) (ha : 2 ≤ a)
    (n r s : ℕ) (e f : Departure) (hd : digit α (n+2)=a)
    (hp : ExactPastRun α n a r e) (hf : ExactFutureRun α n a s f) :
    minimumTriple α n < (rationalMinimumSupremum a r s e f : ℝ) ∧
      (rationalMaximumInfimum a r s e f : ℝ) < maximumTriple α n := by
  sorry
theorem rational_silver_one_mixed :
    rationalMinimumSupremum 2 1 1 .low .high = 10/29 ∧
    rationalMaximumInfimum 2 1 1 .low .high = 21/58 := by
  sorry

end ContinuedFractionBounds
