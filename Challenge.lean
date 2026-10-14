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
@[expose] noncomputable def levelBoundary (a t z : ℝ) : ℝ :=
  t * (a + z) / (a + z - t)

theorem convergent_eq (α : ℝ) (n : ℕ) :
    numerator α n / denominator α n = (α.convergent n : ℝ) :=
  Real.convs_eq_convergent α n

theorem past_rational (α : ℝ) (n : ℕ) : ∃ r : ℚ, past α n = r := by
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

end ContinuedFractionBounds
