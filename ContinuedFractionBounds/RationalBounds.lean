module

public import ContinuedFractionBounds.ActualRuns

/-! # Executable rational bounds and descriptive API names -/

@[expose] public section
namespace ContinuedFractionBounds

/-- Supremum of the minimum of an actual triple in a terminated two-sided run class. -/
noncomputable def minimumTripleSupremum := runLowerBound

/-- Infimum of the maximum of an actual triple in a terminated two-sided run class. -/
noncomputable def maximumTripleInfimum := runUpperBound

/-- Exact rational inverse-branch iteration, executable at every finite length. -/
def rationalTailIter (a : ℚ) (r : ℕ) (t : ℚ) : ℚ :=
  (fun z : ℚ => 1 / (a + z))^[r] t

def rationalDepartureLeft (a : ℚ) : Departure → ℚ
  | .low => 1/a
  | .high => 0

def rationalDepartureRight (a : ℚ) : Departure → ℚ
  | .low => 1
  | .high => 1/(a+1)

def rationalRunLower (a : ℚ) (r : ℕ) (e : Departure) : ℚ :=
  min (rationalTailIter a r (rationalDepartureLeft a e))
    (rationalTailIter a r (rationalDepartureRight a e))

def rationalRunUpper (a : ℚ) (r : ℕ) (e : Departure) : ℚ :=
  max (rationalTailIter a r (rationalDepartureLeft a e))
    (rationalTailIter a r (rationalDepartureRight a e))

def rationalLower (a x y : ℚ) : ℚ :=
  min 1 (min (x*(a+y)) (y*(a+x))) / (a+x+y)

def rationalUpper (a x y : ℚ) : ℚ :=
  max 1 (max (x*(a+y)) (y*(a+x))) / (a+x+y)

def rationalMinimumSupremum (a : ℚ) (r s : ℕ) (e f : Departure) : ℚ :=
  max (max (rationalLower a (rationalRunLower a r e) (rationalRunLower a s f))
    (rationalLower a (rationalRunLower a r e) (rationalRunUpper a s f)))
    (max (rationalLower a (rationalRunUpper a r e) (rationalRunLower a s f))
      (rationalLower a (rationalRunUpper a r e) (rationalRunUpper a s f)))

def rationalMaximumInfimum (a : ℚ) (r s : ℕ) (e f : Departure) : ℚ :=
  min (min (rationalUpper a (rationalRunLower a r e) (rationalRunLower a s f))
    (rationalUpper a (rationalRunLower a r e) (rationalRunUpper a s f)))
    (min (rationalUpper a (rationalRunUpper a r e) (rationalRunLower a s f))
      (rationalUpper a (rationalRunUpper a r e) (rationalRunUpper a s f)))

theorem rationalTailIter_cast (a t : ℚ) (r : ℕ) :
    (rationalTailIter a r t : ℝ) = tailIter a r t :=
  (tailIter_rat a t r).symm

theorem rationalDepartureLeft_cast (a : ℚ) (e : Departure) :
    (rationalDepartureLeft a e : ℝ) = departureLeft a e := by
  cases e <;> simp [rationalDepartureLeft, departureLeft]

theorem rationalDepartureRight_cast (a : ℚ) (e : Departure) :
    (rationalDepartureRight a e : ℝ) = departureRight a e := by
  cases e <;> simp [rationalDepartureRight, departureRight]

theorem rationalRunLower_cast (a : ℚ) (r : ℕ) (e : Departure) :
    (rationalRunLower a r e : ℝ) = runLower (a:ℝ) r e := by
  simp only [rationalRunLower, runLower, Rat.cast_min, rationalTailIter_cast,
    rationalDepartureLeft_cast, rationalDepartureRight_cast]

theorem rationalRunUpper_cast (a : ℚ) (r : ℕ) (e : Departure) :
    (rationalRunUpper a r e : ℝ) = runUpper (a:ℝ) r e := by
  simp only [rationalRunUpper, runUpper, Rat.cast_max, rationalTailIter_cast,
    rationalDepartureLeft_cast, rationalDepartureRight_cast]

theorem rationalLower_cast (a x y : ℚ) : (rationalLower a x y : ℝ) = lower a x y :=
  (lower_rat a x y).symm

theorem rationalUpper_cast (a x y : ℚ) : (rationalUpper a x y : ℝ) = upper a x y :=
  (upper_rat a x y).symm

/-- The executable rational result is definitionally connected to the proved real bound. -/
theorem rationalMinimumSupremum_cast (a : ℚ) (r s : ℕ) (e f : Departure) :
    (rationalMinimumSupremum a r s e f : ℝ) = minimumTripleSupremum a r s e f := by
  simp only [rationalMinimumSupremum, minimumTripleSupremum, runLowerBound,
    Rat.cast_max, rationalLower_cast, rationalRunLower_cast, rationalRunUpper_cast]

theorem rationalMaximumInfimum_cast (a : ℚ) (r s : ℕ) (e f : Departure) :
    (rationalMaximumInfimum a r s e f : ℝ) = maximumTripleInfimum a r s e f := by
  simp only [rationalMaximumInfimum, maximumTripleInfimum, runUpperBound,
    Rat.cast_min, rationalUpper_cast, rationalRunLower_cast, rationalRunUpper_cast]

/-- Rational outputs bound actual irrational triples, with the literal run hypotheses. -/
theorem rational_actual_run_bounds {α : ℝ} {a : ℤ} (hα : Irrational α) (ha : 2 ≤ a)
    (n r s : ℕ) (e f : Departure) (hd : digit α (n+2)=a)
    (hp : ExactPastRun α n a r e) (hf : ExactFutureRun α n a s f) :
    minimumTriple α n < (rationalMinimumSupremum a r s e f : ℝ) ∧
      (rationalMaximumInfimum a r s e f : ℝ) < maximumTriple α n := by
  rw [rationalMinimumSupremum_cast, rationalMaximumInfimum_cast]
  norm_cast
  have hh := actual_run_bounds hα ha n r s e f hd hp hf
  exact ⟨hh.1, hh.2.2.2⟩

theorem rational_silver_one_mixed :
    rationalMinimumSupremum 2 1 1 .low .high = 10/29 ∧
    rationalMaximumInfimum 2 1 1 .low .high = 21/58 := by
  norm_num [rationalMinimumSupremum,rationalMaximumInfimum,rationalLower,rationalUpper,
    rationalRunLower,rationalRunUpper,rationalTailIter,rationalDepartureLeft,rationalDepartureRight]

end ContinuedFractionBounds
