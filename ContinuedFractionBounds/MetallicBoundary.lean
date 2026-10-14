module

public import ContinuedFractionBounds.Applications
public import ContinuedFractionBounds.ContinuedFractionsRunSharpness
public import ContinuedFractionBounds.Runs
public import ContinuedFractionBounds.Rectangles

/-! # Metallic futures and the finite-past boundary -/

@[expose] public section
namespace ContinuedFractionBounds

theorem metallic_irrational {a : ℤ} (ha : 2 ≤ a) : Irrational (metallic (a : ℝ)) := by
  have hn : ¬ IsSquare (a^2+4) := by
    rintro ⟨b, hb⟩
    have habs : 0 ≤ |b| := abs_nonneg b
    have he : |b|^2 = a^2+4 := by nlinarith [sq_abs b]
    have hlo : a < |b| := by nlinarith
    have hhi : |b| < a+1 := by nlinarith
    omega
  have hs := (irrational_sqrt_intCast_iff_of_nonneg (show (0:ℤ) ≤ a^2+4 by positivity)).mpr hn
  have ht := (hs.sub_intCast a).div_intCast (m := 2) (by norm_num)
  simpa [metallic] using ht

theorem metallic_inverse (a : ℝ) : (metallic a)⁻¹ = a+metallic a := by
  apply (inv_eq_iff_eq_inv).mpr
  have he := metallic_equation a
  apply eq_inv_of_mul_eq_one_left
  simpa only [mul_comm] using he

/-- The metallic irrational has the constant positive digit expansion. -/
theorem metallic_digits {a : ℤ} (ha : 2 ≤ a) (n : ℕ) :
    digit (metallic (a:ℝ)) (n+1) = a := by
  have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha
  have hb := metallic_pos (a:ℝ)
  have hb1 := metallic_lt_one (by linarith : (1:ℝ) ≤ a)
  have hfract : Int.fract (metallic (a:ℝ)) = metallic (a:ℝ) :=
    Int.fract_eq_self.mpr ⟨hb.le, hb1⟩
  have hq (n : ℕ) : completeQuotient (metallic (a:ℝ)) (n+1) = (a:ℝ)+metallic a := by
    induction n with
    | zero => simpa only [completeQuotient, hfract] using metallic_inverse (a:ℝ)
    | succ n ih =>
      change (Int.fract (completeQuotient (metallic (a:ℝ)) (n+1)))⁻¹ = _
      rw [ih, fract_int_add_tail a hb.le hb1, metallic_inverse]
  unfold digit
  rw [hq]
  exact floor_int_add_tail a hb.le hb1

theorem metallic_future {a : ℤ} (ha : 2 ≤ a) (n : ℕ) :
    future (metallic (a:ℝ)) n = metallic (a:ℝ) := by
  have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha
  have hb := metallic_pos (a:ℝ)
  have hb1 := metallic_lt_one (by linarith : (1:ℝ) ≤ a)
  have hq (k : ℕ) : Int.fract (completeQuotient (metallic (a:ℝ)) k) = metallic (a:ℝ) := by
    induction k with
    | zero => exact Int.fract_eq_self.mpr ⟨hb.le, hb1⟩
    | succ k ih =>
      change Int.fract (Int.fract (completeQuotient (metallic (a:ℝ)) k))⁻¹ = _
      rw [ih, metallic_inverse]
      exact fract_int_add_tail a hb.le hb1
  exact hq (n+2)

/-- Below the metallic past, the first side coefficient is the minimum. -/
theorem metallic_future_low {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) (hxb : x ≤ metallic a) :
    lower a x (metallic a) = x*(a+metallic a)/(a+x+metallic a) ∧
    upper a x (metallic a) = 1/(a+x+metallic a) := by
  have hb := metallic_pos a
  have he := metallic_equation a
  have hleft : x*(a+metallic a) ≤ 1 := by nlinarith
  have hright : metallic a*(a+x) ≤ 1 := by nlinarith
  have hlr : x*(a+metallic a) ≤ metallic a*(a+x) := by nlinarith
  simp only [lower, upper, min_eq_left hlr, min_eq_right hleft,
    max_eq_right hlr, max_eq_left hright, and_self]

/-- Above the metallic past, the central coefficient is the minimum. -/
theorem metallic_future_high {a x : ℝ} (ha : 1 ≤ a) (hxb : metallic a ≤ x) :
    lower a x (metallic a) = 1/(a+x+metallic a) ∧
    upper a x (metallic a) = x*(a+metallic a)/(a+x+metallic a) := by
  have hb := metallic_pos a
  have he := metallic_equation a
  have hleft : 1 ≤ x*(a+metallic a) := by nlinarith
  have hright : 1 ≤ metallic a*(a+x) := by nlinarith
  have hrl : metallic a*(a+x) ≤ x*(a+metallic a) := by nlinarith
  simp only [lower, upper, min_eq_right hrl, min_eq_left hright,
    max_eq_left hrl, max_eq_right hleft, and_self]

/-- A fully exhausted constant past is the iterate of zero, with its literal
finite continued-fraction convention. -/
theorem exhausted_past {α : ℝ} (hα : Irrational α) {a : ℤ} (n : ℕ)
    (hd : ∀ k, 1 ≤ k → k ≤ n+1 → digit α k = a) :
    past α n = tailIter a (n+1) 0 := by
  have hb (k : ℕ) (hk : k ≤ n+1) : backwardState α k = tailIter a k 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [backwardState, hd (k+1) (by omega) hk, ih (by omega), tailIter_succ]
      simp [prependDigit, tailMap, one_div]
  rw [← backwardState_eq_past hα]
  exact hb (n+1) le_rfl

theorem metallic_past {a : ℤ} (ha : 2 ≤ a) (n : ℕ) :
    past (metallic (a:ℝ)) n = tailIter a (n+1) 0 := by
  apply exhausted_past (metallic_irrational ha)
  intro k hk _
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact metallic_digits ha m

@[simp] theorem metallic_numerator_zero {a : ℤ} (ha : 2 ≤ a) :
    numerator (metallic (a:ℝ)) 0 = 0 := by
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have hf : ⌊metallic (a:ℝ)⌋ = 0 := Int.floor_eq_iff.mpr
    (by simpa using ⟨(metallic_pos (a:ℝ)).le, metallic_lt_one ha'⟩)
  simp [numerator, GenContFract.zeroth_num_eq_h, GenContFract.of_h_eq_floor, hf]

@[simp] theorem metallic_numerator_one {a : ℤ} (ha : 2 ≤ a) :
    numerator (metallic (a:ℝ)) 1 = 1 := by
  have h := GenContFract.first_num_eq (gcf_digit (metallic_irrational ha) 0)
  have hz := metallic_numerator_zero ha
  change (GenContFract.of (metallic (a:ℝ))).h = 0 at hz
  simpa only [numerator, hz, mul_zero, one_mul, add_zero, zero_add] using h

@[simp] theorem metallic_denominator_one {a : ℤ} (ha : 2 ≤ a) :
    denominator (metallic (a:ℝ)) 1 = a := by
  rw [denominator_one (metallic_irrational ha), metallic_digits ha 0]

/-- The signed ordinary-convergent error for a constant positive digit. -/
theorem metallic_signed_error {a : ℤ} (ha : 2 ≤ a) (k : ℕ) :
    denominator (metallic (a:ℝ)) k * metallic a - numerator (metallic (a:ℝ)) k =
      (-1:ℝ)^k * (metallic a)^(k+1) := by
  have hr := metallic_equation (a:ℝ)
  induction k using Nat.twoStepInduction with
  | zero => simp [metallic_numerator_zero ha]
  | one =>
    rw [metallic_numerator_one ha, metallic_denominator_one ha]
    norm_num
    nlinarith
  | more k hk hk₁ =>
    rw [denominator_recurrence (metallic_irrational ha),
      numerator_recurrence (metallic_irrational ha), metallic_digits ha (k+1)]
    calc
      _ = (a:ℝ) * (denominator (metallic (a:ℝ)) (k+1) * metallic a -
            numerator (metallic (a:ℝ)) (k+1)) +
          (denominator (metallic (a:ℝ)) k * metallic a - numerator (metallic (a:ℝ)) k) := by ring
      _ = (a:ℝ) * ((-1:ℝ)^(k+1) * (metallic a)^(k+1+1)) +
          (-1:ℝ)^k * (metallic a)^(k+1) := by rw [hk, hk₁]
      _ = (-1:ℝ)^(k+2) * (metallic a)^(k+2+1) := by
        simp only [pow_succ]
        linear_combination -((-1:ℝ)^k * (metallic a)^k * metallic a) * hr

private theorem metallic_denominator_formula {a : ℤ} (ha : 2 ≤ a) (k : ℕ) :
    denominator (metallic (a:ℝ)) k * (metallic a)^(k+1) *
      ((a:ℝ)+2*metallic a) = 1 - (-1:ℝ)^(k+1)*(metallic a)^(2*k+2) := by
  have hr := metallic_equation (a:ℝ)
  have hab : (a:ℝ)*metallic a = 1-(metallic a)^2 := by nlinarith
  induction k using Nat.twoStepInduction with
  | zero => norm_num [denominator_zero]; nlinarith
  | one =>
    rw [metallic_denominator_one ha]
    norm_num
    calc
      _ = ((a:ℝ)*metallic a) * ((a:ℝ)*metallic a + 2*(metallic a)^2) := by ring
      _ = _ := by rw [hab]; ring
  | more k hk hk₁ =>
    rw [denominator_recurrence (metallic_irrational ha), metallic_digits ha (k+1)]
    calc
      _ = ((a:ℝ)*metallic a) *
          (denominator (metallic (a:ℝ)) (k+1) * (metallic a)^(k+1+1) *
            ((a:ℝ)+2*metallic a)) + (metallic a)^2 *
          (denominator (metallic (a:ℝ)) k * (metallic a)^(k+1) *
            ((a:ℝ)+2*metallic a)) := by ring
      _ = ((a:ℝ)*metallic a) * (1-(-1:ℝ)^(k+1+1)*(metallic a)^(2*(k+1)+2)) +
          (metallic a)^2 * (1-(-1:ℝ)^(k+1)*(metallic a)^(2*k+2)) := by rw [hk, hk₁]
      _ = _ := by
        rw [hab]
        simp only [pow_add, pow_mul]
        ring

/-- Exact alternating coefficients of the all-constant irrational.
The alternation is retained rather than claiming monotonicity of all coefficients. -/
theorem metallic_theta {a : ℤ} (ha : 2 ≤ a) (k : ℕ) :
    theta (metallic (a:ℝ)) k =
      (1 - (-1:ℝ)^(k+1)*(metallic a)^(2*k+2)) / Real.sqrt ((a:ℝ)^2+4) := by
  rw [theta, metallic_signed_error ha, abs_mul, abs_neg_one_pow,
    abs_of_pos (pow_pos (metallic_pos (a:ℝ)) _), one_mul]
  have he := metallic_denominator_formula ha k
  rw [metallic_add_eq_sqrt] at he
  exact (eq_div_iff (by positivity)).mpr he

theorem metallic_theta_even {a : ℤ} (ha : 2 ≤ a) (j : ℕ) :
    theta (metallic (a:ℝ)) (2*j) =
      (1+(metallic a)^(4*j+2)) / Real.sqrt ((a:ℝ)^2+4) := by
  rw [metallic_theta ha]
  simp only [pow_add, pow_mul]
  norm_num
  congr 2
  ring

theorem metallic_theta_odd {a : ℤ} (ha : 2 ≤ a) (j : ℕ) :
    theta (metallic (a:ℝ)) (2*j+1) =
      (1-(metallic a)^(4*j+4)) / Real.sqrt ((a:ℝ)^2+4) := by
  rw [metallic_theta ha]
  simp only [pow_add, pow_mul]
  norm_num
  congr 2
  ring

theorem metallic_theta_even_gt {a : ℤ} (ha : 2 ≤ a) (j : ℕ) :
    threshold (a:ℝ) < theta (metallic (a:ℝ)) (2*j) := by
  rw [metallic_theta_even ha]
  exact (div_lt_div_iff_of_pos_right (by positivity)).mpr
    (by have := pow_pos (metallic_pos (a:ℝ)) (4*j+2); linarith)

theorem metallic_theta_odd_lt {a : ℤ} (ha : 2 ≤ a) (j : ℕ) :
    theta (metallic (a:ℝ)) (2*j+1) < threshold (a:ℝ) := by
  rw [metallic_theta_odd ha]
  exact (div_lt_div_iff_of_pos_right (by positivity)).mpr
    (by have := pow_pos (metallic_pos (a:ℝ)) (4*j+4); linarith)

private theorem metallic_theta_even_step {a : ℤ} (ha : 2 ≤ a) (j : ℕ) :
    theta (metallic (a:ℝ)) (2*j+2) ≤ theta (metallic (a:ℝ)) (2*j) := by
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  rw [show 2*j+2=2*(j+1) by omega, metallic_theta_even ha, metallic_theta_even ha]
  apply (div_le_div_iff_of_pos_right (by positivity)).mpr
  have hp := pow_le_pow_of_le_one (metallic_pos (a:ℝ)).le
    (metallic_lt_one ha').le (show 4*j+2 ≤ 4*(j+1)+2 by omega)
  linarith

private theorem metallic_theta_odd_step {a : ℤ} (ha : 2 ≤ a) (j : ℕ) :
    theta (metallic (a:ℝ)) (2*j+1) ≤ theta (metallic (a:ℝ)) (2*j+3) := by
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  rw [show 2*j+3=2*(j+1)+1 by omega, metallic_theta_odd ha, metallic_theta_odd ha]
  apply (div_le_div_iff_of_pos_right (by positivity)).mpr
  have hp := pow_le_pow_of_le_one (metallic_pos (a:ℝ)).le
    (metallic_lt_one ha').le (show 4*j+4 ≤ 4*(j+1)+4 by omega)
  linarith

/-- Exact three-coefficient minima and maxima when the middle index is odd. -/
theorem metallic_triple_even {a : ℤ} (ha : 2 ≤ a) (j : ℕ) :
    minimumTriple (metallic (a:ℝ)) (2*j) =
      (1-(metallic a)^(4*j+4)) / Real.sqrt ((a:ℝ)^2+4) ∧
    maximumTriple (metallic (a:ℝ)) (2*j) =
      (1+(metallic a)^(4*j+2)) / Real.sqrt ((a:ℝ)^2+4) := by
  have hl : theta (metallic (a:ℝ)) (2*j+1) ≤ theta (metallic (a:ℝ)) (2*j) :=
    (metallic_theta_odd_lt ha j).le.trans (metallic_theta_even_gt ha j).le
  have hr : theta (metallic (a:ℝ)) (2*j+1) ≤ theta (metallic (a:ℝ)) (2*j+2) := by
    simpa only [show 2*(j+1)=2*j+2 by omega] using
      (metallic_theta_odd_lt ha j).le.trans (metallic_theta_even_gt ha (j+1)).le
  have hh := metallic_theta_even_step ha j
  unfold minimumTriple maximumTriple
  rw [min_eq_left hr, min_eq_right hl, max_eq_right hr, max_eq_left hh]
  exact ⟨metallic_theta_odd ha j, metallic_theta_even ha j⟩

/-- Exact three-coefficient minima and maxima when the middle index is even. -/
theorem metallic_triple_odd {a : ℤ} (ha : 2 ≤ a) (j : ℕ) :
    minimumTriple (metallic (a:ℝ)) (2*j+1) =
      (1-(metallic a)^(4*j+4)) / Real.sqrt ((a:ℝ)^2+4) ∧
    maximumTriple (metallic (a:ℝ)) (2*j+1) =
      (1+(metallic a)^(4*j+6)) / Real.sqrt ((a:ℝ)^2+4) := by
  have hl : theta (metallic (a:ℝ)) (2*j+1) ≤ theta (metallic (a:ℝ)) (2*j+2) := by
    simpa only [show 2*(j+1)=2*j+2 by omega] using
      (metallic_theta_odd_lt ha j).le.trans (metallic_theta_even_gt ha (j+1)).le
  have hr : theta (metallic (a:ℝ)) (2*j+3) ≤ theta (metallic (a:ℝ)) (2*j+2) := by
    simpa only [show 2*(j+1)+1=2*j+3 by omega, show 2*(j+1)=2*j+2 by omega] using
      (metallic_theta_odd_lt ha (j+1)).le.trans (metallic_theta_even_gt ha (j+1)).le
  have hh := metallic_theta_odd_step ha j
  unfold minimumTriple maximumTriple
  rw [show 2*j+1+1=2*j+2 by omega, show 2*j+1+2=2*j+3 by omega,
    min_eq_right hr, min_eq_left hh, max_eq_left hr, max_eq_right hl]
  constructor
  · exact metallic_theta_odd ha j
  · simpa only [show 2*(j+1)=2*j+2 by omega, show 4*(j+1)+2=4*j+6 by omega] using
      metallic_theta_even ha (j+1)

open Filter in
/-- The alternating individual coefficients converge to the classical threshold. -/
theorem metallic_theta_tendsto {a : ℤ} (ha : 2 ≤ a) :
    Tendsto (theta (metallic (a:ℝ))) atTop (nhds (threshold (a:ℝ))) := by
  have hb := metallic_pos (a:ℝ)
  have hb1 := metallic_lt_one (show (1:ℝ) ≤ a by exact_mod_cast (show 1 ≤ a by omega))
  have hp := tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (show |-(metallic (a:ℝ))^2| < 1 by rw [abs_neg, abs_of_nonneg (sq_nonneg _)]; nlinarith)
  have hs := hp.mul_const (-(metallic (a:ℝ))^2)
  have hh := ((tendsto_const_nhds (x := (1:ℝ))).sub hs).div_const (Real.sqrt ((a:ℝ)^2+4))
  convert hh using 1
  · ext k
    rw [metallic_theta ha]
    congr 2
    rw [show -(metallic (a:ℝ))^2 = (-1:ℝ)*(metallic a)^2 by ring]
    simp only [pow_add, pow_mul, mul_pow]
    ring
  · simp [threshold]

open Filter in
theorem metallic_triples_tendsto {a : ℤ} (ha : 2 ≤ a) :
    Tendsto (minimumTriple (metallic (a:ℝ))) atTop (nhds (threshold (a:ℝ))) ∧
    Tendsto (maximumTriple (metallic (a:ℝ))) atTop (nhds (threshold (a:ℝ))) := by
  have h := metallic_theta_tendsto ha
  have h₁ := h.comp (tendsto_add_atTop_nat 1)
  have h₂ := h.comp (tendsto_add_atTop_nat 2)
  unfold minimumTriple maximumTriple
  exact ⟨by simpa only [Function.comp_def, min_self] using h.min (h₁.min h₂),
    by simpa only [Function.comp_def, max_self] using h.max (h₁.max h₂)⟩

theorem metallic_tail_propagation {α : ℝ} {a : ℤ} (ha : 2 ≤ a) {k : ℕ}
    (hk : forwardState α k = metallic (a:ℝ)) (i : ℕ) :
    forwardState α (k+i) = metallic (a:ℝ) ∧ digit α (k+i+1) = a := by
  have hb := metallic_pos (a:ℝ)
  have hb1 := metallic_lt_one (show (1:ℝ) ≤ a by exact_mod_cast (show 1 ≤ a by omega))
  have hs : ∀ j, forwardState α (k+j) = metallic (a:ℝ) := by
    intro j
    induction j with
    | zero => simpa using hk
    | succ j ih =>
      change Int.fract (Int.fract (completeQuotient α (k+j)))⁻¹ = _
      change Int.fract (forwardState α (k+j))⁻¹ = _
      rw [ih, metallic_inverse]
      exact fract_int_add_tail a hb.le hb1
  refine ⟨hs i, ?_⟩
  change ⌊(forwardState α (k+i))⁻¹⌋ = a
  rw [hs i, metallic_inverse]
  exact floor_int_add_tail a hb.le hb1

/-- The fixed irrational `[0;1,a-1,overline a]`. -/
noncomputable def metallicLowExample (a : ℤ) : ℝ :=
  prependWord [1,a-1] (metallic (a:ℝ))

/-- The fixed irrational `[0;a+1,overline a]`. -/
noncomputable def metallicHighExample (a : ℤ) : ℝ :=
  prependWord [a+1] (metallic (a:ℝ))

/-- A genuine equality candidate in every below-digit finite-past class. -/
theorem metallic_low_example_states {a : ℤ} (ha : 2 ≤ a) (r : ℕ) :
    Irrational (metallicLowExample a) ∧
    digit (metallicLowExample a) (r+3) = a ∧
    ExactPastRun (metallicLowExample a) (r+1) a r .low ∧
    past (metallicLowExample a) (r+1) = tailIter a r (1/(a:ℝ)) ∧
    future (metallicLowExample a) (r+1) = metallic (a:ℝ) := by
  have hw : PositiveWord [1,a-1] := by intro b hb; simp at hb; rcases hb with rfl | rfl <;> omega
  have hb := metallic_pos (a:ℝ)
  have hb1 := metallic_lt_one (show (1:ℝ) ≤ a by exact_mod_cast (show 1 ≤ a by omega))
  have hα : Irrational (metallicLowExample a) := prependWord_irrational _ (metallic_irrational ha)
  have hd₁ : digit (metallicLowExample a) 1 = 1 := prependWord_digit hw hb hb1 0 (by simp)
  have hd₂ : digit (metallicLowExample a) 2 = a-1 := prependWord_digit hw hb hb1 1 (by simp)
  have ht : forwardState (metallicLowExample a) 2 = metallic (a:ℝ) := prependWord_tail hw hb hb1
  have hds (j : ℕ) : digit (metallicLowExample a) (j+3) = a := by
    simpa only [show 2+j+1=j+3 by omega] using (metallic_tail_propagation ha ht j).2
  have hrun : ExactPastRun (metallicLowExample a) (r+1) a r .low := by
    refine ⟨by omega, ?_, ?_⟩
    · intro i hi
      rw [show r+1+1-i=(r-1-i)+3 by omega]
      exact hds _
    · rw [show r+1+1-r=2 by omega, hd₂]
      exact ⟨by omega, by omega⟩
  refine ⟨hα, hds r, hrun, ?_, ?_⟩
  · rw [← backwardState_eq_past hα, backwardState_run _ a (r+1+1) r (by omega) hrun.2.1]
    have hs : backwardState (metallicLowExample a) 2 = 1/(a:ℝ) := by
      simp [backwardState, hd₁, hd₂, prependDigit]
    rw [show r+1+1-r=2 by omega, hs]
  · change forwardState (metallicLowExample a) (r+1+2) = _
    simpa only [show 2+(r+1)=r+1+2 by omega] using (metallic_tail_propagation ha ht (r+1)).1

/-- A genuine equality candidate in every above-digit finite-past class. -/
theorem metallic_high_example_states {a : ℤ} (ha : 2 ≤ a) (r : ℕ) :
    Irrational (metallicHighExample a) ∧
    digit (metallicHighExample a) (r+2) = a ∧
    ExactPastRun (metallicHighExample a) r a r .high ∧
    past (metallicHighExample a) r = tailIter a r (1/((a:ℝ)+1)) ∧
    future (metallicHighExample a) r = metallic (a:ℝ) := by
  have hw : PositiveWord [a+1] := by intro b hb; simp at hb; subst b; omega
  have hb := metallic_pos (a:ℝ)
  have hb1 := metallic_lt_one (show (1:ℝ) ≤ a by exact_mod_cast (show 1 ≤ a by omega))
  have hα : Irrational (metallicHighExample a) := prependWord_irrational _ (metallic_irrational ha)
  have hd₁ : digit (metallicHighExample a) 1 = a+1 := prependWord_digit hw hb hb1 0 (by simp)
  have ht : forwardState (metallicHighExample a) 1 = metallic (a:ℝ) := prependWord_tail hw hb hb1
  have hds (j : ℕ) : digit (metallicHighExample a) (j+2) = a := by
    simpa only [show 1+j+1=j+2 by omega] using (metallic_tail_propagation ha ht j).2
  have hrun : ExactPastRun (metallicHighExample a) r a r .high := by
    refine ⟨le_rfl, ?_, ?_⟩
    · intro i hi
      rw [show r+1-i=(r-1-i)+2 by omega]
      exact hds _
    · rw [show r+1-r=1 by omega, hd₁]
      change a < a+1
      omega
  refine ⟨hα, hds r, hrun, ?_, ?_⟩
  · rw [← backwardState_eq_past hα, backwardState_run _ a (r+1) r (by omega) hrun.2.1]
    have hs : backwardState (metallicHighExample a) 1 = 1/((a:ℝ)+1) := by
      simp [backwardState, hd₁, prependDigit]
    rw [show r+1-r=1 by omega, hs]
  · change forwardState (metallicHighExample a) (r+2) = _
    simpa only [show 1+(r+1)=r+2 by omega] using (metallic_tail_propagation ha ht (r+1)).1

/-- The departure endpoint nearest the metallic fixed point. -/
noncomputable def metallicNearestTail (a : ℝ) : Departure → ℝ
  | .low => 1/a
  | .high => 1/(a+1)

private theorem metallic_boundary_between {a x z : ℝ} (ha : 1 < a)
    (hx : 0 ≤ x) (hz : 0 < z)
    (hbet : (x ≤ z ∧ z ≤ metallic a) ∨ (metallic a ≤ z ∧ z ≤ x)) :
    lower a x (metallic a) ≤ lower a z (metallic a) ∧
    upper a z (metallic a) ≤ upper a x (metallic a) ∧
    (lower a x (metallic a) = lower a z (metallic a) ↔ x = z) ∧
    (upper a x (metallic a) = upper a z (metallic a) ↔ x = z) := by
  have hb := metallic_pos a
  rcases hbet with ⟨hxz, hzb⟩ | ⟨hbz, hzx⟩
  · have hP := products_below_metallic (by linarith : 0<a) hz.le hb.le hzb le_rfl
    have hQ : min (z*(a+metallic a)) (metallic a*(a+z)) ≤ 1 :=
      (min_le_max).trans hP
    have hL := lower_below_corner (by linarith : 0<a) hx hb.le hz hb hxz le_rfl hQ
    have hU := upper_below_corner (by linarith : 0<a) hx hb.le hxz le_rfl hP
    exact ⟨hL.1, hU.1, by simpa using hL.2, by simpa using hU.2⟩
  · have hQ := products_above_metallic (by linarith : 0<a) hbz le_rfl
    have hP : 1 ≤ max (z*(a+metallic a)) (metallic a*(a+z)) :=
      hQ.trans min_le_max
    have hL := lower_above_corner (by linarith : 0<a) hz.le hb.le hzx le_rfl hQ
    have hU := upper_above_corner (by linarith : 0<a) hz.le hb.le hzx le_rfl hP
    exact ⟨hL.1, hU.1, by simpa using hL.2, by simpa using hU.2⟩

private theorem tailIter_nearest_between {a : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure)
    {t : ℝ} (ht : t ∈ departureInterval a e) :
    (tailIter a r t ≤ tailIter a r (metallicNearestTail a e) ∧
      tailIter a r (metallicNearestTail a e) ≤ metallic a) ∨
    (metallic a ≤ tailIter a r (metallicNearestTail a e) ∧
      tailIter a r (metallicNearestTail a e) ≤ tailIter a r t) := by
  have hc := tailIter_continuousOn ha r
  have hi := (tailIter_injective a r).injOn (s := Set.Icc (0:ℝ) 1)
  have hbunit : metallic a ∈ Set.Icc (0:ℝ) 1 :=
    ⟨(metallic_pos a).le, (metallic_lt_one ha.le).le⟩
  have htunit := departureInterval_subset_unit ha e ht
  have hnear : metallicNearestTail a e ∈ Set.Icc (0:ℝ) 1 := by
    cases e
    · exact selectedDepartureEndpoint_mem ha .low false
    · exact selectedDepartureEndpoint_mem ha .high true
  have hfix := metallic_tailIter ha r
  have hmiddle := metallic_mem_middle ha
  rcases hc.strictMonoOn_of_injOn_Icc' (by norm_num : (0:ℝ) ≤ 1) hi with hm | hm
  · cases e with
    | low =>
      apply Or.inr
      constructor
      · rw [← hfix]
        exact hm.monotoneOn hbunit hnear hmiddle.2.le
      · exact hm.monotoneOn hnear htunit ht.1
    | high =>
      apply Or.inl
      constructor
      · exact hm.monotoneOn htunit hnear ht.2
      · rw [← hfix]
        exact hm.monotoneOn hnear hbunit hmiddle.1.le
  · cases e with
    | low =>
      apply Or.inl
      constructor
      · exact hm.antitoneOn hnear htunit ht.1
      · rw [← hfix]
        exact hm.antitoneOn hbunit hnear hmiddle.2.le
    | high =>
      apply Or.inr
      constructor
      · rw [← hfix]
        exact hm.antitoneOn hnear hbunit hmiddle.1.le
      · exact hm.antitoneOn htunit hnear ht.2

/-- Both extrema for a terminated past and an infinite metallic future occur
at the same nearest endpoint, with a unique coordinate equality case. -/
theorem metallic_future_run_extrema {a x : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure)
    (hx : x ∈ runCell a r e) :
    let z := tailIter a r (metallicNearestTail a e)
    lower a x (metallic a) ≤ lower a z (metallic a) ∧
    upper a z (metallic a) ≤ upper a x (metallic a) ∧
    (lower a x (metallic a) = lower a z (metallic a) ↔ x = z) ∧
    (upper a x (metallic a) = upper a z (metallic a) ↔ x = z) := by
  have hxunit := runCell_subset_unit ha r e hx
  have hn : metallicNearestTail a e ∈ Set.Ioo (0:ℝ) 1 := by
    cases e <;> dsimp [metallicNearestTail]
    · exact ⟨by positivity, (div_lt_one (by linarith)).mpr ha⟩
    · exact ⟨by positivity, (div_lt_one (by linarith)).mpr (by linarith)⟩
  have hz := (tailIter_mem_unit_strict ha r hn).1
  obtain ⟨t, ht, rfl⟩ := hx
  exact metallic_boundary_between ha hxunit.1 hz (tailIter_nearest_between ha r e ht)

/-- The displayed low-departure irrational attains both sharp metallic-future bounds. -/
theorem metallic_low_example_attains {a : ℤ} (ha : 2 ≤ a) (r : ℕ) :
    minimumTriple (metallicLowExample a) (r+1) =
      lower a (tailIter a r (1/(a:ℝ))) (metallic a) ∧
    maximumTriple (metallicLowExample a) (r+1) =
      upper a (tailIter a r (1/(a:ℝ))) (metallic a) := by
  obtain ⟨hα, hd, _, hx, hy⟩ := metallic_low_example_states ha r
  rw [actual_minimum_eq hα, actual_maximum_eq hα, show r+1+2=r+3 by omega, hd, hx, hy]
  exact ⟨rfl, rfl⟩

/-- The displayed high-departure irrational attains both sharp metallic-future bounds. -/
theorem metallic_high_example_attains {a : ℤ} (ha : 2 ≤ a) (r : ℕ) :
    minimumTriple (metallicHighExample a) r =
      lower a (tailIter a r (1/((a:ℝ)+1))) (metallic a) ∧
    maximumTriple (metallicHighExample a) r =
      upper a (tailIter a r (1/((a:ℝ)+1))) (metallic a) := by
  obtain ⟨hα, hd, _, hx, hy⟩ := metallic_high_example_states ha r
  rw [actual_minimum_eq hα, actual_maximum_eq hα, hd, hx, hy]
  exact ⟨rfl, rfl⟩

/-- A finite ordinary past never equals the irrational metallic state. -/
theorem past_ne_metallic {a : ℤ} (ha : 2 ≤ a) (α : ℝ) (n : ℕ) :
    past α n ≠ metallic (a:ℝ) := by
  obtain ⟨q, hq⟩ := past_rational α n
  intro he
  exact (metallic_irrational ha).ne_rat q (he.symm.trans hq)

/-- Infinite constant actual future digits are equivalent to the metallic future state. -/
theorem infinite_future_iff_metallic {α : ℝ} (hα : Irrational α)
    {a : ℤ} (ha : 2 ≤ a) (n : ℕ) :
    (∀ i : ℕ, digit α (n+3+i) = a) ↔ future α n = metallic (a:ℝ) := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  have hbunit : metallic (a:ℝ) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨(metallic_pos (a:ℝ)).le, (metallic_lt_one ha'.le).le⟩
  constructor
  · intro hd
    have he (r : ℕ) : forwardState α (n+2) = tailIter a r (forwardState α (n+2+r)) := by
      apply forwardState_run hα
      intro i _
      simpa only [show n+2+i+1=n+3+i by omega] using hd i
    have hbound (r : ℕ) : |future α n - metallic (a:ℝ)| ≤ (1/(a:ℝ)^2)^r := by
      have htunit : forwardState α (n+2+r) ∈ Set.Icc (0:ℝ) 1 :=
        ⟨(fract_completeQuotient_pos hα _).le, (Int.fract_lt_one _).le⟩
      have hh := tailIter_abs_sub_le ha' r htunit hbunit
      rw [metallic_tailIter ha', ← he r] at hh
      have hdif : |forwardState α (n+2+r) - metallic (a:ℝ)| ≤ 1 := by
        apply abs_le.mpr
        constructor <;> linarith [htunit.1, htunit.2, hbunit.1, hbunit.2]
      exact hh.trans (by simpa using (mul_le_mul_of_nonneg_left hdif
        (show 0 ≤ (1/(a:ℝ)^2)^r by positivity)))
    have hpow : Filter.Tendsto (fun r : ℕ => (1/(a:ℝ)^2)^r) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        ((div_lt_one (by positivity)).mpr (by nlinarith))
    have hzero : |future α n - metallic (a:ℝ)| ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hpow (Filter.Eventually.of_forall hbound)
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))
  · intro hf i
    have ht : forwardState α (n+2) = metallic (a:ℝ) := hf
    simpa only [show n+2+i+1=n+3+i by omega] using (metallic_tail_propagation ha ht i).2

end ContinuedFractionBounds
