module

public import ContinuedFractionBounds.ContinuedFractions

@[expose] public section

namespace ContinuedFractionBounds

/-- Prepend a positive partial quotient to a tail. -/
noncomputable def prependDigit (b : ℤ) (t : ℝ) : ℝ := ((b : ℝ) + t)⁻¹

theorem prependDigit_mem {b : ℤ} {t : ℝ} (hb : 1 ≤ b) (ht : 0 < t) :
    0 < prependDigit b t ∧ prependDigit b t < 1 := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hd : 1 < (b : ℝ) + t := by linarith
  exact ⟨inv_pos.mpr (by linarith), (inv_lt_one₀ (by linarith)).mpr hd⟩

theorem prependDigit_irrational {b : ℤ} {t : ℝ} (ht : Irrational t) :
    Irrational (prependDigit b t) := (ht.intCast_add b).inv

theorem floor_prependDigit {b : ℤ} {t : ℝ} (hb : 1 ≤ b) (ht : 0 < t) :
    ⌊prependDigit b t⌋ = 0 := by
  apply Int.floor_eq_iff.mpr
  simpa using ⟨(prependDigit_mem hb ht).1.le, (prependDigit_mem hb ht).2⟩

theorem fract_prependDigit {b : ℤ} {t : ℝ} (hb : 1 ≤ b) (ht : 0 < t) :
    Int.fract (prependDigit b t) = prependDigit b t := by
  simp only [Int.fract, floor_prependDigit hb ht, Int.cast_zero, sub_zero]

theorem floor_int_add_tail (b : ℤ) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    ⌊(b : ℝ) + t⌋ = b := by
  apply Int.floor_eq_iff.mpr
  constructor <;> linarith

theorem fract_int_add_tail (b : ℤ) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    Int.fract ((b : ℝ) + t) = t := by
  rw [Int.fract, floor_int_add_tail b ht₀ ht₁]; ring

/-- An irrational with first digits `[0;1,a]` and prescribed future `y`. -/
noncomputable def onePastRealization (a : ℤ) (y : ℝ) : ℝ :=
  prependDigit 1 (prependDigit a y)

theorem onePastRealization_irrational {a : ℤ} {y : ℝ} (hy : Irrational y) :
    Irrational (onePastRealization a y) := prependDigit_irrational (prependDigit_irrational hy)

theorem onePastRealization_quotients {a : ℤ} {y : ℝ}
    (ha : 1 ≤ a) (hy₀ : 0 < y) (_hy₁ : y < 1) :
    completeQuotient (onePastRealization a y) 1 = 1 + prependDigit a y ∧
    completeQuotient (onePastRealization a y) 2 = (a : ℝ) + y := by
  have hi := prependDigit_mem ha hy₀
  have h₁ : completeQuotient (onePastRealization a y) 1 = 1 + prependDigit a y := by
    change (Int.fract (prependDigit 1 (prependDigit a y)))⁻¹ = _
    rw [fract_prependDigit (by norm_num) hi.1]
    simp [prependDigit]
  refine ⟨h₁, ?_⟩
  change (Int.fract (completeQuotient (onePastRealization a y) 1))⁻¹ = _
  rw [h₁]
  have hf : Int.fract (1 + prependDigit a y) = prependDigit a y :=
    by simpa only [Int.cast_one] using fract_int_add_tail 1 hi.1.le hi.2
  rw [hf]
  simp [prependDigit]

/-- This realizes the actual finite state `x=1`, retaining the legitimate last digit `1`. -/
theorem onePastRealization_states {a : ℤ} {y : ℝ}
    (ha : 1 ≤ a) (hy : Irrational y) (hy₀ : 0 < y) (hy₁ : y < 1) :
    Irrational (onePastRealization a y) ∧
    digit (onePastRealization a y) 0 = 0 ∧
    digit (onePastRealization a y) 1 = 1 ∧
    digit (onePastRealization a y) 2 = a ∧
    past (onePastRealization a y) 0 = 1 ∧
    future (onePastRealization a y) 0 = y := by
  have hi := prependDigit_mem ha hy₀
  have hq := onePastRealization_quotients ha hy₀ hy₁
  have hα := onePastRealization_irrational (a := a) hy
  have hd₁ : digit (onePastRealization a y) 1 = 1 := by
    change ⌊completeQuotient (onePastRealization a y) 1⌋ = _
    rw [hq.1]
    simpa only [Int.cast_one] using floor_int_add_tail 1 hi.1.le hi.2
  refine ⟨hα, floor_prependDigit (by norm_num) hi.1, hd₁, ?_, ?_, ?_⟩
  · change ⌊completeQuotient (onePastRealization a y) 2⌋ = a
    rw [hq.2]; exact floor_int_add_tail a hy₀.le hy₁
  · simp only [past, denominator_zero, zero_add, denominator_one hα, hd₁,
      Int.cast_one, div_one]
  · change Int.fract (completeQuotient (onePastRealization a y) 2) = y
    rw [hq.2]; exact fract_int_add_tail a hy₀.le hy₁

/-- The positive silver tail `[0;2,2,2,…]`. -/
noncomputable def silverTail : ℝ := Real.sqrt 2 - 1

theorem silverTail_mem : 0 < silverTail ∧ silverTail < 1 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2:ℝ)
  dsimp [silverTail]
  constructor <;> nlinarith

theorem silverTail_irrational : Irrational silverTail := by
  simpa only [silverTail, Rat.cast_one] using irrational_sqrt_two.sub_ratCast 1

theorem silverTail_inv : silverTail⁻¹ = 2 + silverTail := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  apply inv_eq_of_mul_eq_one_right
  dsimp [silverTail]
  nlinarith

/-- The future `[0;a+1,N+1,2,2,…]`, with `N+1` ensuring a positive digit. -/
noncomputable def sharpFuture (a : ℤ) (N : ℕ) : ℝ :=
  prependDigit (a+1) (prependDigit (N+1) silverTail)

/-- The actual irrational `[0;1,a,a+1,N+1,2,2,…]`. -/
noncomputable def sharpReal (a : ℤ) (N : ℕ) : ℝ :=
  onePastRealization a (sharpFuture a N)

theorem sharpFuture_irrational (a : ℤ) (N : ℕ) : Irrational (sharpFuture a N) :=
  prependDigit_irrational (prependDigit_irrational silverTail_irrational)

theorem sharpFuture_mem {a : ℤ} (ha : 1 ≤ a) (N : ℕ) :
    0 < sharpFuture a N ∧ sharpFuture a N < 1 :=
  prependDigit_mem (by omega) (prependDigit_mem (by omega) silverTail_mem.1).1

theorem sharpReal_states {a : ℤ} (ha : 1 ≤ a) (N : ℕ) :
    Irrational (sharpReal a N) ∧
    digit (sharpReal a N) 0 = 0 ∧ digit (sharpReal a N) 1 = 1 ∧
    digit (sharpReal a N) 2 = a ∧
    past (sharpReal a N) 0 = 1 ∧ future (sharpReal a N) 0 = sharpFuture a N :=
  onePastRealization_states ha (sharpFuture_irrational a N)
    (sharpFuture_mem ha N).1 (sharpFuture_mem ha N).2

/-- The actual futures approach the rational endpoint from below. -/
theorem sharpFuture_lt_endpoint {a : ℤ} (ha : 1 ≤ a) (N : ℕ) :
    sharpFuture a N < 1 / ((a : ℝ)+1) := by
  have ht := (prependDigit_mem (b := (N+1 : ℤ)) (by omega) silverTail_mem.1).1
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
  dsimp [sharpFuture, prependDigit] at *
  simp only [Int.cast_add, Int.cast_one, Int.cast_natCast] at ht ⊢
  rw [one_div]
  exact inv_lt_inv₀ (by linarith) (by positivity) |>.mpr (by linarith)

open Filter in
/-- The explicit actual family converges to the sharp stability corner. -/
theorem sharpFuture_tendsto {a : ℤ} (ha : 1 ≤ a) :
    Tendsto (sharpFuture a) atTop (nhds (1 / ((a : ℝ)+1))) := by
  have hn : Tendsto (fun N : ℕ => (N:ℝ) + (1+silverTail)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp hn
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
  have ht := (tendsto_const_nhds.add hi).inv₀ (show (a:ℝ)+1+0 ≠ 0 by linarith)
  change Tendsto (fun N : ℕ => (((a+1 : ℤ):ℝ) +
    (((N+1 : ℤ):ℝ) + silverTail)⁻¹)⁻¹) atTop (nhds (1 / ((a:ℝ)+1)))
  simpa only [Int.cast_add, Int.cast_one, Int.cast_natCast, add_assoc, add_zero, one_div, Function.comp_def] using ht

end ContinuedFractionBounds
