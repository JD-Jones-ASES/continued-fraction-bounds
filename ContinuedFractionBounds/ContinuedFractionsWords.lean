module

public import ContinuedFractionBounds.ContinuedFractionsRealization

@[expose] public section

namespace ContinuedFractionBounds

/-- Evaluate a finite word of positive digits before an arbitrary remaining tail. -/
noncomputable def prependWord : List ℤ → ℝ → ℝ
  | [], t => t
  | b :: bs, t => prependDigit b (prependWord bs t)

def PositiveWord (w : List ℤ) : Prop := ∀ b ∈ w, 1 ≤ b

theorem prependWord_mem {w : List ℤ} (hw : PositiveWord w) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) :
    0 < prependWord w t ∧ prependWord w t < 1 := by
  induction w with
  | nil => exact ⟨ht₀, ht₁⟩
  | cons b bs ih =>
    exact prependDigit_mem (hw b (by simp)) (ih (fun c hc => hw c (by simp [hc]))).1

theorem prependWord_irrational (w : List ℤ) {t : ℝ} (ht : Irrational t) :
    Irrational (prependWord w t) := by
  induction w with
  | nil => exact ht
  | cons b bs ih => exact prependDigit_irrational ih

theorem completeQuotient_prepend_two {b : ℤ} {t : ℝ}
    (hb : 1 ≤ b) (ht₀ : 0 < t) (ht₁ : t < 1) (n : ℕ) :
    completeQuotient (prependDigit b t) (n+2) = completeQuotient t (n+1) := by
  induction n with
  | zero =>
    change (Int.fract (Int.fract (prependDigit b t))⁻¹)⁻¹ = (Int.fract t)⁻¹
    rw [fract_prependDigit hb ht₀]
    simp only [prependDigit, inv_inv, fract_int_add_tail b ht₀.le ht₁,
      Int.fract_eq_self.mpr ⟨ht₀.le, ht₁⟩]
  | succ n ih =>
    change (Int.fract (completeQuotient (prependDigit b t) (n+2)))⁻¹ =
      (Int.fract (completeQuotient t (n+1)))⁻¹
    rw [ih]

theorem fract_completeQuotient_prepend {b : ℤ} {t : ℝ}
    (hb : 1 ≤ b) (ht₀ : 0 < t) (ht₁ : t < 1) (n : ℕ) :
    Int.fract (completeQuotient (prependDigit b t) (n+1)) =
      Int.fract (completeQuotient t n) := by
  cases n with
  | zero =>
    change Int.fract (Int.fract (prependDigit b t))⁻¹ = Int.fract t
    rw [fract_prependDigit hb ht₀]
    simp only [prependDigit, inv_inv, fract_int_add_tail b ht₀.le ht₁,
      Int.fract_eq_self.mpr ⟨ht₀.le, ht₁⟩]
  | succ n => rw [show n+1+1=n+2 by omega, completeQuotient_prepend_two hb ht₀ ht₁]

theorem digit_prepend_one {b : ℤ} {t : ℝ}
    (hb : 1 ≤ b) (ht₀ : 0 < t) (ht₁ : t < 1) :
    digit (prependDigit b t) 1 = b := by
  change ⌊(Int.fract (prependDigit b t))⁻¹⌋ = b
  rw [fract_prependDigit hb ht₀]
  simp only [prependDigit, inv_inv, floor_int_add_tail b ht₀.le ht₁]

theorem digit_prepend_succ {b : ℤ} {t : ℝ}
    (hb : 1 ≤ b) (ht₀ : 0 < t) (ht₁ : t < 1) (n : ℕ) :
    digit (prependDigit b t) (n+2) = digit t (n+1) := by
  unfold digit
  rw [completeQuotient_prepend_two hb ht₀ ht₁]

/-- Removing the prescribed word returns exactly the given tail. -/
theorem prependWord_tail {w : List ℤ} (hw : PositiveWord w) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) :
    Int.fract (completeQuotient (prependWord w t) w.length) = t := by
  induction w with
  | nil => exact Int.fract_eq_self.mpr ⟨ht₀.le, ht₁⟩
  | cons b bs ih =>
    have hbs : PositiveWord bs := fun c hc => hw c (by simp [hc])
    have hm := prependWord_mem hbs ht₀ ht₁
    rw [List.length_cons, prependWord, fract_completeQuotient_prepend (hw b (by simp)) hm.1 hm.2]
    exact ih hbs

/-- Every actual extracted digit agrees with the prescribed finite word. -/
theorem prependWord_digit {w : List ℤ} (hw : PositiveWord w) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (k : ℕ) (hk : k < w.length) :
    digit (prependWord w t) (k+1) = w[k] := by
  induction w generalizing k with
  | nil => simp at hk
  | cons b bs ih =>
    have hbs : PositiveWord bs := fun c hc => hw c (by simp [hc])
    have hm := prependWord_mem hbs ht₀ ht₁
    cases k with
    | zero => exact digit_prepend_one (hw b (by simp)) hm.1 hm.2
    | succ k =>
      rw [prependWord, show k+1+1=k+2 by omega, digit_prepend_succ (hw b (by simp)) hm.1 hm.2]
      exact ih hbs k (by simpa using hk)

/-- The finite reversed continued fraction, including the exhausted value at index zero. -/
noncomputable def backwardState (α : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => prependDigit (digit α (n+1)) (backwardState α n)

theorem backwardState_eq_past {α : ℝ} (hα : Irrational α) (n : ℕ) :
    backwardState α (n+1) = past α n := by
  induction n with
  | zero =>
    simp only [backwardState, prependDigit, add_zero, past, denominator_zero,
      denominator_one hα, one_div]
  | succ n ih =>
    rw [backwardState, ih]
    unfold prependDigit past
    rw [denominator_recurrence hα n]
    have hq := ordinary_denominator_pos hα (n+1)
    have ha : (1:ℝ) ≤ digit α (n+2) := by exact_mod_cast digit_succ_pos hα (n+1)
    have hq₀ := ordinary_denominator_pos hα n
    field_simp

theorem prependWord_eq_foldr (w : List ℤ) (t : ℝ) :
    prependWord w t = w.foldr prependDigit t := by
  induction w <;> simp_all [prependWord]

theorem backwardState_of_digits (α : ℝ) (w : List ℤ)
    (hw : ∀ k, (hk : k < w.length) → digit α (k+1) = w[k]) :
    backwardState α w.length = prependWord w.reverse 0 := by
  have h : ∀ k, k ≤ w.length → backwardState α k =
      (w.take k).foldl (fun t b => prependDigit b t) 0 := by
    intro k hk
    induction k with
    | zero => simp [backwardState]
    | succ k ih =>
      rw [backwardState, hw k (by omega), ih (by omega),
        List.take_succ_eq_append_getElem (by omega), List.foldl_append]
      rfl
  rw [h _ le_rfl, List.take_length, prependWord_eq_foldr, List.foldr_reverse]

/-- Independent realization of an arbitrary finite past word and an irrational future.
The finite past is reversed literally, including a possible final digit `1`. -/
theorem finite_word_realization {w : List ℤ} (hw : PositiveWord w)
    (hwne : w ≠ []) {a : ℤ} (ha : 1 ≤ a) {y : ℝ}
    (hy : Irrational y) (hy₀ : 0 < y) (hy₁ : y < 1) :
    ∃ α : ℝ, Irrational α ∧
      (∀ k, (hk : k < w.length) → digit α (k+1) = w[k]) ∧
      digit α (w.length+1) = a ∧
      past α (w.length-1) = prependWord w.reverse 0 ∧
      future α (w.length-1) = y := by
  let α := prependWord w (prependDigit a y)
  have ht := prependDigit_mem ha hy₀
  have hα : Irrational α := prependWord_irrational w (prependDigit_irrational hy)
  have hp := prependWord_tail hw ht.1 ht.2
  have hlen : w.length - 1 + 1 = w.length := by
    have : 0 < w.length := List.length_pos_iff.mpr hwne
    omega
  have hnext : completeQuotient α (w.length+1) = (a:ℝ)+y := by
    change (Int.fract (completeQuotient (prependWord w (prependDigit a y)) w.length))⁻¹ = _
    rw [hp]
    simp [prependDigit]
  have hd : ∀ k, (hk : k < w.length) → digit α (k+1) = w[k] :=
    prependWord_digit hw ht.1 ht.2
  refine ⟨α, hα, hd, ?_, ?_, ?_⟩
  · unfold digit
    rw [hnext]
    exact floor_int_add_tail a hy₀.le hy₁
  · rw [← backwardState_eq_past hα, hlen]
    exact backwardState_of_digits α w hd
  · unfold future
    rw [show w.length-1+2=w.length+1 by omega, hnext]
    exact fract_int_add_tail a hy₀.le hy₁

/-- The noncanonical terminal pair is essential for the below-digit finite endpoint. -/
theorem terminal_one_endpoint (a : ℤ) :
    prependWord [a-1,1] 0 = 1/(a:ℝ) := by
  simp [prependWord, prependDigit]

theorem single_one_endpoint : prependWord [1] 0 = 1 := by
  simp [prependWord, prependDigit]

end ContinuedFractionBounds
