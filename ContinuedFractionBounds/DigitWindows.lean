module

public import ContinuedFractionBounds.Quantitative

/-! # Near-threshold coefficients force long constant-digit windows -/

@[expose] public section
namespace ContinuedFractionBounds

lemma constant_interior_preimage {a x : ℝ} (ha : 1 < a) (r : ℕ)
    (hx : x ∈ interior (constantCell a r)) :
    ∃ t ∈ Set.Ioo (0:ℝ) 1, x = tailIter a r t := by
  have hclosed : x ∈ constantCell a r := interior_subset hx
  obtain ⟨t,ht,he⟩ := hclosed
  rw [constantCell_eq_Icc ha, interior_Icc] at hx
  have ht₀ : t ≠ 0 := by
    intro hzero
    subst t
    rw [← he] at hx
    rcases le_total (tailIter a r 0) (tailIter a r 1) with hh | hh
    · simpa only [Set.mem_Ioo, constantLower, min_eq_left hh, lt_self_iff_false, false_and] using hx
    · simpa only [Set.mem_Ioo, constantUpper, max_eq_left hh, lt_self_iff_false, and_false] using hx
  have ht₁ : t ≠ 1 := by
    intro hone
    subst t
    rw [← he] at hx
    rcases le_total (tailIter a r 0) (tailIter a r 1) with hh | hh
    · simpa only [Set.mem_Ioo, constantUpper, max_eq_right hh, lt_self_iff_false, and_false] using hx
    · simpa only [Set.mem_Ioo, constantLower, min_eq_right hh, lt_self_iff_false, false_and] using hx
  exact ⟨t,⟨lt_of_le_of_ne ht.1 ht₀.symm, lt_of_le_of_ne ht.2 ht₁⟩,he.symm⟩

private lemma digit_unique {a b : ℤ} {u v : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) 1)
    (hv : v ∈ Set.Icc (0:ℝ) 1) (h : (a:ℝ)+u = (b:ℝ)+v) : a=b := by
  apply le_antisymm
  · by_contra hn
    have hh : (b:ℝ)+1 ≤ a := by exact_mod_cast (show b+1 ≤ a by omega)
    linarith [hu.1,hv.2]
  · by_contra hn
    have hh : (a:ℝ)+1 ≤ b := by exact_mod_cast (show a+1 ≤ b by omega)
    linarith [hu.2,hv.1]

theorem backward_digits_of_constant_prefix {α : ℝ} (hα : Irrational α)
    {a : ℤ} (ha : 2 ≤ a) (r k : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1)
    (he : backwardState α k = tailIter a r t) :
    r < k ∧ ∀ i < r, digit α (k-i) = a := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  induction r generalizing k with
  | zero =>
    have hk : 0 < k := by
      cases k with
      | zero => simp only [backwardState,tailIter,Function.iterate_zero,Function.id_def] at he; linarith [ht.1]
      | succ k => omega
    exact ⟨hk,fun i hi => by omega⟩
  | succ r ih =>
    have hu := tailIter_mem_unit_strict ha' r ht
    rw [tailIter_succ] at he
    cases k with
    | zero =>
      have hp := (tailMap_mem_unit ha' ⟨hu.1.le,hu.2.le⟩).1
      simp only [backwardState] at he
      linarith
    | succ k =>
      have hv := backwardState_mem hα k
      have heq : (a:ℝ)+tailIter a r t = (digit α (k+1):ℝ)+backwardState α k := by
        apply inv_injective
        simpa only [backwardState,prependDigit,tailMap,one_div] using he.symm
      have hd : digit α (k+1)=a := (digit_unique hu hv heq).symm
      have he' : backwardState α k=tailIter a r t := by rw [hd] at heq; linarith
      obtain ⟨hr,hi⟩ := ih k he'
      refine ⟨by omega, ?_⟩
      intro i hir
      cases i with
      | zero => simpa using hd
      | succ i => simpa only [Nat.succ_sub_succ_eq_sub] using hi i (by omega)

theorem forward_digits_of_constant_prefix {α : ℝ} (hα : Irrational α)
    {a : ℤ} (ha : 2 ≤ a) (r k : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1)
    (he : forwardState α k = tailIter a r t) :
    ∀ i < r, digit α (k+i+1)=a := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  induction r generalizing k with
  | zero => intro i hi; omega
  | succ r ih =>
    have hu := tailIter_mem_unit_strict ha' r ht
    have hv : forwardState α (k+1) ∈ Set.Icc (0:ℝ) 1 :=
      ⟨(fract_completeQuotient_pos hα _).le,(Int.fract_lt_one _).le⟩
    rw [tailIter_succ,forwardState_recurrence hα k] at he
    have heq : (a:ℝ)+tailIter a r t = (digit α (k+1):ℝ)+forwardState α (k+1) := by
      apply inv_injective
      simpa only [prependDigit,tailMap,one_div] using he.symm
    have hd : digit α (k+1)=a := (digit_unique hu hv heq).symm
    have he' : forwardState α (k+1)=tailIter a r t := by rw [hd] at heq; linarith
    intro i hir
    cases i with
    | zero => simpa using hd
    | succ i => simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (k+1) he' i (by omega)

/-- A quantitative deficit threshold forces an actual constant-digit window
on both sides. The past-length conclusion rules out exhaustion. -/
theorem small_deficit_digit_window {α : ℝ} {a : ℤ} (hα : Irrational α)
    (ha : 2 ≤ a) (n r : ℕ) (hd : digit α (n+2)=a)
    (hdef : threshold a-minimumTriple α n < stabilityConstant a *
      min (metallic a-constantLower a r) (constantUpper a r-metallic a)) :
    r < n+1 ∧ (∀ i < r, digit α (n+1-i)=a) ∧
      (∀ i < r, digit α (n+3+i)=a) := by
  have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha
  have hx := past_mem hα n
  have hy := future_mem hα n
  rw [actual_minimum_eq hα n,hd] at hdef
  obtain ⟨hp,hf⟩ := small_deficit_constant_cell ha' r hx.1.le hx.2 hy.1.le hy.2.le hdef
  obtain ⟨u,hu,he⟩ := constant_interior_preimage (by linarith : (1:ℝ)<a) r hp
  obtain ⟨v,hv,he'⟩ := constant_interior_preimage (by linarith : (1:ℝ)<a) r hf
  rw [← backwardState_eq_past hα n] at he
  have hback := backward_digits_of_constant_prefix hα ha r (n+1) hu he
  have hfor := forward_digits_of_constant_prefix hα ha r (n+2) hv he'
  refine ⟨hback.1,hback.2,?_⟩
  intro i hi
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hfor i hi

end ContinuedFractionBounds
