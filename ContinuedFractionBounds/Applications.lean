module

public import ContinuedFractionBounds.Stability
public import ContinuedFractionBounds.ContinuedFractionsRealization
public import ContinuedFractionBounds.LevelSets

/-!
# Ordinary-convergent stability and quantitative localization

The actual approximation coefficients are defined through Mathlib's ordinary
continued fraction of a real input. Their error identities are proved from
those definitions, and the sharp coefficient is optimal on actual inputs.
-/

@[expose] public section
namespace ContinuedFractionBounds

/-- Minimum of the three chronological ordinary approximation coefficients. -/
noncomputable def minimumTriple (α : ℝ) (n : ℕ) : ℝ :=
  min (theta α n) (min (theta α (n+1)) (theta α (n+2)))

/-- Maximum of the three chronological ordinary approximation coefficients. -/
noncomputable def maximumTriple (α : ℝ) (n : ℕ) : ℝ :=
  max (theta α n) (max (theta α (n+1)) (theta α (n+2)))

theorem actual_minimum_eq {α : ℝ} (hα : Irrational α) (n : ℕ) :
    minimumTriple α n = lower (digit α (n+2)) (past α n) (future α n) := by
  obtain ⟨h₀, h₁, h₂⟩ := ordinary_convergent_triple hα n
  have ha : (1 : ℝ) ≤ digit α (n+2) := by exact_mod_cast digit_succ_pos hα (n+1)
  have hd : 0 ≤ (digit α (n+2) : ℝ) + past α n + future α n := by
    have := (past_mem hα n).1
    have := (future_mem hα n).1
    linarith
  unfold minimumTriple lower
  rw [h₀, h₁, h₂, min_div_div_right hd, min_div_div_right hd, min_left_comm]

theorem actual_maximum_eq {α : ℝ} (hα : Irrational α) (n : ℕ) :
    maximumTriple α n = upper (digit α (n+2)) (past α n) (future α n) := by
  obtain ⟨h₀, h₁, h₂⟩ := ordinary_convergent_triple hα n
  have ha : (1 : ℝ) ≤ digit α (n+2) := by exact_mod_cast digit_succ_pos hα (n+1)
  have hd : 0 ≤ (digit α (n+2) : ℝ) + past α n + future α n := by
    have := (past_mem hα n).1
    have := (future_mem hα n).1
    linarith
  unfold maximumTriple upper
  rw [h₀, h₁, h₂, max_div_div_right hd, max_div_div_right hd, max_left_comm]

/-- Actual irrational inputs never attain the square's stability equality locus. -/
theorem actual_stability_strict {α : ℝ} {a : ℤ} (hα : Irrational α)
    (ha : 2 ≤ a) (n : ℕ) (hdigit : digit α (n+2) = a) :
    stabilityConstant a * max |past α n - metallic a| |future α n - metallic a| <
      threshold a - minimumTriple α n := by
  have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
  obtain ⟨hx, hx1⟩ := past_mem hα n
  obtain ⟨hy, hy1⟩ := future_mem hα n
  rw [actual_minimum_eq hα n, hdigit]
  have hle := global_stability ha' hx.le hx1 hy.le hy1.le
  apply lt_of_le_of_ne hle
  intro heq
  have he := (global_stability_eq_iff ha' hx.le hx1 hy.le hy1.le).mp heq.symm
  rcases he with ⟨hxb, hyb⟩ | ⟨_, hyd⟩ | ⟨_, hyone⟩
  · obtain ⟨q, hq⟩ := past_rational α n
    exact (future_irrational hα n).ne_rat q (hyb.trans (hxb.symm.trans hq))
  · have he : future α n = ((1 / ((a : ℚ)+1) : ℚ) : ℝ) := by
      simpa using hyd
    exact (future_irrational hα n).ne_rat _ he
  · exact (future_irrational hα n).ne_int 1 (by simpa using hyone)

/-- No larger coefficient works even on actual ordinary convergent triples. -/
theorem actual_stabilityConstant_optimal {a : ℤ} {K : ℝ} (ha : 2 ≤ a)
    (hK : ∀ α : ℝ, Irrational α → ∀ n : ℕ, digit α (n+2) = a →
      K * max |past α n - metallic a| |future α n - metallic a| ≤
        threshold a - minimumTriple α n) : K ≤ stabilityConstant a := by
  have ha1 : 1 ≤ a := by omega
  have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hseq (N : ℕ) :
      K * max |(1 : ℝ) - metallic a| |sharpFuture a N - metallic a| ≤
        threshold a - lower a 1 (sharpFuture a N) := by
    obtain ⟨hirr, _, _, hdigit, hpast, hfuture⟩ := sharpReal_states ha1 N
    have hh := hK (sharpReal a N) hirr 0 hdigit
    rw [actual_minimum_eq hirr 0, hdigit, hpast, hfuture] at hh
    exact hh
  have hf := sharpFuture_tendsto ha1
  have hl : Filter.Tendsto
      (fun N : ℕ => K * max |(1 : ℝ)-metallic a| |sharpFuture a N-metallic a|)
      Filter.atTop (nhds (K * max |(1 : ℝ)-metallic a| |1/((a:ℝ)+1)-metallic a|)) :=
    tendsto_const_nhds.mul
      (tendsto_const_nhds.max ((hf.sub tendsto_const_nhds).abs))
  have hc : ContinuousAt (fun y : ℝ => lower (a : ℝ) 1 y) (1 / ((a : ℝ)+1)) := by
    unfold lower
    fun_prop (disch := positivity)
  have hr : Filter.Tendsto (fun N : ℕ => threshold a - lower a 1 (sharpFuture a N))
      Filter.atTop (nhds (threshold a-lower a 1 (1/((a:ℝ)+1)))) :=
    tendsto_const_nhds.sub (hc.tendsto.comp hf)
  have hend := le_of_tendsto_of_tendsto hl hr (Filter.Eventually.of_forall hseq)
  rw [endpoint_stability_eq ha', endpoint_distance ha'] at hend
  have hp : 0 < 1 - metallic (a : ℝ) := by
    have := metallic_lt_one (by linarith : (1 : ℝ) ≤ a)
    linarith
  exact (mul_le_mul_iff_left₀ hp).mp hend

/-- A deficit bound gives an explicit coordinate radius. -/
theorem near_extremizer_radius {a x y ε : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hε : threshold a - ε ≤ lower a x y) :
    max |x-metallic a| |y-metallic a| ≤ ε / stabilityConstant a := by
  have h := global_stability ha hx hx1 hy hy1
  apply (le_div_iff₀ (stabilityConstant_pos ha)).mpr
  nlinarith

/-- A sufficiently small deficit places both coordinates in any interval
whose interior contains the metallic point. -/
theorem small_deficit_in_interval {a x y L U : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hdef : threshold a - lower a x y <
      stabilityConstant a * min (metallic a-L) (U-metallic a)) :
    x ∈ Set.Ioo L U ∧ y ∈ Set.Ioo L U := by
  have h := global_stability ha hx hx1 hy hy1
  have hm : max |x-metallic a| |y-metallic a| <
      min (metallic a-L) (U-metallic a) :=
    (mul_lt_mul_iff_right₀ (stabilityConstant_pos ha)).mp (h.trans_lt hdef)
  have hxx := (le_max_left |x-metallic a| |y-metallic a|).trans_lt hm
  have hyy := (le_max_right |x-metallic a| |y-metallic a|).trans_lt hm
  have hxl := abs_lt.mp (hxx.trans_le (min_le_left _ _))
  have hxu := abs_lt.mp (hxx.trans_le (min_le_right _ _))
  have hyl := abs_lt.mp (hyy.trans_le (min_le_left _ _))
  have hyu := abs_lt.mp (hyy.trans_le (min_le_right _ _))
  exact ⟨⟨by linarith [hxl.1], by linarith [hxu.2]⟩,
    ⟨by linarith [hyl.1], by linarith [hyu.2]⟩⟩

end ContinuedFractionBounds
