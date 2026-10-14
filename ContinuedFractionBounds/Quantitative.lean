module

public import ContinuedFractionBounds.ActualRuns

/-! # Effective convergence and quantitative cylinder localization -/

@[expose] public section
namespace ContinuedFractionBounds

private lemma leftRatio_lipschitz_left {a x u y : ℝ} (ha : 0 < a)
    (hx : 0 ≤ x) (hu : 0 ≤ u) (hy : 0 ≤ y) :
    |leftRatio a x y-leftRatio a u y| ≤ |x-u| := by
  have hd₁ : 0 < a+x+y := by linarith
  have hd₂ : 0 < a+u+y := by linarith
  have hprod : 0 < (a+x+y)*(a+u+y) := mul_pos hd₁ hd₂
  have he : leftRatio a x y-leftRatio a u y =
      (a+y)^2*(x-u)/((a+x+y)*(a+u+y)) := by
    unfold leftRatio
    field_simp
    <;> ring
  rw [he, abs_div, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos hprod]
  apply (div_le_iff₀ hprod).mpr
  have hb : (a+y)^2 ≤ (a+x+y)*(a+u+y) := by
    nlinarith [mul_nonneg hx hu, mul_nonneg (show 0 ≤ a+y by linarith) hx,
      mul_nonneg (show 0 ≤ a+y by linarith) hu]
  nlinarith [mul_le_mul_of_nonneg_right hb (abs_nonneg (x-u))]

private lemma leftRatio_lipschitz_right {a x y v : ℝ} (ha : 0 < a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hv : 0 ≤ v) :
    |leftRatio a x y-leftRatio a x v| ≤ |y-v| := by
  have hd₁ : 0 < a+x+y := by linarith
  have hd₂ : 0 < a+x+v := by linarith
  have hprod : 0 < (a+x+y)*(a+x+v) := mul_pos hd₁ hd₂
  have he : leftRatio a x y-leftRatio a x v =
      x^2*(y-v)/((a+x+y)*(a+x+v)) := by
    unfold leftRatio
    field_simp
    <;> ring
  rw [he, abs_div, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos hprod]
  apply (div_le_iff₀ hprod).mpr
  have hb : x^2 ≤ (a+x+y)*(a+x+v) := by
    have h₁ : x ≤ a+x+y := by linarith
    have h₂ : x ≤ a+x+v := by linarith
    nlinarith [mul_le_mul h₁ h₂ hx hd₁.le]
  nlinarith [mul_le_mul_of_nonneg_right hb (abs_nonneg (y-v))]

lemma leftRatio_lipschitz {a x y u v : ℝ} (ha : 0 < a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |leftRatio a x y-leftRatio a u v| ≤ |x-u|+|y-v| := by
  exact (abs_sub_le (leftRatio a x y) (leftRatio a u y) (leftRatio a u v)).trans
    (add_le_add (leftRatio_lipschitz_left ha hx hu hy)
      (leftRatio_lipschitz_right ha hu hy hv))

private lemma central_lipschitz {a x y u v : ℝ} (ha : 1 ≤ a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |1/(a+x+y)-1/(a+u+v)| ≤ |x-u|+|y-v| := by
  have hd₁ : 0 < a+x+y := by linarith
  have hd₂ : 0 < a+u+v := by linarith
  have hp : 0 < (a+x+y)*(a+u+v) := mul_pos hd₁ hd₂
  have he : 1/(a+x+y)-1/(a+u+v) =
      ((u-x)+(v-y))/((a+x+y)*(a+u+v)) := by field_simp; ring
  rw [he, abs_div, abs_of_pos hp]
  have hb : 1 ≤ (a+x+y)*(a+u+v) := by
    have h₁ : 1 ≤ a+x+y := by linarith
    have h₂ : 1 ≤ a+u+v := by linarith
    nlinarith [mul_le_mul h₁ h₂ (by norm_num : (0:ℝ) ≤ 1) hd₁.le]
  calc
    |(u-x)+(v-y)|/((a+x+y)*(a+u+v)) ≤ |(u-x)+(v-y)| :=
      div_le_self (abs_nonneg _) hb
    _ ≤ |x-u|+|y-v| := by simpa only [abs_sub_comm] using abs_add_le (u-x) (v-y)

theorem envelopes_lipschitz {a x y u v : ℝ} (ha : 1 ≤ a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |lower a x y-lower a u v| ≤ |x-u|+|y-v| ∧
      |upper a x y-upper a u v| ≤ |x-u|+|y-v| := by
  have ha₀ : 0 < a := by linarith
  have hd₁ : 0 ≤ a+x+y := by linarith
  have hd₂ : 0 ≤ a+u+v := by linarith
  have hleft := leftRatio_lipschitz ha₀ hx hy hu hv
  have hright : |leftRatio a y x-leftRatio a v u| ≤ |x-u|+|y-v| := by
    simpa only [add_comm] using leftRatio_lipschitz ha₀ hy hx hv hu
  have hc := central_lipschitz ha hx hy hu hv
  have hmin : |min (leftRatio a x y) (leftRatio a y x)-
      min (leftRatio a u v) (leftRatio a v u)| ≤ |x-u|+|y-v| :=
    (abs_min_sub_min_le_max _ _ _ _).trans (max_le hleft hright)
  have hmax : |max (leftRatio a x y) (leftRatio a y x)-
      max (leftRatio a u v) (leftRatio a v u)| ≤ |x-u|+|y-v| :=
    (abs_max_sub_max_le_max _ _ _ _).trans (max_le hleft hright)
  have hemin := (abs_min_sub_min_le_max (1/(a+x+y))
    (min (leftRatio a x y) (leftRatio a y x)) (1/(a+u+v))
    (min (leftRatio a u v) (leftRatio a v u))).trans (max_le hc hmin)
  have hemax := (abs_max_sub_max_le_max (1/(a+x+y))
    (max (leftRatio a x y) (leftRatio a y x)) (1/(a+u+v))
    (max (leftRatio a u v) (leftRatio a v u))).trans (max_le hc hmax)
  simp only [leftRatio, leftRatio_comm_den] at hemin hemax
  simp only [← min_div_div_right hd₁, ← min_div_div_right hd₂,
    ← max_div_div_right hd₁, ← max_div_div_right hd₂, lower, upper]
  constructor
  · convert hemin using 1 <;> ring_nf
  · convert hemax using 1 <;> ring_nf

private lemma endpoint_mem {a x : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure)
    (hx : runEndpoint a r e x) : x ∈ runCell a r e := by
  rcases (runEndpoint_iff a x r e).mp hx with rfl | rfl
  · exact runLower_mem ha r e
  · exact runUpper_mem ha r e

/-- Both sharp run constants converge effectively to the metallic threshold. -/
theorem run_constants_convergence {a : ℝ} (ha : 1 < a) (r s : ℕ) (e f : Departure) :
    0 < threshold a-runLowerBound a r s e f ∧
      threshold a-runLowerBound a r s e f ≤ (1/a^2)^r+(1/a^2)^s ∧
      0 < runUpperBound a r s e f-threshold a ∧
      runUpperBound a r s e f-threshold a ≤ (1/a^2)^r+(1/a^2)^s := by
  have hgap := runBounds_strict_threshold ha r s e f
  obtain ⟨x,y,hx,hy,he,_⟩ := runLowerBound_extremizer ha r s e f
  obtain ⟨u,v,hu,hv,he',_⟩ := runUpperBound_extremizer ha r s e f
  have hxm := endpoint_mem ha r e hx
  have hym := endpoint_mem ha s f hy
  have hum := endpoint_mem ha r e hu
  have hvm := endpoint_mem ha s f hv
  have hb := (metallic_pos a).le
  have hl := (envelopes_lipschitz ha.le
    (runCell_subset_unit ha r e hxm).1 (runCell_subset_unit ha s f hym).1 hb hb).1
  have hh := (envelopes_lipschitz ha.le
    (runCell_subset_unit ha r e hum).1 (runCell_subset_unit ha s f hvm).1 hb hb).2
  rw [he, lower_metallic (by linarith : 0 < a), abs_sub_comm,
    abs_of_pos (sub_pos.mpr hgap.1)] at hl
  rw [he', upper_metallic, abs_of_pos (sub_pos.mpr hgap.2)] at hh
  exact ⟨sub_pos.mpr hgap.1, hl.trans (add_le_add (runCell_distance_le ha r e hxm)
    (runCell_distance_le ha s f hym)), sub_pos.mpr hgap.2,
    hh.trans (add_le_add (runCell_distance_le ha r e hum) (runCell_distance_le ha s f hvm))⟩

/-- Explicit sufficient deficit threshold for membership in an arbitrary
constant-prefix cylinder on both sides of the central digit. -/
theorem small_deficit_constant_cell {a x y : ℝ} (ha : 2 ≤ a) (r : ℕ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hd : threshold a-lower a x y < stabilityConstant a *
      min (metallic a-constantLower a r) (constantUpper a r-metallic a)) :
    x ∈ interior (constantCell a r) ∧ y ∈ interior (constantCell a r) := by
  rw [constantCell_eq_Icc (by linarith : 1 < a), interior_Icc]
  exact small_deficit_in_interval ha hx hx1 hy hy1 hd

end ContinuedFractionBounds
