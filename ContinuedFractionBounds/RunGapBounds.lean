module

public import ContinuedFractionBounds.Quantitative
public import ContinuedFractionBounds.UpperStability

/-! # Two-sided bounds for the gaps of the exact run constants

The distances from the metallic point to the two run endpoints give
positive lower and upper estimates for both sharp approximation gaps.
-/

@[expose] public section
namespace ContinuedFractionBounds

/-- Distance from the metallic point to the nearer endpoint of a run cell. -/
noncomputable def runDistanceNear (a : ℝ) (r : ℕ) (e : Departure) : ℝ :=
  min |runLower a r e-metallic a| |runUpper a r e-metallic a|

/-- Distance from the metallic point to the farther endpoint of a run cell. -/
noncomputable def runDistanceFar (a : ℝ) (r : ℕ) (e : Departure) : ℝ :=
  max |runLower a r e-metallic a| |runUpper a r e-metallic a|

lemma runDistanceNear_pos {a : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure) :
    0 < runDistanceNear a r e := by
  apply lt_min
  · apply abs_pos.mpr
    intro h
    exact metallic_not_mem_runCell ha r e
      ((sub_eq_zero.mp h) ▸ runLower_mem ha r e)
  · apply abs_pos.mpr
    intro h
    exact metallic_not_mem_runCell ha r e
      ((sub_eq_zero.mp h) ▸ runUpper_mem ha r e)

lemma runDistanceNear_le_far (a : ℝ) (r : ℕ) (e : Departure) :
    runDistanceNear a r e ≤ runDistanceFar a r e :=
  (min_le_left _ _).trans (le_max_left _ _)

/-- These endpoint distances bound every point, since the cell excludes the metallic point. -/
theorem runCell_distance_bounds {a x : ℝ} (ha : 1 < a)
    (r : ℕ) (e : Departure) (hx : x ∈ runCell a r e) :
    runDistanceNear a r e ≤ |x-metallic a| ∧
      |x-metallic a| ≤ runDistanceFar a r e := by
  rw [runCell_eq_Icc ha] at hx
  have hle := (runLower_lt_runUpper ha r e).le
  unfold runDistanceNear runDistanceFar
  rcases run_side ha r e with h | h
  · rw [abs_of_neg (by linarith : runLower a r e-metallic a < 0),
      abs_of_neg (by linarith : runUpper a r e-metallic a < 0),
      abs_of_neg (by linarith [hx.2] : x-metallic a < 0),
      min_eq_right (by linarith), max_eq_left (by linarith)]
    constructor <;> linarith [hx.1, hx.2]
  · rw [abs_of_pos (by linarith : 0 < runLower a r e-metallic a),
      abs_of_pos (by linarith : 0 < runUpper a r e-metallic a),
      abs_of_pos (by linarith [hx.1] : 0 < x-metallic a),
      min_eq_left (by linarith), max_eq_right (by linarith)]
    constructor <;> linarith [hx.1, hx.2]

/-- The near and far distances are each attained by an endpoint. -/
theorem runCell_distance_extrema {a : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure) :
    (∃ x ∈ runCell a r e, |x-metallic a| = runDistanceNear a r e) ∧
      (∃ x ∈ runCell a r e, |x-metallic a| = runDistanceFar a r e) := by
  rcases le_total |runLower a r e-metallic a| |runUpper a r e-metallic a| with h | h
  · exact ⟨⟨_, runLower_mem ha r e, (min_eq_left h).symm⟩,
      ⟨_, runUpper_mem ha r e, (max_eq_right h).symm⟩⟩
  · exact ⟨⟨_, runUpper_mem ha r e, (min_eq_right h).symm⟩,
      ⟨_, runLower_mem ha r e, (max_eq_left h).symm⟩⟩

private lemma gap_endpoint_mem {a x : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure)
    (hx : runEndpoint a r e x) : x ∈ runCell a r e := by
  rcases (runEndpoint_iff a x r e).mp hx with rfl | rfl
  · exact runLower_mem ha r e
  · exact runUpper_mem ha r e

/-- Positive lower and upper bounds for both exact run gaps, with no restriction on the lengths. -/
theorem run_gap_bounds {a : ℝ} (ha : 2 ≤ a) (r s : ℕ) (e f : Departure) :
    stabilityConstant a * max (runDistanceNear a r e) (runDistanceNear a s f) ≤
        threshold a-runLowerBound a r s e f ∧
      threshold a-runLowerBound a r s e f ≤
        runDistanceFar a r e+runDistanceFar a s f ∧
      upperStabilityConstant a * max (runDistanceNear a r e) (runDistanceNear a s f) ≤
        runUpperBound a r s e f-threshold a ∧
      runUpperBound a r s e f-threshold a ≤
        runDistanceFar a r e+runDistanceFar a s f := by
  have ha1 : 1 < a := by linarith
  obtain ⟨x,y,hx,hy,he,_⟩ := runLowerBound_extremizer ha1 r s e f
  obtain ⟨u,v,hu,hv,he',_⟩ := runUpperBound_extremizer ha1 r s e f
  have hxm := gap_endpoint_mem ha1 r e hx
  have hym := gap_endpoint_mem ha1 s f hy
  have hum := gap_endpoint_mem ha1 r e hu
  have hvm := gap_endpoint_mem ha1 s f hv
  have hxu := runCell_subset_unit ha1 r e hxm
  have hyu := runCell_subset_unit ha1 s f hym
  have huu := runCell_subset_unit ha1 r e hum
  have hvu := runCell_subset_unit ha1 s f hvm
  have hxd := runCell_distance_bounds ha1 r e hxm
  have hyd := runCell_distance_bounds ha1 s f hym
  have hud := runCell_distance_bounds ha1 r e hum
  have hvd := runCell_distance_bounds ha1 s f hvm
  have hlow := global_stability ha hxu.1 hxu.2 hyu.1 hyu.2
  have hupp := global_upper_stability ha huu.1 huu.2 hvu.1 hvu.2
  have hb := (metallic_pos a).le
  have hlip := (envelopes_lipschitz ha1.le hxu.1 hyu.1 hb hb).1
  have hulip := (envelopes_lipschitz ha1.le huu.1 hvu.1 hb hb).2
  rw [he] at hlow hlip
  rw [he'] at hupp hulip
  rw [lower_metallic (by linarith : 0 < a), abs_sub_comm] at hlip
  rw [upper_metallic] at hulip
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (max_le_max hxd.1 hyd.1)
      (stabilityConstant_pos ha).le).trans hlow
  · exact (le_abs_self _).trans (hlip.trans (add_le_add hxd.2 hyd.2))
  · exact (mul_le_mul_of_nonneg_left (max_le_max hud.1 hvd.1)
      (upperStabilityConstant_pos ha).le).trans hupp
  · exact (le_abs_self _).trans (hulip.trans (add_le_add hud.2 hvd.2))

end ContinuedFractionBounds
