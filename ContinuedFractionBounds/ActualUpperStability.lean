module

public import ContinuedFractionBounds.ActualCoordinateDensity
public import ContinuedFractionBounds.UpperStability

@[expose] public section
namespace ContinuedFractionBounds
open Filter

/-- The maximum-side inverse estimate is strict for every ordinary irrational
triple, since its finite past coordinate is rational. -/
theorem actual_upper_stability_strict {α : ℝ} {a : ℤ} (hα : Irrational α)
    (ha : 2 ≤ a) (n : ℕ) (hdigit : digit α (n+2) = a) :
    upperStabilityConstant a * max |past α n-metallic a| |future α n-metallic a| <
      maximumTriple α n-threshold a := by
  have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha
  have hx := past_mem hα n
  have hy := future_mem hα n
  rw [actual_maximum_eq hα n,hdigit]
  exact global_upper_stability_strict ha' hx.1.le hx.2 hy.1.le hy.2.le
    (Or.inl (past_ne_metallic ha α n))

/-- A uniform maximum-side inequality on actual triples extends to the entire
closed square by actual-coordinate density. No rate of perturbation is assumed. -/
theorem actual_upper_inequality_extends {a : ℤ} {K : ℝ} (ha : 1 ≤ a)
    (hK : ∀ α : ℝ, Irrational α → ∀ n : ℕ, digit α (n+2) = a →
      K * max |past α n-metallic a| |future α n-metallic a| ≤
        maximumTriple α n-threshold a) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      K * max |x-metallic a| |y-metallic a| ≤ upper a x y-threshold a := by
  intro x hx y hy
  obtain ⟨α,n,hs,hp,hf⟩ := actual_coordinate_sequences ha hx hy
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hd : (a:ℝ)+x+y ≠ 0 := by linarith [hx.1,hy.1]
  have hl : Tendsto (fun N => K * max |past (α N) (n N)-metallic a|
      |future (α N) (n N)-metallic a|) atTop
      (nhds (K * max |x-metallic a| |y-metallic a|)) :=
    tendsto_const_nhds.mul
      (((hp.sub tendsto_const_nhds).abs).max ((hf.sub tendsto_const_nhds).abs))
  have hr := (upper_tendsto hp hf hd).sub_const (threshold (a:ℝ))
  apply le_of_tendsto_of_tendsto hl hr
  apply Eventually.of_forall
  intro N
  have hh := hK (α N) (hs N).1 (n N) (hs N).2
  rwa [actual_maximum_eq (hs N).1, (hs N).2] at hh

/-- The same coefficient is best possible on actual irrational triples, with
the finite index allowed to vary. -/
theorem actual_upperStabilityConstant_optimal {a : ℤ} {K : ℝ} (ha : 2 ≤ a)
    (hK : ∀ α : ℝ, Irrational α → ∀ n : ℕ, digit α (n+2) = a →
      K * max |past α n-metallic a| |future α n-metallic a| ≤
        maximumTriple α n-threshold a) : K ≤ upperStabilityConstant a := by
  apply upperStabilityConstant_optimal (by exact_mod_cast ha : (2:ℝ) ≤ a)
  exact actual_upper_inequality_extends (by omega : 1 ≤ a) hK

/-- Every larger maximum-side coefficient fails on a genuine irrational input. -/
theorem actual_upper_stability_sharp {a : ℤ} (ha : 2 ≤ a) {K : ℝ}
    (hK : upperStabilityConstant a < K) :
    ∃ α : ℝ, ∃ n : ℕ, Irrational α ∧ digit α (n+2) = a ∧
      maximumTriple α n-threshold a <
        K * max |past α n-metallic a| |future α n-metallic a| := by
  by_contra! hn
  have hh := actual_upperStabilityConstant_optimal ha (fun α hα n hd => hn α n hα hd)
  exact (not_le_of_gt hK) hh

end ContinuedFractionBounds
