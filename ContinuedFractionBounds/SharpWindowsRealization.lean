module

public import ContinuedFractionBounds.ActualCoordinateDensity
public import ContinuedFractionBounds.SharpDigitWindows

@[expose] public section
namespace ContinuedFractionBounds
open Filter

/-- A literal constant future prefix places its coordinate in the closed
constant cylinder, including either rational closure endpoint. -/
theorem future_prefix_mem_constantCell {α : ℝ} (hα : Irrational α)
    (a : ℤ) (n r : ℕ) (hd : ∀ i < r, digit α (n+3+i) = a) :
    future α n ∈ constantCell a r := by
  have he := forwardState_run hα a (n+2) r (fun i hi => by
    simpa only [show n+2+i+1=n+3+i by omega] using hd i hi)
  refine ⟨forwardState α (n+2+r), ?_, he.symm⟩
  exact ⟨(Int.fract_nonneg _), (Int.fract_lt_one _).le⟩

/-- Approach either interval endpoint by actual irrational futures strictly
outside the interval, while approaching any desired past coordinate. -/
theorem actual_future_boundary_sequences {a : ℤ} (ha : 1 ≤ a) {x L U t : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hL : 0 < L) (hLU : L < U) (hU : U < 1)
    (ht : t=L ∨ t=U) :
    ∃ α : ℕ → ℝ, ∃ n : ℕ → ℕ,
      (∀ N, Irrational (α N) ∧ digit (α N) (n N+2) = a ∧
        future (α N) (n N) ∉ Set.Icc L U) ∧
      Tendsto (fun N => past (α N) (n N)) atTop (nhds x) ∧
      Tendsto (fun N => future (α N) (n N)) atTop (nhds t) := by
  have hex : ∃ z : ℕ → ℝ,
      (∀ N, Irrational (z N) ∧ z N ∈ Set.Ioo (0:ℝ) 1 ∧ z N ∉ Set.Icc L U) ∧
      Tendsto z atTop (nhds t) := by
    rcases ht with rfl | rfl
    · obtain ⟨z,hz,ht⟩ := irrational_interval_sequences hL ⟨hL.le,le_rfl⟩
      refine ⟨z,fun N => ⟨(hz N).1,⟨(hz N).2.1,(hz N).2.2.trans (hLU.trans hU)⟩,?_⟩,ht⟩
      intro hm
      exact (not_lt_of_ge hm.1) (hz N).2.2
    · obtain ⟨z,hz,ht⟩ := irrational_interval_sequences hU ⟨le_rfl,hU.le⟩
      refine ⟨z,fun N => ⟨(hz N).1,⟨(hL.trans hLU).trans (hz N).2.1,(hz N).2.2⟩,?_⟩,ht⟩
      intro hm
      exact (not_lt_of_ge hm.2) (hz N).2.1
  obtain ⟨z,hz,htend⟩ := hex
  obtain ⟨α,n,hs,hp⟩ := actual_past_approximation_with_futures ha hx z
    (fun N => ⟨(hz N).1,(hz N).2.1⟩)
  refine ⟨α,n,fun N => ⟨(hs N).1,(hs N).2.1,?_⟩,hp,?_⟩
  · rw [(hs N).2.2]
    exact (hz N).2.2
  · simpa only [fun N => (hs N).2.2] using htend

/-- Both boundary objective values are approached by genuine irrational triples
whose future remains outside the target interval throughout. -/
theorem actual_future_boundary_values {a : ℤ} (ha : 1 ≤ a) {x L U t : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hL : 0 < L) (hLU : L < U) (hU : U < 1)
    (ht : t=L ∨ t=U) :
    ∃ α : ℕ → ℝ, ∃ n : ℕ → ℕ,
      (∀ N, Irrational (α N) ∧ digit (α N) (n N+2) = a ∧
        future (α N) (n N) ∉ Set.Icc L U) ∧
      Tendsto (fun N => minimumTriple (α N) (n N)) atTop (nhds (lower a x t)) ∧
      Tendsto (fun N => maximumTriple (α N) (n N)) atTop (nhds (upper a x t)) := by
  obtain ⟨α,n,hs,hp,hf⟩ := actual_future_boundary_sequences ha hx hL hLU hU ht
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
  have ht0 : 0 < t := by rcases ht with rfl | rfl; exact hL; exact hL.trans hLU
  have hd : (a:ℝ)+x+t ≠ 0 := by linarith [hx.1]
  refine ⟨α,n,hs,?_,?_⟩
  · have hh := lower_tendsto hp hf hd
    convert hh using 1
    funext N
    rw [actual_minimum_eq (hs N).1,(hs N).2.1]
  · have hh := upper_tendsto hp hf hd
    convert hh using 1
    funext N
    rw [actual_maximum_eq (hs N).1,(hs N).2.1]

/-- Every endpoint lower cutoff is approached by actual triples whose future
lies strictly outside the prescribed interval. -/
theorem actual_lower_interval_sharp {a : ℤ} (ha : 2 ≤ a) {L U : ℝ}
    (hL : 0 < L) (hLU : L < U) (hU : U < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ α : ℝ, ∃ n : ℕ, Irrational α ∧ digit α (n+2) = a ∧
      future α n ∉ Set.Icc L U ∧
      sharpLowerWindowThreshold a L U-ε < minimumTriple α n := by
  have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha
  obtain ⟨t,ht,x,hx,he⟩ := sharpLowerWindowThreshold_witness ha'
    ⟨hL.le,(hLU.trans hU).le⟩ ⟨(hL.trans hLU).le,hU.le⟩
  obtain ⟨α,n,hs,hmin,_⟩ := actual_future_boundary_values (by omega : 1 ≤ a) hx hL hLU hU ht
  rw [he] at hmin
  obtain ⟨N,hN⟩ := ((tendsto_order.mp hmin).1
    (sharpLowerWindowThreshold a L U-ε) (by linarith)).exists
  exact ⟨α N,n N,(hs N).1,(hs N).2.1,(hs N).2.2,hN⟩

/-- Every endpoint upper cutoff is approached by actual triples whose future
lies strictly outside the prescribed interval. -/
theorem actual_upper_interval_sharp {a : ℤ} (ha : 2 ≤ a) {L U : ℝ}
    (hL : 0 < L) (hLU : L < U) (hU : U < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ α : ℝ, ∃ n : ℕ, Irrational α ∧ digit α (n+2) = a ∧
      future α n ∉ Set.Icc L U ∧
      maximumTriple α n < sharpUpperWindowThreshold a L U+ε := by
  have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha
  obtain ⟨t,ht,x,hx,he⟩ := sharpUpperWindowThreshold_witness ha'
    ⟨hL.le,(hLU.trans hU).le⟩ ⟨(hL.trans hLU).le,hU.le⟩
  obtain ⟨α,n,hs,_,hmax⟩ := actual_future_boundary_values (by omega : 1 ≤ a) hx hL hLU hU ht
  rw [he] at hmax
  obtain ⟨N,hN⟩ := ((tendsto_order.mp hmax).2
    (sharpUpperWindowThreshold a L U+ε) (by linarith)).exists
  exact ⟨α N,n N,(hs N).1,(hs N).2.1,(hs N).2.2,hN⟩

/-- The minimum cutoff for every positive constant-digit window length is sharp
on actual irrational inputs. The future fails the requested prefix and the
finite index may vary with the approximation. -/
theorem actual_lower_window_sharp {a : ℤ} (ha : 2 ≤ a) (r : ℕ) (hr : 0 < r)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ α : ℝ, ∃ n : ℕ, Irrational α ∧ digit α (n+2) = a ∧
      ¬ (∀ i < r, digit α (n+3+i) = a) ∧
      sharpLowerWindowThreshold a (constantLower a r) (constantUpper a r)-ε <
        minimumTriple α n := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  have hb := metallic_mem_constant_interior ha' r
  rw [constantCell_eq_Icc ha',interior_Icc] at hb
  obtain ⟨α,n,hα,hd,hout,hv⟩ := actual_lower_interval_sharp ha
    (constantLower_pos ha' hr) (hb.1.trans hb.2) (constantUpper_lt_one ha' hr) ε hε
  refine ⟨α,n,hα,hd,?_,hv⟩
  intro hp
  have hm := future_prefix_mem_constantCell hα a n r hp
  rw [constantCell_eq_Icc ha'] at hm
  exact hout hm

/-- The maximum cutoff for every positive constant-digit window length is sharp
on actual irrational inputs, again with a genuinely bad future prefix. -/
theorem actual_upper_window_sharp {a : ℤ} (ha : 2 ≤ a) (r : ℕ) (hr : 0 < r)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ α : ℝ, ∃ n : ℕ, Irrational α ∧ digit α (n+2) = a ∧
      ¬ (∀ i < r, digit α (n+3+i) = a) ∧
      maximumTriple α n <
        sharpUpperWindowThreshold a (constantLower a r) (constantUpper a r)+ε := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  have hb := metallic_mem_constant_interior ha' r
  rw [constantCell_eq_Icc ha',interior_Icc] at hb
  obtain ⟨α,n,hα,hd,hout,hv⟩ := actual_upper_interval_sharp ha
    (constantLower_pos ha' hr) (hb.1.trans hb.2) (constantUpper_lt_one ha' hr) ε hε
  refine ⟨α,n,hα,hd,?_,hv⟩
  intro hp
  have hm := future_prefix_mem_constantCell hα a n r hp
  rw [constantCell_eq_Icc ha'] at hm
  exact hout hm

/-- No smaller minimum cutoff can force even the requested future prefix
uniformly over actual triples. -/
theorem actual_lower_window_threshold_optimal {a : ℤ} (ha : 2 ≤ a)
    (r : ℕ) (hr : 0 < r) {B : ℝ}
    (hB : ∀ α : ℝ, Irrational α → ∀ n : ℕ, digit α (n+2) = a →
      B < minimumTriple α n → ∀ i < r, digit α (n+3+i) = a) :
    sharpLowerWindowThreshold a (constantLower a r) (constantUpper a r) ≤ B := by
  by_contra hn
  have hgap : 0 < sharpLowerWindowThreshold a (constantLower a r) (constantUpper a r)-B :=
    sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨α,n,hα,hd,hbad,hv⟩ := actual_lower_window_sharp ha r hr _ hgap
  have hv' : B < minimumTriple α n := by linarith
  exact hbad (hB α hα n hd hv')

/-- No larger maximum cutoff can force even the requested future prefix
uniformly over actual triples. -/
theorem actual_upper_window_threshold_optimal {a : ℤ} (ha : 2 ≤ a)
    (r : ℕ) (hr : 0 < r) {B : ℝ}
    (hB : ∀ α : ℝ, Irrational α → ∀ n : ℕ, digit α (n+2) = a →
      maximumTriple α n < B → ∀ i < r, digit α (n+3+i) = a) :
    B ≤ sharpUpperWindowThreshold a (constantLower a r) (constantUpper a r) := by
  by_contra hn
  have hgap : 0 < B-sharpUpperWindowThreshold a (constantLower a r) (constantUpper a r) :=
    sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨α,n,hα,hd,hbad,hv⟩ := actual_upper_window_sharp ha r hr _ hgap
  have hv' : maximumTriple α n < B := by linarith
  exact hbad (hB α hα n hd hv')

end ContinuedFractionBounds
