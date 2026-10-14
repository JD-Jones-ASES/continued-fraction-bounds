module

public import ContinuedFractionBounds.Applications
public import ContinuedFractionBounds.ContinuedFractionsRunSharpness
public import ContinuedFractionBounds.RunBounds

/-! # Sharp bounds within actual exact digit classes -/

@[expose] public section
namespace ContinuedFractionBounds

open Filter

theorem lower_tendsto {a x y : ℝ} {u v : ℕ → ℝ}
    (hu : Tendsto u atTop (nhds x)) (hv : Tendsto v atTop (nhds y))
    (hd : a+x+y ≠ 0) :
    Tendsto (fun N => lower a (u N) (v N)) atTop (nhds (lower a x y)) := by
  unfold lower
  exact (tendsto_const_nhds.min
    ((hu.mul (tendsto_const_nhds.add hv)).min
     (hv.mul (tendsto_const_nhds.add hu)))).div
    ((tendsto_const_nhds.add hu).add hv) hd

theorem upper_tendsto {a x y : ℝ} {u v : ℕ → ℝ}
    (hu : Tendsto u atTop (nhds x)) (hv : Tendsto v atTop (nhds y))
    (hd : a+x+y ≠ 0) :
    Tendsto (fun N => upper a (u N) (v N)) atTop (nhds (upper a x y)) := by
  unfold upper
  exact (tendsto_const_nhds.max
    ((hu.mul (tendsto_const_nhds.add hv)).max
     (hv.mul (tendsto_const_nhds.add hu)))).div
    ((tendsto_const_nhds.add hu).add hv) hd

/-- Every corner value is a limit of actual triples in the exact digit class. -/
theorem actual_run_endpoint_values {a : ℤ} (ha : 2 ≤ a) (r s : ℕ)
    (e f : Departure) {x y : ℝ} (hx : runEndpoint a r e x) (hy : runEndpoint a s f y) :
    ∃ α : ℕ → ℝ, ∃ n : ℕ → ℕ,
      (∀ N, Irrational (α N) ∧ digit (α N) (n N+2) = a ∧
        ExactPastRun (α N) (n N) a r e ∧ ExactFutureRun (α N) (n N) a s f) ∧
      Tendsto (fun N => minimumTriple (α N) (n N)) atTop (nhds (lower a x y)) ∧
      Tendsto (fun N => maximumTriple (α N) (n N)) atTop (nhds (upper a x y)) := by
  obtain ⟨α,n,hs,hp,hf⟩ := actual_run_endpoint_sequences ha r s e f hx hy
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  have hxu : x ∈ Set.Icc (0:ℝ) 1 := by
    apply runCell_subset_unit ha' r e
    rcases hx with rfl | rfl
    · exact ⟨_, ⟨le_rfl, (departure_bounds ha' e).2.1.le⟩, rfl⟩
    · exact ⟨_, ⟨(departure_bounds ha' e).2.1.le, le_rfl⟩, rfl⟩
  have hyu : y ∈ Set.Icc (0:ℝ) 1 := by
    apply runCell_subset_unit ha' s f
    rcases hy with rfl | rfl
    · exact ⟨_, ⟨le_rfl, (departure_bounds ha' f).2.1.le⟩, rfl⟩
    · exact ⟨_, ⟨(departure_bounds ha' f).2.1.le, le_rfl⟩, rfl⟩
  have hd : (a:ℝ)+x+y ≠ 0 := by linarith [hxu.1,hyu.1]
  refine ⟨α,n,hs,?_,?_⟩
  · have h := lower_tendsto hp hf hd
    convert h using 1
    funext N
    rw [actual_minimum_eq (hs N).1, (hs N).2.1]
  · have h := upper_tendsto hp hf hd
    convert h using 1
    funext N
    rw [actual_maximum_eq (hs N).1, (hs N).2.1]

/-- The exact-run family is nonempty, with every requested pair of departures. -/
theorem actual_run_nonempty {a : ℤ} (ha : 2 ≤ a) (r s : ℕ) (e f : Departure) :
    ∃ α : ℝ, ∃ n : ℕ, Irrational α ∧ digit α (n+2) = a ∧
      ExactPastRun α n a r e ∧ ExactFutureRun α n a s f := by
  obtain ⟨α,n,h,_,_⟩ := actual_run_corner_sequences ha r s e f false false
  exact ⟨α 0,n 0,h 0⟩

/-- Strict sharp run bounds for actual ordinary convergents, with both exact
departures specified by their actual digits. -/
theorem actual_run_bounds {α : ℝ} {a : ℤ} (hα : Irrational α) (ha : 2 ≤ a)
    (n r s : ℕ) (e f : Departure) (hd : digit α (n+2) = a)
    (hp : ExactPastRun α n a r e) (hf : ExactFutureRun α n a s f) :
    minimumTriple α n < runLowerBound a r s e f ∧
      runLowerBound a r s e f < threshold a ∧
      threshold a < runUpperBound a r s e f ∧
      runUpperBound a r s e f < maximumTriple α n := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  have hx := exactPastRun_mem hα ha hp
  have hy := exactFutureRun_mem hα ha hf
  have hstrict := run_four_corner_bounds_strict (a := (a:ℚ))
    (show (1:ℚ) < a by exact_mod_cast (show 1 < a by omega)) r s e f
    (by simpa using hx) (by simpa using hy) (future_irrational hα n)
  simp only [Rat.cast_intCast] at hstrict
  have hsep := runBounds_strict_threshold ha' r s e f
  rw [actual_minimum_eq hα n, actual_maximum_eq hα n, hd]
  exact ⟨hstrict.1, hsep.1, hsep.2, hstrict.2⟩

/-- The lower constant is the exact supremum over its actual digit class.
The finite index is allowed to vary with the approximation. -/
theorem actual_run_lower_sharp {a : ℤ} (ha : 2 ≤ a) (r s : ℕ) (e f : Departure)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ α : ℝ, ∃ n : ℕ, Irrational α ∧ digit α (n+2) = a ∧
      ExactPastRun α n a r e ∧ ExactFutureRun α n a s f ∧
      runLowerBound a r s e f - ε < minimumTriple α n ∧
      minimumTriple α n < runLowerBound a r s e f := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  obtain ⟨x,y,hx,hy,he,_⟩ := runLowerBound_extremizer ha' r s e f
  obtain ⟨α,n,hs,hl,_⟩ := actual_run_endpoint_values ha r s e f hx hy
  rw [he] at hl
  have hv := (tendsto_order.mp hl).1 (runLowerBound a r s e f-ε) (by linarith)
  obtain ⟨N,hN⟩ := hv.exists
  have hr := actual_run_bounds (hs N).1 ha (n N) r s e f
    (hs N).2.1 (hs N).2.2.1 (hs N).2.2.2
  exact ⟨α N,n N,(hs N).1,(hs N).2.1,(hs N).2.2.1,(hs N).2.2.2,hN,hr.1⟩

/-- The upper constant is the exact infimum over its actual digit class. -/
theorem actual_run_upper_sharp {a : ℤ} (ha : 2 ≤ a) (r s : ℕ) (e f : Departure)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ α : ℝ, ∃ n : ℕ, Irrational α ∧ digit α (n+2) = a ∧
      ExactPastRun α n a r e ∧ ExactFutureRun α n a s f ∧
      runUpperBound a r s e f < maximumTriple α n ∧
      maximumTriple α n < runUpperBound a r s e f + ε := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  obtain ⟨x,y,hx,hy,he,_⟩ := runUpperBound_extremizer ha' r s e f
  obtain ⟨α,n,hs,_,hu⟩ := actual_run_endpoint_values ha r s e f hx hy
  rw [he] at hu
  have hv := (tendsto_order.mp hu).2 (runUpperBound a r s e f+ε) (by linarith)
  obtain ⟨N,hN⟩ := hv.exists
  have hr := actual_run_bounds (hs N).1 ha (n N) r s e f
    (hs N).2.1 (hs N).2.2.1 (hs N).2.2.2
  exact ⟨α N,n N,(hs N).1,(hs N).2.1,(hs N).2.2.1,(hs N).2.2.2,hr.2.2.2,hN⟩

end ContinuedFractionBounds
