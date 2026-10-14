module

public import ContinuedFractionBounds.FixedPast

@[expose] public section
namespace ContinuedFractionBounds
open Filter

/-- Every positive rational at most one has a literal finite positive expansion.
The final digit is not normalized, so endpoint conventions are retained. -/
theorem positive_rational_word (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ w : List ℤ, PositiveWord w ∧ w ≠ [] ∧ prependWord w 0 = (q:ℝ) := by
  let b : ℤ := ⌊q⁻¹⌋
  let t : ℚ := Int.fract q⁻¹
  have hb : 1 ≤ b := Int.le_floor.mpr (by
    simpa using (one_le_inv₀ hq).mpr hq1)
  have ht : 0 ≤ t := Int.fract_nonneg _
  have ht1 : t < 1 := Int.fract_lt_one _
  have he : prependDigit b (t:ℝ) = (q:ℝ) := by
    change ((b:ℝ)+(t:ℝ))⁻¹ = (q:ℝ)
    have hq' : (b:ℚ)+t = q⁻¹ := Int.floor_add_fract _
    have hh := congrArg (fun z : ℚ => (z:ℝ)) hq'
    simp only [Rat.cast_add, Rat.cast_intCast, Rat.cast_inv] at hh
    rw [hh, inv_inv]
  by_cases ht0 : t = 0
  · refine ⟨[b], ?_, by simp, ?_⟩
    · intro c hc
      simpa only [List.mem_singleton.mp hc] using hb
    · simpa only [prependWord, ht0, Rat.cast_zero] using he
  · obtain ⟨w,hw,hne,heq⟩ := positive_rational_word t (lt_of_le_of_ne ht (Ne.symm ht0)) ht1.le
    refine ⟨b::w, ?_, by simp, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hb
      · exact hw c hc
    · simpa only [prependWord, heq] using he
termination_by q.num.toNat
decreasing_by
  have hh := Rat.fract_inv_num_lt_num_of_pos hq
  exact (Int.toNat_lt_toNat (Rat.num_pos.mpr hq)).mpr hh

/-- Arbitrary positive rational past and irrational future coordinates are realized
independently by a genuine ordinary continued fraction. -/
theorem rational_past_irrational_future_realization {a : ℤ} (ha : 1 ≤ a)
    (x : ℚ) (hx : 0 < x) (hx1 : x ≤ 1) {y : ℝ}
    (hiy : Irrational y) (hy : 0 < y) (hy1 : y < 1) :
    ∃ α : ℝ, ∃ n : ℕ, Irrational α ∧ digit α (n+2) = a ∧
      past α n = (x:ℝ) ∧ future α n = y := by
  obtain ⟨w,hw,hne,hxw⟩ := positive_rational_word x hx hx1
  have hwr : PositiveWord w.reverse := fun b hb => hw b (List.mem_reverse.mp hb)
  have hnr : w.reverse ≠ [] := by simpa using hne
  obtain ⟨α,hα,_,hd,hp,hf⟩ := finite_word_realization hwr hnr ha hiy hy hy1
  have hlen : w.reverse.length-1+2=w.reverse.length+1 := by
    have := List.length_pos_iff.mpr hnr
    omega
  refine ⟨α,w.reverse.length-1,hα,?_,?_,hf⟩
  · rw [hlen]; exact hd
  · simpa only [List.reverse_reverse, hxw] using hp

/-- Rational points inside any nonempty real interval approximate its closed interval. -/
theorem rational_interval_sequences {L U x : ℝ} (hLU : L < U) (hx : x ∈ Set.Icc L U) :
    ∃ q : ℕ → ℚ, (∀ N, (q N:ℝ) ∈ Set.Ioo L U) ∧
      Tendsto (fun N => (q N:ℝ)) atTop (nhds x) := by
  have hd : Dense (Set.range fun q : ℚ => (q:ℝ)) := Rat.denseRange_cast
  have hsub := hd.open_subset_closure_inter (isOpen_Ioo : IsOpen (Set.Ioo L U))
  have hc : Set.Icc L U ⊆ closure ((Set.range fun q : ℚ => (q:ℝ)) ∩ Set.Ioo L U) := by
    rw [← closure_Ioo hLU.ne]
    exact closure_minimal (by simpa only [Set.inter_comm] using hsub) isClosed_closure
  obtain ⟨z,hz,ht⟩ := mem_closure_iff_seq_limit.mp (hc hx)
  choose q hq using fun N => (hz N).1
  change ∀ N, (q N:ℝ) = z N at hq
  refine ⟨q,fun N => ?_,?_⟩
  · rw [hq N]
    exact (hz N).2
  · simpa only [hq] using ht

/-- Irrational points inside any nonempty real interval approximate its closed interval. -/
theorem irrational_interval_sequences {L U y : ℝ} (hLU : L < U) (hy : y ∈ Set.Icc L U) :
    ∃ z : ℕ → ℝ, (∀ N, Irrational (z N) ∧ z N ∈ Set.Ioo L U) ∧
      Tendsto z atTop (nhds y) := by
  have hsub := dense_irrational.open_subset_closure_inter (isOpen_Ioo : IsOpen (Set.Ioo L U))
  have hc : Set.Icc L U ⊆ closure ({x : ℝ | Irrational x} ∩ Set.Ioo L U) := by
    rw [← closure_Ioo hLU.ne]
    exact closure_minimal (by simpa only [Set.inter_comm] using hsub) isClosed_closure
  exact mem_closure_iff_seq_limit.mp (hc hy)

/-- Approximate any past coordinate while retaining a separately prescribed
sequence of actual irrational future coordinates exactly. -/
theorem actual_past_approximation_with_futures {a : ℤ} (ha : 1 ≤ a) {x : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) (y : ℕ → ℝ)
    (hy : ∀ N, Irrational (y N) ∧ y N ∈ Set.Ioo (0:ℝ) 1) :
    ∃ α : ℕ → ℝ, ∃ n : ℕ → ℕ,
      (∀ N, Irrational (α N) ∧ digit (α N) (n N+2) = a ∧ future (α N) (n N) = y N) ∧
      Tendsto (fun N => past (α N) (n N)) atTop (nhds x) := by
  obtain ⟨q,hq,ht⟩ := rational_interval_sequences (by norm_num : (0:ℝ)<1) hx
  have hex (N : ℕ) := rational_past_irrational_future_realization ha (q N)
    (by exact_mod_cast (hq N).1) (by exact_mod_cast (hq N).2.le)
    (hy N).1 (hy N).2.1 (hy N).2.2
  choose α n hα hd hp hf using hex
  refine ⟨α,n,fun N => ⟨hα N,hd N,hf N⟩,?_⟩
  simpa only [hp] using ht

/-- Actual past/future pairs for any prescribed positive central digit are dense
in the entire closed square. The finite index is allowed to vary. -/
theorem actual_coordinate_sequences {a : ℤ} (ha : 1 ≤ a) {x y : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    ∃ α : ℕ → ℝ, ∃ n : ℕ → ℕ,
      (∀ N, Irrational (α N) ∧ digit (α N) (n N+2) = a) ∧
      Tendsto (fun N => past (α N) (n N)) atTop (nhds x) ∧
      Tendsto (fun N => future (α N) (n N)) atTop (nhds y) := by
  obtain ⟨z,hz,ht⟩ := irrational_interval_sequences (by norm_num : (0:ℝ)<1) hy
  obtain ⟨α,n,hs,hp⟩ := actual_past_approximation_with_futures ha hx z hz
  exact ⟨α,n,fun N => ⟨(hs N).1,(hs N).2.1⟩,hp,by simpa only [fun N => (hs N).2.2] using ht⟩

end ContinuedFractionBounds
