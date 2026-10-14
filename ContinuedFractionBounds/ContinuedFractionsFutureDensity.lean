module

public import ContinuedFractionBounds.ContinuedFractionsRunSharpness

@[expose] public section

namespace ContinuedFractionBounds

open Filter

/-- Irrational interior tails are dense in each closed departure interval. -/
theorem departure_irrational_sequences {a t : ℝ} (ha : 1 < a) (e : Departure)
    (ht : t ∈ departureInterval a e) :
    ∃ z : ℕ → ℝ, (∀ N, Irrational (z N) ∧
      z N ∈ Set.Ioo (departureLeft a e) (departureRight a e)) ∧
      Tendsto z atTop (nhds t) := by
  have hb := departure_bounds ha e
  have hsub := dense_irrational.open_subset_closure_inter
    (isOpen_Ioo : IsOpen (Set.Ioo (departureLeft a e) (departureRight a e)))
  have hc : departureInterval a e ⊆
      closure ({x : ℝ | Irrational x} ∩ Set.Ioo (departureLeft a e) (departureRight a e)) := by
    rw [departureInterval, ← closure_Ioo hb.2.1.ne]
    exact closure_minimal (by simpa only [Set.inter_comm] using hsub) isClosed_closure
  obtain ⟨z, hz, htend⟩ := mem_closure_iff_seq_limit.mp (hc ht)
  exact ⟨z, hz, htend⟩

theorem departure_interior_unit {a : ℝ} (ha : 1 < a) (e : Departure) {t : ℝ}
    (ht : t ∈ Set.Ioo (departureLeft a e) (departureRight a e)) :
    0 < t ∧ t < 1 := by
  have hb := departure_bounds ha e
  exact ⟨hb.1.trans_lt ht.1, ht.2.trans_le hb.2.2⟩

/-- The inverse floor of every interior tail has the literal required departure side. -/
theorem departure_digit_of_tail {a : ℤ} (ha : 2 ≤ a) (e : Departure) {t : ℝ}
    (ht : t ∈ Set.Ioo (departureLeft a e) (departureRight a e)) :
    DigitDeparture a ⌊t⁻¹⌋ e := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  have hunit := departure_interior_unit ha' e ht
  have hinv : 1 < t⁻¹ := (one_lt_inv₀ hunit.1).mpr hunit.2
  cases e with
  | low =>
    constructor
    · apply Int.le_floor.mpr
      simpa only [Int.cast_one] using hinv.le
    · apply Int.floor_lt.mpr
      have h := ht.1
      dsimp [departureLeft] at h
      have hh := (inv_lt_inv₀ hunit.1 (show (0:ℝ)<1/(a:ℝ) by positivity)).mpr h
      simpa only [one_div, inv_inv] using hh
  | high =>
    have h : ((a:ℝ)+1) < t⁻¹ := by
      have hh := ht.2
      dsimp [departureRight] at hh
      have hh' := (inv_lt_inv₀ (show (0:ℝ)<1/((a:ℝ)+1) by positivity) hunit.1).mpr hh
      simpa only [one_div, inv_inv] using hh' 
    have hf : a+1 ≤ ⌊t⁻¹⌋ := Int.le_floor.mpr (by simpa only [Int.cast_add, Int.cast_one] using h.le)
    change a < ⌊t⁻¹⌋
    omega

/-- A repeated-digit prefix followed by an interior departure tail has its exact digits. -/
theorem future_run_digits {a : ℤ} (ha : 2 ≤ a) (s : ℕ) (e : Departure) {t : ℝ}
    (ht : t ∈ Set.Ioo (departureLeft a e) (departureRight a e)) :
    (∀ i < s, digit (tailIter a s t) (i+1) = a) ∧
      DigitDeparture a (digit (tailIter a s t) (s+1)) e := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  have hunit := departure_interior_unit ha' e ht
  have hw := positiveWord_replicate (by omega : 1 ≤ a) s
  rw [← prependWord_replicate a s t]
  constructor
  · intro i hi
    have hh := prependWord_digit hw hunit.1 hunit.2 i (by simpa using hi)
    simpa using hh
  · have htail := prependWord_tail hw hunit.1 hunit.2
    simp only [List.length_replicate] at htail
    change DigitDeparture a ⌊(Int.fract (completeQuotient
      (prependWord (List.replicate s a) t) s))⁻¹⌋ e
    rw [htail]
    exact departure_digit_of_tail ha e ht

/-- An arbitrary prescribed finite past can be combined with every interior run future. -/
theorem fixed_word_future_realization {w : List ℤ} (hw : PositiveWord w) (hwne : w ≠ [])
    {a : ℤ} (ha : 2 ≤ a) (s : ℕ) (e : Departure) {t : ℝ}
    (hit : Irrational t) (ht : t ∈ Set.Ioo (departureLeft a e) (departureRight a e)) :
    ∃ α : ℝ, Irrational α ∧
      (∀ k, (hk : k < w.length) → digit α (k+1) = w[k]) ∧
      digit α (w.length+1) = a ∧ ExactFutureRun α (w.length-1) a s e ∧
      past α (w.length-1) = prependWord w.reverse 0 ∧
      future α (w.length-1) = tailIter a s t := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  have hunit := departure_interior_unit ha' e ht
  have hy := tailIter_mem_unit_strict ha' s hunit
  have hiy : Irrational (tailIter a s t) := by
    rw [← prependWord_replicate]
    exact prependWord_irrational _ hit
  obtain ⟨α, hα, hd, hc, hp, hf⟩ := finite_word_realization hw hwne (by omega : 1 ≤ a)
    hiy hy.1 hy.2
  have hwlen : 0 < w.length := List.length_pos_iff.mpr hwne
  have hft : forwardState α (w.length+1) = tailIter a s t := by
    simpa only [future, forwardState, show w.length-1+2=w.length+1 by omega] using hf
  have hshift (i : ℕ) : digit α (w.length+2+i) = digit (tailIter a s t) (i+1) := by
    unfold digit
    rw [show w.length+2+i=(w.length+1)+i+1 by omega,
      completeQuotient_tail_shift hy.1.le hy.2 hft i]
  have hdigits := future_run_digits ha s e ht
  refine ⟨α, hα, hd, hc, ?_, hp, hf⟩
  constructor
  · intro i hi
    rw [show w.length-1+3+i=w.length+2+i by omega, hshift]
    exact hdigits.1 i hi
  · rw [show w.length-1+3+s=w.length+2+s by omega, hshift]
    exact hdigits.2

/-- Fixed-index sharpness transfer for a fully prescribed finite past:
all points of the closed future cell are limits of actual exact-run futures. -/
theorem fixed_word_future_sequences {w : List ℤ} (hw : PositiveWord w) (hwne : w ≠ [])
    {a : ℤ} (ha : 2 ≤ a) (s : ℕ) (e : Departure) {y : ℝ} (hy : y ∈ runCell a s e) :
    ∃ α : ℕ → ℝ,
      (∀ N, Irrational (α N) ∧
        (∀ k, (hk : k < w.length) → digit (α N) (k+1) = w[k]) ∧
        digit (α N) (w.length+1) = a ∧ ExactFutureRun (α N) (w.length-1) a s e ∧
        past (α N) (w.length-1) = prependWord w.reverse 0) ∧
      Tendsto (fun N => future (α N) (w.length-1)) atTop (nhds y) := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  obtain ⟨t, ht, rfl⟩ := hy
  obtain ⟨z, hz, htend⟩ := departure_irrational_sequences ha' e ht
  have hex (N : ℕ) := fixed_word_future_realization hw hwne ha s e (hz N).1 (hz N).2
  choose α hα hd hc hr hp hf using hex
  refine ⟨α, fun N => ⟨hα N, hd N, hc N, hr N, hp N⟩, ?_⟩
  simp only [hf]
  exact tailIter_tendsto ha' (departureInterval_subset_unit ha' e ht) htend s

/-- Every irrational point of a closed run cell has an irrational interior
preimage; rational boundary conventions therefore do not affect future digits. -/
theorem irrational_run_preimage {a : ℤ} (s : ℕ) (e : Departure) {y : ℝ}
    (hiy : Irrational y) (hy : y ∈ runCell a s e) :
    ∃ t : ℝ, Irrational t ∧
      t ∈ Set.Ioo (departureLeft a e) (departureRight a e) ∧ y = tailIter a s t := by
  obtain ⟨t, ht, he⟩ := hy
  have hit : Irrational t := by
    by_contra hn
    obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hn
    rw [hq] at he
    have hr := tailIter_rat (a:ℚ) q s
    simp only [Rat.cast_intCast] at hr
    exact hiy.ne_rat _ (he.symm.trans hr)
  obtain ⟨L,hL⟩ := departureLeft_rational (a:ℚ) e
  obtain ⟨U,hU⟩ := departureRight_rational (a:ℚ) e
  simp only [Rat.cast_intCast] at hL hU
  have htL : t ≠ departureLeft a e := fun h => hit.ne_rat L (h.trans hL.symm)
  have htU : t ≠ departureRight a e := fun h => hit.ne_rat U (h.trans hU.symm)
  exact ⟨t,hit,⟨lt_of_le_of_ne ht.1 htL.symm,lt_of_le_of_ne ht.2 htU⟩,he.symm⟩

/-- The closed run-cell test is equivalent to the exact literal future digit
condition for an actual irrational continued fraction. -/
theorem exactFutureRun_iff_mem {α : ℝ} (hα : Irrational α) {a : ℤ} (ha : 2 ≤ a)
    (n s : ℕ) (e : Departure) :
    ExactFutureRun α n a s e ↔ future α n ∈ runCell a s e := by
  constructor
  · exact exactFutureRun_mem hα ha
  · intro hy
    obtain ⟨t,_,ht,he⟩ := irrational_run_preimage s e (future_irrational hα n) hy
    have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
    have hunit := departure_interior_unit ha' e ht
    have hyt := tailIter_mem_unit_strict ha' s hunit
    have hshift (i : ℕ) : digit α (n+3+i) = digit (tailIter a s t) (i+1) := by
      unfold digit
      rw [show n+3+i=(n+2)+i+1 by omega,
        completeQuotient_tail_shift hyt.1.le hyt.2 he i]
    obtain ⟨hp,hd⟩ := future_run_digits ha s e ht
    exact ⟨fun i hi => (hshift i).trans (hp i hi), by rw [hshift]; exact hd⟩

/-- Every irrational point in the specified run cell is realized exactly,
with every digit of an arbitrary nonempty positive initial word retained. -/
theorem fixed_word_irrational_future_realization {w : List ℤ}
    (hw : PositiveWord w) (hwne : w ≠ []) {a : ℤ} (ha : 2 ≤ a)
    (s : ℕ) (e : Departure) {y : ℝ} (hiy : Irrational y) (hy : y ∈ runCell a s e) :
    ∃ α : ℝ, Irrational α ∧
      (∀ k, (hk : k < w.length) → digit α (k+1) = w[k]) ∧
      digit α (w.length+1) = a ∧ ExactFutureRun α (w.length-1) a s e ∧
      past α (w.length-1) = prependWord w.reverse 0 ∧ future α (w.length-1) = y := by
  obtain ⟨t,hit,ht,he⟩ := irrational_run_preimage s e hiy hy
  rw [he]
  exact fixed_word_future_realization hw hwne ha s e hit ht

end ContinuedFractionBounds
