module

public import ContinuedFractionBounds.ContinuedFractionsRuns

@[expose] public section

namespace ContinuedFractionBounds

/-- A finite word that includes the first actual departure after a constant run. -/
def DepartingWord (a : ℤ) (r : ℕ) (e : Departure) (w : List ℤ) : Prop :=
  ∃ b rest, w = List.replicate r a ++ b :: rest ∧
    DigitDeparture a b e ∧ PositiveWord w

theorem departingWord_length {a : ℤ} {r : ℕ} {e : Departure} {w : List ℤ}
    (hw : DepartingWord a r e w) : r < w.length := by
  obtain ⟨b, rest, rfl, _, _⟩ := hw
  simp

theorem departingWord_positive {a : ℤ} {r : ℕ} {e : Departure} {w : List ℤ}
    (hw : DepartingWord a r e w) : PositiveWord w := by
  obtain ⟨_, _, _, _, hw⟩ := hw
  exact hw

theorem departingWord_digit {a : ℤ} {r : ℕ} {e : Departure} {w : List ℤ}
    (hw : DepartingWord a r e w) (i : ℕ) (hi : i < r) :
    w[i]'(hi.trans (departingWord_length hw)) = a := by
  obtain ⟨b, rest, rfl, _, _⟩ := hw
  rw [List.getElem_append_left (by simpa using hi), List.getElem_replicate]

theorem departingWord_departure {a : ℤ} {r : ℕ} {e : Departure} {w : List ℤ}
    (hw : DepartingWord a r e w) :
    DigitDeparture a (w[r]'(departingWord_length hw)) e := by
  obtain ⟨b, rest, rfl, hd, _⟩ := hw
  simpa using hd

theorem completeQuotient_tail_shift {α t : ℝ} {k : ℕ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (ht : forwardState α k = t) (i : ℕ) :
    completeQuotient α (k+i+1) = completeQuotient t (i+1) := by
  induction i with
  | zero =>
    change (forwardState α k)⁻¹ = (Int.fract t)⁻¹
    rw [ht, Int.fract_eq_self.mpr ⟨ht₀, ht₁⟩]
  | succ i ih =>
    rw [show k+(i+1)+1=(k+i+1)+1 by omega, completeQuotient, ih]
    rfl

theorem reversed_word_digits {α : ℝ} {v : List ℤ}
    (hd : ∀ k, (hk : k < v.reverse.length) → digit α (k+1) = v.reverse[k])
    (i : ℕ) (hi : i < v.length) :
    digit α (v.length-i) = v[i] := by
  have hk : v.length-1-i < v.reverse.length := by simp; omega
  have h := hd (v.length-1-i) hk
  rw [List.getElem_reverse] at h
  simpa only [show v.length-1-i+1=v.length-i by omega,
    show v.length-1-(v.length-1-i)=i by omega] using h

/-- Simultaneous realization of two literal departing words, with an arbitrary irrational tail. -/
theorem actual_run_word_realization {a : ℤ} (ha : 2 ≤ a)
    {r s : ℕ} {e f : Departure} {v u : List ℤ}
    (hv : DepartingWord a r e v) (hu : DepartingWord a s f u)
    {t : ℝ} (ht : Irrational t) (ht₀ : 0 < t) (ht₁ : t < 1) :
    ∃ α : ℝ, ∃ n : ℕ, Irrational α ∧ digit α (n+2) = a ∧
      ExactPastRun α n a r e ∧ ExactFutureRun α n a s f ∧
      past α n = prependWord v 0 ∧ future α n = prependWord u t := by
  have hvlen := departingWord_length hv
  have hulen := departingWord_length hu
  have hvpos : PositiveWord v.reverse := by
    intro b hb
    exact departingWord_positive hv b (List.mem_reverse.mp hb)
  have hvne : v.reverse ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [List.length_reverse, List.length_nil] at hlen
    omega
  have hy := prependWord_mem (departingWord_positive hu) ht₀ ht₁
  obtain ⟨α, hα, hd, hcentral, hpast, hfuture⟩ :=
    finite_word_realization hvpos hvne (by omega : 1 ≤ a)
      (prependWord_irrational u ht) hy.1 hy.2
  simp only [List.length_reverse, List.reverse_reverse] at hcentral hpast hfuture
  have hlen : v.length-1+1=v.length := by omega
  have hfwd : forwardState α (v.length+1) = prependWord u t := by
    simpa only [forwardState, future, show v.length-1+2=v.length+1 by omega] using hfuture
  have hshift (i : ℕ) : digit α (v.length+2+i) = digit (prependWord u t) (i+1) := by
    unfold digit
    rw [show v.length+2+i=(v.length+1)+i+1 by omega,
      completeQuotient_tail_shift hy.1.le hy.2 hfwd i]
  refine ⟨α, v.length-1, hα, ?_, ?_, ?_, hpast, hfuture⟩
  · simpa only [show v.length-1+2=v.length+1 by omega] using hcentral
  · refine ⟨by omega, ?_, ?_⟩
    · intro i hi
      rw [hlen, reversed_word_digits hd i (hi.trans hvlen)]
      exact departingWord_digit hv i hi
    · rw [hlen, reversed_word_digits hd r hvlen]
      exact departingWord_departure hv
  · constructor
    · intro i hi
      rw [show v.length-1+3+i=v.length+2+i by omega, hshift,
        prependWord_digit (departingWord_positive hu) ht₀ ht₁ i (hi.trans hulen)]
      exact departingWord_digit hu i hi
    · rw [show v.length-1+3+s=v.length+2+s by omega, hshift,
        prependWord_digit (departingWord_positive hu) ht₀ ht₁ s hulen]
      exact departingWord_departure hu

end ContinuedFractionBounds
