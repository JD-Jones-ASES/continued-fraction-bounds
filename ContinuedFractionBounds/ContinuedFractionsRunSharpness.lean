module

public import ContinuedFractionBounds.ContinuedFractionsRunRealization

@[expose] public section

namespace ContinuedFractionBounds

/-- `false` selects the left departure endpoint and `true` the right one. -/
noncomputable def selectedDepartureEndpoint (a : ℝ) (e : Departure) (right : Bool) : ℝ :=
  if right then departureRight a e else departureLeft a e

/-- Finite past endpoint approximants, retaining the terminal digit `1`. -/
def pastTailWord (a : ℤ) : Departure → Bool → ℕ → List ℤ
  | .low, false, _ => [a-1, 1]
  | .low, true, _ => [1]
  | .high, false, N => [a+N+1]
  | .high, true, _ => [a+1]

/-- Infinite future endpoint approximants, completed by the irrational silver tail. -/
def futureTailWord (a : ℤ) : Departure → Bool → ℕ → List ℤ
  | .low, false, N => [a-1, 1, N+1]
  | .low, true, N => [1, N+1]
  | .high, false, N => [a+N+1]
  | .high, true, N => [a+1, N+1]

def pastRunWord (a : ℤ) (r : ℕ) (e : Departure) (right : Bool) (N : ℕ) : List ℤ :=
  List.replicate r a ++ pastTailWord a e right N

def futureRunWord (a : ℤ) (r : ℕ) (e : Departure) (right : Bool) (N : ℕ) : List ℤ :=
  List.replicate r a ++ futureTailWord a e right N

theorem positiveWord_append {v w : List ℤ} (hv : PositiveWord v) (hw : PositiveWord w) :
    PositiveWord (v ++ w) := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact hv b hb
  · exact hw b hb

theorem positiveWord_replicate {a : ℤ} (ha : 1 ≤ a) (r : ℕ) :
    PositiveWord (List.replicate r a) := by
  intro b hb
  obtain ⟨_, rfl⟩ := List.mem_replicate.mp hb
  exact ha

theorem pastRunWord_departing {a : ℤ} (ha : 2 ≤ a) (r : ℕ)
    (e : Departure) (right : Bool) (N : ℕ) :
    DepartingWord a r e (pastRunWord a r e right N) := by
  have hp := positiveWord_replicate (by omega : 1 ≤ a) r
  cases e <;> cases right
  · refine ⟨a-1, [1], rfl, ⟨by omega, by omega⟩, positiveWord_append hp ?_⟩
    intro b hb
    simp [pastTailWord] at hb
    rcases hb with rfl | rfl <;> omega
  · exact ⟨1, [], rfl, ⟨by omega, by omega⟩, positiveWord_append hp (by simp [PositiveWord, pastTailWord])⟩
  · refine ⟨a+N+1, [], rfl, ?_, positiveWord_append hp ?_⟩
    · change a < a+N+1; omega
    · intro b hb
      simp only [pastTailWord, List.mem_singleton] at hb
      subst b
      omega
  · refine ⟨a+1, [], rfl, ?_, positiveWord_append hp ?_⟩
    · change a < a+1; omega
    · intro b hb
      simp only [pastTailWord, List.mem_singleton] at hb
      subst b
      omega

theorem futureRunWord_departing {a : ℤ} (ha : 2 ≤ a) (r : ℕ)
    (e : Departure) (right : Bool) (N : ℕ) :
    DepartingWord a r e (futureRunWord a r e right N) := by
  have hp := positiveWord_replicate (by omega : 1 ≤ a) r
  cases e <;> cases right
  · refine ⟨a-1, [1,N+1], rfl, ⟨by omega, by omega⟩, positiveWord_append hp ?_⟩
    intro b hb
    simp [futureTailWord] at hb
    rcases hb with rfl | rfl | rfl <;> omega
  · refine ⟨1, [N+1], rfl, ⟨by omega, by omega⟩, positiveWord_append hp ?_⟩
    intro b hb
    simp [futureTailWord] at hb
    rcases hb with rfl | rfl <;> omega
  · refine ⟨a+N+1, [], rfl, ?_, positiveWord_append hp ?_⟩
    · change a < a+N+1; omega
    · intro b hb
      simp only [futureTailWord, List.mem_singleton] at hb
      subst b
      omega
  · refine ⟨a+1, [N+1], rfl, ?_, positiveWord_append hp ?_⟩
    · change a < a+1; omega
    · intro b hb
      simp [futureTailWord] at hb
      rcases hb with rfl | rfl <;> omega

theorem prependWord_append (v w : List ℤ) (t : ℝ) :
    prependWord (v ++ w) t = prependWord v (prependWord w t) := by
  induction v <;> simp_all [prependWord]

theorem prependWord_replicate (a : ℤ) (r : ℕ) (t : ℝ) :
    prependWord (List.replicate r a) t = tailIter a r t := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.replicate_succ, prependWord, ih, tailIter_succ]
    simp only [prependDigit, tailMap, one_div]

open Filter

private theorem largeDigit_tendsto (b t : ℝ) :
    Tendsto (fun N : ℕ => (b+(N:ℝ)+t)⁻¹) atTop (nhds 0) := by
  apply tendsto_inv_atTop_zero.comp
  have h := tendsto_atTop_add_const_right (atTop : Filter ℕ) (b+t)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, add_assoc, add_comm, add_left_comm] using h

theorem pastTailWord_tendsto {a : ℤ} (ha : 2 ≤ a) (e : Departure) (right : Bool) :
    Tendsto (fun N => prependWord (pastTailWord a e right N) 0) atTop
      (nhds (selectedDepartureEndpoint a e right)) := by
  have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha
  cases e <;> cases right
  · simpa [pastTailWord, prependWord, prependDigit, selectedDepartureEndpoint,
      departureLeft, show (a:ℝ)-1+1=(a:ℝ) by ring] using
      (tendsto_const_nhds (x := (a:ℝ)⁻¹) (f := atTop (α := ℕ)))
  · simpa [pastTailWord, prependWord, prependDigit, selectedDepartureEndpoint,
      departureRight] using (tendsto_const_nhds (x := (1:ℝ)) (f := atTop (α := ℕ)))
  · simpa [pastTailWord, prependWord, prependDigit, selectedDepartureEndpoint,
      departureLeft] using largeDigit_tendsto (a:ℝ) 1
  · simpa [pastTailWord, prependWord, prependDigit, selectedDepartureEndpoint,
      departureRight] using
      (tendsto_const_nhds (x := ((a:ℝ)+1)⁻¹) (f := atTop (α := ℕ)))

theorem futureTailWord_tendsto {a : ℤ} (ha : 2 ≤ a) (e : Departure) (right : Bool) :
    Tendsto (fun N => prependWord (futureTailWord a e right N) silverTail) atTop
      (nhds (selectedDepartureEndpoint a e right)) := by
  have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha
  have ht : Tendsto (fun N : ℕ => ((N:ℝ)+1+silverTail)⁻¹) atTop (nhds 0) := by
    simpa [add_assoc, add_comm, add_left_comm] using largeDigit_tendsto 0 (1+silverTail)
  have ht₁ := (tendsto_const_nhds.add ht).inv₀ (show (1:ℝ)+0 ≠ 0 by norm_num)
  cases e <;> cases right
  · have hh := (tendsto_const_nhds.add ht₁).inv₀
      (show ((a:ℝ)-1)+(1+0)⁻¹ ≠ 0 by norm_num; linarith)
    simpa [futureTailWord, prependWord, prependDigit, selectedDepartureEndpoint,
      departureLeft] using hh
  · simpa [futureTailWord, prependWord, prependDigit, selectedDepartureEndpoint,
      departureRight] using ht₁
  · simpa [futureTailWord, prependWord, prependDigit, selectedDepartureEndpoint,
      departureLeft, add_assoc] using largeDigit_tendsto (a:ℝ) (1+silverTail)
  · have hh := (tendsto_const_nhds.add ht).inv₀ (show (a:ℝ)+1+0 ≠ 0 by linarith)
    simpa [futureTailWord, prependWord, prependDigit, selectedDepartureEndpoint,
      departureRight] using hh

theorem tailIter_tendsto {a t : ℝ} (ha : 1 < a) (ht : t ∈ Set.Icc (0:ℝ) 1)
    {z : ℕ → ℝ} (hz : Tendsto z atTop (nhds t)) (r : ℕ) :
    Tendsto (fun N => tailIter a r (z N)) atTop (nhds (tailIter a r t)) := by
  induction r with
  | zero => exact hz
  | succ r ih =>
    have hn : a + tailIter a r t ≠ 0 := by
      have hm := tailIter_mem_unit ha r ht
      linarith [hm.1]
    have hh := (tendsto_const_nhds.add ih).inv₀ hn
    simpa only [tailIter_succ, tailMap, one_div] using hh

theorem selectedDepartureEndpoint_mem {a : ℝ} (ha : 1 < a) (e : Departure) (right : Bool) :
    selectedDepartureEndpoint a e right ∈ Set.Icc (0:ℝ) 1 := by
  apply departureInterval_subset_unit ha e
  have hb := departure_bounds ha e
  cases right <;> simp only [selectedDepartureEndpoint, Bool.false_eq_true, ↓reduceIte]
  · exact ⟨le_rfl, hb.2.1.le⟩
  · exact ⟨hb.2.1.le, le_rfl⟩

theorem pastRunWord_tendsto {a : ℤ} (ha : 2 ≤ a) (r : ℕ) (e : Departure) (right : Bool) :
    Tendsto (fun N => prependWord (pastRunWord a r e right N) 0) atTop
      (nhds (tailIter a r (selectedDepartureEndpoint a e right))) := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  simpa only [pastRunWord, prependWord_append, prependWord_replicate] using
    tailIter_tendsto ha' (selectedDepartureEndpoint_mem ha' e right)
      (pastTailWord_tendsto ha e right) r

theorem futureRunWord_tendsto {a : ℤ} (ha : 2 ≤ a) (r : ℕ) (e : Departure) (right : Bool) :
    Tendsto (fun N => prependWord (futureRunWord a r e right N) silverTail) atTop
      (nhds (tailIter a r (selectedDepartureEndpoint a e right))) := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  simpa only [futureRunWord, prependWord_append, prependWord_replicate] using
    tailIter_tendsto ha' (selectedDepartureEndpoint_mem ha' e right)
      (futureTailWord_tendsto ha e right) r

/-- Every pair of run-cell corners is approached by actual irrational inputs
with the prescribed exact past and future departure digits. The index is allowed to vary. -/
theorem actual_run_corner_sequences {a : ℤ} (ha : 2 ≤ a) (r s : ℕ)
    (e f : Departure) (rightPast rightFuture : Bool) :
    ∃ α : ℕ → ℝ, ∃ n : ℕ → ℕ,
      (∀ N, Irrational (α N) ∧ digit (α N) (n N+2) = a ∧
        ExactPastRun (α N) (n N) a r e ∧ ExactFutureRun (α N) (n N) a s f) ∧
      Tendsto (fun N => past (α N) (n N)) atTop
        (nhds (tailIter a r (selectedDepartureEndpoint a e rightPast))) ∧
      Tendsto (fun N => future (α N) (n N)) atTop
        (nhds (tailIter a s (selectedDepartureEndpoint a f rightFuture))) := by
  have hex (N : ℕ) := actual_run_word_realization ha
    (pastRunWord_departing ha r e rightPast N)
    (futureRunWord_departing ha s f rightFuture N)
    silverTail_irrational silverTail_mem.1 silverTail_mem.2
  choose α n hα hd hp hf hxp hyp using hex
  refine ⟨α, n, fun N => ⟨hα N, hd N, hp N, hf N⟩, ?_, ?_⟩
  · simp only [hxp]
    exact pastRunWord_tendsto ha r e rightPast
  · simp only [hyp]
    exact futureRunWord_tendsto ha s f rightFuture

/-- Formulation independent of the orientation of the iterated inverse branch. -/
theorem actual_run_endpoint_sequences {a : ℤ} (ha : 2 ≤ a) (r s : ℕ)
    (e f : Departure) {x y : ℝ} (hx : runEndpoint a r e x) (hy : runEndpoint a s f y) :
    ∃ α : ℕ → ℝ, ∃ n : ℕ → ℕ,
      (∀ N, Irrational (α N) ∧ digit (α N) (n N+2) = a ∧
        ExactPastRun (α N) (n N) a r e ∧ ExactFutureRun (α N) (n N) a s f) ∧
      Tendsto (fun N => past (α N) (n N)) atTop (nhds x) ∧
      Tendsto (fun N => future (α N) (n N)) atTop (nhds y) := by
  obtain ⟨b, hb⟩ : ∃ b : Bool, x = tailIter a r (selectedDepartureEndpoint a e b) := by
    rcases hx with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  obtain ⟨c, hc⟩ : ∃ c : Bool, y = tailIter a s (selectedDepartureEndpoint a f c) := by
    rcases hy with hy | hy
    · exact ⟨false, hy⟩
    · exact ⟨true, hy⟩
  rw [hb, hc]
  exact actual_run_corner_sequences ha r s e f b c

end ContinuedFractionBounds
