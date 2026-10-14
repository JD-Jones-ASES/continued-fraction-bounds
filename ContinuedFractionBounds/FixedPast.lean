module

public import ContinuedFractionBounds.ActualRuns
public import ContinuedFractionBounds.ContinuedFractionsFutureDensity
public import ContinuedFractionBounds.UpperRectangleOptimization
public import ContinuedFractionBounds.MetallicBoundary

@[expose] public section

namespace ContinuedFractionBounds

/-- A literal positive initial word, before the central digit. -/
def HasInitialWord (α : ℝ) (w : List ℤ) : Prop :=
  ∀ k, (hk : k < w.length) → digit α (k+1) = w[k]

/-- The finite reversed-past coordinate, retaining the supplied word exactly. -/
noncomputable def wordPast (w : List ℤ) : ℝ := prependWord w.reverse 0

theorem prependWord_mem_closed {w : List ℤ} (hw : PositiveWord w) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : prependWord w t ∈ Set.Icc (0:ℝ) 1 := by
  induction w with
  | nil => exact ht
  | cons b bs ih =>
    have hb : (1:ℝ) ≤ b := by exact_mod_cast hw b (by simp)
    have hbs : PositiveWord bs := fun c hc => hw c (by simp [hc])
    have hm := ih hbs
    constructor
    · change 0 ≤ ((b:ℝ)+prependWord bs t)⁻¹
      apply inv_nonneg.mpr; linarith [hm.1]
    · change ((b:ℝ)+prependWord bs t)⁻¹ ≤ 1
      exact (inv_le_one₀ (by linarith [hm.1])).mpr (by linarith [hm.1])

theorem prependWord_pos {w : List ℤ} (hw : PositiveWord w) (hwne : w ≠ []) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : 0 < prependWord w t := by
  cases w with
  | nil => contradiction
  | cons b bs =>
    have hb : (1:ℝ) ≤ b := by exact_mod_cast hw b (by simp)
    have hbs : PositiveWord bs := fun c hc => hw c (by simp [hc])
    have hm := prependWord_mem_closed hbs ht
    change 0 < ((b:ℝ)+prependWord bs t)⁻¹
    apply inv_pos.mpr; linarith [hm.1]

theorem wordPast_mem {w : List ℤ} (hw : PositiveWord w) (hwne : w ≠ []) :
    0 < wordPast w ∧ wordPast w ≤ 1 := by
  have hwr : PositiveWord w.reverse := fun b hb => hw b (List.mem_reverse.mp hb)
  have hne : w.reverse ≠ [] := by simpa using hwne
  exact ⟨prependWord_pos hwr hne ⟨le_rfl, by norm_num⟩,
    (prependWord_mem_closed hwr ⟨le_rfl, by norm_num⟩).2⟩

theorem prependWord_rational (w : List ℤ) (q : ℚ) : ∃ r : ℚ, prependWord w q = r := by
  induction w with
  | nil => exact ⟨q, rfl⟩
  | cons b bs ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨((b:ℚ)+r)⁻¹, ?_⟩
    simp only [prependWord, prependDigit, hr, Rat.cast_inv, Rat.cast_add, Rat.cast_intCast]

theorem wordPast_rational (w : List ℤ) : ∃ r : ℚ, wordPast w = r := by
  simpa only [wordPast, Rat.cast_zero] using prependWord_rational w.reverse 0

theorem initialWord_past {α : ℝ} (hα : Irrational α) {w : List ℤ} (hwne : w ≠ [])
    (hw : HasInitialWord α w) : past α (w.length-1) = wordPast w := by
  have hlen : w.length-1+1=w.length := by
    have := List.length_pos_iff.mpr hwne
    omega
  rw [← backwardState_eq_past hα, hlen]
  exact backwardState_of_digits α w hw

noncomputable def fixedPastLowerY (a : ℝ) (w : List ℤ) (s : ℕ) (e : Departure) : ℝ :=
  lowerRectangleY a (wordPast w) (wordPast w) (runLower a s e) (runUpper a s e)

noncomputable def fixedPastUpperY (a : ℝ) (w : List ℤ) (s : ℕ) (e : Departure) : ℝ :=
  upperRectangleY a (wordPast w) (wordPast w) (runLower a s e) (runUpper a s e)

/-- Exact supremum of the three-coefficient minimum with the entire past fixed. -/
noncomputable def fixedPastLowerBound (a : ℝ) (w : List ℤ) (s : ℕ) (e : Departure) : ℝ :=
  lower a (wordPast w) (fixedPastLowerY a w s e)

/-- Exact infimum of the three-coefficient maximum with the entire past fixed. -/
noncomputable def fixedPastUpperBound (a : ℝ) (w : List ℤ) (s : ℕ) (e : Departure) : ℝ :=
  upper a (wordPast w) (fixedPastUpperY a w s e)

theorem fixedPastLower_extremum {a : ℝ} (ha : 1 < a) {w : List ℤ}
    (hw : PositiveWord w) (hwne : w ≠ []) (s : ℕ) (e : Departure) :
    fixedPastLowerY a w s e ∈ runCell a s e ∧
    ∀ y ∈ runCell a s e,
      lower a (wordPast w) y ≤ fixedPastLowerBound a w s e ∧
      (lower a (wordPast w) y = fixedPastLowerBound a w s e ↔ y = fixedPastLowerY a w s e) := by
  have hx := wordPast_mem hw hwne
  have hb := run_bounds ha s e
  have hh := lower_rectangle_maximum ha.le hx.1.le le_rfl hx.2 hb.1 hb.2.1.le hb.2.2
  have hX : lowerRectangleX a (wordPast w) (wordPast w) (runLower a s e) (runUpper a s e) =
      wordPast w := le_antisymm hh.1.2 hh.1.1
  have hprod : wordPast w * runUpper a s e ≠ 0 := by
    have hu : 0 < runUpper a s e := hb.1.trans_lt hb.2.1
    exact ne_of_gt (mul_pos hx.1 hu)
  rw [hX] at hh
  refine ⟨by rw [runCell_eq_Icc ha]; exact hh.2.1, ?_⟩
  intro y hy
  rw [runCell_eq_Icc ha] at hy
  have he := hh.2.2 (wordPast w) ⟨le_rfl, le_rfl⟩ y hy
  simpa only [fixedPastLowerBound, fixedPastLowerY, hprod, false_or, true_and] using he

theorem fixedPastUpper_extremum {a : ℝ} (ha : 1 < a) {w : List ℤ}
    (hw : PositiveWord w) (hwne : w ≠ []) (s : ℕ) (e : Departure) :
    fixedPastUpperY a w s e ∈ runCell a s e ∧
    ∀ y ∈ runCell a s e,
      fixedPastUpperBound a w s e ≤ upper a (wordPast w) y ∧
      (upper a (wordPast w) y = fixedPastUpperBound a w s e ↔ y = fixedPastUpperY a w s e) := by
  have hx := wordPast_mem hw hwne
  have hb := run_bounds ha s e
  have hh := upper_rectangle_minimum ha.le hx.1.le le_rfl hx.2 hb.1 hb.2.1.le hb.2.2
  have hX : upperRectangleX a (wordPast w) (wordPast w) (runLower a s e) (runUpper a s e) =
      wordPast w := le_antisymm hh.1.2 hh.1.1
  rw [hX] at hh
  refine ⟨by rw [runCell_eq_Icc ha]; exact hh.2.1, ?_⟩
  intro y hy
  rw [runCell_eq_Icc ha] at hy
  have he := hh.2.2 (wordPast w) ⟨le_rfl, le_rfl⟩ y hy
  simpa only [fixedPastUpperBound, fixedPastUpperY, true_and] using he

private theorem lowerSwitch_rational (a x : ℚ) : ∃ q : ℚ, lowerSwitch a x = q := by
  refine ⟨max (1/x-a) (1/(a+x)), ?_⟩
  simp [lowerSwitch]

private theorem upperSwitch_rational (a x : ℚ) : ∃ q : ℚ, upperSwitch a x = q := by
  unfold upperSwitch
  split_ifs
  · exact ⟨1/(a+x), by simp⟩
  · exact ⟨max 0 (1/x-a), by simp⟩

private theorem lower_fixed_selector_rational {a x L U : ℚ}
    (ha : (1:ℝ) ≤ a) (hx : (0:ℝ) ≤ x) (hx1 : (x:ℝ) ≤ 1)
    (hL : (0:ℝ) ≤ L) (hLU : (L:ℝ) ≤ U) (hU : (U:ℝ) ≤ 1) :
    ∃ q : ℚ, lowerRectangleY a x x L U = q := by
  have hh := lower_rectangle_maximum ha hx le_rfl hx1 hL hLU hU
  have hX : lowerRectangleX a x x L U = (x:ℝ) := le_antisymm hh.1.2 hh.1.1
  unfold lowerRectangleY
  split_ifs with hz hhi hlo
  · exact ⟨U, rfl⟩
  · exact ⟨U, rfl⟩
  · exact ⟨L, rfl⟩
  · have hxc : lowerClipX a x x L U = (x:ℝ) := by
      simpa only [lowerRectangleX, hz, hhi, hlo, ↓reduceIte] using hX
    rw [lowerClipY, hxc]
    exact lowerSwitch_rational a x

private theorem upper_fixed_selector_rational {a x L U : ℚ}
    (ha : (1:ℝ) ≤ a) (hx : (0:ℝ) ≤ x) (hx1 : (x:ℝ) ≤ 1)
    (hL : (0:ℝ) ≤ L) (hLU : (L:ℝ) ≤ U) (hU : (U:ℝ) ≤ 1) :
    ∃ q : ℚ, upperRectangleY a x x L U = q := by
  have hh := upper_rectangle_minimum ha hx le_rfl hx1 hL hLU hU
  have hX : upperRectangleX a x x L U = (x:ℝ) := le_antisymm hh.1.2 hh.1.1
  unfold upperRectangleY
  split_ifs with hhi hlo
  · exact ⟨U, rfl⟩
  · exact ⟨L, rfl⟩
  · have hxc : upperClipX a x x L U = (x:ℝ) := by
      simpa only [upperRectangleX, hhi, hlo, ↓reduceIte] using hX
    rw [upperClipY, hxc]
    exact upperSwitch_rational a x

theorem fixedPast_selectors_rational {a : ℤ} (ha : 2 ≤ a) {w : List ℤ}
    (hw : PositiveWord w) (hwne : w ≠ []) (s : ℕ) (e : Departure) :
    (∃ q : ℚ, fixedPastLowerY a w s e = q) ∧
      (∃ q : ℚ, fixedPastUpperY a w s e = q) := by
  obtain ⟨x, hx⟩ := wordPast_rational w
  obtain ⟨⟨L, hL⟩, ⟨U, hU⟩⟩ := run_endpoints_rational (a:ℚ) s e
  simp only [Rat.cast_intCast] at hL hU
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  have hxmem := wordPast_mem hw hwne
  have hb := run_bounds ha' s e
  rw [hx] at hxmem
  rw [← hL, ← hU] at hb
  have har : (1:ℝ) ≤ (a:ℚ) := by simpa using ha'.le
  constructor
  · obtain ⟨q, hq⟩ := lower_fixed_selector_rational har hxmem.1.le hxmem.2
      hb.1 hb.2.1.le hb.2.2
    exact ⟨q, by simpa only [fixedPastLowerY, hx, ← hL, ← hU, Rat.cast_intCast] using hq⟩
  · obtain ⟨q, hq⟩ := upper_fixed_selector_rational har hxmem.1.le hxmem.2
      hb.1 hb.2.1.le hb.2.2
    exact ⟨q, by simpa only [fixedPastUpperY, hx, ← hL, ← hU, Rat.cast_intCast] using hq⟩

/-- Both fixed-prefix constants are strict for every actual irrational future. -/
theorem fixed_past_bounds {α : ℝ} (hα : Irrational α) {w : List ℤ}
    (hw : PositiveWord w) (hwne : w ≠ []) (hword : HasInitialWord α w)
    {a : ℤ} (ha : 2 ≤ a) (s : ℕ) (e : Departure)
    (hd : digit α (w.length+1) = a) (hf : ExactFutureRun α (w.length-1) a s e) :
    minimumTriple α (w.length-1) < fixedPastLowerBound a w s e ∧
      fixedPastUpperBound a w s e < maximumTriple α (w.length-1) := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  have hp := initialWord_past hα hwne hword
  have hy := exactFutureRun_mem hα ha hf
  have hlo := (fixedPastLower_extremum ha' hw hwne s e).2 _ hy
  have hup := (fixedPastUpper_extremum ha' hw hwne s e).2 _ hy
  obtain ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ := fixedPast_selectors_rational ha hw hwne s e
  have hlen : w.length-1+2=w.length+1 := by
    have := List.length_pos_iff.mpr hwne
    omega
  rw [actual_minimum_eq hα, actual_maximum_eq hα, hlen, hd, hp]
  constructor
  · apply lt_of_le_of_ne hlo.1
    intro he
    have h := hlo.2.mp he
    rw [hl] at h
    exact (future_irrational hα _).ne_rat l h
  · apply lt_of_le_of_ne hup.1
    intro he
    have h := hup.2.mp he.symm
    rw [hu] at h
    exact (future_irrational hα _).ne_rat u h

open Filter

/-- With every finite past digit and the index fixed, all closed-cell objective
values are limits of actual exact-run triples. -/
theorem fixed_past_value_sequences {w : List ℤ} (hw : PositiveWord w) (hwne : w ≠ [])
    {a : ℤ} (ha : 2 ≤ a) (s : ℕ) (e : Departure) {y : ℝ} (hy : y ∈ runCell a s e) :
    ∃ α : ℕ → ℝ,
      (∀ N, Irrational (α N) ∧ HasInitialWord (α N) w ∧
        digit (α N) (w.length+1) = a ∧ ExactFutureRun (α N) (w.length-1) a s e) ∧
      Tendsto (fun N => minimumTriple (α N) (w.length-1)) atTop
        (nhds (lower a (wordPast w) y)) ∧
      Tendsto (fun N => maximumTriple (α N) (w.length-1)) atTop
        (nhds (upper a (wordPast w) y)) := by
  obtain ⟨α, hs, hf⟩ := fixed_word_future_sequences hw hwne ha s e hy
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  have hxu := wordPast_mem hw hwne
  have hyu := runCell_subset_unit ha' s e hy
  have hd : (a:ℝ)+wordPast w+y ≠ 0 := by linarith [hxu.1, hyu.1]
  have hlen : w.length-1+2=w.length+1 := by
    have := List.length_pos_iff.mpr hwne
    omega
  have hp : Tendsto (fun N => past (α N) (w.length-1)) atTop (nhds (wordPast w)) := by
    simp only [fun N => (hs N).2.2.2.2]
    exact tendsto_const_nhds
  refine ⟨α, fun N => ⟨(hs N).1, (hs N).2.1, (hs N).2.2.1, (hs N).2.2.2.1⟩, ?_, ?_⟩
  · have h := lower_tendsto hp hf hd
    convert h using 1
    funext N
    rw [actual_minimum_eq (hs N).1, hlen, (hs N).2.2.1]
  · have h := upper_tendsto hp hf hd
    convert h using 1
    funext N
    rw [actual_maximum_eq (hs N).1, hlen, (hs N).2.2.1]

/-- The exact constants are rational, including switching points inside the cell. -/
theorem fixedPast_bounds_rational {a : ℤ} (ha : 2 ≤ a) {w : List ℤ}
    (hw : PositiveWord w) (hwne : w ≠ []) (s : ℕ) (e : Departure) :
    (∃ q : ℚ, fixedPastLowerBound a w s e = q) ∧
      (∃ q : ℚ, fixedPastUpperBound a w s e = q) := by
  obtain ⟨x, hx⟩ := wordPast_rational w
  obtain ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ := fixedPast_selectors_rational ha hw hwne s e
  unfold fixedPastLowerBound fixedPastUpperBound
  rw [hx, hy, hz]
  exact ⟨⟨_, by simpa only [Rat.cast_intCast] using lower_rat (a:ℚ) x y⟩,
    ⟨_, by simpa only [Rat.cast_intCast] using upper_rat (a:ℚ) x z⟩⟩

/-- A fixed finite past leaves a uniform positive gap from the metallic threshold. -/
theorem fixedPast_bounds_strict_threshold {a : ℤ} (ha : 2 ≤ a) {w : List ℤ}
    (hw : PositiveWord w) (hwne : w ≠ []) (s : ℕ) (e : Departure) :
    fixedPastLowerBound a w s e < threshold a ∧
      threshold a < fixedPastUpperBound a w s e := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  have hx := wordPast_mem hw hwne
  have hne : wordPast w ≠ metallic (a:ℝ) := by
    obtain ⟨q, hq⟩ := wordPast_rational w
    intro he
    exact (metallic_irrational ha).ne_rat q (he.symm.trans hq)
  have hy := runCell_subset_unit ha' s e (fixedPastLower_extremum ha' hw hwne s e).1
  have hz := runCell_subset_unit ha' s e (fixedPastUpper_extremum ha' hw hwne s e).1
  exact ⟨lower_lt_threshold_of_ne ha'.le hx.1.le hx.2 hy.1 hne,
    threshold_lt_upper_of_ne ha'.le hx.1.le hx.2 hz.1 hne⟩

/-- The fixed-prefix lower constant is the exact supremum, at the same finite index. -/
theorem fixed_past_lower_sharp {w : List ℤ} (hw : PositiveWord w) (hwne : w ≠ [])
    {a : ℤ} (ha : 2 ≤ a) (s : ℕ) (e : Departure) (ε : ℝ) (hε : 0 < ε) :
    ∃ α : ℝ, Irrational α ∧ HasInitialWord α w ∧ digit α (w.length+1) = a ∧
      ExactFutureRun α (w.length-1) a s e ∧
      fixedPastLowerBound a w s e - ε < minimumTriple α (w.length-1) ∧
      minimumTriple α (w.length-1) < fixedPastLowerBound a w s e := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  obtain ⟨α, hs, hl, _⟩ := fixed_past_value_sequences hw hwne ha s e
    (fixedPastLower_extremum ha' hw hwne s e).1
  have hv := (tendsto_order.mp hl).1 (fixedPastLowerBound a w s e-ε) (by
    change fixedPastLowerBound a w s e-ε < fixedPastLowerBound a w s e
    linarith)
  obtain ⟨N,hN⟩ := hv.exists
  have hr := fixed_past_bounds (hs N).1 hw hwne (hs N).2.1 ha s e
    (hs N).2.2.1 (hs N).2.2.2
  exact ⟨α N,(hs N).1,(hs N).2.1,(hs N).2.2.1,(hs N).2.2.2,hN,hr.1⟩

/-- The fixed-prefix upper constant is the exact infimum, at the same finite index. -/
theorem fixed_past_upper_sharp {w : List ℤ} (hw : PositiveWord w) (hwne : w ≠ [])
    {a : ℤ} (ha : 2 ≤ a) (s : ℕ) (e : Departure) (ε : ℝ) (hε : 0 < ε) :
    ∃ α : ℝ, Irrational α ∧ HasInitialWord α w ∧ digit α (w.length+1) = a ∧
      ExactFutureRun α (w.length-1) a s e ∧
      fixedPastUpperBound a w s e < maximumTriple α (w.length-1) ∧
      maximumTriple α (w.length-1) < fixedPastUpperBound a w s e + ε := by
  have ha' : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  obtain ⟨α, hs, _, hu⟩ := fixed_past_value_sequences hw hwne ha s e
    (fixedPastUpper_extremum ha' hw hwne s e).1
  have hv := (tendsto_order.mp hu).2 (fixedPastUpperBound a w s e+ε) (by
    change fixedPastUpperBound a w s e < fixedPastUpperBound a w s e+ε
    linarith)
  obtain ⟨N,hN⟩ := hv.exists
  have hr := fixed_past_bounds (hs N).1 hw hwne (hs N).2.1 ha s e
    (hs N).2.2.1 (hs N).2.2.2
  exact ⟨α N,(hs N).1,(hs N).2.1,(hs N).2.2.1,(hs N).2.2.2,hr.2,hN⟩

/-- Literal exhausted pasts are covered without replacing the finite zero tail. -/
theorem wordPast_replicate (a : ℤ) (n : ℕ) :
    wordPast (List.replicate n a) = tailIter a n 0 := by
  simp only [wordPast, List.reverse_replicate, prependWord_replicate]

theorem initialWord_replicate {α : ℝ} {a : ℤ} (n : ℕ)
    (hd : ∀ k, 1 ≤ k → k ≤ n+1 → digit α k = a) :
    HasInitialWord α (List.replicate (n+1) a) := by
  intro k hk
  simp only [List.length_replicate] at hk
  simpa using hd (k+1) (by omega) (by omega)

/-- Actual exhausted-past bounds at index n, with the entire n+1-digit past fixed.
Their sharpness follows from the same-word theorems above. -/
theorem exhausted_fixed_past_bounds {α : ℝ} (hα : Irrational α) {a : ℤ} (ha : 2 ≤ a)
    (n s : ℕ) (e : Departure) (hp : ∀ k, 1 ≤ k → k ≤ n+1 → digit α k = a)
    (hd : digit α (n+2) = a) (hf : ExactFutureRun α n a s e) :
    minimumTriple α n < fixedPastLowerBound a (List.replicate (n+1) a) s e ∧
      fixedPastUpperBound a (List.replicate (n+1) a) s e < maximumTriple α n := by
  have hw := positiveWord_replicate (by omega : 1 ≤ a) (n+1)
  have hwne : List.replicate (n+1) a ≠ [] := by simp
  have hword := initialWord_replicate n hp
  simpa using fixed_past_bounds hα hw hwne hword ha s e (by simpa using hd) (by simpa using hf)

/-- Every prescribed positive finite past admits an actual infinite constant future,
with exact attained values for both three-coefficient extrema. -/
theorem fixed_word_metallic_realization {w : List ℤ} (hw : PositiveWord w) (hwne : w ≠ [])
    {a : ℤ} (ha : 2 ≤ a) :
    ∃ α : ℝ, Irrational α ∧ HasInitialWord α w ∧ digit α (w.length+1) = a ∧
      (∀ i : ℕ, digit α (w.length-1+3+i) = a) ∧
      minimumTriple α (w.length-1) = lower a (wordPast w) (metallic a) ∧
      maximumTriple α (w.length-1) = upper a (wordPast w) (metallic a) := by
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  obtain ⟨α,hα,hwα,hd,hp,hf⟩ := finite_word_realization hw hwne (by omega : 1 ≤ a)
    (metallic_irrational ha) (metallic_pos (a:ℝ)) (metallic_lt_one ha')
  have hlen : w.length-1+2=w.length+1 := by
    have := List.length_pos_iff.mpr hwne
    omega
  refine ⟨α,hα,hwα,hd,(infinite_future_iff_metallic hα ha _).mpr hf,?_,?_⟩
  · rw [actual_minimum_eq hα, hlen, hd, hp, hf]
    rfl
  · rw [actual_maximum_eq hα, hlen, hd, hp, hf]
    rfl

end ContinuedFractionBounds
