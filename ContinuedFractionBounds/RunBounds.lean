module

public import ContinuedFractionBounds.Runs
public import ContinuedFractionBounds.Rectangles
public import ContinuedFractionBounds.ClassicalBounds

@[expose] public section

namespace ContinuedFractionBounds

/-- The sharp maximum of the lower envelope on an exact run rectangle. -/
noncomputable def runLowerBound (a : ℝ) (r s : ℕ) (e f : Departure) : ℝ :=
  max (max (lower a (runLower a r e) (runLower a s f))
    (lower a (runLower a r e) (runUpper a s f)))
    (max (lower a (runUpper a r e) (runLower a s f))
      (lower a (runUpper a r e) (runUpper a s f)))

/-- The sharp minimum of the upper envelope on an exact run rectangle. -/
noncomputable def runUpperBound (a : ℝ) (r s : ℕ) (e f : Departure) : ℝ :=
  min (min (upper a (runLower a r e) (runLower a s f))
    (upper a (runLower a r e) (runUpper a s f)))
    (min (upper a (runUpper a r e) (runLower a s f))
      (upper a (runUpper a r e) (runUpper a s f)))

lemma lower_rat (a x y : ℚ) :
    lower (a : ℝ) (x : ℝ) (y : ℝ) =
      ((min 1 (min (x * (a + y)) (y * (a + x))) / (a + x + y) : ℚ) : ℝ) := by
  simp only [lower, Rat.cast_div, Rat.cast_min, Rat.cast_one, Rat.cast_mul, Rat.cast_add]

lemma upper_rat (a x y : ℚ) :
    upper (a : ℝ) (x : ℝ) (y : ℝ) =
      ((max 1 (max (x * (a + y)) (y * (a + x))) / (a + x + y) : ℚ) : ℝ) := by
  simp only [upper, Rat.cast_div, Rat.cast_max, Rat.cast_one, Rat.cast_mul, Rat.cast_add]

/-- Exact rationality of both four-corner constants at every finite run pair. -/
theorem runBounds_rational (a : ℚ) (r s : ℕ) (e f : Departure) :
    (∃ q : ℚ, (q : ℝ) = runLowerBound (a : ℝ) r s e f) ∧
      (∃ q : ℚ, (q : ℝ) = runUpperBound (a : ℝ) r s e f) := by
  obtain ⟨⟨lx, hlx⟩, ⟨ux, hux⟩⟩ := run_endpoints_rational a r e
  obtain ⟨⟨ly, hly⟩, ⟨uy, huy⟩⟩ := run_endpoints_rational a s f
  unfold runLowerBound runUpperBound
  rw [← hlx, ← hux, ← hly, ← huy]
  simp only [lower_rat, upper_rat, ← Rat.cast_max, ← Rat.cast_min]
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

lemma runLower_mem {a : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure) :
    runLower a r e ∈ runCell a r e := by
  rw [runCell_eq_Icc ha]
  exact ⟨le_rfl, (runLower_lt_runUpper ha r e).le⟩

lemma runUpper_mem {a : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure) :
    runUpper a r e ∈ runCell a r e := by
  rw [runCell_eq_Icc ha]
  exact ⟨(runLower_lt_runUpper ha r e).le, le_rfl⟩

lemma run_point_strict_threshold {a x y : ℝ} (ha : 1 < a)
    (r s : ℕ) (e f : Departure) (hx : x ∈ runCell a r e) (hy : y ∈ runCell a s f) :
    lower a x y < threshold a ∧ threshold a < upper a x y := by
  have hxu := runCell_subset_unit ha r e hx
  have hyu := runCell_subset_unit ha s f hy
  have hne : x ≠ metallic a := fun h => metallic_not_mem_runCell ha r e (h ▸ hx)
  exact ⟨lower_lt_threshold_of_ne ha.le hxu.1 hxu.2 hyu.1 hne,
    threshold_lt_upper_of_ne ha.le hxu.1 hxu.2 hyu.1 hne⟩

/-- Uniform strict separation of the four-corner constants from the classical threshold. -/
theorem runBounds_strict_threshold {a : ℝ} (ha : 1 < a) (r s : ℕ) (e f : Departure) :
    runLowerBound a r s e f < threshold a ∧ threshold a < runUpperBound a r s e f := by
  have hLL := run_point_strict_threshold ha r s e f (runLower_mem ha r e) (runLower_mem ha s f)
  have hLU := run_point_strict_threshold ha r s e f (runLower_mem ha r e) (runUpper_mem ha s f)
  have hUL := run_point_strict_threshold ha r s e f (runUpper_mem ha r e) (runLower_mem ha s f)
  have hUU := run_point_strict_threshold ha r s e f (runUpper_mem ha r e) (runUpper_mem ha s f)
  simp only [runLowerBound, runUpperBound, max_lt_iff, lt_min_iff]
  exact ⟨⟨⟨hLL.1, hLU.1⟩, ⟨hUL.1, hUU.1⟩⟩,
    ⟨⟨hLL.2, hLU.2⟩, ⟨hUL.2, hUU.2⟩⟩⟩

/-- The abstract corner criterion applies to every pair of exact run cells. -/
lemma run_corner_extrema {a : ℝ} (ha : 1 < a) (r s : ℕ) (e f : Departure) :
    CornerMaximum (lower a) (runLower a r e) (runUpper a r e)
      (runLower a s f) (runUpper a s f) ∧
    CornerMinimum (upper a) (runLower a r e) (runUpper a r e)
      (runLower a s f) (runUpper a s f) := by
  have hx := run_bounds ha r e
  have hy := run_bounds ha s f
  apply rectangle_corner_extrema ha hx.1 hx.2.1 hx.2.2 hy.1 hy.2.1 hy.2.2
    (run_side ha r e) (run_side ha s f)
  · exact run_switch_alternatives ha r s e f
  · exact run_switch_alternatives ha s r f e

/-- The lower-envelope four-corner constant is attained at one and only one corner. -/
theorem runLowerBound_extremizer {a : ℝ} (ha : 1 < a) (r s : ℕ) (e f : Departure) :
    ∃ cx cy, runEndpoint a r e cx ∧ runEndpoint a s f cy ∧
      lower a cx cy = runLowerBound a r s e f ∧
      ∀ x ∈ runCell a r e, ∀ y ∈ runCell a s f,
        lower a x y ≤ runLowerBound a r s e f ∧
        (lower a x y = runLowerBound a r s e f ↔ x = cx ∧ y = cy) := by
  obtain ⟨cx, cy, hcx, hcy, hh⟩ := (run_corner_extrema ha r s e f).1
  have hr := (runLower_lt_runUpper ha r e).le
  have hs := (runLower_lt_runUpper ha s f).le
  have hLL := (hh _ ⟨le_rfl, hr⟩ _ ⟨le_rfl, hs⟩).1
  have hLU := (hh _ ⟨le_rfl, hr⟩ _ ⟨hs, le_rfl⟩).1
  have hUL := (hh _ ⟨hr, le_rfl⟩ _ ⟨le_rfl, hs⟩).1
  have hUU := (hh _ ⟨hr, le_rfl⟩ _ ⟨hs, le_rfl⟩).1
  have hb : runLowerBound a r s e f ≤ lower a cx cy :=
    max_le (max_le hLL hLU) (max_le hUL hUU)
  have hc : lower a cx cy ≤ runLowerBound a r s e f := by
    rcases hcx with rfl | rfl <;> rcases hcy with rfl | rfl
    · exact le_max_of_le_left (le_max_left _ _)
    · exact le_max_of_le_left (le_max_right _ _)
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_of_le_right (le_max_right _ _)
  have he := le_antisymm hc hb
  refine ⟨cx, cy, (runEndpoint_iff a cx r e).2 hcx,
    (runEndpoint_iff a cy s f).2 hcy, he, ?_⟩
  intro x hx y hy
  rw [runCell_eq_Icc ha] at hx hy
  simpa only [he] using hh x hx y hy

/-- The upper-envelope four-corner constant is attained at one and only one corner. -/
theorem runUpperBound_extremizer {a : ℝ} (ha : 1 < a) (r s : ℕ) (e f : Departure) :
    ∃ cx cy, runEndpoint a r e cx ∧ runEndpoint a s f cy ∧
      upper a cx cy = runUpperBound a r s e f ∧
      ∀ x ∈ runCell a r e, ∀ y ∈ runCell a s f,
        runUpperBound a r s e f ≤ upper a x y ∧
        (upper a x y = runUpperBound a r s e f ↔ x = cx ∧ y = cy) := by
  obtain ⟨cx, cy, hcx, hcy, hh⟩ := (run_corner_extrema ha r s e f).2
  have hr := (runLower_lt_runUpper ha r e).le
  have hs := (runLower_lt_runUpper ha s f).le
  have hLL := (hh _ ⟨le_rfl, hr⟩ _ ⟨le_rfl, hs⟩).1
  have hLU := (hh _ ⟨le_rfl, hr⟩ _ ⟨hs, le_rfl⟩).1
  have hUL := (hh _ ⟨hr, le_rfl⟩ _ ⟨le_rfl, hs⟩).1
  have hUU := (hh _ ⟨hr, le_rfl⟩ _ ⟨hs, le_rfl⟩).1
  have hb : upper a cx cy ≤ runUpperBound a r s e f :=
    le_min (le_min hLL hLU) (le_min hUL hUU)
  have hc : runUpperBound a r s e f ≤ upper a cx cy := by
    rcases hcx with rfl | rfl <;> rcases hcy with rfl | rfl
    · exact min_le_of_left_le (min_le_left _ _)
    · exact min_le_of_left_le (min_le_right _ _)
    · exact min_le_of_right_le (min_le_left _ _)
    · exact min_le_of_right_le (min_le_right _ _)
  have he := le_antisymm hb hc
  refine ⟨cx, cy, (runEndpoint_iff a cx r e).2 hcx,
    (runEndpoint_iff a cy s f).2 hcy, he, ?_⟩
  intro x hx y hy
  rw [runCell_eq_Icc ha] at hx hy
  simpa only [he] using hh x hx y hy

/-- Both four-corner bounds hold at every point, for all finite exact run lengths. -/
theorem run_four_corner_bounds {a x y : ℝ} (ha : 1 < a) (r s : ℕ) (e f : Departure)
    (hx : x ∈ runCell a r e) (hy : y ∈ runCell a s f) :
    lower a x y ≤ runLowerBound a r s e f ∧ runUpperBound a r s e f ≤ upper a x y := by
  obtain ⟨_, _, _, _, _, hL⟩ := runLowerBound_extremizer ha r s e f
  obtain ⟨_, _, _, _, _, hU⟩ := runUpperBound_extremizer ha r s e f
  exact ⟨(hL x hx y hy).1, (hU x hx y hy).1⟩

lemma runEndpoint_rational {a : ℚ} {x : ℝ} (r : ℕ) (e : Departure)
    (hx : runEndpoint (a : ℝ) r e x) : ∃ q : ℚ, (q : ℝ) = x := by
  rcases (runEndpoint_iff (a : ℝ) x r e).1 hx with rfl | rfl
  · exact (run_endpoints_rational a r e).1
  · exact (run_endpoints_rational a r e).2

/-- Irrational future coordinates cannot attain a rational optimizing corner. -/
theorem run_four_corner_bounds_strict {a : ℚ} (ha : 1 < a) {x y : ℝ}
    (r s : ℕ) (e f : Departure)
    (hx : x ∈ runCell (a : ℝ) r e) (hy : y ∈ runCell (a : ℝ) s f)
    (hiy : Irrational y) :
    lower (a : ℝ) x y < runLowerBound (a : ℝ) r s e f ∧
      runUpperBound (a : ℝ) r s e f < upper (a : ℝ) x y := by
  have ha' : 1 < (a : ℝ) := by exact_mod_cast ha
  obtain ⟨cx, cy, _, hcy, _, hL⟩ := runLowerBound_extremizer ha' r s e f
  obtain ⟨dx, dy, _, hdy, _, hU⟩ := runUpperBound_extremizer ha' r s e f
  constructor
  · apply lt_of_le_of_ne (hL x hx y hy).1
    intro he
    have hyc := ((hL x hx y hy).2.1 he).2
    obtain ⟨q, hq⟩ := runEndpoint_rational s f hcy
    exact hiy ⟨q, hq.trans hyc.symm⟩
  · apply lt_of_le_of_ne (hU x hx y hy).1
    intro he
    have hyd := ((hU x hx y hy).2.1 he.symm).2
    obtain ⟨q, hq⟩ := runEndpoint_rational s f hdy
    exact hiy ⟨q, hq.trans hyd.symm⟩

end ContinuedFractionBounds
