module

public import ContinuedFractionBounds.Basic

@[expose] public section

namespace ContinuedFractionBounds

/-- One inverse branch for a constant continued-fraction digit. -/
noncomputable def tailMap (a t : ℝ) : ℝ := 1 / (a + t)

/-- A finite constant-digit prefix. -/
noncomputable def tailIter (a : ℝ) (r : ℕ) (t : ℝ) : ℝ := (tailMap a)^[r] t

/-- The first departure is below or above the constant digit. -/
inductive Departure | low | high
  deriving DecidableEq, Repr

noncomputable def departureLeft (a : ℝ) : Departure → ℝ
  | .low => 1 / a
  | .high => 0

noncomputable def departureRight (a : ℝ) : Departure → ℝ
  | .low => 1
  | .high => 1 / (a + 1)

/-- Closed departure interval; endpoints encode closure, not irrational attainability. -/
def departureInterval (a : ℝ) (e : Departure) : Set ℝ :=
  Set.Icc (departureLeft a e) (departureRight a e)

/-- The exact closed run cell, for any finite run length. -/
def runCell (a : ℝ) (r : ℕ) (e : Departure) : Set ℝ :=
  tailIter a r '' departureInterval a e

/-- Images of the two endpoints, without assuming an orientation. -/
def runEndpoint (a : ℝ) (r : ℕ) (e : Departure) (x : ℝ) : Prop :=
  x = tailIter a r (departureLeft a e) ∨ x = tailIter a r (departureRight a e)

lemma tailMap_injective (a : ℝ) : Function.Injective (tailMap a) := by
  intro x y h
  unfold tailMap at h
  simp only [one_div] at h
  exact add_left_cancel (inv_injective h)

lemma tailIter_injective (a : ℝ) (r : ℕ) : Function.Injective (tailIter a r) :=
  (tailMap_injective a).iterate r

@[simp] lemma tailIter_zero (a t : ℝ) : tailIter a 0 t = t := rfl

lemma tailIter_succ (a : ℝ) (r : ℕ) (t : ℝ) :
    tailIter a (r + 1) t = tailMap a (tailIter a r t) :=
  Function.iterate_succ_apply' _ _ _

lemma tailIter_add (a : ℝ) (r s : ℕ) (t : ℝ) :
    tailIter a (r + s) t = tailIter a r (tailIter a s t) :=
  Function.iterate_add_apply _ _ _ _

lemma tailMap_mem_unit {a t : ℝ} (ha : 1 < a) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    tailMap a t ∈ Set.Ioo (0 : ℝ) 1 := by
  dsimp [tailMap]
  have ht0 := ht.1
  constructor
  · positivity
  · apply (div_lt_one (by linarith)).2
    linarith [ht.1]

lemma tailMap_mem_middle {a t : ℝ} (ha : 1 < a) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    tailMap a t ∈ Set.Icc (1 / (a + 1)) (1 / a) := by
  dsimp [tailMap]
  constructor
  · exact one_div_le_one_div_of_le (by linarith [ht.1]) (by linarith [ht.2])
  · exact one_div_le_one_div_of_le (by linarith) (by linarith [ht.1])

lemma tailMap_mem_middle_strict {a t : ℝ} (ha : 1 < a)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    tailMap a t ∈ Set.Ioo (1 / (a + 1)) (1 / a) := by
  dsimp [tailMap]
  constructor
  · exact one_div_lt_one_div_of_lt (by linarith [ht.1]) (by linarith [ht.2])
  · exact one_div_lt_one_div_of_lt (by linarith) (by linarith [ht.1])

lemma tailIter_mem_unit {a t : ℝ} (ha : 1 < a) (r : ℕ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : tailIter a r t ∈ Set.Icc (0 : ℝ) 1 := by
  induction r with
  | zero => simpa using ht
  | succ r ih =>
    rw [tailIter_succ]
    exact (tailMap_mem_unit ha ih).imp le_of_lt le_of_lt

lemma tailIter_mem_unit_strict {a t : ℝ} (ha : 1 < a) (r : ℕ)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) : tailIter a r t ∈ Set.Ioo (0 : ℝ) 1 := by
  induction r with
  | zero => simpa using ht
  | succ r ih =>
    rw [tailIter_succ]
    exact tailMap_mem_unit ha ⟨ih.1.le, ih.2.le⟩

lemma departureInterval_subset_unit {a : ℝ} (ha : 1 < a) (e : Departure) :
    departureInterval a e ⊆ Set.Icc (0 : ℝ) 1 := by
  intro t ht
  cases e <;> dsimp [departureInterval, departureLeft, departureRight] at ht
  · exact ⟨(by positivity : 0 ≤ 1 / a).trans ht.1, ht.2⟩
  · refine ⟨ht.1, ht.2.trans ?_⟩
    exact (div_le_one (by linarith)).2 (by linarith)

lemma runCell_subset_unit {a : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure) :
    runCell a r e ⊆ Set.Icc (0 : ℝ) 1 := by
  rintro x ⟨t, ht, rfl⟩
  exact tailIter_mem_unit ha r (departureInterval_subset_unit ha e ht)

lemma runCell_shift (a : ℝ) (r : ℕ) (e : Departure) :
    tailMap a '' runCell a r e = runCell a (r + 1) e := by
  ext x
  simp only [runCell, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, tailIter_succ a r t⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨tailIter a r t, ⟨t, ht, rfl⟩, (tailIter_succ a r t).symm⟩

lemma metallic_tailMap {a : ℝ} (ha : 1 < a) : tailMap a (metallic a) = metallic a := by
  have hp := metallic_pos a
  have he := metallic_equation a
  apply (div_eq_iff (by positivity : a + metallic a ≠ 0)).2
  nlinarith

lemma metallic_tailIter {a : ℝ} (ha : 1 < a) (r : ℕ) :
    tailIter a r (metallic a) = metallic a := by
  induction r with
  | zero => rfl
  | succ r ih => rw [tailIter_succ, ih, metallic_tailMap ha]

lemma metallic_mem_middle {a : ℝ} (ha : 1 < a) :
    metallic a ∈ Set.Ioo (1 / (a + 1)) (1 / a) := by
  rw [← metallic_tailMap ha]
  exact tailMap_mem_middle_strict ha ⟨metallic_pos a, metallic_lt_one ha.le⟩

lemma metallic_not_mem_departure {a : ℝ} (ha : 1 < a) (e : Departure) :
    metallic a ∉ departureInterval a e := by
  have hm := metallic_mem_middle ha
  cases e <;> dsimp [departureInterval, departureLeft, departureRight]
  · intro h
    linarith [h.1, hm.2]
  · intro h
    linarith [h.2, hm.1]

lemma metallic_not_mem_runCell {a : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure) :
    metallic a ∉ runCell a r e := by
  rintro ⟨t, ht, he⟩
  have : t = metallic a := tailIter_injective a r (he.trans (metallic_tailIter ha r).symm)
  exact metallic_not_mem_departure ha e (this ▸ ht)

lemma departure_bounds {a : ℝ} (ha : 1 < a) (e : Departure) :
    0 ≤ departureLeft a e ∧ departureLeft a e < departureRight a e ∧
      departureRight a e ≤ 1 := by
  cases e <;> dsimp [departureLeft, departureRight]
  · constructor
    · positivity
    constructor
    · exact (div_lt_one (by linarith)).2 ha
    · exact le_rfl
  · refine ⟨le_rfl, by positivity, ?_⟩
    exact (div_le_one (by linarith)).2 (by linarith)

lemma departure_middle_only_endpoint {a u : ℝ} (ha : 1 < a) (e : Departure)
    (hu : u ∈ departureInterval a e)
    (hm : u ∈ Set.Icc (1 / (a + 1)) (1 / a)) :
    u = departureLeft a e ∨ u = departureRight a e := by
  cases e <;> dsimp [departureInterval, departureLeft, departureRight] at hu ⊢
  · exact Or.inl (le_antisymm hm.2 hu.1)
  · exact Or.inr (le_antisymm hu.2 hm.1)

lemma departure_not_middle_strict {a u : ℝ} (ha : 1 < a) (e : Departure)
    (hu : u ∈ departureInterval a e) :
    u ∉ Set.Ioo (1 / (a + 1)) (1 / a) := by
  cases e <;> dsimp [departureInterval, departureLeft, departureRight] at hu
  · intro hm
    exact (not_lt_of_ge hu.1) hm.2
  · intro hm
    exact (not_lt_of_ge hu.2) hm.1

/-- At distinct depths, any shared point is an endpoint of both cells. -/
lemma runCell_inter_endpoints_of_lt {a x : ℝ} (ha : 1 < a) {r s : ℕ}
    (hrs : r < s) (e f : Departure)
    (hx : x ∈ runCell a r e) (hy : x ∈ runCell a s f) :
    runEndpoint a r e x ∧ runEndpoint a s f x := by
  obtain ⟨u, hu, hux⟩ := hx
  obtain ⟨v, hv, hvx⟩ := hy
  obtain ⟨k, hk⟩ : ∃ k, s = r + (k + 1) := by
    exact ⟨s - r - 1, by omega⟩
  have huv : u = tailMap a (tailIter a k v) := by
    apply tailIter_injective a r
    rw [← tailIter_succ, ← tailIter_add, ← hk]
    exact hux.trans hvx.symm
  have hvunit := departureInterval_subset_unit ha f hv
  have huend : u = departureLeft a e ∨ u = departureRight a e := by
    apply departure_middle_only_endpoint ha e hu
    rw [huv]
    exact tailMap_mem_middle ha (tailIter_mem_unit ha k hvunit)
  have hvend : v = departureLeft a f ∨ v = departureRight a f := by
    by_contra hvend
    push Not at hvend
    have hb := departure_bounds ha f
    have hvstrict : v ∈ Set.Ioo (0 : ℝ) 1 := by
      exact ⟨hb.1.trans_lt (lt_of_le_of_ne hv.1 hvend.1.symm),
        (lt_of_le_of_ne hv.2 hvend.2).trans_le hb.2.2⟩
    have hm := tailMap_mem_middle_strict ha (tailIter_mem_unit_strict ha k hvstrict)
    rw [← huv] at hm
    exact departure_not_middle_strict ha e hu hm
  constructor
  · rcases huend with h | h
    · exact Or.inl (hux.symm.trans (congrArg _ h))
    · exact Or.inr (hux.symm.trans (congrArg _ h))
  · rcases hvend with h | h
    · exact Or.inl (hvx.symm.trans (congrArg _ h))
    · exact Or.inr (hvx.symm.trans (congrArg _ h))

lemma departure_disjoint {a : ℝ} (ha : 1 < a) :
    Disjoint (departureInterval a .low) (departureInterval a .high) := by
  apply Set.disjoint_left.2
  intro t hl hh
  have hgap : 1 / (a + 1) < 1 / a :=
    one_div_lt_one_div_of_lt (by linarith) (by linarith)
  exact (not_lt_of_ge (hl.1.trans hh.2)) hgap

/-- Distinct exact run cells meet only at common endpoints, for all depths. -/
theorem runCell_inter_endpoints {a x : ℝ} (ha : 1 < a) (r s : ℕ)
    (e f : Departure) (hdiff : r ≠ s ∨ e ≠ f)
    (hx : x ∈ runCell a r e) (hy : x ∈ runCell a s f) :
    runEndpoint a r e x ∧ runEndpoint a s f x := by
  rcases lt_trichotomy r s with h | h | h
  · exact runCell_inter_endpoints_of_lt ha h e f hx hy
  · subst s
    have hef : e ≠ f := hdiff.resolve_left (not_not_intro rfl)
    obtain ⟨u, hu, hux⟩ := hx
    obtain ⟨v, hv, hvx⟩ := hy
    have huv := tailIter_injective a r (hux.trans hvx.symm)
    subst v
    cases e <;> cases f
    · exact False.elim (hef rfl)
    · exact False.elim (Set.disjoint_left.1 (departure_disjoint ha) hu hv)
    · exact False.elim (Set.disjoint_left.1 (departure_disjoint ha) hv hu)
    · exact False.elim (hef rfl)
  · exact (runCell_inter_endpoints_of_lt ha h f e hy hx).symm

noncomputable def runLower (a : ℝ) (r : ℕ) (e : Departure) : ℝ :=
  min (tailIter a r (departureLeft a e)) (tailIter a r (departureRight a e))

noncomputable def runUpper (a : ℝ) (r : ℕ) (e : Departure) : ℝ :=
  max (tailIter a r (departureLeft a e)) (tailIter a r (departureRight a e))

lemma tailMap_continuousOn {a : ℝ} (ha : 1 < a) :
    ContinuousOn (tailMap a) (Set.Icc (0 : ℝ) 1) := by
  apply continuousOn_const.div (continuousOn_const.add continuousOn_id)
  intro x hx
  change a + x ≠ 0
  linarith [hx.1]

lemma tailIter_continuousOn {a : ℝ} (ha : 1 < a) (r : ℕ) :
    ContinuousOn (tailIter a r) (Set.Icc (0 : ℝ) 1) := by
  induction r with
  | zero => exact continuousOn_id
  | succ r ih =>
    have hh := (tailMap_continuousOn ha).comp ih (fun x hx => tailIter_mem_unit ha r hx)
    convert hh using 1
    ext x
    exact tailIter_succ a r x

/-- Exact sorted-endpoint interval description, valid for every run length. -/
theorem runCell_eq_Icc {a : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure) :
    runCell a r e = Set.Icc (runLower a r e) (runUpper a r e) := by
  have hb := departure_bounds ha e
  have hc := (tailIter_continuousOn ha r).mono (departureInterval_subset_unit ha e)
  have hi := (tailIter_injective a r).injOn (s := departureInterval a e)
  rcases hc.strictMonoOn_of_injOn_Icc' hb.2.1.le hi with hm | hm
  · have he := hm.monotoneOn ⟨le_rfl, hb.2.1.le⟩ ⟨hb.2.1.le, le_rfl⟩ hb.2.1.le
    simpa only [runCell, departureInterval, runLower, runUpper, min_eq_left he,
      max_eq_right he] using hc.image_Icc_of_monotoneOn hb.2.1.le hm.monotoneOn
  · have he := hm.antitoneOn ⟨le_rfl, hb.2.1.le⟩ ⟨hb.2.1.le, le_rfl⟩ hb.2.1.le
    simpa only [runCell, departureInterval, runLower, runUpper, min_eq_right he,
      max_eq_left he] using hc.image_Icc_of_antitoneOn hb.2.1.le hm.antitoneOn

lemma runLower_lt_runUpper {a : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure) :
    runLower a r e < runUpper a r e := by
  have hn : tailIter a r (departureLeft a e) ≠ tailIter a r (departureRight a e) :=
    fun h => (ne_of_lt (departure_bounds ha e).2.1) (tailIter_injective a r h)
  exact min_lt_max.mpr hn

lemma runEndpoint_iff (a x : ℝ) (r : ℕ) (e : Departure) :
    runEndpoint a r e x ↔ x = runLower a r e ∨ x = runUpper a r e := by
  unfold runEndpoint runLower runUpper
  rcases le_total (tailIter a r (departureLeft a e))
    (tailIter a r (departureRight a e)) with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, or_comm]

/-- The interiors of distinct exact run cells are disjoint. -/
theorem runCell_interiors_disjoint {a : ℝ} (ha : 1 < a) (r s : ℕ)
    (e f : Departure) (hdiff : r ≠ s ∨ e ≠ f) :
    Disjoint (interior (runCell a r e)) (interior (runCell a s f)) := by
  rw [runCell_eq_Icc ha, runCell_eq_Icc ha, interior_Icc, interior_Icc]
  apply Set.disjoint_left.2
  intro x hx hy
  have hxc : x ∈ runCell a r e := by
    rw [runCell_eq_Icc ha]; exact ⟨hx.1.le, hx.2.le⟩
  have hyc : x ∈ runCell a s f := by
    rw [runCell_eq_Icc ha]; exact ⟨hy.1.le, hy.2.le⟩
  have hex := runCell_inter_endpoints ha r s e f hdiff hxc hyc
  rcases (runEndpoint_iff a x r e).1 hex.1 with h | h <;> subst x <;> simp_all

lemma run_bounds {a : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure) :
    0 ≤ runLower a r e ∧ runLower a r e < runUpper a r e ∧ runUpper a r e ≤ 1 := by
  have hl := runLower_lt_runUpper ha r e
  have hmL : runLower a r e ∈ runCell a r e := by
    rw [runCell_eq_Icc ha]; exact ⟨le_rfl, hl.le⟩
  have hmU : runUpper a r e ∈ runCell a r e := by
    rw [runCell_eq_Icc ha]; exact ⟨hl.le, le_rfl⟩
  exact ⟨(runCell_subset_unit ha r e hmL).1, hl, (runCell_subset_unit ha r e hmU).2⟩

lemma run_side {a : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure) :
    runUpper a r e < metallic a ∨ metallic a < runLower a r e := by
  have hn := metallic_not_mem_runCell ha r e
  rw [runCell_eq_Icc ha, Set.mem_Icc] at hn
  by_cases h : runLower a r e ≤ metallic a
  · exact Or.inl (lt_of_not_ge (fun hh => hn ⟨h, hh⟩))
  · exact Or.inr (lt_of_not_ge h)

lemma tailMap_antitone_nonneg {a x y : ℝ} (ha : 1 < a) (hx : 0 ≤ x)
    (hxy : x ≤ y) : tailMap a y ≤ tailMap a x := by
  apply one_div_le_one_div_of_le <;> linarith

lemma runLower_succ {a : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure) :
    runLower a (r + 1) e = tailMap a (runUpper a r e) := by
  have hb := departure_bounds ha e
  have hL := (tailIter_mem_unit ha r
    (show departureLeft a e ∈ Set.Icc (0 : ℝ) 1 from ⟨hb.1, hb.2.1.le.trans hb.2.2⟩)).1
  have hR := (tailIter_mem_unit ha r
    (show departureRight a e ∈ Set.Icc (0 : ℝ) 1 from ⟨hb.1.trans hb.2.1.le, hb.2.2⟩)).1
  unfold runLower runUpper
  rw [tailIter_succ, tailIter_succ]
  rcases le_total (tailIter a r (departureLeft a e))
    (tailIter a r (departureRight a e)) with h | h
  · rw [max_eq_right h, min_eq_right (tailMap_antitone_nonneg ha hL h)]
  · rw [max_eq_left h, min_eq_left (tailMap_antitone_nonneg ha hR h)]

lemma runUpper_succ {a : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure) :
    runUpper a (r + 1) e = tailMap a (runLower a r e) := by
  have hb := departure_bounds ha e
  have hL := (tailIter_mem_unit ha r
    (show departureLeft a e ∈ Set.Icc (0 : ℝ) 1 from ⟨hb.1, hb.2.1.le.trans hb.2.2⟩)).1
  have hR := (tailIter_mem_unit ha r
    (show departureRight a e ∈ Set.Icc (0 : ℝ) 1 from ⟨hb.1.trans hb.2.1.le, hb.2.2⟩)).1
  unfold runLower runUpper
  rw [tailIter_succ, tailIter_succ]
  rcases le_total (tailIter a r (departureLeft a e))
    (tailIter a r (departureRight a e)) with h | h
  · rw [min_eq_left h, max_eq_left (tailMap_antitone_nonneg ha hL h)]
  · rw [min_eq_right h, max_eq_right (tailMap_antitone_nonneg ha hR h)]

/-- Any pair of cells is ordered, or is literally the same run and departure. -/
theorem runCell_order_or_equal {a : ℝ} (ha : 1 < a) (r s : ℕ) (e f : Departure) :
    runUpper a r e ≤ runLower a s f ∨ runUpper a s f ≤ runLower a r e ∨
      (r = s ∧ e = f) := by
  by_cases heq : r = s ∧ e = f
  · exact Or.inr (Or.inr heq)
  have hd : r ≠ s ∨ e ≠ f := by tauto
  have hj := runCell_interiors_disjoint ha r s e f hd
  rw [runCell_eq_Icc ha, runCell_eq_Icc ha, interior_Icc, interior_Icc,
    Set.Ioo_disjoint_Ioo] at hj
  by_cases h1 : runUpper a r e ≤ runLower a s f
  · exact Or.inl h1
  by_cases h2 : runUpper a s f ≤ runLower a r e
  · exact Or.inr (Or.inl h2)
  have hbad : max (runLower a r e) (runLower a s f) <
      min (runUpper a r e) (runUpper a s f) := by
    simp only [max_lt_iff, lt_min_iff]
    exact ⟨⟨runLower_lt_runUpper ha r e, lt_of_not_ge h1⟩,
      ⟨lt_of_not_ge h2, runLower_lt_runUpper ha s f⟩⟩
  exact False.elim ((not_lt_of_ge hj) hbad)

/-- The structural switching-curve alternatives used by the four-corner theorem. -/
theorem run_switch_alternatives {a : ℝ} (ha : 1 < a) (r s : ℕ) (e f : Departure) :
    runUpper a r e ≤ tailMap a (runUpper a s f) ∨
      tailMap a (runLower a s f) ≤ runLower a r e ∨
      (runLower a r e = tailMap a (runUpper a s f) ∧
        runUpper a r e = tailMap a (runLower a s f)) := by
  rcases runCell_order_or_equal ha r (s + 1) e f with h | h | ⟨h, h'⟩
  · exact Or.inl (by simpa only [runLower_succ ha] using h)
  · exact Or.inr (Or.inl (by simpa only [runUpper_succ ha] using h))
  · subst r; subst e
    exact Or.inr (Or.inr ⟨runLower_succ ha s f, runUpper_succ ha s f⟩)

/-- Iterated inverse branches preserve rational coordinates exactly. -/
lemma tailIter_rat (a t : ℚ) (r : ℕ) :
    tailIter (a : ℝ) r (t : ℝ) = (((fun z : ℚ => 1 / (a + z))^[r] t : ℚ) : ℝ) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [tailIter_succ, Function.iterate_succ_apply']
    simp only [tailMap, ih, Rat.cast_div, Rat.cast_one, Rat.cast_add]

lemma departureLeft_rational (a : ℚ) (e : Departure) :
    ∃ q : ℚ, (q : ℝ) = departureLeft (a : ℝ) e := by
  cases e
  · exact ⟨1 / a, by simp [departureLeft]⟩
  · exact ⟨0, by simp [departureLeft]⟩

lemma departureRight_rational (a : ℚ) (e : Departure) :
    ∃ q : ℚ, (q : ℝ) = departureRight (a : ℝ) e := by
  cases e
  · exact ⟨1, by simp [departureRight]⟩
  · exact ⟨1 / (a + 1), by simp [departureRight]⟩

/-- Both sorted run endpoints are rational for every rational central parameter. -/
theorem run_endpoints_rational (a : ℚ) (r : ℕ) (e : Departure) :
    (∃ q : ℚ, (q : ℝ) = runLower (a : ℝ) r e) ∧
      (∃ q : ℚ, (q : ℝ) = runUpper (a : ℝ) r e) := by
  obtain ⟨l, hl⟩ := departureLeft_rational a e
  obtain ⟨u, hu⟩ := departureRight_rational a e
  let l' : ℚ := (fun z : ℚ => 1 / (a + z))^[r] l
  let u' : ℚ := (fun z : ℚ => 1 / (a + z))^[r] u
  have hl' : tailIter (a : ℝ) r (departureLeft (a : ℝ) e) = (l' : ℝ) := by
    rw [← hl]; exact tailIter_rat a l r
  have hu' : tailIter (a : ℝ) r (departureRight (a : ℝ) e) = (u' : ℝ) := by
    rw [← hu]; exact tailIter_rat a u r
  constructor
  · exact ⟨min l' u', by simp only [runLower, hl', hu', Rat.cast_min]⟩
  · exact ⟨max l' u', by simp only [runUpper, hl', hu', Rat.cast_max]⟩

/-- Closure of a constant-digit prefix without requiring a departure. -/
def constantCell (a : ℝ) (r : ℕ) : Set ℝ := tailIter a r '' Set.Icc (0 : ℝ) 1

noncomputable def constantLower (a : ℝ) (r : ℕ) : ℝ :=
  min (tailIter a r 0) (tailIter a r 1)

noncomputable def constantUpper (a : ℝ) (r : ℕ) : ℝ :=
  max (tailIter a r 0) (tailIter a r 1)

lemma constantCell_eq_Icc {a : ℝ} (ha : 1 < a) (r : ℕ) :
    constantCell a r = Set.Icc (constantLower a r) (constantUpper a r) := by
  have hc := tailIter_continuousOn ha r
  have hi := (tailIter_injective a r).injOn (s := Set.Icc (0 : ℝ) 1)
  rcases hc.strictMonoOn_of_injOn_Icc' (by norm_num : (0 : ℝ) ≤ 1) hi with hm | hm
  · have he := hm.monotoneOn (by simp) (by simp) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [constantCell, constantLower, constantUpper, min_eq_left he,
      max_eq_right he] using hc.image_Icc_of_monotoneOn (by norm_num) hm.monotoneOn
  · have he := hm.antitoneOn (by simp) (by simp) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [constantCell, constantLower, constantUpper, min_eq_right he,
      max_eq_left he] using hc.image_Icc_of_antitoneOn (by norm_num) hm.antitoneOn

lemma metallic_mem_constant_interior {a : ℝ} (ha : 1 < a) (r : ℕ) :
    metallic a ∈ interior (constantCell a r) := by
  rw [constantCell_eq_Icc ha, interior_Icc]
  have hc := tailIter_continuousOn ha r
  have hi := (tailIter_injective a r).injOn (s := Set.Icc (0 : ℝ) 1)
  have hb : metallic a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(metallic_pos a).le, (metallic_lt_one ha.le).le⟩
  rcases hc.strictMonoOn_of_injOn_Icc' (by norm_num : (0 : ℝ) ≤ 1) hi with hm | hm
  · have he := hm.monotoneOn (by simp) (by simp) (by norm_num : (0 : ℝ) ≤ 1)
    have hl := hm (by simp) hb (metallic_pos a)
    have hu := hm hb (by simp) (metallic_lt_one ha.le)
    simpa only [constantLower, constantUpper, min_eq_left he, max_eq_right he,
      metallic_tailIter ha, Set.mem_Ioo] using And.intro hl hu
  · have he := hm.antitoneOn (by simp) (by simp) (by norm_num : (0 : ℝ) ≤ 1)
    have hl := hm hb (by simp) (metallic_lt_one ha.le)
    have hu := hm (by simp) hb (metallic_pos a)
    simpa only [constantLower, constantUpper, min_eq_right he, max_eq_left he,
      metallic_tailIter ha, Set.mem_Ioo] using And.intro hl hu

lemma constantCell_nested {a : ℝ} (ha : 1 < a) (r : ℕ) :
    constantCell a (r + 1) ⊆ constantCell a r := by
  rintro x ⟨t, ht, rfl⟩
  refine ⟨tailMap a t, (tailMap_mem_unit ha ht).imp le_of_lt le_of_lt, ?_⟩
  exact (Function.iterate_succ_apply (tailMap a) r t).symm

lemma runCell_subset_constantCell (a : ℝ) (r : ℕ) (e : Departure) (ha : 1 < a) :
    runCell a r e ⊆ constantCell a r :=
  Set.image_mono (departureInterval_subset_unit ha e)

lemma tailMap_abs_sub_le {a x y : ℝ} (ha : 1 < a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |tailMap a x - tailMap a y| ≤ (1 / a ^ 2) * |x - y| := by
  have hax : 0 < a + x := by linarith
  have hay : 0 < a + y := by linarith
  have ha0 : 0 < a := by linarith
  have hid : tailMap a x - tailMap a y = (y - x) / ((a + x) * (a + y)) := by
    unfold tailMap
    field_simp
    <;> ring
  rw [hid, abs_div, abs_mul, abs_of_pos hax, abs_of_pos hay, abs_sub_comm]
  have hden : a ^ 2 ≤ (a + x) * (a + y) := by nlinarith [mul_nonneg hx hy]
  calc
    |x - y| / ((a + x) * (a + y)) ≤ |x - y| / a ^ 2 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos ha0) hden
    _ = (1 / a ^ 2) * |x - y| := by ring

lemma tailIter_abs_sub_le {a x y : ℝ} (ha : 1 < a) (r : ℕ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |tailIter a r x - tailIter a r y| ≤ (1 / a ^ 2) ^ r * |x - y| := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [tailIter_succ, tailIter_succ]
    calc
      |tailMap a (tailIter a r x) - tailMap a (tailIter a r y)| ≤
          (1 / a ^ 2) * |tailIter a r x - tailIter a r y| :=
        tailMap_abs_sub_le ha (tailIter_mem_unit ha r hx).1 (tailIter_mem_unit ha r hy).1
      _ ≤ (1 / a ^ 2) * ((1 / a ^ 2) ^ r * |x - y|) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (1 / a ^ 2) ^ (r + 1) * |x - y| := by ring

/-- Quantitative convergence of every exact run cell to the metallic point. -/
theorem runCell_distance_le {a x : ℝ} (ha : 1 < a) (r : ℕ) (e : Departure)
    (hx : x ∈ runCell a r e) : |x - metallic a| ≤ (1 / a ^ 2) ^ r := by
  obtain ⟨t, ht, rfl⟩ := hx
  have htunit := departureInterval_subset_unit ha e ht
  have hbunit : metallic a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(metallic_pos a).le, (metallic_lt_one ha.le).le⟩
  have hd : |t - metallic a| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [htunit.1, htunit.2, hbunit.1, hbunit.2]
  have hc := tailIter_abs_sub_le ha r htunit hbunit
  rw [metallic_tailIter ha] at hc
  exact hc.trans (by simpa using (mul_le_mul_of_nonneg_left hd
    (show 0 ≤ (1 / a ^ 2) ^ r by positivity)))

end ContinuedFractionBounds
