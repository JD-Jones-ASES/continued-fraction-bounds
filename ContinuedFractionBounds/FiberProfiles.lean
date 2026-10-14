module

public import ContinuedFractionBounds.UpperRectangleOptimization

@[expose] public section

namespace ContinuedFractionBounds

/-- Exact maximum of the lower envelope along a vertical unit segment. -/
noncomputable def lowerProfile (a t : ℝ) : ℝ :=
  if t ≤ 1 / (a + 1) then t * (a + 1) / (a + 1 + t)
  else if t ≤ metallic a then t / (1 + t ^ 2)
  else (a + t) / (1 + (a + t) ^ 2)

/-- A maximizing second coordinate, including the nonunique zero fiber. -/
noncomputable def lowerProfileWitness (a t : ℝ) : ℝ :=
  if t ≤ 1 / (a + 1) then 1 else if t ≤ metallic a then 1 / t - a else 1 / (a + t)

/-- Exact minimum of the upper envelope along a vertical unit segment. -/
noncomputable def upperProfile (a t : ℝ) : ℝ :=
  if t ≤ metallic a then (a + t) / (1 + (a + t) ^ 2)
  else if t ≤ 1 / a then t / (1 + t ^ 2) else a * t / (a + t)

/-- The unique minimizing second coordinate. -/
noncomputable def upperProfileWitness (a t : ℝ) : ℝ :=
  if t ≤ metallic a then 1 / (a + t) else if t ≤ 1 / a then 1 / t - a else 0

lemma lower_first_value {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) (_ht1 : t ≤ 1)
    (hsmall : t ≤ 1 / (a + 1)) : lower a t 1 = t * (a + 1) / (a + 1 + t) := by
  have hA : t * (a + 1) ≤ 1 := (le_div_iff₀ (by linarith : 0 < a + 1)).1 hsmall
  have hAB : t * (a + 1) ≤ 1 * (a + t) := by nlinarith
  unfold lower
  rw [min_eq_left hAB, min_eq_right hA]
  congr 1
  ring

lemma upper_last_value {a t : ℝ} (ha : 2 ≤ a) (ht : 1 / a ≤ t) :
    upper a t 0 = a * t / (a + t) := by
  have hat : 1 ≤ a * t := by
    have hh := (div_le_iff₀ (by linarith : 0 < a)).1 ht
    nlinarith
  unfold upper
  simp only [add_zero, zero_mul]
  rw [max_eq_left (show 0 ≤ t * a by nlinarith), max_eq_right (by nlinarith : 1 ≤ t * a)]
  congr 1
  ring

/-- Full lower fiber profile, attainment, and all equality cases. -/
theorem lowerProfile_optimal {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    lowerProfileWitness a t ∈ Set.Icc (0 : ℝ) 1 ∧
      lower a t (lowerProfileWitness a t) = lowerProfile a t ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        lower a t u ≤ lowerProfile a t ∧
        (lower a t u = lowerProfile a t ↔ t = 0 ∨ u = lowerProfileWitness a t) := by
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  by_cases hs : t ≤ 1 / (a + 1)
  · simp only [lowerProfile, lowerProfileWitness, hs, ↓reduceIte]
    have hv := lower_first_value ha ht ht1 hs
    refine ⟨by norm_num, hv, ?_⟩
    intro u hu
    by_cases hz : t = 0
    · simp [hz, lower, mul_nonneg hu.1 ha0.le]
    · have ht0 : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
      have hQ : min (t * (a + 1)) (1 * (a + t)) ≤ 1 :=
        (min_le_left _ _).trans ((le_div_iff₀ (by linarith : 0 < a + 1)).1 hs)
      have hh := lower_below_corner ha0 ht hu.1 ht0 (by norm_num : (0:ℝ)<1)
        le_rfl hu.2 hQ
      simpa only [hv, hz, false_or, true_and] using hh
  · have hdpos : 0 < 1 / (a + 1) := by positivity
    have ht0 : 0 < t := hdpos.trans (lt_of_not_ge hs)
    by_cases hb : t ≤ metallic a
    · simp only [lowerProfile, lowerProfileWitness, hs, hb, ↓reduceIte]
      have hsw := lowerSwitch_low ha0 ht0 hb
      have hpos : 0 < 1 / t - a := by rw [← hsw]; exact lowerSwitch_pos ha0 ht0
      have hle : 1 / t - a ≤ 1 := by
        have hh : 1 / t ≤ a + 1 := (div_le_iff₀ ht0).2
          (by nlinarith [(div_le_iff₀ (by linarith : 0 < a + 1)).1 (le_of_not_ge hs)])
        linarith
      have hv := lowerSwitch_value_low ha0 ht0 hb
      rw [hsw] at hv
      refine ⟨⟨hpos.le, hle⟩, hv, ?_⟩
      intro u hu
      have hh := lower_low_boundary ha1 ht0 hb ht le_rfl hu.1
      simpa only [hsw, hv, ne_of_gt ht0, false_or, true_and] using hh
    · simp only [lowerProfile, lowerProfileWitness, hs, hb, ↓reduceIte]
      have hbt := le_of_not_ge hb
      have hsw := lowerSwitch_high ha0 hbt
      have hpos : 0 < 1 / (a + t) := by positivity
      have hle : 1 / (a + t) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
      have hv := lowerSwitch_value_high ha0 hbt
      rw [hsw] at hv
      refine ⟨⟨hpos.le, hle⟩, hv, ?_⟩
      intro u hu
      have hh := lower_high_boundary ha1 hbt le_rfl hu.1
      simpa only [hsw, hv, ne_of_gt ht0, false_or, true_and] using hh

/-- Full upper fiber profile, its witness, and uniqueness including endpoint fibers. -/
theorem upperProfile_optimal {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    upperProfileWitness a t ∈ Set.Icc (0 : ℝ) 1 ∧
      upper a t (upperProfileWitness a t) = upperProfile a t ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        upperProfile a t ≤ upper a t u ∧
        (upper a t u = upperProfile a t ↔ u = upperProfileWitness a t) := by
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  by_cases hb : t ≤ metallic a
  · simp only [upperProfile, upperProfileWitness, hb, ↓reduceIte]
    have hsw := upperSwitch_left hb
    have hv := upperSwitch_value_low ha1 ht hb
    rw [hsw] at hv
    have hle : 1 / (a + t) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    refine ⟨⟨by positivity, hle⟩, hv, ?_⟩
    intro u hu
    have hh := upper_low_boundary ha1 ht hb ht le_rfl hu.1
    simpa only [hsw, hv, true_and] using hh
  · have hbt := le_of_not_ge hb
    have ht0 : 0 < t := (metallic_pos a).trans_le hbt
    by_cases hi : t ≤ 1 / a
    · simp only [upperProfile, upperProfileWitness, hb, hi, ↓reduceIte]
      have hsw := upperSwitch_right ha1 hbt hi
      have hm := upperSwitch_mem ha1 ht
      have hle : 1 / a ≤ 1 := (div_le_one ha0).2 ha1
      rw [hsw] at hm
      have hv := upperSwitch_value_high ha1 hbt hi
      rw [hsw] at hv
      refine ⟨⟨hm.1, hm.2.trans hle⟩, hv, ?_⟩
      intro u hu
      have hh := upper_high_boundary ha1 hbt hi le_rfl ht1 hu.1
      simpa only [hsw, hv, true_and] using hh
    · simp only [upperProfile, upperProfileWitness, hb, hi, ↓reduceIte]
      have hit := le_of_not_ge hi
      have hv := upper_last_value ha hit
      refine ⟨by norm_num, hv, ?_⟩
      intro u hu
      have hP : 1 ≤ max (t * (a + 0)) (0 * (a + t)) := by
        apply le_trans _ (le_max_left _ _)
        have hh := (div_le_iff₀ ha0).1 hit
        nlinarith
      have hh := upper_above_corner ha0 ht (by norm_num : (0:ℝ)≤0) le_rfl hu.1 hP
      simpa only [hv, true_and] using hh

lemma lowerProfile_eq_switch {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hd : 1 / (a + 1) < t) :
    lowerProfile a t = lower a t (lowerSwitch a t) := by
  have hw : lowerProfileWitness a t = lowerSwitch a t := by
    unfold lowerProfileWitness
    simp only [not_le.mpr hd, ↓reduceIte]
    split_ifs with hb
    · exact (lowerSwitch_low (by linarith) (lt_trans (by positivity : 0 < 1 / (a + 1)) hd) hb).symm
    · exact (lowerSwitch_high (by linarith) (le_of_not_ge hb)).symm
  rw [← hw]
  exact (lowerProfile_optimal ha ht ht1).2.1.symm

lemma upperProfile_eq_switch {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hi : t ≤ 1 / a) :
    upperProfile a t = upper a t (upperSwitch a t) := by
  have hw : upperProfileWitness a t = upperSwitch a t := by
    unfold upperProfileWitness
    split_ifs with hb
    · exact (upperSwitch_left hb).symm
    · exact (upperSwitch_right (by linarith) (le_of_not_ge hb) hi).symm
  rw [← hw]
  exact (upperProfile_optimal ha ht ht1).2.1.symm

/-- The lower fiber optimum is strictly increasing up to the metallic point. -/
theorem lowerProfile_strictMono_below {a x y : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ metallic a) :
    lowerProfile a x < lowerProfile a y := by
  have ha1 : 1 ≤ a := by linarith
  have hy1 : y ≤ 1 := hy.trans (metallic_lt_one ha1).le
  have hx1 : x ≤ 1 := hxy.le.trans hy1
  by_cases hd : y ≤ 1 / (a + 1)
  · have hxd := hxy.le.trans hd
    simp only [lowerProfile, hd, hxd, ↓reduceIte]
    apply (div_lt_div_iff₀ (by positivity : 0 < a + 1 + x)
      (by linarith : 0 < a + 1 + y)).2
    have hp : 0 < (y - x) * (a + 1) ^ 2 := mul_pos (sub_pos.mpr hxy) (by positivity)
    nlinarith
  · have hdy := lt_of_not_ge hd
    have hop := lowerProfile_optimal ha hx hx1
    have hb := lower_low_boundary ha1 (by linarith : 0 < y) hy hx hxy.le hop.1.1
    rw [← lowerProfile_eq_switch ha (by linarith) hy1 hdy, hop.2.1] at hb
    exact lt_of_le_of_ne hb.1 (fun he => (ne_of_lt hxy) (hb.2.mp he).1)

/-- The lower fiber optimum is strictly decreasing after the metallic point. -/
theorem lowerProfile_strictAnti_above {a x y : ℝ} (ha : 2 ≤ a)
    (hx : metallic a ≤ x) (hxy : x < y) (hy : y ≤ 1) :
    lowerProfile a y < lowerProfile a x := by
  have ha1 : 1 ≤ a := by linarith
  have hx0 : 0 ≤ x := (metallic_pos a).le.trans hx
  have hy0 : 0 ≤ y := hx0.trans hxy.le
  have hd : 1 / (a + 1) < x := (endpoint_lt_metallic ha).trans_le hx
  have hop := lowerProfile_optimal ha hy0 hy
  have hb := lower_high_boundary ha1 hx hxy.le hop.1.1
  rw [← lowerProfile_eq_switch ha hx0 (hxy.le.trans hy) hd, hop.2.1] at hb
  exact lt_of_le_of_ne hb.1 (fun he => (ne_of_gt hxy) (hb.2.mp he).1)

/-- The upper fiber optimum is strictly decreasing up to the metallic point. -/
theorem upperProfile_strictAnti_below {a x y : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ metallic a) :
    upperProfile a y < upperProfile a x := by
  have ha1 : 1 ≤ a := by linarith
  have hy1 : y ≤ 1 := hy.trans (metallic_lt_one ha1).le
  have hi : y ≤ 1 / a := hy.trans (metallic_lt_inv ha1).le
  have hop := upperProfile_optimal ha hx (hxy.le.trans hy1)
  have hb := upper_low_boundary ha1 (by linarith : 0 ≤ y) hy hx hxy.le hop.1.1
  rw [← upperProfile_eq_switch ha (by linarith) hy1 hi, hop.2.1] at hb
  exact lt_of_le_of_ne hb.1 (fun he => (ne_of_lt hxy) (hb.2.mp he.symm).1)

/-- The upper fiber optimum is strictly increasing after the metallic point. -/
theorem upperProfile_strictMono_above {a x y : ℝ} (ha : 2 ≤ a)
    (hx : metallic a ≤ x) (hxy : x < y) (hy : y ≤ 1) :
    upperProfile a x < upperProfile a y := by
  have ha1 : 1 ≤ a := by linarith
  have hx0 : 0 < x := (metallic_pos a).trans_le hx
  by_cases hi : x ≤ 1 / a
  · have hop := upperProfile_optimal ha (hx0.le.trans hxy.le) hy
    have hb := upper_high_boundary ha1 hx hi hxy.le hy hop.1.1
    rw [← upperProfile_eq_switch ha hx0.le (hxy.le.trans hy) hi, hop.2.1] at hb
    exact lt_of_le_of_ne hb.1 (fun he => (ne_of_gt hxy) (hb.2.mp he.symm).1)
  · have hxi := lt_of_not_ge hi
    have hyi := hxi.trans hxy
    have hxb : ¬x ≤ metallic a := not_le.mpr ((metallic_lt_inv ha1).trans hxi)
    have hyb : ¬y ≤ metallic a := not_le.mpr ((metallic_lt_inv ha1).trans hyi)
    simp only [upperProfile, hxb, hyb, hi, not_le.mpr hyi, ↓reduceIte]
    apply (div_lt_div_iff₀ (by positivity : 0 < a + x)
      (by linarith : 0 < a + y)).2
    have hp : 0 < (y - x) * a ^ 2 := mul_pos (sub_pos.mpr hxy) (by positivity)
    nlinarith

lemma lowerProfile_small {a t : ℝ} (ht : t ≤ 1 / (a + 1)) :
    lowerProfile a t = t * (a + 1) / (a + 1 + t) := by
  simp only [lowerProfile,ht,↓reduceIte]

/-- The middle formula also holds at its shared left endpoint. -/
lemma lowerProfile_middle {a t : ℝ} (ha : 2 ≤ a)
    (hl : 1 / (a + 1) ≤ t) (hu : t ≤ metallic a) :
    lowerProfile a t = t / (1 + t ^ 2) := by
  by_cases hs : t ≤ 1 / (a + 1)
  · have he : t = 1 / (a + 1) := le_antisymm hs hl
    subst t
    rw [lowerProfile_small le_rfl]
    have ha0 : a + 1 ≠ 0 := by linarith
    field_simp
  · simp only [lowerProfile,hs,hu,↓reduceIte]

/-- The high formula includes the metallic junction. -/
lemma lowerProfile_high {a t : ℝ} (ha : 2 ≤ a) (ht : metallic a ≤ t) :
    lowerProfile a t = (a + t) / (1 + (a + t) ^ 2) := by
  have hs : ¬t ≤ 1 / (a + 1) := not_le.mpr ((endpoint_lt_metallic ha).trans_le ht)
  simp only [lowerProfile,hs,↓reduceIte]
  by_cases hb : t ≤ metallic a
  · have he : t = metallic a := le_antisymm hb ht
    subst t
    simp only [le_refl,↓reduceIte]
    exact (threshold_eq_metallic a).symm.trans (threshold_eq_high a)
  · simp only [hb,↓reduceIte]

lemma upperProfile_low {a t : ℝ} (ht : t ≤ metallic a) :
    upperProfile a t = (a + t) / (1 + (a + t) ^ 2) := by
  simp only [upperProfile,ht,↓reduceIte]

/-- The upper middle formula includes both shared endpoints. -/
lemma upperProfile_middle {a t : ℝ} (_ha : 2 ≤ a)
    (hl : metallic a ≤ t) (hu : t ≤ 1 / a) :
    upperProfile a t = t / (1 + t ^ 2) := by
  by_cases hb : t ≤ metallic a
  · have he : t = metallic a := le_antisymm hb hl
    subst t
    rw [upperProfile_low le_rfl]
    exact (threshold_eq_high a).symm.trans (threshold_eq_metallic a)
  · simp only [upperProfile,hb,hu,↓reduceIte]

/-- The upper last formula includes the clipping junction at `1/a`. -/
lemma upperProfile_high {a t : ℝ} (ha : 2 ≤ a) (ht : 1 / a ≤ t) :
    upperProfile a t = a * t / (a + t) := by
  have hb : ¬t ≤ metallic a := not_le.mpr ((metallic_lt_inv (by linarith : 1 ≤ a)).trans_le ht)
  simp only [upperProfile,hb,↓reduceIte]
  by_cases hi : t ≤ 1 / a
  · have he : t = 1 / a := le_antisymm hi ht
    subst t
    simp only [le_refl,↓reduceIte]
    have ha0 : a ≠ 0 := by linarith
    field_simp
  · simp only [hi,↓reduceIte]

@[simp] lemma lowerProfile_zero (a : ℝ) (ha : 2 ≤ a) : lowerProfile a 0 = 0 := by
  rw [lowerProfile_small (by positivity)]
  simp

@[simp] lemma upperProfile_zero (a : ℝ) : upperProfile a 0 = a / (1 + a ^ 2) := by
  rw [upperProfile_low (metallic_pos a).le]
  simp

lemma lowerProfile_metallic {a : ℝ} (ha : 2 ≤ a) :
    lowerProfile a (metallic a) = threshold a := by
  rw [lowerProfile_high ha le_rfl, ← threshold_eq_high]

lemma upperProfile_metallic (a : ℝ) :
    upperProfile a (metallic a) = threshold a := by
  rw [upperProfile_low le_rfl, ← threshold_eq_high]

/-- The two profiles meet the classical threshold only at the metallic coordinate. -/
theorem profiles_threshold {a t : ℝ} (ha : 2 ≤ a) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    lowerProfile a t ≤ threshold a ∧ threshold a ≤ upperProfile a t ∧
      (lowerProfile a t = threshold a ↔ t = metallic a) ∧
      (upperProfile a t = threshold a ↔ t = metallic a) := by
  have hlo := lowerProfile_optimal ha ht.1 ht.2
  have hup := upperProfile_optimal ha ht.1 ht.2
  by_cases he : t = metallic a
  · simp only [he,lowerProfile_metallic ha,upperProfile_metallic,le_refl,and_self]
  · have hl := lower_lt_threshold_of_ne (by linarith : 1 ≤ a) ht.1 ht.2 hlo.1.1 he
    have hu := threshold_lt_upper_of_ne (by linarith : 1 ≤ a) ht.1 ht.2 hup.1.1 he
    rw [hlo.2.1] at hl
    rw [hup.2.1] at hu
    exact ⟨hl.le,hu.le,iff_of_false (ne_of_lt hl) he,iff_of_false (ne_of_gt hu) he⟩

end ContinuedFractionBounds
