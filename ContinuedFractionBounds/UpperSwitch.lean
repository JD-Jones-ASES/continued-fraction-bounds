module

public import ContinuedFractionBounds.Basic

@[expose] public section

namespace ContinuedFractionBounds

/-- The upper-envelope switching curve, extended by zero beyond its positive domain. -/
noncomputable def upperSwitch (a t : ℝ) : ℝ :=
  if t ≤ metallic a then 1 / (a + t) else max 0 (1 / t - a)

lemma metallic_lt_inv {a : ℝ} (ha : 1 ≤ a) : metallic a < 1 / a := by
  have hb := metallic_pos a
  have he := metallic_equation a
  apply (lt_div_iff₀ (by linarith : 0 < a)).2
  nlinarith

lemma upperSwitch_nonneg {a t : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t) :
    0 ≤ upperSwitch a t := by
  unfold upperSwitch
  split_ifs
  · positivity
  · exact le_max_left _ _

lemma upperSwitch_left {a t : ℝ} (ht : t ≤ metallic a) :
    upperSwitch a t = 1 / (a + t) := ite_eq_left ht

lemma upperSwitch_right {a t : ℝ} (ha : 1 ≤ a)
    (ht : metallic a ≤ t) (ht1 : t ≤ 1 / a) :
    upperSwitch a t = 1 / t - a := by
  have hb := metallic_pos a
  have he := metallic_equation a
  have ht0 : 0 < t := hb.trans_le ht
  have ha0 : 0 < a := by linarith
  have hnum : 0 ≤ 1 / t - a := by
    have hat : t * a ≤ 1 := (le_div_iff₀ ha0).1 ht1
    have hat' : a ≤ 1 / t := (le_div_iff₀ ht0).2 (by nlinarith)
    linarith
  by_cases hh : t ≤ metallic a
  · have htb : t = metallic a := le_antisymm hh ht
    rw [upperSwitch_left hh, htb]
    have hab : a + metallic a ≠ 0 := by positivity
    have hb0 : metallic a ≠ 0 := ne_of_gt hb
    field_simp
    nlinarith
  · rw [upperSwitch, ite_eq_right hh, max_eq_right hnum]

lemma upperSwitch_zero {a t : ℝ} (ha : 1 ≤ a) (ht : 1 / a ≤ t) :
    upperSwitch a t = 0 := by
  have hb := metallic_lt_inv ha
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := (by positivity : 0 < 1 / a).trans_le ht
  have htb : ¬ t ≤ metallic a := by linarith
  have hnum : 1 / t - a ≤ 0 := by
    have hat : 1 ≤ t * a := (div_le_iff₀ ha0).1 ht
    have hat' : 1 / t ≤ a := (div_le_iff₀ ht0).2 (by nlinarith)
    linarith
  rw [upperSwitch, ite_eq_right htb, max_eq_left hnum]

lemma upperSwitch_le_inv {a t : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t) :
    upperSwitch a t ≤ 1 / a := by
  have ha0 : 0 < a := by linarith
  by_cases htb : t ≤ metallic a
  · rw [upperSwitch_left htb]
    exact one_div_le_one_div_of_le ha0 (by linarith)
  · have hb := metallic_pos a
    have he := metallic_equation a
    have ht0 : 0 < t := by linarith
    have hsmall : 1 / t - a ≤ metallic a := by
      have hh : 1 / t ≤ a + metallic a := by
        apply (div_le_iff₀ ht0).2
        nlinarith [mul_nonneg (show 0 ≤ a + metallic a by positivity)
          (show 0 ≤ t - metallic a by linarith)]
      linarith
    rw [upperSwitch, ite_eq_right htb]
    exact max_le (by positivity) (hsmall.trans (metallic_lt_inv ha).le)

lemma upperSwitch_mem {a t : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t) :
    upperSwitch a t ∈ Set.Icc (0 : ℝ) (1 / a) :=
  ⟨upperSwitch_nonneg ha ht, upperSwitch_le_inv ha ht⟩

/-- The complete upper switching curve is exactly the level `max(A,B)=1`. -/
theorem upperSwitch_level {a t : ℝ} (ha : 1 ≤ a)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / a) :
    max (t * (a + upperSwitch a t)) (upperSwitch a t * (a + t)) = 1 := by
  have hb := metallic_pos a
  have he := metallic_equation a
  by_cases htb : t ≤ metallic a
  · rw [upperSwitch_left htb]
    have hden : a + t ≠ 0 := by positivity
    have hright : 1 / (a + t) * (a + t) = 1 := by field_simp
    have horder : t ≤ 1 / (a + t) := by
      apply (le_div_iff₀ (by positivity : 0 < a + t)).2
      nlinarith [mul_nonneg (sub_nonneg.mpr htb) (show 0 ≤ a + t by positivity)]
    have hleft : t * (a + 1 / (a + t)) ≤ 1 := by
      nlinarith [mul_nonneg (show 0 ≤ a by linarith) (sub_nonneg.mpr horder)]
    rw [hright, max_eq_right hleft]
  · have ht0 : 0 < t := by linarith
    rw [upperSwitch_right ha (by linarith) ht1]
    have hleft : t * (a + (1 / t - a)) = 1 := by field_simp; ring
    have horder : 1 / t - a ≤ t := by
      have hh : 1 / t ≤ a + t := by
        apply (div_le_iff₀ ht0).2
        nlinarith [mul_nonneg (show 0 ≤ t - metallic a by linarith)
          (show 0 ≤ a + t by positivity)]
      linarith
    have hright : (1 / t - a) * (a + t) ≤ 1 := by
      nlinarith [mul_nonneg (show 0 ≤ a by linarith) (sub_nonneg.mpr horder)]
    rw [hleft, max_eq_left hright]

lemma upperSwitch_unique {a t y : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t) (hy : 0 ≤ y)
    (hlevel : max (t * (a + y)) (y * (a + t)) = 1) : y = upperSwitch a t := by
  have hb := metallic_pos a
  have he := metallic_equation a
  have hA : t * (a + y) ≤ 1 := (le_max_left _ _).trans_eq hlevel
  have hB : y * (a + t) ≤ 1 := (le_max_right _ _).trans_eq hlevel
  have ht1 : t ≤ 1 / a := by
    apply (le_div_iff₀ (by linarith : 0 < a)).2
    nlinarith [mul_nonneg ht hy]
  rcases le_total (t * (a + y)) (y * (a + t)) with horder | horder
  · have hBe : y * (a + t) = 1 := by simpa only [max_eq_right horder] using hlevel
    have hty : t ≤ y := by nlinarith
    have htb : t ≤ metallic a := by
      by_contra hh
      have hbt : metallic a < t := lt_of_not_ge hh
      have hp : 0 < (t - metallic a) * (a + t + metallic a) := by positivity
      nlinarith [mul_nonneg ht (sub_nonneg.mpr hty)]
    rw [upperSwitch_left htb]
    exact (eq_div_iff (by positivity : a + t ≠ 0)).2 hBe
  · have hAe : t * (a + y) = 1 := by simpa only [max_eq_left horder] using hlevel
    have hyt : y ≤ t := by nlinarith
    have hbt : metallic a ≤ t := by
      by_contra hh
      have htb : t < metallic a := lt_of_not_ge hh
      have hp : 0 < (metallic a - t) * (a + t + metallic a) := by positivity
      nlinarith [mul_nonneg ht (sub_nonneg.mpr hyt)]
    have ht0 : 0 < t := hb.trans_le hbt
    rw [upperSwitch_right ha hbt ht1]
    have hh : a + y = 1 / t := (eq_div_iff (ne_of_gt ht0)).2 (by nlinarith)
    linarith

/-- On its nonnegative level-set domain the upper switching curve is an involution. -/
theorem upperSwitch_involution {a t : ℝ} (ha : 1 ≤ a)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / a) : upperSwitch a (upperSwitch a t) = t := by
  apply Eq.symm
  apply upperSwitch_unique ha (upperSwitch_nonneg ha ht) ht
  simpa only [max_comm] using upperSwitch_level ha ht ht1

lemma upperSwitch_level_iff {a t y : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t)
    (ht1 : t ≤ 1 / a) (hy : 0 ≤ y) :
    max (t * (a + y)) (y * (a + t)) = 1 ↔ y = upperSwitch a t := by
  constructor
  · exact upperSwitch_unique ha ht hy
  · rintro rfl
    exact upperSwitch_level ha ht ht1

lemma upperSwitch_metallic {a : ℝ} (ha : 1 ≤ a) :
    upperSwitch a (metallic a) = metallic a := by
  rw [upperSwitch_left le_rfl]
  apply (div_eq_iff (by have := metallic_pos a; positivity : a + metallic a ≠ 0)).2
  exact (metallic_equation a).symm

lemma upperSwitch_le_metallic {a t : ℝ} (ha : 1 ≤ a) (ht : metallic a ≤ t) :
    upperSwitch a t ≤ metallic a := by
  have hb := metallic_pos a
  have he := metallic_equation a
  by_cases hh : t ≤ metallic a
  · have htb : t = metallic a := le_antisymm hh ht
    rw [htb, upperSwitch_metallic ha]
  · have ht0 : 0 < t := hb.trans_le ht
    have hv : 1 / t - a ≤ metallic a := by
      have hh' : 1 / t ≤ a + metallic a := by
        apply (div_le_iff₀ ht0).2
        nlinarith [mul_nonneg (sub_nonneg.mpr ht)
          (show 0 ≤ a + metallic a by positivity)]
      linarith
    rw [upperSwitch, ite_eq_right hh]
    exact max_le hb.le hv

lemma metallic_le_upperSwitch {a t : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t)
    (htb : t ≤ metallic a) : metallic a ≤ upperSwitch a t := by
  have hb := metallic_pos a
  have he := metallic_equation a
  rw [upperSwitch_left htb]
  apply (le_div_iff₀ (by positivity : 0 < a + t)).2
  nlinarith [mul_nonneg hb.le (sub_nonneg.mpr htb)]

/-- The extended upper switching curve is nonincreasing on the nonnegative axis. -/
theorem upperSwitch_antitone {a x y : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) (hxy : x ≤ y) :
    upperSwitch a y ≤ upperSwitch a x := by
  by_cases hyb : y ≤ metallic a
  · rw [upperSwitch_left hyb, upperSwitch_left (hxy.trans hyb)]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · by_cases hxb : x ≤ metallic a
    · exact (upperSwitch_le_metallic ha (by linarith : metallic a ≤ y)).trans
        (metallic_le_upperSwitch ha hx hxb)
    · rw [upperSwitch, ite_eq_right hyb, upperSwitch, ite_eq_right hxb]
      apply max_le_max le_rfl
      have hx0 : 0 < x := (metallic_pos a).trans (lt_of_not_ge hxb)
      have hh := one_div_le_one_div_of_le hx0 hxy
      linarith

/-- It is strictly decreasing on the exact level-set domain. -/
theorem upperSwitch_strictAntiOn {a : ℝ} (ha : 1 ≤ a) :
    StrictAntiOn (upperSwitch a) (Set.Icc (0 : ℝ) (1 / a)) := by
  intro x hx y hy hxy
  apply lt_of_le_of_ne (upperSwitch_antitone ha hx.1 hxy.le)
  intro he
  have hx' := upperSwitch_involution ha hx.1 hx.2
  have hy' := upperSwitch_involution ha hy.1 hy.2
  have hsame := congrArg (upperSwitch a) he
  rw [hx', hy'] at hsame
  linarith

lemma upper_level_strict_increase {a t y z : ℝ} (ha : 1 ≤ a)
    (ht : 0 ≤ t) (hy : 0 ≤ y) (hyz : y < z)
    (he : max (t * (a + y)) (y * (a + t)) = 1) :
    1 < max (t * (a + z)) (z * (a + t)) := by
  rcases le_total (t * (a + y)) (y * (a + t)) with h | h
  · have hh : y * (a + t) = 1 := by simpa only [max_eq_right h] using he
    apply lt_of_lt_of_le _ (le_max_right _ _)
    have hp : 0 < (z - y) * (a + t) := by positivity
    nlinarith
  · have hh : t * (a + y) = 1 := by simpa only [max_eq_left h] using he
    have ht0 : 0 < t := by
      by_contra hn
      have hz : t = 0 := by linarith
      simp [hz] at hh
    apply lt_of_lt_of_le _ (le_max_left _ _)
    have hp : 0 < t * (z - y) := by positivity
    nlinarith

lemma upper_level_strict_decrease {a t y z : ℝ} (ha : 1 ≤ a)
    (ht : 0 ≤ t) (hz : 0 ≤ z) (hzy : z < y)
    (he : max (t * (a + y)) (y * (a + t)) = 1) :
    max (t * (a + z)) (z * (a + t)) < 1 := by
  have hA : t * (a + y) ≤ 1 := (le_max_left _ _).trans_eq he
  have hB : y * (a + t) ≤ 1 := (le_max_right _ _).trans_eq he
  apply max_lt
  · by_cases ht0 : t = 0
    · simp [ht0]
    · have hp : 0 < t * (y - z) := mul_pos (lt_of_le_of_ne ht (Ne.symm ht0)) (by linarith)
      nlinarith
  · have hp : 0 < (y - z) * (a + t) := by positivity
    nlinarith

lemma le_upperSwitch_iff {a t x : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t)
    (ht1 : t ≤ 1 / a) (hx : 0 ≤ x) :
    x ≤ upperSwitch a t ↔ max (t * (a + x)) (x * (a + t)) ≤ 1 := by
  have he := upperSwitch_level ha ht ht1
  constructor
  · intro h
    apply le_trans (max_le_max ?_ ?_) he.le
    · exact mul_le_mul_of_nonneg_left (by linarith) ht
    · exact mul_le_mul_of_nonneg_right h (by positivity)
  · intro h
    by_contra hh
    have hs := upper_level_strict_increase ha ht (upperSwitch_nonneg ha ht)
      (lt_of_not_ge hh) he
    linarith

lemma upperSwitch_le_iff {a t x : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    upperSwitch a t ≤ x ↔ 1 ≤ max (t * (a + x)) (x * (a + t)) := by
  by_cases ht1 : t ≤ 1 / a
  · have he := upperSwitch_level ha ht ht1
    constructor
    · intro h
      apply le_trans he.ge (max_le_max ?_ ?_)
      · exact mul_le_mul_of_nonneg_left (by linarith) ht
      · exact mul_le_mul_of_nonneg_right h (by positivity)
    · intro h
      by_contra hh
      have hs := upper_level_strict_decrease ha ht hx (lt_of_not_ge hh) he
      linarith
  · have hzero := upperSwitch_zero ha (le_of_not_ge ht1)
    have hat : 1 ≤ t * a := (div_le_iff₀ (by linarith : 0 < a)).1 (le_of_not_ge ht1)
    have hbig : 1 ≤ max (t * (a + x)) (x * (a + t)) := by
      apply le_trans _ (le_max_left _ _)
      nlinarith [mul_nonneg ht hx]
    simp only [hzero, hx, hbig]

end ContinuedFractionBounds
