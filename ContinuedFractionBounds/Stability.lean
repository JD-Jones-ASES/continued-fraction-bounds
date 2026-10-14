module

public import ContinuedFractionBounds.Basic

@[expose] public section

/-!
# Sharp inverse stability

The lower three-coefficient envelope on the unit square satisfies a sharp
linear bound in the maximum coordinate distance from its metallic point.
The proof uses fraction differences, including an explicit positive
factorization of the high-coordinate secant difference.
-/

namespace ContinuedFractionBounds

private lemma cappedProduct_le {p q : ℝ} (_hp : 0 ≤ p) (_hq : 0 ≤ q)
    (hd : 0 < p + q) : min 1 (p * q) / (p + q) ≤ p / (1 + p ^ 2) := by
  have hf : 0 < 1 + p ^ 2 := by positivity
  rcases le_total (p * q) 1 with h | h
  · rw [min_eq_right h]
    apply (div_le_div_iff₀ hd hf).2
    have := mul_nonneg (sq_nonneg p) (sub_nonneg.mpr h)
    nlinarith
  · rw [min_eq_left h]
    apply (div_le_div_iff₀ hd hf).2
    nlinarith

lemma lower_le_lowEnvelope {a x y : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    lower a x y ≤ x / (1 + x ^ 2) := by
  have hd : 0 < a + x + y := by linarith
  calc
    lower a x y ≤ min 1 (x * (a + y)) / (a + x + y) := by
      exact div_le_div_of_nonneg_right (min_le_min_left _ (min_le_left _ _)) hd.le
    _ = min 1 (x * (a + y)) / (x + (a + y)) := by ring_nf
    _ ≤ x / (1 + x ^ 2) := cappedProduct_le hx (by linarith) (by linarith)

lemma lower_le_highEnvelope {a x y : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    lower a x y ≤ (a + x) / (1 + (a + x) ^ 2) := by
  have hd : 0 < a + x + y := by linarith
  calc
    lower a x y ≤ min 1 (y * (a + x)) / (a + x + y) := by
      exact div_le_div_of_nonneg_right (min_le_min_left _ (min_le_right _ _)) hd.le
    _ = min 1 ((a + x) * y) / ((a + x) + y) := by rw [mul_comm y]
    _ ≤ (a + x) / (1 + (a + x) ^ 2) :=
      cappedProduct_le (by linarith) hy hd

lemma highEnvelope_equality_product {a x y : ℝ} (ha : 0 < a)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (he : lower a x y = (a + x) / (1 + (a + x) ^ 2)) :
    y * (a + x) = 1 := by
  have hd : 0 < a + x + y := by linarith
  have hp : 0 < a + x := by linarith
  have hf : 0 < 1 + (a + x) ^ 2 := by positivity
  have h₀ := lower_le_one_div hd
  have h₁ := lower_le_right_div hd
  rw [he] at h₀ h₁
  have h₀' := (div_le_div_iff₀ hf hd).1 h₀
  have h₁' := (div_le_div_iff₀ hf hd).1 h₁
  have hle : y * (a + x) ≤ 1 := by nlinarith [h₀']
  have hge : 1 ≤ y * (a + x) := by
    by_contra h
    have hn : 0 < 1 - y * (a + x) := by linarith
    have hs : 0 < (a + x) ^ 2 := sq_pos_of_pos hp
    have hh := mul_pos hs hn
    nlinarith [h₁']
  exact le_antisymm hle hge

lemma stabilityConstant_lt_threshold {a : ℝ} (ha : 2 ≤ a) :
    stabilityConstant a < threshold a := by
  have hb := metallic_pos a
  have hc := threshold_pos a
  have hd : 0 < 1 + (a + 1) ^ 2 := by positivity
  have h : a + 1 - metallic a < 1 + (a + 1) ^ 2 := by
    nlinarith [sq_nonneg (a + 1 - 1 / 2)]
  unfold stabilityConstant
  apply (div_lt_iff₀ hd).2
  nlinarith [mul_pos hc (sub_pos.mpr h)]

private lemma low_secant {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t)
    (htb : t ≤ metallic a) :
    threshold a - t / (1 + t ^ 2) ≥ threshold a * (metallic a - t) := by
  set β := metallic a
  have hb : 0 < β := metallic_pos a
  have hbhalf : β < 1 / 2 := metallic_lt_half ha
  have ht1 : t ≤ 1 := by linarith
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have hbt : 0 ≤ β * (t - t ^ 2) := mul_nonneg hb.le (by linarith)
  have hbt' : 0 ≤ β * (1 - 2 * t) := mul_nonneg hb.le (by linarith)
  have hfactor : 0 ≤ 1 - β * t - β - β * t ^ 2 := by nlinarith
  have hprod := mul_nonneg (show 0 ≤ β - t by linarith) hfactor
  rw [threshold_eq_metallic]
  change β / (1 + β ^ 2) - t / (1 + t ^ 2) ≥
    β / (1 + β ^ 2) * (β - t)
  have hd : 0 < (1 + β ^ 2) * (1 + t ^ 2) := by positivity
  apply (le_of_sub_nonneg ?_)
  apply (nonneg_of_mul_nonneg_right ?_ hd)
  field_simp
  nlinarith [hprod]

private lemma high_secant_identity (a t : ℝ) :
    threshold a - (a + t) / (1 + (a + t) ^ 2) =
      threshold a * (t - metallic a) * (a + t - metallic a) /
        (1 + (a + t) ^ 2) := by
  rw [threshold_eq_metallic]
  have he := metallic_equation a
  have hd : (1 + metallic a ^ 2) ≠ 0 := by positivity
  have ht : (1 + (a + t) ^ 2) ≠ 0 := by positivity
  field_simp
  nlinarith [congrArg (fun z : ℝ => z * (a + t - metallic a)) he]

private lemma high_slope_identity (a t : ℝ) :
    (a + t - metallic a) / (1 + (a + t) ^ 2) -
      (a + 1 - metallic a) / (1 + (a + 1) ^ 2) =
    (1 - t) * ((a + 1 - metallic a) * (a + t) - 1 - metallic a * (a + 1)) /
      ((1 + (a + t) ^ 2) * (1 + (a + 1) ^ 2)) := by
  have ht : (1 + (a + t) ^ 2) ≠ 0 := by positivity
  have h1 : (1 + (a + 1) ^ 2) ≠ 0 := by positivity
  field_simp
  ring

private lemma high_slope_factor_pos {a t : ℝ} (ha : 2 ≤ a) (ht : metallic a ≤ t) :
    0 < (a + 1 - metallic a) * (a + t) - 1 - metallic a * (a + 1) := by
  have hb := metallic_pos a
  have hb1 := metallic_lt_one (by linarith : 1 ≤ a)
  have he := metallic_equation a
  have hp := mul_nonneg (show 0 ≤ a + 1 - metallic a by linarith)
    (show 0 ≤ t - metallic a by linarith)
  nlinarith [sq_nonneg a]

private lemma high_secant {a t : ℝ} (ha : 2 ≤ a) (ht : metallic a ≤ t) (ht1 : t ≤ 1) :
    stabilityConstant a * (t - metallic a) ≤
      threshold a - (a + t) / (1 + (a + t) ^ 2) := by
  have hc := threshold_pos a
  have hf := high_slope_factor_pos ha ht
  have hi := high_slope_identity a t
  have hdiv : 0 ≤ (1 - t) *
      ((a + 1 - metallic a) * (a + t) - 1 - metallic a * (a + 1)) /
      ((1 + (a + t) ^ 2) * (1 + (a + 1) ^ 2)) := by positivity
  have hs : (a + 1 - metallic a) / (1 + (a + 1) ^ 2) ≤
      (a + t - metallic a) / (1 + (a + t) ^ 2) := by linarith
  rw [high_secant_identity]
  unfold stabilityConstant
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ threshold a * (t - metallic a) by positivity)
  convert hm using 1 <;> ring

lemma coordinate_stability {a x y : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) :
    stabilityConstant a * |x - metallic a| ≤ threshold a - lower a x y := by
  rcases le_total x (metallic a) with h | h
  · rw [abs_of_nonpos (by linarith : x - metallic a ≤ 0)]
    have hs := low_secant ha hx h
    have hf := lower_le_lowEnvelope (by linarith : 0 < a) hx hy
    have hk := stabilityConstant_lt_threshold ha
    have hm := mul_le_mul_of_nonneg_right hk.le (show 0 ≤ metallic a - x by linarith)
    nlinarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ x - metallic a)]
    have hs := high_secant ha h hx1
    have hf := lower_le_highEnvelope (by linarith : 0 < a) hx hy
    linarith

/-- Sharp global inverse stability on the entire closed unit square. -/
theorem global_stability {a x y : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    stabilityConstant a * max |x - metallic a| |y - metallic a| ≤
      threshold a - lower a x y := by
  rw [mul_max_of_nonneg _ _ (stabilityConstant_pos ha).le]
  apply max_le
  · exact coordinate_stability ha hx hx1 hy
  · simpa [lower_comm] using coordinate_stability ha hy hy1 hx


private lemma high_secant_strict {a t : ℝ} (ha : 2 ≤ a)
    (ht : metallic a < t) (ht1 : t < 1) :
    stabilityConstant a * (t - metallic a) <
      threshold a - (a + t) / (1 + (a + t) ^ 2) := by
  have hc := threshold_pos a
  have hf := high_slope_factor_pos ha ht.le
  have hi := high_slope_identity a t
  have hdiv : 0 < (1 - t) *
      ((a + 1 - metallic a) * (a + t) - 1 - metallic a * (a + 1)) /
      ((1 + (a + t) ^ 2) * (1 + (a + 1) ^ 2)) := by positivity
  have hs : (a + 1 - metallic a) / (1 + (a + 1) ^ 2) <
      (a + t - metallic a) / (1 + (a + t) ^ 2) := by linarith
  rw [high_secant_identity]
  unfold stabilityConstant
  have hm := mul_lt_mul_of_pos_left hs
    (show 0 < threshold a * (t - metallic a) by positivity)
  convert hm using 1 <;> ring

lemma coordinate_stability_eq {a x y : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y)
    (hne : x ≠ metallic a)
    (he : threshold a - lower a x y = stabilityConstant a * |x - metallic a|) :
    x = 1 ∧ y = 1 / (a + 1) := by
  have hxhigh : metallic a < x := by
    by_contra h
    have hlow : x < metallic a := lt_of_le_of_ne (by linarith) hne
    rw [abs_of_neg (by linarith : x - metallic a < 0)] at he
    have hs := low_secant ha hx hlow.le
    have hf := lower_le_lowEnvelope (by linarith : 0 < a) hx hy
    have hk := stabilityConstant_lt_threshold ha
    have hm := mul_lt_mul_of_pos_right hk (show 0 < metallic a - x by linarith)
    nlinarith
  rw [abs_of_pos (by linarith : 0 < x - metallic a)] at he
  have hxone : x = 1 := by
    by_contra h
    have hlt : x < 1 := lt_of_le_of_ne hx1 h
    have hs := high_secant_strict ha hxhigh hlt
    have hf := lower_le_highEnvelope (by linarith : 0 < a) hx hy
    linarith
  refine ⟨hxone, ?_⟩
  have hs := high_secant ha hxhigh.le hx1
  have hf := lower_le_highEnvelope (by linarith : 0 < a) hx hy
  have hg : lower a x y = (a + x) / (1 + (a + x) ^ 2) := by linarith
  have hp := highEnvelope_equality_product (by linarith : 0 < a) hx hy hg
  rw [hxone] at hp
  apply (eq_div_iff (show a + 1 ≠ 0 by linarith)).2
  exact hp

lemma endpoint_lt_metallic {a : ℝ} (ha : 2 ≤ a) :
    1 / (a + 1) < metallic a := by
  have hb := metallic_pos a
  have hb1 := metallic_lt_one (by linarith : 1 ≤ a)
  have he := metallic_equation a
  apply (div_lt_iff₀ (show 0 < a + 1 by linarith)).2
  have := mul_pos hb (sub_pos.mpr hb1)
  nlinarith

lemma lower_one_endpoint {a : ℝ} (ha : 2 ≤ a) :
    lower a 1 (1 / (a + 1)) = (a + 1) / (1 + (a + 1) ^ 2) := by
  have hb : 0 < a + 1 := by linarith
  have hd : 0 < 1 / (a + 1) := by positivity
  have he : 1 / (a + 1) * (a + 1) = 1 := by field_simp
  have hn : 1 ≤ 1 * (a + 1 / (a + 1)) := by linarith
  unfold lower
  rw [he, min_eq_right hn, min_self]
  have hf : 1 + (a + 1) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

lemma endpoint_distance {a : ℝ} (ha : 2 ≤ a) :
    max |(1 : ℝ) - metallic a| |1 / (a + 1) - metallic a| = 1 - metallic a := by
  have hb := metallic_lt_half ha
  have hd := endpoint_lt_metallic ha
  have hp : 0 < 1 / (a + 1) := by positivity
  rw [abs_of_pos (by linarith : 0 < (1 : ℝ) - metallic a),
    abs_of_neg (by linarith : 1 / (a + 1) - metallic a < 0)]
  apply max_eq_left
  linarith

lemma endpoint_stability_eq {a : ℝ} (ha : 2 ≤ a) :
    threshold a - lower a 1 (1 / (a + 1)) =
      stabilityConstant a * max |(1 : ℝ) - metallic a| |1 / (a + 1) - metallic a| := by
  rw [lower_one_endpoint ha, endpoint_distance ha, high_secant_identity]
  unfold stabilityConstant
  ring

/-- The complete equality locus consists of the metallic point and two boundary points. -/
theorem global_stability_eq_iff {a x y : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    threshold a - lower a x y = stabilityConstant a * max |x - metallic a| |y - metallic a| ↔
      (x = metallic a ∧ y = metallic a) ∨
      (x = 1 ∧ y = 1 / (a + 1)) ∨ (x = 1 / (a + 1) ∧ y = 1) := by
  constructor
  · intro he
    by_cases hzero : max |x - metallic a| |y - metallic a| = 0
    · left
      have hxx : |x - metallic a| ≤ 0 := by simpa [hzero] using le_max_left |x - metallic a| |y - metallic a|
      have hyy : |y - metallic a| ≤ 0 := by simpa [hzero] using le_max_right |x - metallic a| |y - metallic a|
      exact ⟨sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hxx (abs_nonneg _))),
        sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hyy (abs_nonneg _)))⟩
    · rcases le_total |y - metallic a| |x - metallic a| with hxy | hyx
      · rw [max_eq_left hxy] at he hzero
        have hne : x ≠ metallic a := by intro h; simp [h] at hzero
        exact Or.inr (Or.inl (coordinate_stability_eq ha hx hx1 hy hne he))
      · rw [max_eq_right hyx] at he hzero
        have hne : y ≠ metallic a := by intro h; simp [h] at hzero
        have he' : threshold a - lower a y x = stabilityConstant a * |y - metallic a| := by
          simpa [lower_comm] using he
        have hh := coordinate_stability_eq ha hy hy1 hx hne he'
        exact Or.inr (Or.inr ⟨hh.2, hh.1⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simp [lower_metallic (by linarith : 0 < a)]
    · exact endpoint_stability_eq ha
    · simpa only [lower_comm, max_comm] using endpoint_stability_eq ha

/-- No coefficient larger than `stabilityConstant a` works on the unit square. -/
theorem stabilityConstant_optimal {a K : ℝ} (ha : 2 ≤ a)
    (hK : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      K * max |x - metallic a| |y - metallic a| ≤ threshold a - lower a x y) :
    K ≤ stabilityConstant a := by
  have hd0 : 0 ≤ 1 / (a + 1) := by positivity
  have hd1 : 1 / (a + 1) ≤ 1 := (div_le_one (by linarith : 0 < a + 1)).2 (by linarith)
  have hh := hK 1 ⟨by norm_num, le_rfl⟩ (1 / (a + 1)) ⟨hd0, hd1⟩
  rw [endpoint_stability_eq ha, endpoint_distance ha] at hh
  exact (mul_le_mul_iff_left₀ (show 0 < 1 - metallic a by
    have := metallic_lt_one (by linarith : 1 ≤ a); linarith)).1 hh


/-- The metallic point for the silver digit. -/
lemma metallic_two : metallic 2 = Real.sqrt 2 - 1 := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h8 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 ^ 2 + 4 by norm_num)
  have hp2 := Real.sqrt_nonneg (2 : ℝ)
  have hp8 := Real.sqrt_nonneg ((2 : ℝ) ^ 2 + 4)
  have hs : Real.sqrt ((2 : ℝ) ^ 2 + 4) = 2 * Real.sqrt 2 := by nlinarith
  unfold metallic
  rw [hs]
  ring

/-- The sharp coefficient for the silver digit, in closed form. -/
lemma stabilityConstant_two : stabilityConstant 2 = (2 * Real.sqrt 2 - 1) / 20 := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp2 : 0 < Real.sqrt (2 : ℝ) := by positivity
  have h8 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 ^ 2 + 4 by norm_num)
  have hp8 := Real.sqrt_nonneg ((2 : ℝ) ^ 2 + 4)
  have hs : Real.sqrt ((2 : ℝ) ^ 2 + 4) = 2 * Real.sqrt 2 := by nlinarith
  unfold stabilityConstant threshold
  rw [metallic_two, hs]
  field_simp
  nlinarith

end ContinuedFractionBounds
