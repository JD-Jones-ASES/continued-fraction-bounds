module

public import ContinuedFractionBounds.Basic
public import ContinuedFractionBounds.Stability

/-! # Classical metallic thresholds and their equality loci -/

@[expose] public section
namespace ContinuedFractionBounds

private lemma raisedProduct_ge {p q : ℝ} (_hp : 0 ≤ p) (_hq : 0 ≤ q)
    (hd : 0 < p + q) : p / (1+p^2) ≤ max 1 (p*q) / (p+q) := by
  have hf : 0 < 1+p^2 := by positivity
  rcases le_total (p*q) 1 with h | h
  · rw [max_eq_left h]
    apply (div_le_div_iff₀ hf hd).2
    nlinarith
  · rw [max_eq_right h]
    apply (div_le_div_iff₀ hf hd).2
    have hh := mul_nonneg (sq_nonneg p) (sub_nonneg.mpr h)
    nlinarith

lemma lowEnvelope_le_upper {a x y : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x/(1+x^2) ≤ upper a x y := by
  have hd : 0 < a+x+y := by linarith
  calc
    x/(1+x^2) ≤ max 1 (x*(a+y))/(x+(a+y)) :=
      raisedProduct_ge hx (by linarith) (by linarith)
    _ = max 1 (x*(a+y))/(a+x+y) := by ring_nf
    _ ≤ upper a x y := by
      exact div_le_div_of_nonneg_right (max_le_max_left _ (le_max_left _ _)) hd.le

lemma highEnvelope_le_upper {a x y : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (a+x)/(1+(a+x)^2) ≤ upper a x y := by
  have hd : 0 < a+x+y := by linarith
  calc
    (a+x)/(1+(a+x)^2) ≤ max 1 ((a+x)*y)/((a+x)+y) :=
      raisedProduct_ge (by linarith) hy hd
    _ = max 1 (y*(a+x))/(a+x+y) := by rw [mul_comm (a+x)]
    _ ≤ upper a x y := by
      exact div_le_div_of_nonneg_right (max_le_max_left _ (le_max_right _ _)) hd.le

lemma threshold_eq_high (a : ℝ) :
    threshold a = (a+metallic a)/(1+(a+metallic a)^2) := by
  rw [threshold_eq_metallic]
  have hb := metallic_pos a
  have he := metallic_equation a
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  nlinarith

lemma threshold_lt_upper_of_ne {a x y : ℝ} (ha : 1 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hne : x ≠ metallic a) :
    threshold a < upper a x y := by
  have hb := metallic_pos a
  have hb1 := metallic_lt_one ha
  have hha : 0 < a := by linarith
  have hd : 0 < 1+(metallic a)^2 := by positivity
  rcases lt_or_gt_of_ne hne with hxb | hbx
  · apply lt_of_lt_of_le _ (highEnvelope_le_upper hha hx hy)
    rw [threshold_eq_high]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    have hh : 0 < ((a+metallic a)-(a+x))*((a+x)*(a+metallic a)-1) := by
      apply mul_pos (by linarith)
      have hax : 1 ≤ a+x := by linarith
      have hab : 1 < a+metallic a := by linarith
      nlinarith
    nlinarith
  · apply lt_of_lt_of_le _ (lowEnvelope_le_upper hha hx hy)
    rw [threshold_eq_metallic]
    apply (div_lt_div_iff₀ hd (by positivity)).2
    have hp : 0 < (x-metallic a)*(1-x*metallic a) := by
      apply mul_pos (by linarith)
      nlinarith
    nlinarith

lemma upper_metallic (a : ℝ) : upper a (metallic a) (metallic a) = threshold a := by
  unfold upper threshold
  rw [metallic_equation, max_self, max_self]
  congr 1
  rw [← metallic_add_eq_sqrt]
  ring

theorem threshold_le_upper {a x y : ℝ} (ha : 1 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    threshold a ≤ upper a x y := by
  by_cases hxb : x = metallic a
  · by_cases hyb : y = metallic a
    · simp only [hxb, hyb, upper_metallic, le_refl]
    · rw [upper_comm]
      exact (threshold_lt_upper_of_ne ha hy hy1 hx hyb).le
  · exact (threshold_lt_upper_of_ne ha hx hx1 hy hxb).le

theorem upper_eq_threshold_iff {a x y : ℝ} (ha : 1 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    upper a x y = threshold a ↔ x = metallic a ∧ y = metallic a := by
  constructor
  · intro he
    constructor
    · by_contra hn
      have := threshold_lt_upper_of_ne ha hx hx1 hy hn
      linarith
    · by_contra hn
      have hh := threshold_lt_upper_of_ne ha hy hy1 hx hn
      rw [upper_comm] at hh
      linarith
  · rintro ⟨rfl, rfl⟩
    exact upper_metallic a

theorem lower_lt_threshold_of_ne {a x y : ℝ} (ha : 1 ≤ a)
    (hx : 0 ≤ x) (_hx1 : x ≤ 1) (hy : 0 ≤ y) (hne : x ≠ metallic a) :
    lower a x y < threshold a := by
  have hb := metallic_pos a
  have hb1 := metallic_lt_one ha
  have hha : 0 < a := by linarith
  rcases lt_or_gt_of_ne hne with hxb | hbx
  · apply lt_of_le_of_lt (lower_le_lowEnvelope hha hx hy)
    rw [threshold_eq_metallic]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    have hh : 0 < (metallic a-x)*(1-x*metallic a) := by
      apply mul_pos (by linarith)
      nlinarith
    nlinarith
  · apply lt_of_le_of_lt (lower_le_highEnvelope hha hx hy)
    rw [threshold_eq_high]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    have hh : 0 < ((a+x)-(a+metallic a))*((a+x)*(a+metallic a)-1) := by
      apply mul_pos (by linarith)
      have hax : 1 ≤ a+x := by linarith
      have hab : 1 < a+metallic a := by linarith
      nlinarith
    nlinarith

theorem lower_le_threshold {a x y : ℝ} (ha : 1 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    lower a x y ≤ threshold a := by
  by_cases hxb : x = metallic a
  · by_cases hyb : y = metallic a
    · simp only [hxb, hyb, lower_metallic (by linarith : 0 < a), le_refl]
    · rw [lower_comm]
      exact (lower_lt_threshold_of_ne ha hy hy1 hx hyb).le
  · exact (lower_lt_threshold_of_ne ha hx hx1 hy hxb).le

theorem lower_eq_threshold_iff {a x y : ℝ} (ha : 1 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    lower a x y = threshold a ↔ x = metallic a ∧ y = metallic a := by
  constructor
  · intro he
    constructor
    · by_contra hn
      have := lower_lt_threshold_of_ne ha hx hx1 hy hn
      linarith
    · by_contra hn
      have hh := lower_lt_threshold_of_ne ha hy hy1 hx hn
      rw [lower_comm] at hh
      linarith
  · rintro ⟨rfl, rfl⟩
    exact lower_metallic (by linarith)

end ContinuedFractionBounds
