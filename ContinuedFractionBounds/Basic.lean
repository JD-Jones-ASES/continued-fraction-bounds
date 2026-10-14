module

public import Mathlib

@[expose] public section

/-!
# Three-coefficient envelopes

This module defines the lower and upper envelopes of the three rational
approximation-coefficient expressions and their metallic reference point.
-/

namespace ContinuedFractionBounds

noncomputable def lower (a x y : ℝ) : ℝ :=
  min 1 (min (x * (a + y)) (y * (a + x))) / (a + x + y)

noncomputable def upper (a x y : ℝ) : ℝ :=
  max 1 (max (x * (a + y)) (y * (a + x))) / (a + x + y)

noncomputable def metallic (a : ℝ) : ℝ := (Real.sqrt (a ^ 2 + 4) - a) / 2

noncomputable def threshold (a : ℝ) : ℝ := 1 / Real.sqrt (a ^ 2 + 4)

noncomputable def stabilityConstant (a : ℝ) : ℝ :=
  threshold a * (a + 1 - metallic a) / (1 + (a + 1) ^ 2)

lemma denominator_pos {a x y : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 < a + x + y := by linarith

lemma metallic_equation (a : ℝ) : metallic a * (a + metallic a) = 1 := by
  have hs : (Real.sqrt (a ^ 2 + 4)) ^ 2 = a ^ 2 + 4 := Real.sq_sqrt (by positivity)
  unfold metallic
  nlinarith

lemma metallic_pos (a : ℝ) : 0 < metallic a := by
  have hs := Real.sqrt_nonneg (a ^ 2 + 4)
  have he := Real.sq_sqrt (show 0 ≤ a ^ 2 + 4 by positivity)
  unfold metallic
  nlinarith

lemma metallic_lt_one {a : ℝ} (ha : 1 ≤ a) : metallic a < 1 := by
  have hp := metallic_pos a
  have he := metallic_equation a
  nlinarith

lemma metallic_lt_half {a : ℝ} (ha : 2 ≤ a) : metallic a < 1 / 2 := by
  have hp := metallic_pos a
  have he := metallic_equation a
  nlinarith

lemma metallic_add_eq_sqrt (a : ℝ) : a + 2 * metallic a = Real.sqrt (a ^ 2 + 4) := by
  unfold metallic
  ring

lemma threshold_pos (a : ℝ) : 0 < threshold a := by
  unfold threshold
  positivity

lemma threshold_eq_metallic (a : ℝ) :
    threshold a = metallic a / (1 + metallic a ^ 2) := by
  have hb := metallic_pos a
  have he := metallic_equation a
  have hs : 0 < Real.sqrt (a ^ 2 + 4) := by positivity
  have hd : 0 < 1 + metallic a ^ 2 := by positivity
  apply (div_eq_div_iff (ne_of_gt hs) (ne_of_gt hd)).2
  rw [← metallic_add_eq_sqrt]
  nlinarith

lemma lower_comm (a x y : ℝ) : lower a x y = lower a y x := by
  unfold lower
  rw [min_comm (x * (a + y)) (y * (a + x))]
  congr 1
  ring

lemma upper_comm (a x y : ℝ) : upper a x y = upper a y x := by
  unfold upper
  rw [max_comm (x * (a + y)) (y * (a + x))]
  congr 1
  ring

lemma lower_le_one_div {a x y : ℝ} (hd : 0 < a + x + y) :
    lower a x y ≤ 1 / (a + x + y) := by
  exact div_le_div_of_nonneg_right (min_le_left _ _) hd.le

lemma lower_le_left_div {a x y : ℝ} (hd : 0 < a + x + y) :
    lower a x y ≤ x * (a + y) / (a + x + y) := by
  exact div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hd.le

lemma lower_le_right_div {a x y : ℝ} (hd : 0 < a + x + y) :
    lower a x y ≤ y * (a + x) / (a + x + y) := by
  exact div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hd.le

lemma lower_nonneg {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ lower a x y := by
  unfold lower
  positivity

lemma lower_metallic {a : ℝ} (_ha : 0 < a) :
    lower a (metallic a) (metallic a) = threshold a := by
  have he := metallic_equation a
  unfold lower
  rw [he, min_self, min_self]
  unfold threshold
  congr 1
  rw [← metallic_add_eq_sqrt]
  ring

lemma stabilityConstant_pos {a : ℝ} (ha : 2 ≤ a) : 0 < stabilityConstant a := by
  have hb := metallic_lt_one (by linarith : 1 ≤ a)
  have hc := threshold_pos a
  unfold stabilityConstant
  apply div_pos
  · exact mul_pos hc (by linarith)
  · positivity

end ContinuedFractionBounds
