module

public import ContinuedFractionBounds.ClassicalBounds

/-!
# Sharp inverse stability for the maximum coefficient

The upper envelope has a sharp linear bound in the maximum distance from
its metallic minimizer. Equality occurs only at that minimizer; optimality
is approached along the central/side switching curve.
-/

@[expose] public section
namespace ContinuedFractionBounds

noncomputable def upperStabilityConstant (a : ℝ) : ℝ :=
  a * metallic a / (a ^ 2 + 4)

lemma upperStabilityConstant_pos {a : ℝ} (ha : 2 ≤ a) :
    0 < upperStabilityConstant a := by
  have hb := metallic_pos a
  unfold upperStabilityConstant
  positivity

lemma upperStabilityConstant_eq_high (a : ℝ) :
    upperStabilityConstant a =
      threshold a * a / (1 + (a + metallic a) ^ 2) := by
  have he := metallic_equation a
  rw [upperStabilityConstant, threshold_eq_metallic]
  field_simp
  linear_combination a * metallic a * (a*metallic a + metallic a^2 + 3) * he

lemma upperStabilityConstant_eq_metallic (a : ℝ) :
    upperStabilityConstant a =
      metallic a^2 * (1-metallic a^2)/(1+metallic a^2)^2 := by
  have he := metallic_equation a
  unfold upperStabilityConstant
  field_simp
  linear_combination (a*(metallic a^3-metallic a)+4*metallic a^2) * he

lemma upperStabilityConstant_two :
    upperStabilityConstant 2 = (Real.sqrt 2-1)/4 := by
  rw [upperStabilityConstant, metallic_two]
  ring

/-- The high-envelope gap, valid on either side of the metallic coordinate. -/
lemma upper_high_gap_identity (a t : ℝ) :
    (a+t)/(1+(a+t)^2) - threshold a =
      threshold a * (metallic a-t) * (a+t-metallic a) / (1+(a+t)^2) := by
  rw [threshold_eq_metallic]
  have he := metallic_equation a
  field_simp
  nlinarith [congrArg (fun z : ℝ => z * (a+t-metallic a)) he]

/-- The exact positive quadratic remainder below the metallic coordinate. -/
lemma upper_high_remainder_identity (a t : ℝ) :
    (a+t)/(1+(a+t)^2) - threshold a -
        upperStabilityConstant a * (metallic a-t) =
      threshold a * (metallic a-t)^2 * (a*(a+t)-2) /
        ((1+(a+t)^2)*(1+(a+metallic a)^2)) := by
  rw [upper_high_gap_identity, upperStabilityConstant_eq_high]
  have he := metallic_equation a
  field_simp
  linear_combination -threshold a * (metallic a-t)^2 * he

/-- The low-envelope gap above the metallic coordinate. -/
lemma upper_low_gap_identity (a t : ℝ) :
    t/(1+t^2) - threshold a =
      (t-metallic a)*(1-metallic a*t) / ((1+t^2)*(1+metallic a^2)) := by
  rw [threshold_eq_metallic]
  field_simp
  ring

lemma upperStabilityConstant_lt_eighth {a : ℝ} (ha : 2 ≤ a) :
    upperStabilityConstant a < 1/8 := by
  have hb := metallic_pos a
  have he := metallic_equation a
  unfold upperStabilityConstant
  apply (div_lt_iff₀ (show 0 < a^2+4 by positivity)).2
  nlinarith [sq_nonneg (a-2), sq_pos_of_pos hb]

lemma upper_low_gap_bound {a t : ℝ} (ha : 2 ≤ a)
    (ht : metallic a ≤ t) (ht1 : t ≤ 1) :
    (1/8 : ℝ) * (t-metallic a) ≤ t/(1+t^2)-threshold a := by
  have hb := metallic_pos a
  have hbhalf := metallic_lt_half ha
  have ht0 : 0 ≤ t := by linarith
  have ht2 : t^2 ≤ 1 := by nlinarith
  have hb2 : metallic a^2 < 1/4 := by nlinarith
  have hbt : metallic a*t ≤ metallic a := mul_le_of_le_one_right hb.le ht1
  have hs : (1/8 : ℝ) ≤ (1-metallic a*t)/((1+t^2)*(1+metallic a^2)) := by
    apply (le_div_iff₀ (show 0 < (1+t^2)*(1+metallic a^2) by positivity)).2
    have hh := mul_nonneg (show 0 ≤ 1-t^2 by linarith)
      (show 0 ≤ 1+metallic a^2 by positivity)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ t-metallic a by linarith)
  rw [upper_low_gap_identity]
  convert hm using 1 <;> ring

lemma coordinate_upper_stability_strict {a x y : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hne : x ≠ metallic a) :
    upperStabilityConstant a * |x-metallic a| < upper a x y-threshold a := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [abs_of_neg (by linarith : x-metallic a < 0)]
    have hf := highEnvelope_le_upper (by linarith : 0 < a) hx hy
    have hi := upper_high_remainder_identity a x
    have hc := threshold_pos a
    have hp : 0 < a*(a+x)-2 := by nlinarith
    have hdiff : 0 < metallic a-x := by linarith
    have hr : 0 < threshold a * (metallic a-x)^2 * (a*(a+x)-2) /
        ((1+(a+x)^2)*(1+(a+metallic a)^2)) := by positivity
    linarith
  · rw [abs_of_pos (by linarith : 0 < x-metallic a)]
    have hf := lowEnvelope_le_upper (by linarith : 0 < a) hx hy
    have hs := upper_low_gap_bound ha h.le hx1
    have hk := upperStabilityConstant_lt_eighth ha
    have hm := mul_lt_mul_of_pos_right hk (show 0 < x-metallic a by linarith)
    linarith

lemma coordinate_upper_stability {a x y : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    upperStabilityConstant a * |x-metallic a| ≤ upper a x y-threshold a := by
  by_cases h : x = metallic a
  · simp only [h, sub_self, abs_zero, mul_zero]
    exact sub_nonneg.mpr (threshold_le_upper (by linarith) (metallic_pos a).le
      (metallic_lt_one (by linarith)).le hy hy1)
  · exact (coordinate_upper_stability_strict ha hx hx1 hy h).le

/-- Sharp global inverse stability for the maximum on the closed unit square. -/
theorem global_upper_stability {a x y : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    upperStabilityConstant a * max |x-metallic a| |y-metallic a| ≤
      upper a x y-threshold a := by
  rw [mul_max_of_nonneg _ _ (upperStabilityConstant_pos ha).le]
  exact max_le (coordinate_upper_stability ha hx hx1 hy hy1)
    (by simpa only [upper_comm] using coordinate_upper_stability ha hy hy1 hx hx1)

theorem global_upper_stability_strict {a x y : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hne : x ≠ metallic a ∨ y ≠ metallic a) :
    upperStabilityConstant a * max |x-metallic a| |y-metallic a| <
      upper a x y-threshold a := by
  have hp : 0 < max |x-metallic a| |y-metallic a| := by
    rcases hne with h | h
    · exact lt_of_lt_of_le (abs_pos.mpr (sub_ne_zero.mpr h)) (le_max_left _ _)
    · exact lt_of_lt_of_le (abs_pos.mpr (sub_ne_zero.mpr h)) (le_max_right _ _)
  rcases le_total |y-metallic a| |x-metallic a| with h | h
  · rw [max_eq_left h] at hp ⊢
    exact coordinate_upper_stability_strict ha hx hx1 hy
      (fun hh => by simp [hh] at hp)
  · rw [max_eq_right h] at hp ⊢
    simpa only [upper_comm] using coordinate_upper_stability_strict ha hy hy1 hx
      (fun hh => by simp [hh] at hp)

/-- The sharp coefficient has no off-center equality point. -/
theorem global_upper_stability_eq_iff {a x y : ℝ} (ha : 2 ≤ a)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    upper a x y-threshold a =
        upperStabilityConstant a * max |x-metallic a| |y-metallic a| ↔
      x = metallic a ∧ y = metallic a := by
  constructor
  · intro he
    by_contra hn
    have hh := global_upper_stability_strict ha hx hx1 hy hy1 (by tauto)
    linarith
  · rintro ⟨rfl, rfl⟩
    simp [upper_metallic]

/-- Exact upper-envelope value on the switching curve below its fixed point. -/
lemma upper_switching_value {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t)
    (htb : t ≤ metallic a) :
    upper a t (1/(a+t)) = (a+t)/(1+(a+t)^2) := by
  have ha0 : 0 < a := by linarith
  have hd : 0 < a+t := by linarith
  have he := metallic_equation a
  have hb := metallic_pos a
  have hp : t*(a+t) ≤ 1 := by
    have hh := mul_nonneg (show 0 ≤ metallic a-t by linarith)
      (show 0 ≤ a+metallic a+t by positivity)
    nlinarith
  have hty : t ≤ 1/(a+t) := (le_div_iff₀ hd).2 hp
  have hy : 1/(a+t)*(a+t) = 1 := by field_simp
  have hleft : t*(a+1/(a+t)) ≤ 1 := by nlinarith
  unfold upper
  rw [hy, max_eq_right hleft, max_self]
  field_simp
  ring

/-- On the sharpness curve the lower coordinate controls the maximum distance. -/
lemma upper_switching_distance {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t)
    (htb : t ≤ metallic a) :
    max |t-metallic a| |1/(a+t)-metallic a| = metallic a-t := by
  have hd : 0 < a+t := by linarith
  have hb := metallic_pos a
  have hbhalf := metallic_lt_half ha
  have he := metallic_equation a
  have hyb : metallic a ≤ 1/(a+t) := by
    apply (le_div_iff₀ hd).2
    nlinarith
  have hyu : 1/(a+t) ≤ 2*metallic a-t := by
    apply (div_le_iff₀ hd).2
    have hh := mul_nonneg (show 0 ≤ metallic a-t by linarith)
      (show 0 ≤ a+t-metallic a by linarith)
    nlinarith
  rw [abs_of_nonpos (by linarith : t-metallic a ≤ 0),
    abs_of_nonneg (by linarith : 0 ≤ 1/(a+t)-metallic a), max_eq_left (by linarith)]
  ring

/-- The off-center switching-curve ratio tending to the optimal coefficient. -/
lemma upper_switching_ratio {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t)
    (htb : t < metallic a) :
    (upper a t (1/(a+t))-threshold a) /
        max |t-metallic a| |1/(a+t)-metallic a| =
      threshold a * (a+t-metallic a)/(1+(a+t)^2) := by
  rw [upper_switching_value ha ht htb.le, upper_switching_distance ha ht htb.le,
    upper_high_gap_identity]
  have hn : metallic a-t ≠ 0 := by linarith
  field_simp

/-- No larger coefficient works uniformly throughout the closed unit square. -/
theorem upperStabilityConstant_optimal {a K : ℝ} (ha : 2 ≤ a)
    (hK : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      K * max |x-metallic a| |y-metallic a| ≤ upper a x y-threshold a) :
    K ≤ upperStabilityConstant a := by
  have hb := metallic_pos a
  have hb1 := metallic_lt_one (by linarith : 1 ≤ a)
  have hbound (t : ℝ) (ht : 0 ≤ t) (htb : t < metallic a) :
      K ≤ threshold a * (a+t-metallic a)/(1+(a+t)^2) := by
    have hd : 0 < a+t := by linarith
    have hy0 : 0 ≤ 1/(a+t) := by positivity
    have hy1 : 1/(a+t) ≤ 1 := (div_le_one hd).2 (by linarith)
    have hh := hK t ⟨ht, by linarith⟩ (1/(a+t)) ⟨hy0, hy1⟩
    rw [upper_switching_distance ha ht htb.le, upper_switching_value ha ht htb.le,
      upper_high_gap_identity] at hh
    have heq : threshold a * (metallic a-t) * (a+t-metallic a)/(1+(a+t)^2) =
        (threshold a * (a+t-metallic a)/(1+(a+t)^2)) * (metallic a-t) := by ring
    rw [heq] at hh
    exact (mul_le_mul_iff_left₀ (show 0 < metallic a-t by linarith)).1 hh
  let t : ℕ → ℝ := fun n => metallic a-metallic a/(n+1)
  have ht (n : ℕ) : 0 ≤ t n ∧ t n < metallic a := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hp : 0 < metallic a/(n+1) := div_pos hb (by positivity)
    have hu : metallic a/(n+1) ≤ metallic a := by
      apply (div_le_iff₀ (show (0 : ℝ) < n+1 by positivity)).2
      nlinarith
    dsimp [t]
    constructor <;> linarith
  have htlim : Filter.Tendsto t Filter.atTop (nhds (metallic a)) := by
    simpa only [mul_one_div, mul_zero, sub_zero] using
      (tendsto_const_nhds (x := metallic a)).sub
        ((tendsto_const_nhds (x := metallic a)).mul
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hnum := ((tendsto_const_nhds (x := a)).add htlim).sub
    (tendsto_const_nhds (x := metallic a))
  have hden := (tendsto_const_nhds (x := (1 : ℝ))).add
    (((tendsto_const_nhds (x := a)).add htlim).pow 2)
  have hlim : Filter.Tendsto
      (fun n => threshold a*(a+t n-metallic a)/(1+(a+t n)^2))
      Filter.atTop (nhds (upperStabilityConstant a)) := by
    rw [upperStabilityConstant_eq_high]
    convert ((tendsto_const_nhds (x := threshold a)).mul hnum).div hden
      (by positivity) using 1
    congr 1
    ring
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun n => hbound (t n) (ht n).1 (ht n).2)

end ContinuedFractionBounds
