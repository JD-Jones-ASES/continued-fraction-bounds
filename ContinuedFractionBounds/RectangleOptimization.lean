module

public import ContinuedFractionBounds.Rectangles
public import ContinuedFractionBounds.LowerSwitch

@[expose] public section

/-!
# Exact clipping on arbitrary closed rectangles

The clipped switching-curve point gives the unique extremum in each
crossing case. Constant zero rectangles are retained separately.
-/

namespace ContinuedFractionBounds

noncomputable def clip (z L U : ℝ) := min U (max L z)

lemma clip_mem {z L U : ℝ} (hLU : L ≤ U) : clip z L U ∈ Set.Icc L U := by
  exact ⟨le_min hLU (le_max_left _ _), min_le_left _ _⟩

lemma lowEnvelope_strictMono {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q) (hq : q ≤ 1) :
    p / (1 + p ^ 2) < q / (1 + q ^ 2) := by
  have hpq1 : p * q < 1 := by
    have hqpos : 0 < q := by linarith
    have h := mul_lt_mul_of_pos_right hpq hqpos
    nlinarith
  apply (div_lt_div_iff₀ (by positivity : 0 < 1 + p ^ 2) (by positivity : 0 < 1 + q ^ 2)).2
  have hh := mul_pos (sub_pos.mpr hpq) (sub_pos.mpr hpq1)
  nlinarith

lemma lowEnvelope_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    p / (1 + p ^ 2) ≤ q / (1 + q ^ 2) := by
  rcases hpq.eq_or_lt with h | h
  · rw [h]
  · exact (lowEnvelope_strictMono hp h hq).le

lemma highEnvelope_strictAntitone_one_le {p q : ℝ} (hp : 1 ≤ p) (hpq : p < q) :
    q / (1 + q ^ 2) < p / (1 + p ^ 2) := by
  have hpq1 : 0 < p * q - 1 := by nlinarith
  apply (div_lt_div_iff₀ (by positivity : 0 < 1 + q ^ 2) (by positivity : 0 < 1 + p ^ 2)).2
  have h := mul_pos (sub_pos.mpr hpq) hpq1
  nlinarith

lemma highEnvelope_antitone_one_le {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    q / (1 + q ^ 2) ≤ p / (1 + p ^ 2) := by
  rcases hpq.eq_or_lt with h | h
  · rw [h]
  · exact (highEnvelope_strictAntitone_one_le hp h).le

lemma lowEnvelope_equality_product {a x y : ℝ} (ha : 0 < a)
    (hx : 0 < x) (hy : 0 ≤ y)
    (he : lower a x y = x / (1 + x ^ 2)) : x * (a + y) = 1 := by
  have hd : 0 < a + x + y := by linarith
  have hf : 0 < 1 + x ^ 2 := by positivity
  have h₀ := lower_le_one_div hd
  have h₁ := lower_le_left_div hd
  rw [he] at h₀ h₁
  have h₀' := (div_le_div_iff₀ hf hd).1 h₀
  have h₁' := (div_le_div_iff₀ hf hd).1 h₁
  have hle : x * (a + y) ≤ 1 := by nlinarith [h₀']
  have hge : 1 ≤ x * (a + y) := by
    by_contra h
    have hn : 0 < 1 - x * (a + y) := by linarith
    have hs : 0 < x ^ 2 := sq_pos_of_pos hx
    have hh := mul_pos hs hn
    nlinarith [h₁']
  exact le_antisymm hle hge

lemma upper_lowEnvelope_equality_product {a x y : ℝ} (ha : 0 < a)
    (hx : 0 < x) (hy : 0 ≤ y)
    (he : upper a x y = x / (1 + x ^ 2)) : x * (a + y) = 1 := by
  have hd : 0 < a + x + y := by linarith
  have hf : 0 < 1 + x ^ 2 := by positivity
  have h₀ := one_div_le_upper ha hx.le hy
  have h₁ : x * (a + y) / (a + x + y) ≤ upper a x y := by
    exact div_le_div_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hd.le
  rw [he] at h₀ h₁
  have h₀' := (div_le_div_iff₀ hd hf).1 h₀
  have h₁' := (div_le_div_iff₀ hd hf).1 h₁
  have hge : 1 ≤ x * (a + y) := by nlinarith [h₀']
  have hle : x * (a + y) ≤ 1 := by
    by_contra h
    have hn : 0 < x * (a + y) - 1 := by linarith
    have hs : 0 < x ^ 2 := sq_pos_of_pos hx
    have hh := mul_pos hs hn
    nlinarith [h₁']
  exact le_antisymm hle hge

lemma lowerSwitch_value_low {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (htb : t ≤ metallic a) :
    lower a t (lowerSwitch a t) = t / (1 + t ^ 2) := by
  have hcurve := lowerSwitch_curve ha ht
  unfold lower
  rw [hcurve, min_self, lowerSwitch_low ha ht htb]
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hf : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp
  convert mul_inv_cancel₀ hf using 1
  ring

lemma lowerSwitch_value_high {a t : ℝ} (ha : 0 < a) (htb : metallic a ≤ t) :
    lower a t (lowerSwitch a t) = (a + t) / (1 + (a + t) ^ 2) := by
  have ht := (metallic_pos a).trans_le htb
  have hcurve := lowerSwitch_curve ha ht
  unfold lower
  rw [hcurve, min_self, lowerSwitch_high ha htb]
  have hd : a + t ≠ 0 := by linarith
  field_simp
  ring

lemma lower_low_boundary {a t x y : ℝ} (ha : 1 ≤ a) (ht : 0 < t)
    (htb : t ≤ metallic a) (hx : 0 ≤ x) (hxt : x ≤ t) (hy : 0 ≤ y) :
    lower a x y ≤ lower a t (lowerSwitch a t) ∧
      (lower a x y = lower a t (lowerSwitch a t) ↔ x = t ∧ y = lowerSwitch a t) := by
  have ha0 : 0 < a := by linarith
  have ht1 : t < 1 := htb.trans_lt (metallic_lt_one ha)
  have hc := lowerSwitch_value_low ha0 ht htb
  have hf := lower_le_lowEnvelope ha0 hx hy
  have hs := lowEnvelope_mono hx hxt ht1.le
  refine ⟨by linarith, ?_⟩
  constructor
  · intro he
    have hxt' : x = t := by
      by_contra h
      have hh := lowEnvelope_strictMono hx (lt_of_le_of_ne hxt h) ht1.le
      linarith
    subst x
    have hp := lowEnvelope_equality_product ha0 ht hy (he.trans hc)
    refine ⟨rfl, ?_⟩
    rw [lowerSwitch_low ha0 ht htb]
    have hh : a + y = 1 / t := (eq_div_iff (ne_of_gt ht)).2 (by nlinarith)
    linarith
  · rintro ⟨rfl, rfl⟩
    rfl

lemma lower_high_boundary {a t x y : ℝ} (ha : 1 ≤ a)
    (htb : metallic a ≤ t) (htx : t ≤ x) (hy : 0 ≤ y) :
    lower a x y ≤ lower a t (lowerSwitch a t) ∧
      (lower a x y = lower a t (lowerSwitch a t) ↔ x = t ∧ y = lowerSwitch a t) := by
  have ha0 : 0 < a := by linarith
  have ht := (metallic_pos a).trans_le htb
  have hx : 0 ≤ x := by linarith
  have hc := lowerSwitch_value_high ha0 htb
  have hf := lower_le_highEnvelope ha0 hx hy
  have hmz : 1 < a + t := by linarith
  have hs := highEnvelope_antitone hmz (show a + t ≤ a + x by linarith)
  refine ⟨by linarith, ?_⟩
  constructor
  · intro he
    have hxt' : x = t := by
      by_contra h
      have hh := highEnvelope_strict_antitone hmz (show a + t < a + x by
        have := lt_of_le_of_ne htx (Ne.symm h); linarith)
      linarith
    subst x
    have hp := highEnvelope_equality_product ha0 ht.le hy (he.trans hc)
    refine ⟨rfl, ?_⟩
    rw [lowerSwitch_high ha0 htb]
    exact (eq_div_iff (show a + t ≠ 0 by linarith)).2 hp
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The candidate is the metallic point or has an active rectangle edge facing it. -/
def MetallicSupport (β lx ux ly uy x y : ℝ) : Prop :=
  (x = β ∧ y = β) ∨ (x = lx ∧ β ≤ x) ∨ (x = ux ∧ x ≤ β) ∨
    (y = ly ∧ β ≤ y) ∨ (y = uy ∧ y ≤ β)

lemma lower_supported_maximum {a lx ux ly uy t u x y : ℝ} (ha : 1 ≤ a)
    (ht : 0 < t) (hu : u = lowerSwitch a t)
    (hs : MetallicSupport (metallic a) lx ux ly uy t u)
    (hlx : 0 ≤ lx) (hux : ux ≤ 1) (hly : 0 ≤ ly) (huy : uy ≤ 1)
    (hx : x ∈ Set.Icc lx ux) (hy : y ∈ Set.Icc ly uy) :
    lower a x y ≤ lower a t u ∧ (lower a x y = lower a t u ↔ x = t ∧ y = u) := by
  have ha0 : 0 < a := by linarith
  have hx0 := hlx.trans hx.1
  have hy0 := hly.trans hy.1
  have hu0 : 0 < u := hu ▸ lowerSwitch_pos ha0 ht
  have htu : t = lowerSwitch a u := by rw [hu, lowerSwitch_involutive ha0 ht]
  rcases hs with h | h | h | h | h
  · obtain ⟨rfl, rfl⟩ := h
    rw [lower_metallic ha0]
    exact ⟨lower_le_threshold ha hx0 (hx.2.trans hux) hy0 (hy.2.trans huy),
      lower_eq_threshold_iff ha hx0 (hx.2.trans hux) hy0 (hy.2.trans huy)⟩
  · rw [hu]
    exact lower_high_boundary ha h.2 (h.1 ▸ hx.1) hy0
  · rw [hu]
    exact lower_low_boundary ha ht h.2 hx0 (h.1 ▸ hx.2) hy0
  · have hh := lower_high_boundary ha h.2 (h.1 ▸ hy.1) hx0
    rw [← htu] at hh
    simpa only [lower_comm a y x, lower_comm a u t, and_comm (b := x = t)] using hh
  · have hh := lower_low_boundary ha hu0 h.2 hy0 (h.1 ▸ hy.2) hx0
    rw [← htu] at hh
    simpa only [lower_comm a y x, lower_comm a u t, and_comm (b := x = t)] using hh


noncomputable def lowerClipLeft (a lx uy : ℝ) := max lx (lowerSwitch a uy)

/-- At a zero lower edge, no evaluation of the infinite switching endpoint is used. -/
noncomputable def lowerClipRight (a ux ly : ℝ) :=
  if ly = 0 then ux else min ux (lowerSwitch a ly)

noncomputable def lowerClipX (a lx ux ly uy : ℝ) :=
  clip (metallic a) (lowerClipLeft a lx uy) (lowerClipRight a ux ly)

noncomputable def lowerClipY (a lx ux ly uy : ℝ) :=
  lowerSwitch a (lowerClipX a lx ux ly uy)

/-- Exact clipped maximizer in the crossing case, including degenerate rectangles. -/
theorem lower_clipped_maximum {a lx ux ly uy : ℝ} (ha : 1 ≤ a)
    (hlx : 0 ≤ lx) (hlxu : lx ≤ ux) (hux : ux ≤ 1)
    (hly : 0 ≤ ly) (hlyu : ly ≤ uy) (huy : uy ≤ 1)
    (hlo : min (lx * (a + ly)) (ly * (a + lx)) < 1)
    (hhi : 1 < min (ux * (a + uy)) (uy * (a + ux))) :
    let t := lowerClipX a lx ux ly uy
    let u := lowerClipY a lx ux ly uy
    t ∈ Set.Icc lx ux ∧ u ∈ Set.Icc ly uy ∧
      lower a t u = 1 / (a + t + u) ∧
      ∀ x ∈ Set.Icc lx ux, ∀ y ∈ Set.Icc ly uy,
        lower a x y ≤ lower a t u ∧ (lower a x y = lower a t u ↔ x = t ∧ y = u) := by
  have ha0 : 0 < a := by linarith
  have hux0 : 0 ≤ ux := hlx.trans hlxu
  have huy0 : 0 ≤ uy := hly.trans hlyu
  have huypos : 0 < uy := by
    have hh := (lt_min_iff.1 hhi).2
    nlinarith
  have hHuy : lowerSwitch a uy ≤ ux := by
    apply (lowerSwitch_le_iff ha0 huypos).2
    simpa only [min_comm] using hhi.le
  let L := lowerClipLeft a lx uy
  let U := lowerClipRight a ux ly
  let t := lowerClipX a lx ux ly uy
  let u := lowerClipY a lx ux ly uy
  have hLpos : 0 < L := (lowerSwitch_pos ha0 huypos).trans_le (le_max_right _ _)
  have hLU : L ≤ U := by
    by_cases hz : ly = 0
    · simp only [U, lowerClipRight, hz, ↓reduceIte]
      exact max_le hlxu hHuy
    · have hlypos : 0 < ly := lt_of_le_of_ne hly (Ne.symm hz)
      have hlxH : lx ≤ lowerSwitch a ly := by
        apply (le_lowerSwitch_iff ha0 hlypos).2
        simpa only [min_comm] using hlo.le
      have hHH := lowerSwitch_antitone ha0 hlypos hlyu
      simp only [U, lowerClipRight, hz, ↓reduceIte]
      exact le_min (max_le hlxu hHuy) (max_le hlxH hHH)
  have htLU : t ∈ Set.Icc L U := clip_mem hLU
  have htpos : 0 < t := hLpos.trans_le htLU.1
  have htmem : t ∈ Set.Icc lx ux := by
    constructor
    · exact (le_max_left _ _).trans htLU.1
    · apply htLU.2.trans
      by_cases hz : ly = 0
      · simp [U, lowerClipRight, hz]
      · simp only [U, lowerClipRight, hz, ↓reduceIte]
        exact min_le_left _ _
  have humem : u ∈ Set.Icc ly uy := by
    constructor
    · by_cases hz : ly = 0
      · rw [hz]
        exact (lowerSwitch_pos ha0 htpos).le
      · have hlypos : 0 < ly := lt_of_le_of_ne hly (Ne.symm hz)
        have htH : t ≤ lowerSwitch a ly := by
          apply htLU.2.trans
          simp only [U, lowerClipRight, hz, ↓reduceIte]
          exact min_le_right _ _
        apply (le_lowerSwitch_iff ha0 htpos).2
        have hh := (le_lowerSwitch_iff ha0 hlypos).1 htH
        simpa only [min_comm] using hh
    · apply (lowerSwitch_le_iff ha0 htpos).2
      have hh := (lowerSwitch_le_iff ha0 huypos).1
        ((le_max_right _ _).trans htLU.1)
      simpa only [min_comm] using hh
  have hs : MetallicSupport (metallic a) lx ux ly uy t u := by
    by_cases hlow : metallic a < L
    · have htL : t = L := by
        dsimp [t, lowerClipX, clip]
        rw [max_eq_left hlow.le, min_eq_right hLU]
      have htβ : metallic a ≤ t := by linarith
      rcases le_total lx (lowerSwitch a uy) with hh | hh
      · have htH : t = lowerSwitch a uy := htL.trans (max_eq_right hh)
        have huuy : u = uy := by
          change lowerSwitch a t = uy
          rw [htH, lowerSwitch_involutive ha0 huypos]
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨huuy, lowerSwitch_le_metallic ha0 htβ⟩)))
      · exact Or.inr (Or.inl ⟨htL.trans (max_eq_left hh), htβ⟩)
    · have hLβ : L ≤ metallic a := le_of_not_gt hlow
      by_cases hhigh : U < metallic a
      · have htU : t = U := by
          dsimp [t, lowerClipX, clip]
          rw [max_eq_right hLβ, min_eq_left hhigh.le]
        have htβ : t ≤ metallic a := by linarith
        by_cases hz : ly = 0
        · have htux : t = ux := by simpa [U, lowerClipRight, hz] using htU
          exact Or.inr (Or.inr (Or.inl ⟨htux, htβ⟩))
        · have hlypos : 0 < ly := lt_of_le_of_ne hly (Ne.symm hz)
          rcases le_total ux (lowerSwitch a ly) with hh | hh
          · have htux : t = ux := by
              simpa [U, lowerClipRight, hz, min_eq_left hh] using htU
            exact Or.inr (Or.inr (Or.inl ⟨htux, htβ⟩))
          · have htH : t = lowerSwitch a ly := by
              simpa [U, lowerClipRight, hz, min_eq_right hh] using htU
            have huly : u = ly := by
              change lowerSwitch a t = ly
              rw [htH, lowerSwitch_involutive ha0 hlypos]
            exact Or.inr (Or.inr (Or.inr (Or.inl
              ⟨huly, metallic_le_lowerSwitch ha0 htpos htβ⟩)))
      · have hβU : metallic a ≤ U := le_of_not_gt hhigh
        have htβ : t = metallic a := by
          dsimp [t, lowerClipX, clip]
          rw [max_eq_right hLβ, min_eq_right hβU]
        have huβ : u = metallic a := by
          change lowerSwitch a t = metallic a
          rw [htβ, lowerSwitch_metallic ha0]
        exact Or.inl ⟨htβ, huβ⟩
  change t ∈ Set.Icc lx ux ∧ u ∈ Set.Icc ly uy ∧ _
  refine ⟨htmem, humem, ?_, ?_⟩
  · exact lower_eq_one_div (lowerSwitch_curve ha0 htpos).ge
  · intro x hx y hy
    exact lower_supported_maximum ha htpos rfl hs hlx hux hly huy hx hy

/-- On a rectangle whose upper corner is on an axis, the lower envelope is identically zero. -/
theorem lower_axis_rectangle {a lx ux ly uy : ℝ} (ha : 0 ≤ a)
    (hlx : 0 ≤ lx) (hly : 0 ≤ ly) (haxis : ux * uy = 0) :
    ∀ x ∈ Set.Icc lx ux, ∀ y ∈ Set.Icc ly uy, lower a x y = 0 := by
  intro x hx y hy
  have hx0 := hlx.trans hx.1
  have hy0 := hly.trans hy.1
  rcases mul_eq_zero.mp haxis with h | h
  · have hxx : x = 0 := by linarith [hx.2]
    simp [lower, hxx, mul_nonneg hy0 ha]
  · have hyy : y = 0 := by linarith [hy.2]
    simp [lower, hyy, mul_nonneg hx0 ha]


/-- The prescribed maximizing first coordinate for every closed rectangle. -/
noncomputable def lowerRectangleX (a lx ux ly uy : ℝ) :=
  if ux * uy = 0 then ux
  else if min (ux * (a + uy)) (uy * (a + ux)) ≤ 1 then ux
  else if 1 ≤ min (lx * (a + ly)) (ly * (a + lx)) then lx
  else lowerClipX a lx ux ly uy

/-- The prescribed maximizing second coordinate for every closed rectangle. -/
noncomputable def lowerRectangleY (a lx ux ly uy : ℝ) :=
  if ux * uy = 0 then uy
  else if min (ux * (a + uy)) (uy * (a + ux)) ≤ 1 then uy
  else if 1 ≤ min (lx * (a + ly)) (ly * (a + lx)) then ly
  else lowerClipY a lx ux ly uy

/-- Complete lower-envelope optimization on every closed rectangle in the unit square.
The only failure of uniqueness is the identically zero axis case. -/
theorem lower_rectangle_maximum {a lx ux ly uy : ℝ} (ha : 1 ≤ a)
    (hlx : 0 ≤ lx) (hlxu : lx ≤ ux) (hux : ux ≤ 1)
    (hly : 0 ≤ ly) (hlyu : ly ≤ uy) (huy : uy ≤ 1) :
    let t := lowerRectangleX a lx ux ly uy
    let u := lowerRectangleY a lx ux ly uy
    t ∈ Set.Icc lx ux ∧ u ∈ Set.Icc ly uy ∧
      ∀ x ∈ Set.Icc lx ux, ∀ y ∈ Set.Icc ly uy,
        lower a x y ≤ lower a t u ∧
        (lower a x y = lower a t u ↔ ux * uy = 0 ∨ (x = t ∧ y = u)) := by
  have ha0 : 0 < a := by linarith
  by_cases hz : ux * uy = 0
  · simp only [lowerRectangleX, lowerRectangleY, hz, ↓reduceIte, true_or, iff_true]
    refine ⟨⟨hlxu, le_rfl⟩, ⟨hlyu, le_rfl⟩, ?_⟩
    intro x hx y hy
    have hh := lower_axis_rectangle ha0.le hlx hly hz x hx y hy
    have hc := lower_axis_rectangle ha0.le hlx hly hz ux ⟨hlxu, le_rfl⟩ uy ⟨hlyu, le_rfl⟩
    exact ⟨by linarith, by linarith⟩
  · have huxpos : 0 < ux := lt_of_le_of_ne (hlx.trans hlxu)
      (Ne.symm (mul_ne_zero_iff.1 hz).1)
    have huypos : 0 < uy := lt_of_le_of_ne (hly.trans hlyu)
      (Ne.symm (mul_ne_zero_iff.1 hz).2)
    by_cases hQup : min (ux * (a + uy)) (uy * (a + ux)) ≤ 1
    · simp only [lowerRectangleX, lowerRectangleY, hz, hQup, ↓reduceIte, false_or]
      refine ⟨⟨hlxu, le_rfl⟩, ⟨hlyu, le_rfl⟩, ?_⟩
      intro x hx y hy
      exact lower_below_corner ha0 (hlx.trans hx.1) (hly.trans hy.1)
        huxpos huypos hx.2 hy.2 hQup
    · by_cases hQlo : 1 ≤ min (lx * (a + ly)) (ly * (a + lx))
      · simp only [lowerRectangleX, lowerRectangleY, hz, hQup, hQlo, ↓reduceIte, false_or]
        refine ⟨⟨le_rfl, hlxu⟩, ⟨le_rfl, hlyu⟩, ?_⟩
        intro x hx y hy
        exact lower_above_corner ha0 hlx hly hx.1 hy.1 hQlo
      · simp only [lowerRectangleX, lowerRectangleY, hz, hQup, hQlo, ↓reduceIte, false_or]
        have hh := lower_clipped_maximum ha hlx hlxu hux hly hlyu huy
          (lt_of_not_ge hQlo) (lt_of_not_ge hQup)
        exact ⟨hh.1, hh.2.1, hh.2.2.2⟩


/-- A rectangle retains the classical lower threshold exactly when it contains the metallic point. -/
theorem lower_rectangle_threshold_iff {a lx ux ly uy : ℝ} (ha : 1 ≤ a)
    (hlx : 0 ≤ lx) (hlxu : lx ≤ ux) (hux : ux ≤ 1)
    (hly : 0 ≤ ly) (hlyu : ly ≤ uy) (huy : uy ≤ 1) :
    lower a (lowerRectangleX a lx ux ly uy) (lowerRectangleY a lx ux ly uy) = threshold a ↔
      metallic a ∈ Set.Icc lx ux ∧ metallic a ∈ Set.Icc ly uy := by
  have hh := lower_rectangle_maximum ha hlx hlxu hux hly hlyu huy
  have htx0 := hlx.trans hh.1.1
  have htx1 := hh.1.2.trans hux
  have hty0 := hly.trans hh.2.1.1
  have hty1 := hh.2.1.2.trans huy
  constructor
  · intro he
    obtain ⟨hx, hy⟩ := (lower_eq_threshold_iff ha htx0 htx1 hty0 hty1).1 he
    exact ⟨hx ▸ hh.1, hy ▸ hh.2.1⟩
  · rintro ⟨hx, hy⟩
    have hmax := (hh.2.2 (metallic a) hx (metallic a) hy).1
    rw [lower_metallic (by linarith : 0 < a)] at hmax
    exact le_antisymm (lower_le_threshold ha htx0 htx1 hty0 hty1) hmax

/-- Excluding the metallic point strictly improves the lower bound on every closed rectangle. -/
theorem lower_rectangle_strict {a lx ux ly uy : ℝ} (ha : 1 ≤ a)
    (hlx : 0 ≤ lx) (hlxu : lx ≤ ux) (hux : ux ≤ 1)
    (hly : 0 ≤ ly) (hlyu : ly ≤ uy) (huy : uy ≤ 1)
    (hexclude : ¬ (metallic a ∈ Set.Icc lx ux ∧ metallic a ∈ Set.Icc ly uy)) :
    lower a (lowerRectangleX a lx ux ly uy) (lowerRectangleY a lx ux ly uy) < threshold a := by
  have hh := lower_rectangle_maximum ha hlx hlxu hux hly hlyu huy
  have hle := lower_le_threshold ha (hlx.trans hh.1.1) (hh.1.2.trans hux)
    (hly.trans hh.2.1.1) (hh.2.1.2.trans huy)
  apply lt_of_le_of_ne hle
  exact fun he => hexclude ((lower_rectangle_threshold_iff ha hlx hlxu hux hly hlyu huy).1 he)

/-- A rational point beats every corner on an arbitrary rectangle: the run-cell
alignment hypotheses in the four-corner theorem cannot simply be deleted. -/
theorem arbitrary_rectangle_lower_corners_fail :
    max (max (lower 2 0 0) (lower 2 0 1)) (max (lower 2 1 0) (lower 2 1 1)) <
      lower 2 (1 / 2) (1 / 2) := by norm_num [lower]

/-- The corresponding upper-envelope counterexample on the full unit square. -/
theorem arbitrary_rectangle_upper_corners_fail :
    upper 2 (1 / 2) (1 / 2) <
      min (min (upper 2 0 0) (upper 2 0 1)) (min (upper 2 1 0) (upper 2 1 1)) := by
  norm_num [upper]

end ContinuedFractionBounds
