module

public import ContinuedFractionBounds.RectangleOptimization
public import ContinuedFractionBounds.UpperSwitch

@[expose] public section

namespace ContinuedFractionBounds

lemma upperSwitch_value_low {a t : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t)
    (htb : t ≤ metallic a) :
    upper a t (upperSwitch a t) = (a + t) / (1 + (a + t) ^ 2) := by
  have ht1 : t ≤ 1 / a := htb.trans (metallic_lt_inv ha).le
  unfold upper
  rw [upperSwitch_level ha ht ht1, max_self, upperSwitch_left htb]
  have hd : a + t ≠ 0 := by positivity
  field_simp
  ring

lemma upperSwitch_value_high {a t : ℝ} (ha : 1 ≤ a)
    (htb : metallic a ≤ t) (ht1 : t ≤ 1 / a) :
    upper a t (upperSwitch a t) = t / (1 + t ^ 2) := by
  have ht : 0 < t := (metallic_pos a).trans_le htb
  unfold upper
  rw [upperSwitch_level ha ht.le ht1, max_self, upperSwitch_right ha htb ht1]
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hf : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp
  convert mul_inv_cancel₀ hf using 1 <;> ring

lemma upper_low_boundary {a t x y : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t)
    (htb : t ≤ metallic a) (hx : 0 ≤ x) (hxt : x ≤ t) (hy : 0 ≤ y) :
    upper a t (upperSwitch a t) ≤ upper a x y ∧
      (upper a x y = upper a t (upperSwitch a t) ↔ x = t ∧ y = upperSwitch a t) := by
  have ha0 : 0 < a := by linarith
  have hc := upperSwitch_value_low ha ht htb
  have hf := highEnvelope_le_upper ha0 hx hy
  have hs := highEnvelope_antitone_one_le (show 1 ≤ a + x by linarith)
    (show a + x ≤ a + t by linarith)
  refine ⟨by linarith, ?_⟩
  constructor
  · intro he
    have hxt' : x = t := by
      by_contra h
      have hh := highEnvelope_strictAntitone_one_le (show 1 ≤ a + x by linarith)
        (show a + x < a + t by have := lt_of_le_of_ne hxt h; linarith)
      linarith
    subst x
    have hp := upper_highEnvelope_equality_product ha0 ht hy (he.trans hc)
    refine ⟨rfl, ?_⟩
    rw [upperSwitch_left htb]
    exact (eq_div_iff (show a + t ≠ 0 by positivity)).2 hp
  · rintro ⟨rfl, rfl⟩
    rfl

lemma upper_high_boundary {a t x y : ℝ} (ha : 1 ≤ a)
    (htb : metallic a ≤ t) (ht1 : t ≤ 1 / a)
    (htx : t ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) :
    upper a t (upperSwitch a t) ≤ upper a x y ∧
      (upper a x y = upper a t (upperSwitch a t) ↔ x = t ∧ y = upperSwitch a t) := by
  have ha0 : 0 < a := by linarith
  have ht := (metallic_pos a).trans_le htb
  have hx : 0 ≤ x := by linarith
  have hc := upperSwitch_value_high ha htb ht1
  have hf := lowEnvelope_le_upper ha0 hx hy
  have hs := lowEnvelope_mono ht.le htx hx1
  refine ⟨by linarith, ?_⟩
  constructor
  · intro he
    have hxt' : x = t := by
      by_contra h
      have hh := lowEnvelope_strictMono ht.le (lt_of_le_of_ne htx (Ne.symm h)) hx1
      linarith
    subst x
    have hp := upper_lowEnvelope_equality_product ha0 ht hy (he.trans hc)
    refine ⟨rfl, ?_⟩
    rw [upperSwitch_right ha htb ht1]
    have hh : a + y = 1 / t := (eq_div_iff (ne_of_gt ht)).2 (by nlinarith)
    linarith
  · rintro ⟨rfl, rfl⟩
    rfl

lemma upper_supported_minimum {a lx ux ly uy t u x y : ℝ} (ha : 1 ≤ a)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / a) (hu : u = upperSwitch a t)
    (hs : MetallicSupport (metallic a) lx ux ly uy t u)
    (hlx : 0 ≤ lx) (hux : ux ≤ 1) (hly : 0 ≤ ly) (huy : uy ≤ 1)
    (hx : x ∈ Set.Icc lx ux) (hy : y ∈ Set.Icc ly uy) :
    upper a t u ≤ upper a x y ∧ (upper a x y = upper a t u ↔ x = t ∧ y = u) := by
  have ha0 : 0 < a := by linarith
  have hx0 := hlx.trans hx.1
  have hy0 := hly.trans hy.1
  have hu0 : 0 ≤ u := hu ▸ upperSwitch_nonneg ha ht
  have hu1 : u ≤ 1 / a := hu ▸ upperSwitch_le_inv ha ht
  have htu : t = upperSwitch a u := by rw [hu, upperSwitch_involution ha ht ht1]
  rcases hs with h | h | h | h | h
  · obtain ⟨rfl, rfl⟩ := h
    rw [upper_metallic]
    exact ⟨threshold_le_upper ha hx0 (hx.2.trans hux) hy0 (hy.2.trans huy),
      upper_eq_threshold_iff ha hx0 (hx.2.trans hux) hy0 (hy.2.trans huy)⟩
  · rw [hu]
    exact upper_high_boundary ha h.2 ht1 (h.1 ▸ hx.1) (hx.2.trans hux) hy0
  · rw [hu]
    exact upper_low_boundary ha ht h.2 hx0 (h.1 ▸ hx.2) hy0
  · have hh := upper_high_boundary ha h.2 hu1 (h.1 ▸ hy.1) (hy.2.trans huy) hx0
    rw [← htu] at hh
    simpa only [upper_comm a y x, upper_comm a u t, and_comm (b := x = t)] using hh
  · have hh := upper_low_boundary ha hu0 h.2 hy0 (h.1 ▸ hy.2) hx0
    rw [← htu] at hh
    simpa only [upper_comm a y x, upper_comm a u t, and_comm (b := x = t)] using hh

noncomputable def upperClipLeft (a lx uy : ℝ) := max lx (upperSwitch a uy)
noncomputable def upperClipRight (a ux ly : ℝ) := min ux (upperSwitch a ly)
noncomputable def upperClipX (a lx ux ly uy : ℝ) :=
  clip (metallic a) (upperClipLeft a lx uy) (upperClipRight a ux ly)
noncomputable def upperClipY (a lx ux ly uy : ℝ) :=
  upperSwitch a (upperClipX a lx ux ly uy)

/-- Exact clipped minimizer of the upper envelope on every crossing rectangle. -/
theorem upper_clipped_minimum {a lx ux ly uy : ℝ} (ha : 1 ≤ a)
    (hlx : 0 ≤ lx) (hlxu : lx ≤ ux) (hux : ux ≤ 1)
    (hly : 0 ≤ ly) (hlyu : ly ≤ uy) (huy : uy ≤ 1)
    (hlo : max (lx * (a + ly)) (ly * (a + lx)) < 1)
    (hhi : 1 < max (ux * (a + uy)) (uy * (a + ux))) :
    let t := upperClipX a lx ux ly uy
    let u := upperClipY a lx ux ly uy
    t ∈ Set.Icc lx ux ∧ u ∈ Set.Icc ly uy ∧
      upper a t u = 1 / (a + t + u) ∧
      ∀ x ∈ Set.Icc lx ux, ∀ y ∈ Set.Icc ly uy,
        upper a t u ≤ upper a x y ∧ (upper a x y = upper a t u ↔ x = t ∧ y = u) := by
  have hux0 : 0 ≤ ux := hlx.trans hlxu
  have huy0 : 0 ≤ uy := hly.trans hlyu
  have hly1 : ly ≤ 1 / a := by
    apply (le_div_iff₀ (by linarith : 0 < a)).2
    have hh := (max_lt_iff.1 hlo).2
    nlinarith [mul_nonneg hlx hly]
  have hKuy : upperSwitch a uy ≤ ux := by
    apply (upperSwitch_le_iff ha huy0 hux0).2
    simpa only [max_comm] using hhi.le
  have hlxK : lx ≤ upperSwitch a ly := by
    apply (le_upperSwitch_iff ha hly hly1 hlx).2
    simpa only [max_comm] using hlo.le
  let L := upperClipLeft a lx uy
  let U := upperClipRight a ux ly
  let t := upperClipX a lx ux ly uy
  let u := upperClipY a lx ux ly uy
  have hL0 : 0 ≤ L := hlx.trans (le_max_left _ _)
  have hLU : L ≤ U :=
    le_min (max_le hlxu hKuy)
      (max_le hlxK (upperSwitch_antitone ha hly hlyu))
  have htLU : t ∈ Set.Icc L U := clip_mem hLU
  have ht0 : 0 ≤ t := hL0.trans htLU.1
  have ht1 : t ≤ 1 / a :=
    htLU.2.trans ((min_le_right _ _).trans (upperSwitch_le_inv ha hly))
  have htmem : t ∈ Set.Icc lx ux :=
    ⟨(le_max_left _ _).trans htLU.1, htLU.2.trans (min_le_left _ _)⟩
  have humem : u ∈ Set.Icc ly uy := by
    constructor
    · have htK : t ≤ upperSwitch a ly := htLU.2.trans (min_le_right _ _)
      have hh := (le_upperSwitch_iff ha hly hly1 ht0).1 htK
      apply (le_upperSwitch_iff ha ht0 ht1 hly).2
      simpa only [max_comm] using hh
    · apply (upperSwitch_le_iff ha ht0 huy0).2
      have hh := (upperSwitch_le_iff ha huy0 ht0).1 ((le_max_right _ _).trans htLU.1)
      simpa only [max_comm] using hh
  have hs : MetallicSupport (metallic a) lx ux ly uy t u := by
    by_cases hlow : metallic a < L
    · have htL : t = L := by
        dsimp [t, upperClipX, clip]
        rw [max_eq_left hlow.le, min_eq_right hLU]
      have htβ : metallic a ≤ t := by linarith
      rcases le_total lx (upperSwitch a uy) with hh | hh
      · have htK : t = upperSwitch a uy := htL.trans (max_eq_right hh)
        have huy1 : uy ≤ 1 / a := by
          by_contra hn
          have hz := upperSwitch_zero ha (le_of_not_ge hn)
          have hb := metallic_pos a
          rw [hz] at htK
          linarith
        have huuy : u = uy := by
          change upperSwitch a t = uy
          rw [htK, upperSwitch_involution ha huy0 huy1]
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨huuy, upperSwitch_le_metallic ha htβ⟩)))
      · exact Or.inr (Or.inl ⟨htL.trans (max_eq_left hh), htβ⟩)
    · have hLβ : L ≤ metallic a := le_of_not_gt hlow
      by_cases hhigh : U < metallic a
      · have htU : t = U := by
          dsimp [t, upperClipX, clip]
          rw [max_eq_right hLβ, min_eq_left hhigh.le]
        have htβ : t ≤ metallic a := by linarith
        rcases le_total ux (upperSwitch a ly) with hh | hh
        · exact Or.inr (Or.inr (Or.inl ⟨htU.trans (min_eq_left hh), htβ⟩))
        · have htK : t = upperSwitch a ly := htU.trans (min_eq_right hh)
          have huly : u = ly := by
            change upperSwitch a t = ly
            rw [htK, upperSwitch_involution ha hly hly1]
          exact Or.inr (Or.inr (Or.inr (Or.inl
            ⟨huly, metallic_le_upperSwitch ha ht0 htβ⟩)))
      · have hβU : metallic a ≤ U := le_of_not_gt hhigh
        have htβ : t = metallic a := by
          dsimp [t, upperClipX, clip]
          rw [max_eq_right hLβ, min_eq_right hβU]
        have huβ : u = metallic a := by
          change upperSwitch a t = metallic a
          rw [htβ, upperSwitch_metallic ha]
        exact Or.inl ⟨htβ, huβ⟩
  change t ∈ Set.Icc lx ux ∧ u ∈ Set.Icc ly uy ∧ _
  refine ⟨htmem, humem, ?_, ?_⟩
  · exact upper_eq_one_div (upperSwitch_level ha ht0 ht1).le
  · intro x hx y hy
    exact upper_supported_minimum ha ht0 ht1 rfl hs hlx hux hly huy hx hy

/-- Prescribed minimizing first coordinate on an arbitrary closed rectangle. -/
noncomputable def upperRectangleX (a lx ux ly uy : ℝ) :=
  if max (ux * (a + uy)) (uy * (a + ux)) ≤ 1 then ux
  else if 1 ≤ max (lx * (a + ly)) (ly * (a + lx)) then lx
  else upperClipX a lx ux ly uy

/-- Prescribed minimizing second coordinate on an arbitrary closed rectangle. -/
noncomputable def upperRectangleY (a lx ux ly uy : ℝ) :=
  if max (ux * (a + uy)) (uy * (a + ux)) ≤ 1 then uy
  else if 1 ≤ max (lx * (a + ly)) (ly * (a + lx)) then ly
  else upperClipY a lx ux ly uy

/-- Complete upper-envelope optimization on every closed rectangle in the unit square.
The minimizing point is always unique, including line and singleton rectangles. -/
theorem upper_rectangle_minimum {a lx ux ly uy : ℝ} (ha : 1 ≤ a)
    (hlx : 0 ≤ lx) (hlxu : lx ≤ ux) (hux : ux ≤ 1)
    (hly : 0 ≤ ly) (hlyu : ly ≤ uy) (huy : uy ≤ 1) :
    let t := upperRectangleX a lx ux ly uy
    let u := upperRectangleY a lx ux ly uy
    t ∈ Set.Icc lx ux ∧ u ∈ Set.Icc ly uy ∧
      ∀ x ∈ Set.Icc lx ux, ∀ y ∈ Set.Icc ly uy,
        upper a t u ≤ upper a x y ∧
        (upper a x y = upper a t u ↔ x = t ∧ y = u) := by
  have ha0 : 0 < a := by linarith
  by_cases hPup : max (ux * (a + uy)) (uy * (a + ux)) ≤ 1
  · simp only [upperRectangleX, upperRectangleY, hPup, ↓reduceIte]
    refine ⟨⟨hlxu, le_rfl⟩, ⟨hlyu, le_rfl⟩, ?_⟩
    intro x hx y hy
    exact upper_below_corner ha0 (hlx.trans hx.1) (hly.trans hy.1) hx.2 hy.2 hPup
  · by_cases hPlo : 1 ≤ max (lx * (a + ly)) (ly * (a + lx))
    · simp only [upperRectangleX, upperRectangleY, hPup, hPlo, ↓reduceIte]
      refine ⟨⟨le_rfl, hlxu⟩, ⟨le_rfl, hlyu⟩, ?_⟩
      intro x hx y hy
      exact upper_above_corner ha0 hlx hly hx.1 hy.1 hPlo
    · simp only [upperRectangleX, upperRectangleY, hPup, hPlo, ↓reduceIte]
      have hh := upper_clipped_minimum ha hlx hlxu hux hly hlyu huy
        (lt_of_not_ge hPlo) (lt_of_not_ge hPup)
      exact ⟨hh.1, hh.2.1, hh.2.2.2⟩

/-- A rectangle retains the classical upper threshold exactly when it contains the metallic point. -/
theorem upper_rectangle_threshold_iff {a lx ux ly uy : ℝ} (ha : 1 ≤ a)
    (hlx : 0 ≤ lx) (hlxu : lx ≤ ux) (hux : ux ≤ 1)
    (hly : 0 ≤ ly) (hlyu : ly ≤ uy) (huy : uy ≤ 1) :
    upper a (upperRectangleX a lx ux ly uy) (upperRectangleY a lx ux ly uy) = threshold a ↔
      metallic a ∈ Set.Icc lx ux ∧ metallic a ∈ Set.Icc ly uy := by
  have hh := upper_rectangle_minimum ha hlx hlxu hux hly hlyu huy
  have htx0 := hlx.trans hh.1.1
  have htx1 := hh.1.2.trans hux
  have hty0 := hly.trans hh.2.1.1
  have hty1 := hh.2.1.2.trans huy
  constructor
  · intro he
    obtain ⟨hx, hy⟩ := (upper_eq_threshold_iff ha htx0 htx1 hty0 hty1).1 he
    exact ⟨hx ▸ hh.1, hy ▸ hh.2.1⟩
  · rintro ⟨hx, hy⟩
    have hmin := (hh.2.2 (metallic a) hx (metallic a) hy).1
    rw [upper_metallic] at hmin
    exact le_antisymm hmin (threshold_le_upper ha htx0 htx1 hty0 hty1)

/-- Excluding the metallic point strictly improves the upper bound on every closed rectangle. -/
theorem upper_rectangle_strict {a lx ux ly uy : ℝ} (ha : 1 ≤ a)
    (hlx : 0 ≤ lx) (hlxu : lx ≤ ux) (hux : ux ≤ 1)
    (hly : 0 ≤ ly) (hlyu : ly ≤ uy) (huy : uy ≤ 1)
    (hexclude : ¬ (metallic a ∈ Set.Icc lx ux ∧ metallic a ∈ Set.Icc ly uy)) :
    threshold a < upper a (upperRectangleX a lx ux ly uy) (upperRectangleY a lx ux ly uy) := by
  have hh := upper_rectangle_minimum ha hlx hlxu hux hly hlyu huy
  have hle := threshold_le_upper ha (hlx.trans hh.1.1) (hh.1.2.trans hux)
    (hly.trans hh.2.1.1) (hh.2.1.2.trans huy)
  apply lt_of_le_of_ne hle
  exact fun he => hexclude ((upper_rectangle_threshold_iff ha hlx hlxu hux hly hlyu huy).1 he.symm)

end ContinuedFractionBounds
