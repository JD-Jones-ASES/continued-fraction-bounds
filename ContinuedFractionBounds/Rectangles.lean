module

public import ContinuedFractionBounds.Stability
public import ContinuedFractionBounds.ClassicalBounds

@[expose] public section

/-!
# Rectangle bounds with aligned switching curves

Exact run cells are intervals on one side of the metallic point. The
following criterion proves that their extrema are unique corners whenever
both switching intervals are ordered or have matching endpoints.
-/

namespace ContinuedFractionBounds

noncomputable def leftRatio (a x y : ℝ) := x * (a + y) / (a + x + y)

lemma leftRatio_comm_den (a x y : ℝ) :
    leftRatio a y x = y * (a + x) / (a + x + y) := by
  unfold leftRatio
  congr 1
  ring

lemma leftRatio_mono {a x y u v : ℝ} (ha : 0 < a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxu : x ≤ u) (hyv : y ≤ v) :
    leftRatio a x y ≤ leftRatio a u v := by
  have hu : 0 ≤ u := by linarith
  have hv : 0 ≤ v := by linarith
  have hux : 0 ≤ u - x := sub_nonneg.mpr hxu
  have hvy : 0 ≤ v - y := sub_nonneg.mpr hyv
  have hd : 0 < a + x + y := by linarith
  have hd' : 0 < a + u + v := by linarith
  unfold leftRatio
  apply (div_le_div_iff₀ hd hd').2
  have h₁ : 0 ≤ (u - x) * ((a + y) * (a + v)) := by positivity
  have h₂ : 0 ≤ x * u * (v - y) := by positivity
  nlinarith [h₁, h₂]

lemma leftRatio_strict {a x y u v : ℝ} (ha : 0 < a)
    (hx : 0 < x) (hy : 0 ≤ y) (hxu : x ≤ u) (hyv : y ≤ v)
    (hne : x < u ∨ y < v) : leftRatio a x y < leftRatio a u v := by
  have hu : 0 ≤ u := by linarith
  have hv : 0 ≤ v := by linarith
  have hux : 0 ≤ u - x := sub_nonneg.mpr hxu
  have hvy : 0 ≤ v - y := sub_nonneg.mpr hyv
  have hd : 0 < a + x + y := by linarith
  have hd' : 0 < a + u + v := by linarith
  unfold leftRatio
  apply (div_lt_div_iff₀ hd hd').2
  have h₁ : 0 ≤ (u - x) * ((a + y) * (a + v)) := by positivity
  have h₂ : 0 ≤ x * u * (v - y) := by positivity
  rcases hne with h | h
  · have huxpos : 0 < u - x := sub_pos.mpr h
    have hh : 0 < (u - x) * ((a + y) * (a + v)) := by positivity
    nlinarith [hh, h₂]
  · have hupos : 0 < u := hx.trans_le hxu
    have hvypos : 0 < v - y := sub_pos.mpr h
    have hh : 0 < x * u * (v - y) := by positivity
    nlinarith [h₁, hh]

lemma lower_le_min_ratios {a x y : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    lower a x y ≤ min (leftRatio a x y) (leftRatio a y x) := by
  rw [leftRatio_comm_den a x y]
  change lower a x y ≤ min (x * (a + y) / (a + x + y)) (y * (a + x) / (a + x + y))
  apply le_min
  · exact lower_le_left_div (by linarith : 0 < a + x + y)
  · exact lower_le_right_div (by linarith : 0 < a + x + y)

lemma max_ratios_le_upper {a x y : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    max (leftRatio a x y) (leftRatio a y x) ≤ upper a x y := by
  rw [leftRatio_comm_den a x y]
  unfold upper leftRatio
  apply max_le
  · exact div_le_div_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (by linarith)
  · exact div_le_div_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (by linarith)

lemma one_div_le_upper {a x y : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    1 / (a + x + y) ≤ upper a x y := by
  exact div_le_div_of_nonneg_right (le_max_left _ _) (by linarith)

lemma lower_eq_min_ratios {a x y : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hQ : min (x * (a + y)) (y * (a + x)) ≤ 1) :
    lower a x y = min (leftRatio a x y) (leftRatio a y x) := by
  rw [leftRatio_comm_den a x y]
  unfold lower leftRatio
  rw [min_eq_right hQ, min_div_div_right (show 0 ≤ a + x + y by linarith)]

lemma upper_eq_max_ratios {a x y : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hP : 1 ≤ max (x * (a + y)) (y * (a + x))) :
    upper a x y = max (leftRatio a x y) (leftRatio a y x) := by
  rw [leftRatio_comm_den a x y]
  unfold upper leftRatio
  rw [max_eq_right hP, max_div_div_right (show 0 ≤ a + x + y by linarith)]

lemma lower_eq_one_div {a x y : ℝ}
    (hQ : 1 ≤ min (x * (a + y)) (y * (a + x))) :
    lower a x y = 1 / (a + x + y) := by
  unfold lower
  rw [min_eq_left hQ]

lemma upper_eq_one_div {a x y : ℝ}
    (hP : max (x * (a + y)) (y * (a + x)) ≤ 1) :
    upper a x y = 1 / (a + x + y) := by
  unfold upper
  rw [max_eq_left hP]

/-- If the upper corner is below the lower switching curve, it uniquely maximizes. -/
lemma lower_below_corner {a x y u v : ℝ} (ha : 0 < a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 < u) (hv : 0 < v)
    (hxu : x ≤ u) (hyv : y ≤ v)
    (hQ : min (u * (a + v)) (v * (a + u)) ≤ 1) :
    lower a x y ≤ lower a u v ∧
      (lower a x y = lower a u v ↔ x = u ∧ y = v) := by
  have hc := lower_eq_min_ratios ha hu.le hv.le hQ
  have hm : lower a x y ≤ lower a u v := by
    rw [hc]
    exact (lower_le_min_ratios ha hx hy).trans
      (min_le_min (leftRatio_mono ha hx hy hxu hyv) (leftRatio_mono ha hy hx hyv hxu))
  refine ⟨hm, ?_⟩
  constructor
  · intro he
    by_contra h
    have hn : x < u ∨ y < v := by
      by_contra hn
      push Not at hn
      exact h ⟨le_antisymm hxu hn.1, le_antisymm hyv hn.2⟩
    have hpos : 0 < lower a u v := by
      unfold lower
      positivity
    by_cases hxx : x = 0
    · have hz : lower a x y = 0 := by simp [lower, hxx, mul_nonneg hy (by linarith : 0 ≤ a)]
      linarith
    by_cases hyy : y = 0
    · have hz : lower a x y = 0 := by simp [lower, hyy, mul_nonneg hx (by linarith : 0 ≤ a)]
      linarith
    have hs₁ := leftRatio_strict ha (lt_of_le_of_ne hx (Ne.symm hxx)) hy hxu hyv hn
    have hs₂ := leftRatio_strict ha (lt_of_le_of_ne hy (Ne.symm hyy)) hx hyv hxu hn.symm
    have hs : min (leftRatio a x y) (leftRatio a y x) <
        min (leftRatio a u v) (leftRatio a v u) := min_lt_min hs₁ hs₂
    have hh := lower_le_min_ratios ha hx hy
    rw [← hc] at hs
    linarith
  · rintro ⟨rfl, rfl⟩
    rfl

/-- If the lower corner is above the lower switching curve, it uniquely maximizes. -/
lemma lower_above_corner {a l m x y : ℝ} (ha : 0 < a)
    (hl : 0 ≤ l) (hm : 0 ≤ m) (hlx : l ≤ x) (hmy : m ≤ y)
    (hQ : 1 ≤ min (l * (a + m)) (m * (a + l))) :
    lower a x y ≤ lower a l m ∧
      (lower a x y = lower a l m ↔ x = l ∧ y = m) := by
  have hc := lower_eq_one_div hQ
  have hx : 0 ≤ x := hl.trans hlx
  have hy : 0 ≤ y := hm.trans hmy
  have hden : 0 < a + l + m := by linarith
  have hle : 1 / (a + x + y) ≤ 1 / (a + l + m) :=
    one_div_le_one_div_of_le hden (by linarith)
  have hf := lower_le_one_div (show 0 < a + x + y by linarith)
  refine ⟨by linarith, ?_⟩
  constructor
  · intro he
    have heq : 1 / (a + x + y) = 1 / (a + l + m) := by linarith
    have hd : a + x + y = a + l + m := by apply inv_injective; simpa only [one_div] using heq
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- If the upper corner is below the upper switching curve, it uniquely minimizes. -/
lemma upper_below_corner {a x y u v : ℝ} (ha : 0 < a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxu : x ≤ u) (hyv : y ≤ v)
    (hP : max (u * (a + v)) (v * (a + u)) ≤ 1) :
    upper a u v ≤ upper a x y ∧
      (upper a x y = upper a u v ↔ x = u ∧ y = v) := by
  have hc := upper_eq_one_div hP
  have hden : 0 < a + x + y := by linarith
  have hle : 1 / (a + u + v) ≤ 1 / (a + x + y) :=
    one_div_le_one_div_of_le hden (by linarith)
  have hf := one_div_le_upper ha hx hy
  refine ⟨by linarith, ?_⟩
  constructor
  · intro he
    have heq : 1 / (a + x + y) = 1 / (a + u + v) := by linarith
    have hd : a + x + y = a + u + v := by apply inv_injective; simpa only [one_div] using heq
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- If the lower corner is above the upper switching curve, it uniquely minimizes. -/
lemma upper_above_corner {a l m x y : ℝ} (ha : 0 < a)
    (hl : 0 ≤ l) (hm : 0 ≤ m) (hlx : l ≤ x) (hmy : m ≤ y)
    (hP : 1 ≤ max (l * (a + m)) (m * (a + l))) :
    upper a l m ≤ upper a x y ∧
      (upper a x y = upper a l m ↔ x = l ∧ y = m) := by
  have hc := upper_eq_max_ratios ha hl hm hP
  have hx : 0 ≤ x := hl.trans hlx
  have hy : 0 ≤ y := hm.trans hmy
  have hf := max_ratios_le_upper ha hx hy
  have hle := max_le_max (leftRatio_mono ha hl hm hlx hmy) (leftRatio_mono ha hm hl hmy hlx)
  refine ⟨by rw [hc]; exact hle.trans hf, ?_⟩
  constructor
  · intro he
    by_contra h
    have hn : l < x ∨ m < y := by
      by_contra hn
      push Not at hn
      exact h ⟨le_antisymm hn.1 hlx, le_antisymm hn.2 hmy⟩
    rcases le_total (l * (a + m)) (m * (a + l)) with hactive | hactive
    · have hb : 1 ≤ m * (a + l) := by simpa [max_eq_right hactive] using hP
      have hmp : 0 < m := by nlinarith
      have hs := leftRatio_strict ha hmp hl hmy hlx hn.symm
      have hratio : leftRatio a l m ≤ leftRatio a m l := by
        rw [leftRatio_comm_den a l m]
        exact div_le_div_of_nonneg_right hactive (by linarith)
      rw [max_eq_right hratio] at hc
      have hh := (le_max_right (leftRatio a x y) (leftRatio a y x)).trans hf
      linarith
    · have hb : 1 ≤ l * (a + m) := by simpa [max_eq_left hactive] using hP
      have hlp : 0 < l := by nlinarith
      have hs := leftRatio_strict ha hlp hm hlx hmy hn
      have hratio : leftRatio a m l ≤ leftRatio a l m := by
        rw [leftRatio_comm_den a l m]
        exact div_le_div_of_nonneg_right hactive (by linarith)
      rw [max_eq_left hratio] at hc
      have hh := (le_max_left (leftRatio a x y) (leftRatio a y x)).trans hf
      linarith
  · rintro ⟨rfl, rfl⟩
    rfl


lemma highEnvelope_strict_antitone {p q : ℝ} (hp : 1 < p) (hpq : p < q) :
    q / (1 + q ^ 2) < p / (1 + p ^ 2) := by
  have hdp : 0 < 1 + p ^ 2 := by positivity
  have hdq : 0 < 1 + q ^ 2 := by positivity
  apply (div_lt_div_iff₀ hdq hdp).2
  have hpq1 : 0 < p * q - 1 := by nlinarith
  have h := mul_pos (sub_pos.mpr hpq) hpq1
  nlinarith

lemma highEnvelope_antitone {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) :
    q / (1 + q ^ 2) ≤ p / (1 + p ^ 2) := by
  rcases hpq.eq_or_lt with h | h
  · rw [h]
  · exact (highEnvelope_strict_antitone hp h).le

lemma upper_highEnvelope_equality_product {a x y : ℝ} (ha : 0 < a)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (he : upper a x y = (a + x) / (1 + (a + x) ^ 2)) :
    y * (a + x) = 1 := by
  have hd : 0 < a + x + y := by linarith
  have hp : 0 < a + x := by linarith
  have hf : 0 < 1 + (a + x) ^ 2 := by positivity
  have h₀ := one_div_le_upper ha hx hy
  have h₁ : y * (a + x) / (a + x + y) ≤ upper a x y := by
    exact div_le_div_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hd.le
  rw [he] at h₀ h₁
  have h₀' := (div_le_div_iff₀ hd hf).1 h₀
  have h₁' := (div_le_div_iff₀ hd hf).1 h₁
  have hge : 1 ≤ y * (a + x) := by nlinarith [h₀']
  have hle : y * (a + x) ≤ 1 := by
    by_contra h
    have hn : 0 < y * (a + x) - 1 := by linarith
    have hs : 0 < (a + x) ^ 2 := sq_pos_of_pos hp
    have hh := mul_pos hs hn
    nlinarith [h₁']
  exact le_antisymm hle hge

lemma lower_switch_value {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y)
    (ho : 1 / (a + y) ≤ y) :
    lower a (1 / (a + y)) y = (a + y) / (1 + (a + y) ^ 2) := by
  have hp : 0 < a + y := by linarith
  have he : 1 / (a + y) * (a + y) = 1 := by field_simp
  have hh : 1 ≤ y * (a + 1 / (a + y)) := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ho)]
  unfold lower
  rw [he, min_eq_left hh, min_self]
  field_simp
  ring

lemma upper_switch_value {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x)
    (ho : x ≤ 1 / (a + x)) :
    upper a x (1 / (a + x)) = (a + x) / (1 + (a + x) ^ 2) := by
  have hp : 0 < a + x := by linarith
  have he : 1 / (a + x) * (a + x) = 1 := by field_simp
  have hh : x * (a + 1 / (a + x)) ≤ 1 := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ho)]
  unfold upper
  rw [he, max_eq_right hh, max_self]
  field_simp
  ring

/-- A matching switching interval gives the off-diagonal maximizing corner. -/
lemma lower_matching_corner {a x y u m : ℝ} (ha : 1 < a)
    (hx : 0 ≤ x) (hm : 0 ≤ m) (hmy : m ≤ y)
    (hu : u = 1 / (a + m)) (ho : u ≤ m) :
    lower a x y ≤ lower a u m ∧
      (lower a x y = lower a u m ↔ x = u ∧ y = m) := by
  have hy : 0 ≤ y := hm.trans hmy
  have hc : lower a u m = (a + m) / (1 + (a + m) ^ 2) := by
    rw [hu]
    exact lower_switch_value (by linarith) hm (hu ▸ ho)
  have hf : lower a x y ≤ (a + y) / (1 + (a + y) ^ 2) := by
    simpa only [lower_comm] using lower_le_highEnvelope (by linarith : 0 < a) hy hx
  have hmz : 1 < a + m := by linarith
  have hs := highEnvelope_antitone hmz (show a + m ≤ a + y by linarith)
  refine ⟨by linarith, ?_⟩
  constructor
  · intro he
    have hym : y = m := by
      by_contra h
      have hh := highEnvelope_strict_antitone hmz (show a + m < a + y by
        have := lt_of_le_of_ne hmy (Ne.symm h); linarith)
      linarith
    subst y
    have he' : lower a m x = (a + m) / (1 + (a + m) ^ 2) := by
      rw [lower_comm]
      exact he.trans hc
    have hp := highEnvelope_equality_product (by linarith : 0 < a) hm hx he'
    have hxu : x = u := by
      rw [hu]
      exact (eq_div_iff (show a + m ≠ 0 by linarith)).2 hp
    exact ⟨hxu, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A matching switching interval gives the off-diagonal minimizing corner. -/
lemma upper_matching_corner {a x y u m : ℝ} (ha : 1 < a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxu : x ≤ u)
    (hm : m = 1 / (a + u)) (ho : u ≤ m) :
    upper a u m ≤ upper a x y ∧
      (upper a x y = upper a u m ↔ x = u ∧ y = m) := by
  have hu : 0 ≤ u := hx.trans hxu
  have hc : upper a u m = (a + u) / (1 + (a + u) ^ 2) := by
    rw [hm]
    exact upper_switch_value (by linarith) hu (hm ▸ ho)
  have hf := highEnvelope_le_upper (by linarith : 0 < a) hx hy
  have hmz : 1 < a + x := by linarith
  have hs := highEnvelope_antitone hmz (show a + x ≤ a + u by linarith)
  refine ⟨by linarith, ?_⟩
  constructor
  · intro he
    have hxu' : x = u := by
      by_contra h
      have hh := highEnvelope_strict_antitone hmz (show a + x < a + u by
        have := lt_of_le_of_ne hxu h; linarith)
      linarith
    subst x
    have he' : upper a u y = (a + u) / (1 + (a + u) ^ 2) := he.trans hc
    have hp := upper_highEnvelope_equality_product (by linarith : 0 < a) hu hy he'
    have hym : y = m := by
      rw [hm]
      exact (eq_div_iff (show a + u ≠ 0 by linarith)).2 hp
    exact ⟨rfl, hym⟩
  · rintro ⟨rfl, rfl⟩
    rfl


/-- A unique maximum attained at a corner, including its full equality statement. -/
def CornerMaximum (f : ℝ → ℝ → ℝ) (lx ux ly uy : ℝ) : Prop :=
  ∃ cx cy, (cx = lx ∨ cx = ux) ∧ (cy = ly ∨ cy = uy) ∧
    ∀ x ∈ Set.Icc lx ux, ∀ y ∈ Set.Icc ly uy,
      f x y ≤ f cx cy ∧ (f x y = f cx cy ↔ x = cx ∧ y = cy)

/-- A unique minimum attained at a corner, including its full equality statement. -/
def CornerMinimum (f : ℝ → ℝ → ℝ) (lx ux ly uy : ℝ) : Prop :=
  ∃ cx cy, (cx = lx ∨ cx = ux) ∧ (cy = ly ∨ cy = uy) ∧
    ∀ x ∈ Set.Icc lx ux, ∀ y ∈ Set.Icc ly uy,
      f cx cy ≤ f x y ∧ (f x y = f cx cy ↔ x = cx ∧ y = cy)

lemma cornerMaximum_swap {f : ℝ → ℝ → ℝ} {lx ux ly uy : ℝ}
    (hf : ∀ x y, f x y = f y x) (h : CornerMaximum f ly uy lx ux) :
    CornerMaximum f lx ux ly uy := by
  obtain ⟨cy, cx, hcy, hcx, hh⟩ := h
  refine ⟨cx, cy, hcx, hcy, ?_⟩
  intro x hx y hy
  have h := hh y hy x hx
  simpa only [hf y x, hf cy cx, and_comm (b := x = cx)] using h

lemma cornerMinimum_swap {f : ℝ → ℝ → ℝ} {lx ux ly uy : ℝ}
    (hf : ∀ x y, f x y = f y x) (h : CornerMinimum f ly uy lx ux) :
    CornerMinimum f lx ux ly uy := by
  obtain ⟨cy, cx, hcy, hcx, hh⟩ := h
  refine ⟨cx, cy, hcx, hcy, ?_⟩
  intro x hx y hy
  have h := hh y hy x hx
  simpa only [hf y x, hf cy cx, and_comm (b := x = cx)] using h

lemma products_below_metallic {a x y : ℝ} (ha : 0 < a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxb : x ≤ metallic a) (hyb : y ≤ metallic a) :
    max (x * (a + y)) (y * (a + x)) ≤ 1 := by
  have hb := metallic_pos a
  have he := metallic_equation a
  apply max_le
  · have hh := mul_le_mul hxb (show a + y ≤ a + metallic a by linarith) (by linarith : 0 ≤ a + y) hb.le
    linarith
  · have hh := mul_le_mul hyb (show a + x ≤ a + metallic a by linarith) (by linarith : 0 ≤ a + x) hb.le
    linarith

lemma products_above_metallic {a x y : ℝ} (ha : 0 < a)
    (hxb : metallic a ≤ x) (hyb : metallic a ≤ y) :
    1 ≤ min (x * (a + y)) (y * (a + x)) := by
  have hb := metallic_pos a
  have he := metallic_equation a
  apply le_min
  · have hh := mul_le_mul hxb (show a + metallic a ≤ a + y by linarith) (by linarith : 0 ≤ a + metallic a)
      (show 0 ≤ x by linarith)
    linarith
  · have hh := mul_le_mul hyb (show a + metallic a ≤ a + x by linarith) (by linarith : 0 ≤ a + metallic a)
      (show 0 ≤ y by linarith)
    linarith

/-- The three exact possible placements of an interval and a reversed switching interval. -/
def SwitchAligned (a lx ux ly uy : ℝ) : Prop :=
  ux ≤ 1 / (a + uy) ∨ 1 / (a + ly) ≤ lx ∨
    (lx = 1 / (a + uy) ∧ ux = 1 / (a + ly))

lemma rectangle_opposite_corner_extrema {a lx ux ly uy : ℝ} (ha : 1 < a)
    (hlx : 0 ≤ lx) (hx : lx < ux) (hly : 0 ≤ ly) (hy : ly < uy)
    (ho : ux ≤ ly) (hsx : SwitchAligned a lx ux ly uy)
    (hsy : SwitchAligned a ly uy lx ux) :
    CornerMaximum (lower a) lx ux ly uy ∧ CornerMinimum (upper a) lx ux ly uy := by
  have ha0 : 0 < a := by linarith
  have hux : 0 < ux := by linarith
  have huy : 0 < uy := by linarith
  have hloworder : lx * (a + ly) ≤ ly * (a + lx) := by
    nlinarith [mul_nonneg ha0.le (show 0 ≤ ly - lx by linarith)]
  have huporder : ux * (a + uy) ≤ uy * (a + ux) := by
    nlinarith [mul_nonneg ha0.le (show 0 ≤ uy - ux by linarith)]
  constructor
  · rcases hsx with h | h | h
    · have hQ : min (ux * (a + uy)) (uy * (a + ux)) ≤ 1 := by
        apply (min_le_left _ _).trans
        exact (le_div_iff₀ (show 0 < a + uy by linarith)).1 h
      refine ⟨ux, uy, Or.inr rfl, Or.inr rfl, ?_⟩
      intro x hxx y hyy
      exact lower_below_corner ha0 (hlx.trans hxx.1) (hly.trans hyy.1) hux huy hxx.2 hyy.2 hQ
    · have hQ : 1 ≤ min (lx * (a + ly)) (ly * (a + lx)) := by
        rw [min_eq_left hloworder]
        exact (div_le_iff₀ (show 0 < a + ly by linarith)).1 h
      refine ⟨lx, ly, Or.inl rfl, Or.inl rfl, ?_⟩
      intro x hxx y hyy
      exact lower_above_corner ha0 hlx hly hxx.1 hyy.1 hQ
    · refine ⟨ux, ly, Or.inr rfl, Or.inl rfl, ?_⟩
      intro x hxx y hyy
      exact lower_matching_corner ha (hlx.trans hxx.1) hly hyy.1 h.2 ho
  · rcases hsy with h | h | h
    · have hP : max (ux * (a + uy)) (uy * (a + ux)) ≤ 1 := by
        rw [max_eq_right huporder]
        exact (le_div_iff₀ (show 0 < a + ux by linarith)).1 h
      refine ⟨ux, uy, Or.inr rfl, Or.inr rfl, ?_⟩
      intro x hxx y hyy
      exact upper_below_corner ha0 (hlx.trans hxx.1) (hly.trans hyy.1) hxx.2 hyy.2 hP
    · have hP : 1 ≤ max (lx * (a + ly)) (ly * (a + lx)) := by
        apply le_trans ?_ (le_max_right _ _)
        exact (div_le_iff₀ (show 0 < a + lx by linarith)).1 h
      refine ⟨lx, ly, Or.inl rfl, Or.inl rfl, ?_⟩
      intro x hxx y hyy
      exact upper_above_corner ha0 hlx hly hxx.1 hyy.1 hP
    · refine ⟨ux, ly, Or.inr rfl, Or.inl rfl, ?_⟩
      intro x hxx y hyy
      exact upper_matching_corner ha (hlx.trans hxx.1) (hly.trans hyy.1) hxx.2 h.1 ho

/-- Both extrema are unique corners for intervals separated from the metallic point
and aligned with each other's switching intervals. -/
theorem rectangle_corner_extrema {a lx ux ly uy : ℝ} (ha : 1 < a)
    (hlx : 0 ≤ lx) (hx : lx < ux) (_hux : ux ≤ 1)
    (hly : 0 ≤ ly) (hy : ly < uy) (_huy : uy ≤ 1)
    (hsideX : ux < metallic a ∨ metallic a < lx)
    (hsideY : uy < metallic a ∨ metallic a < ly)
    (hsx : SwitchAligned a lx ux ly uy) (hsy : SwitchAligned a ly uy lx ux) :
    CornerMaximum (lower a) lx ux ly uy ∧ CornerMinimum (upper a) lx ux ly uy := by
  have ha0 : 0 < a := by linarith
  rcases hsideX with hxl | hxh <;> rcases hsideY with hyl | hyh
  · have hp := products_below_metallic ha0 (by linarith : 0 ≤ ux)
      (by linarith : 0 ≤ uy) hxl.le hyl.le
    have hq : min (ux * (a + uy)) (uy * (a + ux)) ≤ 1 :=
      (min_le_max).trans hp
    constructor
    · refine ⟨ux, uy, Or.inr rfl, Or.inr rfl, ?_⟩
      intro x hxx y hyy
      exact lower_below_corner ha0 (hlx.trans hxx.1) (hly.trans hyy.1)
        (by linarith) (by linarith) hxx.2 hyy.2 hq
    · refine ⟨ux, uy, Or.inr rfl, Or.inr rfl, ?_⟩
      intro x hxx y hyy
      exact upper_below_corner ha0 (hlx.trans hxx.1) (hly.trans hyy.1) hxx.2 hyy.2 hp
  · exact rectangle_opposite_corner_extrema ha hlx hx hly hy (by linarith) hsx hsy
  · have hh := rectangle_opposite_corner_extrema ha hly hy hlx hx (by linarith : uy ≤ lx) hsy hsx
    exact ⟨cornerMaximum_swap (lower_comm a) hh.1, cornerMinimum_swap (upper_comm a) hh.2⟩
  · have hq := products_above_metallic ha0 hxh.le hyh.le
    have hp : 1 ≤ max (lx * (a + ly)) (ly * (a + lx)) :=
      hq.trans (min_le_max)
    constructor
    · refine ⟨lx, ly, Or.inl rfl, Or.inl rfl, ?_⟩
      intro x hxx y hyy
      exact lower_above_corner ha0 hlx hly hxx.1 hyy.1 hq
    · refine ⟨lx, ly, Or.inl rfl, Or.inl rfl, ?_⟩
      intro x hxx y hyy
      exact upper_above_corner ha0 hlx hly hxx.1 hyy.1 hp

end ContinuedFractionBounds
