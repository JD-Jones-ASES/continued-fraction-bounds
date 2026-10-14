module

public import ContinuedFractionBounds.Basic

@[expose] public section

/-!
# Lower switching curve

The positive involution parametrizing the level
`min (x * (a + y)) (y * (a + x)) = 1`.
-/

namespace ContinuedFractionBounds

noncomputable def lowerSwitch (a t : ℝ) : ℝ := max (1 / t - a) (1 / (a + t))

lemma lowerSwitch_pos {a t : ℝ} (ha : 0 < a) (ht : 0 < t) : 0 < lowerSwitch a t := by
  exact lt_of_lt_of_le (by positivity : 0 < 1 / (a + t)) (le_max_right _ _)

lemma lowerSwitch_le_iff {a t u : ℝ} (ha : 0 < a) (ht : 0 < t) :
    lowerSwitch a t ≤ u ↔ 1 ≤ min (t * (a + u)) (u * (a + t)) := by
  have hdt : 0 < a + t := by linarith
  unfold lowerSwitch
  rw [max_le_iff, le_min_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    have hh₁ : 1 / t ≤ a + u := by linarith
    have hh₁' := (div_le_iff₀ ht).1 hh₁
    exact ⟨by nlinarith, (div_le_iff₀ hdt).1 h₂⟩
  · rintro ⟨h₁, h₂⟩
    have hh₁ : 1 / t ≤ a + u := (div_le_iff₀ ht).2 (by nlinarith)
    exact ⟨by linarith, (div_le_iff₀ hdt).2 h₂⟩

lemma le_lowerSwitch_iff {a t u : ℝ} (ha : 0 < a) (ht : 0 < t) :
    u ≤ lowerSwitch a t ↔ min (t * (a + u)) (u * (a + t)) ≤ 1 := by
  have hdt : 0 < a + t := by linarith
  unfold lowerSwitch
  rw [le_max_iff, min_le_iff]
  constructor
  · rintro (h | h)
    · left
      have hh : a + u ≤ 1 / t := by linarith
      have hh' := (le_div_iff₀ ht).1 hh
      nlinarith
    · right
      exact (le_div_iff₀ hdt).1 h
  · rintro (h | h)
    · left
      have hh : a + u ≤ 1 / t := (le_div_iff₀ ht).2 (by nlinarith)
      linarith
    · right
      exact (le_div_iff₀ hdt).2 h

lemma lowerSwitch_eq_iff {a t u : ℝ} (ha : 0 < a) (ht : 0 < t) :
    lowerSwitch a t = u ↔ min (t * (a + u)) (u * (a + t)) = 1 := by
  rw [le_antisymm_iff, lowerSwitch_le_iff ha ht, le_lowerSwitch_iff ha ht]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

lemma lowerSwitch_curve {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    min (t * (a + lowerSwitch a t)) (lowerSwitch a t * (a + t)) = 1 :=
  (lowerSwitch_eq_iff ha ht).1 rfl

lemma lowerSwitch_involutive {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    lowerSwitch a (lowerSwitch a t) = t := by
  apply (lowerSwitch_eq_iff ha (lowerSwitch_pos ha ht)).2
  rw [min_comm]
  exact lowerSwitch_curve ha ht

lemma lowerSwitch_strictAnti {a s t : ℝ} (ha : 0 < a) (hs : 0 < s) (hst : s < t) :
    lowerSwitch a t < lowerSwitch a s := by
  unfold lowerSwitch
  apply max_lt_max
  · exact sub_lt_sub_right (one_div_lt_one_div_of_lt hs hst) a
  · exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

lemma lowerSwitch_antitone {a s t : ℝ} (ha : 0 < a) (hs : 0 < s) (hst : s ≤ t) :
    lowerSwitch a t ≤ lowerSwitch a s := by
  rcases hst.eq_or_lt with h | h
  · rw [h]
  · exact (lowerSwitch_strictAnti ha hs h).le

lemma lowerSwitch_metallic {a : ℝ} (ha : 0 < a) :
    lowerSwitch a (metallic a) = metallic a := by
  apply (lowerSwitch_eq_iff ha (metallic_pos a)).2
  rw [metallic_equation, min_self]

lemma lowerSwitch_le_metallic {a t : ℝ} (ha : 0 < a) (ht : metallic a ≤ t) :
    lowerSwitch a t ≤ metallic a := by
  rw [← lowerSwitch_metallic ha]
  exact lowerSwitch_antitone ha (metallic_pos a) ht

lemma metallic_le_lowerSwitch {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (htb : t ≤ metallic a) :
    metallic a ≤ lowerSwitch a t := by
  rw [← lowerSwitch_metallic ha]
  exact lowerSwitch_antitone ha ht htb

lemma lowerSwitch_high {a t : ℝ} (ha : 0 < a) (ht : metallic a ≤ t) :
    lowerSwitch a t = 1 / (a + t) := by
  have hb := metallic_pos a
  have he := metallic_equation a
  have htpos : 0 < t := hb.trans_le ht
  have hs : 1 ≤ t * (a + t) := by
    have h := mul_le_mul ht (show a + metallic a ≤ a + t by linarith)
      (show 0 ≤ a + metallic a by linarith) htpos.le
    linarith
  unfold lowerSwitch
  apply max_eq_right
  apply (sub_le_iff_le_add).2
  apply (div_le_iff₀ htpos).2
  have hd : 0 < a + t := by linarith
  have hi : 1 / (a + t) * (a + t) = 1 := by field_simp
  have hh := mul_nonneg ha.le (sub_nonneg.mpr hs)
  apply (le_of_mul_le_mul_right ?_ hd)
  nlinarith

lemma lowerSwitch_low {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (htb : t ≤ metallic a) :
    lowerSwitch a t = 1 / t - a := by
  have hb := metallic_pos a
  have he := metallic_equation a
  have hs : t * (a + t) ≤ 1 := by
    have h := mul_le_mul htb (show a + t ≤ a + metallic a by linarith)
      (show 0 ≤ a + t by linarith) hb.le
    linarith
  unfold lowerSwitch
  apply max_eq_left
  apply (le_sub_iff_add_le).2
  apply (le_div_iff₀ ht).2
  have hd : 0 < a + t := by linarith
  have hi : 1 / (a + t) * (a + t) = 1 := by field_simp
  have hh := mul_nonneg ha.le (sub_nonneg.mpr hs)
  apply (le_of_mul_le_mul_right ?_ hd)
  nlinarith

end ContinuedFractionBounds
