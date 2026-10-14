module

public import ContinuedFractionBounds.Basic

/-!
# Exact regions for near extremizers

The level sets of both three-coefficient envelopes are intersections of three
explicit inequalities. These formulas also apply inside arbitrary cylinders.
-/

public section
namespace ContinuedFractionBounds

/-- The boundary graph obtained by solving a side-coefficient inequality. -/
@[expose] noncomputable def levelBoundary (a t z : ℝ) : ℝ :=
  t * (a + z) / (a + z - t)

theorem lower_level_iff {a t x y : ℝ} (ht : 0 < t) (hta : t < a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    t ≤ lower a x y ↔
      x + y ≤ 1 / t - a ∧ levelBoundary a t y ≤ x ∧ levelBoundary a t x ≤ y := by
  have hd : 0 < a + x + y := by linarith
  have hdy : 0 < a + y - t := by linarith
  have hdx : 0 < a + x - t := by linarith
  unfold lower levelBoundary
  rw [le_div_iff₀ hd, le_min_iff, le_min_iff]
  have hcentral : t * (a + x + y) ≤ 1 ↔ x + y ≤ 1 / t - a := by
    rw [le_sub_iff_add_le, le_div_iff₀ ht]
    constructor <;> intro h <;> nlinarith
  have hleft : t * (a + x + y) ≤ x * (a + y) ↔
      t * (a + y) / (a + y - t) ≤ x := by
    rw [div_le_iff₀ hdy]
    constructor <;> intro h <;> nlinarith
  have hright : t * (a + x + y) ≤ y * (a + x) ↔
      t * (a + x) / (a + x - t) ≤ y := by
    rw [div_le_iff₀ hdx]
    constructor <;> intro h <;> nlinarith
  exact and_congr hcentral (and_congr hleft hright)

theorem upper_level_iff {a t x y : ℝ} (ht : 0 < t) (hta : t < a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    upper a x y ≤ t ↔
      1 / t - a ≤ x + y ∧ x ≤ levelBoundary a t y ∧ y ≤ levelBoundary a t x := by
  have hd : 0 < a + x + y := by linarith
  have hdy : 0 < a + y - t := by linarith
  have hdx : 0 < a + x - t := by linarith
  unfold upper levelBoundary
  rw [div_le_iff₀ hd, max_le_iff, max_le_iff]
  have hcentral : 1 ≤ t * (a + x + y) ↔ 1 / t - a ≤ x + y := by
    rw [sub_le_iff_le_add, div_le_iff₀ ht]
    constructor <;> intro h <;> nlinarith
  have hleft : x * (a + y) ≤ t * (a + x + y) ↔
      x ≤ t * (a + y) / (a + y - t) := by
    rw [le_div_iff₀ hdy]
    constructor <;> intro h <;> nlinarith
  have hright : y * (a + x) ≤ t * (a + x + y) ↔
      y ≤ t * (a + x) / (a + x - t) := by
    rw [le_div_iff₀ hdx]
    constructor <;> intro h <;> nlinarith
  exact and_congr hcentral (and_congr hleft hright)

end ContinuedFractionBounds
