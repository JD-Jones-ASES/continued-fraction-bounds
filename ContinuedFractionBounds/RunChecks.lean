module

public import ContinuedFractionBounds.RunBounds

@[expose] public section

namespace ContinuedFractionBounds

/-- Immediate low departures have closure `[1/2,1]`. -/
theorem silver_low_endpoints :
    runLower 2 0 .low = 1 / 2 ∧ runUpper 2 0 .low = 1 := by
  norm_num [runLower, runUpper, tailIter_zero, departureLeft, departureRight]

/-- Immediate high departures have closure `[0,1/3]`. -/
theorem silver_high_endpoints :
    runLower 2 0 .high = 0 ∧ runUpper 2 0 .high = 1 / 3 := by
  norm_num [runLower, runUpper, tailIter_zero, departureLeft, departureRight]

/-- One repeated silver digit reverses the low-departure interval. -/
theorem silver_one_low_endpoints :
    runLower 2 1 .low = 1 / 3 ∧ runUpper 2 1 .low = 2 / 5 := by
  norm_num [runLower, runUpper, tailIter, tailMap, departureLeft, departureRight]

/-- One repeated silver digit reverses the high-departure interval. -/
theorem silver_one_high_endpoints :
    runLower 2 1 .high = 3 / 7 ∧ runUpper 2 1 .high = 1 / 2 := by
  norm_num [runLower, runUpper, tailIter, tailMap, departureLeft, departureRight]

/-- Both three-coefficient extrema for two immediate low departures. -/
theorem silver_zero_low_low :
    runLowerBound 2 0 0 .low .low = 1 / 3 ∧
      runUpperBound 2 0 0 .low .low = 5 / 12 := by
  norm_num [runLowerBound, runUpperBound, silver_low_endpoints.1,
    silver_low_endpoints.2, lower, upper]

/-- Both three-coefficient extrema for two immediate high departures. -/
theorem silver_zero_high_high :
    runLowerBound 2 0 0 .high .high = 7 / 24 ∧
      runUpperBound 2 0 0 .high .high = 3 / 8 := by
  norm_num [runLowerBound, runUpperBound, silver_high_endpoints.1,
    silver_high_endpoints.2, lower, upper]

/-- Mixed departures require all four corners: the two optimizers differ. -/
theorem silver_zero_low_high :
    runLowerBound 2 0 0 .low .high = 3 / 10 ∧
      runUpperBound 2 0 0 .low .high = 2 / 5 := by
  norm_num [runLowerBound, runUpperBound, silver_low_endpoints.1,
    silver_low_endpoints.2, silver_high_endpoints.1, silver_high_endpoints.2, lower, upper]

theorem silver_zero_high_low :
    runLowerBound 2 0 0 .high .low = 3 / 10 ∧
      runUpperBound 2 0 0 .high .low = 2 / 5 := by
  norm_num [runLowerBound, runUpperBound, silver_low_endpoints.1,
    silver_low_endpoints.2, silver_high_endpoints.1, silver_high_endpoints.2, lower, upper]

/-- Both bounds after one repeated digit on each side with low departures. -/
theorem silver_one_low_low :
    runLowerBound 2 1 1 .low .low = 12 / 35 ∧
      runUpperBound 2 1 1 .low .low = 5 / 14 := by
  norm_num [runLowerBound, runUpperBound, silver_one_low_endpoints.1,
    silver_one_low_endpoints.2, lower, upper]

/-- Both bounds after one repeated digit on each side with high departures. -/
theorem silver_one_high_high :
    runLowerBound 2 1 1 .high .high = 7 / 20 ∧
      runUpperBound 2 1 1 .high .high = 51 / 140 := by
  norm_num [runLowerBound, runUpperBound, silver_one_high_endpoints.1,
    silver_one_high_endpoints.2, lower, upper]

theorem silver_one_low_high :
    runLowerBound 2 1 1 .low .high = 10 / 29 ∧
      runUpperBound 2 1 1 .low .high = 21 / 58 := by
  norm_num [runLowerBound, runUpperBound, silver_one_low_endpoints.1,
    silver_one_low_endpoints.2, silver_one_high_endpoints.1,
    silver_one_high_endpoints.2, lower, upper]

theorem silver_one_high_low :
    runLowerBound 2 1 1 .high .low = 10 / 29 ∧
      runUpperBound 2 1 1 .high .low = 21 / 58 := by
  norm_num [runLowerBound, runUpperBound, silver_one_low_endpoints.1,
    silver_one_low_endpoints.2, silver_one_high_endpoints.1,
    silver_one_high_endpoints.2, lower, upper]

/-- Keeping only minimum run lengths leaves the metallic point in every closed cell,
so the improved lower constant from an exact departure class cannot remain valid. -/
theorem minimum_run_lower_improvement_fails {a : ℝ} (ha : 1 < a)
    (r s : ℕ) (e f : Departure) :
    ¬ (∀ x ∈ constantCell a r, ∀ y ∈ constantCell a s,
      lower a x y ≤ runLowerBound a r s e f) := by
  intro hh
  have h := hh (metallic a) (interior_subset (metallic_mem_constant_interior ha r))
    (metallic a) (interior_subset (metallic_mem_constant_interior ha s))
  rw [lower_metallic (by linarith : 0 < a)] at h
  exact (not_le_of_gt (runBounds_strict_threshold ha r s e f).1) h

/-- The dual exact-run improvement likewise fails if the departure conditions are erased. -/
theorem minimum_run_upper_improvement_fails {a : ℝ} (ha : 1 < a)
    (r s : ℕ) (e f : Departure) :
    ¬ (∀ x ∈ constantCell a r, ∀ y ∈ constantCell a s,
      runUpperBound a r s e f ≤ upper a x y) := by
  intro hh
  have h := hh (metallic a) (interior_subset (metallic_mem_constant_interior ha r))
    (metallic a) (interior_subset (metallic_mem_constant_interior ha s))
  rw [upper_metallic] at h
  exact (not_le_of_gt (runBounds_strict_threshold ha r s e f).2) h

end ContinuedFractionBounds
