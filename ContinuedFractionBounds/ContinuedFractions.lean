module

public import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
public import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic

@[expose] public section

namespace ContinuedFractionBounds

/-- The ordinary complete quotients obtained from the real input itself. -/
noncomputable def completeQuotient (α : ℝ) : ℕ → ℝ
  | 0 => α
  | n + 1 => (Int.fract (completeQuotient α n))⁻¹

/-- The ordinary simple continued-fraction digits; index zero is the integer part. -/
noncomputable def digit (α : ℝ) (n : ℕ) : ℤ := ⌊completeQuotient α n⌋

/-- The ordinary numerator, using Mathlib's continued fraction of the real number. -/
noncomputable def numerator (α : ℝ) (n : ℕ) : ℝ := (GenContFract.of α).nums n

/-- The ordinary denominator, with denominator zero equal to one. -/
noncomputable def denominator (α : ℝ) (n : ℕ) : ℝ := (GenContFract.of α).dens n

/-- The actual approximation coefficient of an ordinary convergent. -/
noncomputable def theta (α : ℝ) (n : ℕ) : ℝ :=
  denominator α n * |denominator α n * α - numerator α n|

/-- The finite reversed-past state at the middle convergent `n+1`. -/
noncomputable def past (α : ℝ) (n : ℕ) : ℝ := denominator α n / denominator α (n+1)

/-- The infinite-future state after the central digit of index `n+2`. -/
noncomputable def future (α : ℝ) (n : ℕ) : ℝ := Int.fract (completeQuotient α (n+2))

theorem completeQuotient_irrational {α : ℝ} (hα : Irrational α) (n : ℕ) :
    Irrational (completeQuotient α n) := by
  induction n with
  | zero => exact hα
  | succ n ih => exact (ih.sub_intCast _).inv

theorem fract_completeQuotient_irrational {α : ℝ} (hα : Irrational α) (n : ℕ) :
    Irrational (Int.fract (completeQuotient α n)) :=
  (completeQuotient_irrational hα n).sub_intCast _

theorem fract_completeQuotient_pos {α : ℝ} (hα : Irrational α) (n : ℕ) :
    0 < Int.fract (completeQuotient α n) :=
  lt_of_le_of_ne (Int.fract_nonneg _) (fract_completeQuotient_irrational hα n).ne_zero.symm

theorem stream_completeQuotient {α : ℝ} (hα : Irrational α) (n : ℕ) :
    GenContFract.IntFractPair.stream α n =
      some (GenContFract.IntFractPair.of (completeQuotient α n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply GenContFract.IntFractPair.succ_nth_stream_eq_some_iff.mpr
    exact ⟨_, ih, (fract_completeQuotient_irrational hα n).ne_zero, rfl⟩

theorem of_not_terminated {α : ℝ} (hα : Irrational α) (n : ℕ) :
    ¬ (GenContFract.of α).TerminatedAt n := by
  rw [GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none,
    stream_completeQuotient hα]
  simp

theorem ordinary_denominator_pos {α : ℝ} (hα : Irrational α) (n : ℕ) :
    0 < denominator α n := by
  have h := GenContFract.succ_nth_fib_le_of_nth_den (v := α)
    (n := n) (Or.inr (of_not_terminated hα _))
  exact lt_of_lt_of_le (by exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos n)) h

theorem past_mem {α : ℝ} (hα : Irrational α) (n : ℕ) :
    0 < past α n ∧ past α n ≤ 1 := by
  refine ⟨div_pos (ordinary_denominator_pos hα _) (ordinary_denominator_pos hα _), ?_⟩
  exact (div_le_one (ordinary_denominator_pos hα _)).mpr GenContFract.of_den_mono

theorem future_mem {α : ℝ} (hα : Irrational α) (n : ℕ) :
    0 < future α n ∧ future α n < 1 :=
  ⟨fract_completeQuotient_pos hα _, Int.fract_lt_one _⟩

theorem future_irrational {α : ℝ} (hα : Irrational α) (n : ℕ) :
    Irrational (future α n) := fract_completeQuotient_irrational hα _

theorem digit_succ_pos {α : ℝ} (hα : Irrational α) (n : ℕ) :
    1 ≤ digit α (n+1) := by
  exact GenContFract.IntFractPair.one_le_succ_nth_stream_b (stream_completeQuotient hα _)

theorem gcf_digit {α : ℝ} (hα : Irrational α) (n : ℕ) :
    (GenContFract.of α).s.get? n = some ⟨1, (digit α (n+1) : ℝ)⟩ :=
  GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream (stream_completeQuotient hα _)

theorem numerator_recurrence {α : ℝ} (hα : Irrational α) (n : ℕ) :
    numerator α (n+2) = (digit α (n+2) : ℝ) * numerator α (n+1) + numerator α n := by
  simpa [numerator] using GenContFract.nums_recurrence (gcf_digit hα (n+1)) rfl rfl

theorem denominator_recurrence {α : ℝ} (hα : Irrational α) (n : ℕ) :
    denominator α (n+2) = (digit α (n+2) : ℝ) * denominator α (n+1) + denominator α n := by
  simpa [denominator] using GenContFract.dens_recurrence (gcf_digit hα (n+1)) rfl rfl

theorem reconstruction {α : ℝ} (hα : Irrational α) (n : ℕ) :
    α = (numerator α n + completeQuotient α (n+2) * numerator α (n+1)) /
      (denominator α n + completeQuotient α (n+2) * denominator α (n+1)) := by
  have h := GenContFract.compExactValue_correctness_of_stream_eq_some
    (stream_completeQuotient hα (n+1))
  simp only [GenContFract.compExactValue, GenContFract.IntFractPair.of,
    (fract_completeQuotient_irrational hα (n+1)).ne_zero, ↓reduceIte,
    GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen,
    one_mul] at h
  change α = (completeQuotient α (n+2) * numerator α (n+1) + numerator α n) /
    (completeQuotient α (n+2) * denominator α (n+1) + denominator α n) at h
  simpa only [add_comm] using h

theorem completeQuotient_eq_digit_add_future (α : ℝ) (n : ℕ) :
    completeQuotient α (n+2) = (digit α (n+2) : ℝ) + future α n := by
  exact (Int.floor_add_fract _).symm

theorem convergent_eq (α : ℝ) (n : ℕ) :
    numerator α n / denominator α n = (α.convergent n : ℝ) :=
  Real.convs_eq_convergent α n

theorem past_rational (α : ℝ) (n : ℕ) : ∃ r : ℚ, past α n = r := by
  obtain ⟨p, hp⟩ := GenContFract.exists_rat_eq_nth_den α n
  obtain ⟨q, hq⟩ := GenContFract.exists_rat_eq_nth_den α (n+1)
  exact ⟨p/q, by simp [past, denominator, hp, hq]⟩

@[simp] theorem denominator_zero (α : ℝ) : denominator α 0 = 1 :=
  GenContFract.zeroth_den_eq_one

theorem denominator_one {α : ℝ} (hα : Irrational α) :
    denominator α 1 = (digit α 1 : ℝ) :=
  GenContFract.first_den_eq (gcf_digit hα 0)

private theorem triple_algebra {α a x y p₀ p₁ q₀ q₁ : ℝ}
    (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (ha : 1 ≤ a) (hy : 0 < y)
    (hx : x = q₀ / q₁)
    (hdet : |p₀ * q₁ - q₀ * p₁| = 1)
    (hα : α = (p₀ + (a+y)*p₁)/(q₀+(a+y)*q₁)) :
    q₀ * |q₀*α-p₀| = x*(a+y)/(a+x+y) ∧
    q₁ * |q₁*α-p₁| = 1/(a+x+y) ∧
    (a*q₁+q₀)*|(a*q₁+q₀)*α-(a*p₁+p₀)| = y*(a+x)/(a+x+y) := by
  have hD : 0 < q₀ + (a+y)*q₁ := by positivity
  have hay : 0 < a+y := by linarith
  have hxpos : 0 < x := hx ▸ div_pos hq₀ hq₁
  have hsum : 0 < a+x+y := by linarith
  have he₀ : q₀*α-p₀ = -(a+y)*(p₀*q₁-q₀*p₁)/(q₀+(a+y)*q₁) := by
    rw [hα]; field_simp; ring
  have he₁ : q₁*α-p₁ = (p₀*q₁-q₀*p₁)/(q₀+(a+y)*q₁) := by
    rw [hα]; field_simp; ring
  have he₂ : (a*q₁+q₀)*α-(a*p₁+p₀) = -y*(p₀*q₁-q₀*p₁)/(q₀+(a+y)*q₁) := by
    rw [hα]; field_simp; ring
  rw [he₀, he₁, he₂, abs_div, abs_div, abs_div, abs_mul, abs_mul,
    abs_neg, abs_neg, abs_of_pos hay, abs_of_pos hy, abs_of_pos hD, hdet]
  subst x
  constructor
  · field_simp; ring
  constructor
  · field_simp; ring
  · field_simp; ring

/-- The chronological triple of actual ordinary approximation coefficients.
The middle index is `n+1`; its next digit has index `n+2`. -/
theorem ordinary_convergent_triple {α : ℝ} (hα : Irrational α) (n : ℕ) :
    let a := (digit α (n+2) : ℝ)
    let x := past α n
    let y := future α n
    theta α n = x*(a+y)/(a+x+y) ∧
    theta α (n+1) = 1/(a+x+y) ∧
    theta α (n+2) = y*(a+x)/(a+x+y) := by
  have hdet := (SimpContFract.of α).determinant (of_not_terminated hα n)
  change (GenContFract.of α).nums n * (GenContFract.of α).dens (n+1) -
      (GenContFract.of α).dens n * (GenContFract.of α).nums (n+1) = (-1)^(n+1) at hdet
  have hdet' : |numerator α n * denominator α (n+1) -
      denominator α n * numerator α (n+1)| = 1 := by
    change |(GenContFract.of α).nums n * (GenContFract.of α).dens (n+1) -
      (GenContFract.of α).dens n * (GenContFract.of α).nums (n+1)| = 1
    rw [hdet, abs_neg_one_pow]
  have hr := reconstruction hα n
  rw [completeQuotient_eq_digit_add_future] at hr
  have ht := triple_algebra (ordinary_denominator_pos hα n) (ordinary_denominator_pos hα (n+1))
    (show (1:ℝ) ≤ (digit α (n+2) : ℝ) by exact_mod_cast digit_succ_pos hα (n+1))
    (future_mem hα n).1 (show past α n = _ from rfl) hdet' hr
  simpa only [theta, numerator_recurrence hα n, denominator_recurrence hα n] using ht

end ContinuedFractionBounds
