module

public import ContinuedFractionBounds.ContinuedFractionsWords
public import ContinuedFractionBounds.Runs

@[expose] public section

namespace ContinuedFractionBounds

/-- A literal partial quotient on the required side of the central integer. -/
def DigitDeparture (a b : ℤ) : Departure → Prop
  | .low => 1 ≤ b ∧ b < a
  | .high => a < b

/-- Exactly `r` past digits equal `a`, with the next available actual digit departing.
The middle convergent has index `n+1`. -/
def ExactPastRun (α : ℝ) (n : ℕ) (a : ℤ) (r : ℕ) (e : Departure) : Prop :=
  r ≤ n ∧ (∀ i < r, digit α (n+1-i) = a) ∧
    DigitDeparture a (digit α (n+1-r)) e

/-- Exactly `s` future digits equal `a`, followed by an actual departure digit. -/
def ExactFutureRun (α : ℝ) (n : ℕ) (a : ℤ) (s : ℕ) (e : Departure) : Prop :=
  (∀ i < s, digit α (n+3+i) = a) ∧
    DigitDeparture a (digit α (n+3+s)) e

theorem backwardState_mem {α : ℝ} (hα : Irrational α) (k : ℕ) :
    backwardState α k ∈ Set.Icc (0:ℝ) 1 := by
  cases k with
  | zero => simp [backwardState]
  | succ k =>
    rw [backwardState_eq_past hα k]
    exact ⟨(past_mem hα k).1.le, (past_mem hα k).2⟩

theorem backwardState_run (α : ℝ) (a : ℤ) (k r : ℕ) (hrk : r ≤ k)
    (hd : ∀ i < r, digit α (k-i) = a) :
    backwardState α k = tailIter a r (backwardState α (k-r)) := by
  induction r generalizing k with
  | zero => simp
  | succ r ih =>
    have hk : k-1+1=k := by omega
    have hd₀ : digit α k = a := by simpa using hd 0 (by omega)
    have hdr : ∀ i < r, digit α (k-1-i) = a := by
      intro i hi
      simpa [Nat.sub_sub, Nat.add_comm] using hd (i+1) (by omega)
    have hr : backwardState α (k-1) = tailIter a r (backwardState α (k-1-r)) :=
      ih (k-1) (by omega) hdr
    conv_lhs => rw [← hk, backwardState, hk, hd₀, hr]
    rw [tailIter_succ]
    simp only [prependDigit, tailMap, one_div]
    rw [show k-1-r=k-(r+1) by omega]

theorem backward_departure_mem {α : ℝ} (hα : Irrational α)
    {a : ℤ} (ha : 2 ≤ a) {k : ℕ} (hk : 1 ≤ k) (e : Departure)
    (hd : DigitDeparture a (digit α k) e) :
    backwardState α k ∈ departureInterval a e := by
  have hk' : k-1+1=k := by omega
  have hm := backwardState_mem hα (k-1)
  have hb : (1:ℝ) ≤ digit α k := by
    exact_mod_cast (hk' ▸ digit_succ_pos hα (k-1))
  have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha
  rw [← hk', backwardState, hk']
  unfold prependDigit
  cases e with
  | low =>
    obtain ⟨_, hd⟩ := hd
    have hd' : (digit α k : ℝ) + 1 ≤ a := by exact_mod_cast hd
    constructor
    · dsimp [departureLeft]
      rw [one_div]
      exact inv_le_inv₀ (by linarith) (by linarith [hm.1]) |>.mpr (by linarith [hm.2])
    · dsimp [departureRight]
      exact (inv_le_one₀ (by linarith [hm.1])).mpr (by linarith [hm.1])
  | high =>
    have hd' : (a:ℝ)+1 ≤ digit α k := by exact_mod_cast hd
    constructor
    · dsimp [departureLeft]; exact (inv_pos.mpr (by linarith [hm.1])).le
    · dsimp [departureRight]
      rw [one_div]
      exact inv_le_inv₀ (by linarith [hm.1]) (by linarith) |>.mpr (by linarith [hm.1])

/-- Exact past digits imply membership in the correct closed run cell. -/
theorem exactPastRun_mem {α : ℝ} (hα : Irrational α) {a : ℤ} (ha : 2 ≤ a)
    {n r : ℕ} {e : Departure} (hr : ExactPastRun α n a r e) :
    past α n ∈ runCell a r e := by
  obtain ⟨hrn, hd, hdep⟩ := hr
  refine ⟨backwardState α (n+1-r), backward_departure_mem hα ha (by omega) e hdep, ?_⟩
  rw [← backwardState_run α a (n+1) r (by omega) hd, backwardState_eq_past hα n]

/-- The actual fractional tails of complete quotients. -/
noncomputable def forwardState (α : ℝ) (k : ℕ) : ℝ := Int.fract (completeQuotient α k)

theorem forwardState_recurrence {α : ℝ} (_hα : Irrational α) (k : ℕ) :
    forwardState α k = prependDigit (digit α (k+1)) (forwardState α (k+1)) := by
  have he : (digit α (k+1) : ℝ) + forwardState α (k+1) = completeQuotient α (k+1) :=
    Int.floor_add_fract _
  rw [prependDigit, he]
  change _ = ((Int.fract (completeQuotient α k))⁻¹)⁻¹
  rw [inv_inv]
  rfl

theorem forwardState_run {α : ℝ} (hα : Irrational α) (a : ℤ) (k r : ℕ)
    (hd : ∀ i < r, digit α (k+i+1) = a) :
    forwardState α k = tailIter a r (forwardState α (k+r)) := by
  induction r generalizing k with
  | zero => simp
  | succ r ih =>
    have hd₀ : digit α (k+1) = a := by simpa using hd 0 (by omega)
    have hdr : ∀ i < r, digit α (k+1+i+1) = a := by
      intro i hi
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd (i+1) (by omega)
    rw [forwardState_recurrence hα k, hd₀, ih (k+1) hdr, tailIter_succ]
    simp only [prependDigit, tailMap, one_div]
    rw [show k+1+r=k+(r+1) by omega]

theorem forward_departure_mem {α : ℝ} (hα : Irrational α)
    {a : ℤ} (ha : 2 ≤ a) (k : ℕ) (e : Departure)
    (hd : DigitDeparture a (digit α (k+1)) e) :
    forwardState α k ∈ Set.Ioo (departureLeft a e) (departureRight a e) := by
  have ht₀ : 0 < forwardState α (k+1) := fract_completeQuotient_pos hα _
  have ht₁ : forwardState α (k+1) < 1 := Int.fract_lt_one _
  have hb : (1:ℝ) ≤ digit α (k+1) := by exact_mod_cast digit_succ_pos hα k
  have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha
  rw [forwardState_recurrence hα k]
  unfold prependDigit
  cases e with
  | low =>
    obtain ⟨_, hd⟩ := hd
    have hd' : (digit α (k+1) : ℝ) + 1 ≤ a := by exact_mod_cast hd
    constructor
    · dsimp [departureLeft]; rw [one_div]
      exact inv_lt_inv₀ (by linarith) (by linarith) |>.mpr (by linarith)
    · dsimp [departureRight]
      exact (inv_lt_one₀ (by linarith)).mpr (by linarith)
  | high =>
    have hd' : (a:ℝ)+1 ≤ digit α (k+1) := by exact_mod_cast hd
    constructor
    · dsimp [departureLeft]; positivity
    · dsimp [departureRight]; rw [one_div]
      exact inv_lt_inv₀ (by linarith) (by linarith) |>.mpr (by linarith)

/-- Exact future digits give an interior tail; rational closure endpoints are excluded. -/
theorem exactFutureRun_mem {α : ℝ} (hα : Irrational α) {a : ℤ} (ha : 2 ≤ a)
    {n r : ℕ} {e : Departure} (hr : ExactFutureRun α n a r e) :
    future α n ∈ runCell a r e := by
  obtain ⟨hd, hdep⟩ := hr
  have hdep' : DigitDeparture a (digit α (n+2+r+1)) e := by
    simpa only [show n+2+r+1=n+3+r by omega] using hdep
  have hm := forward_departure_mem hα ha (n+2+r) e hdep'
  refine ⟨forwardState α (n+2+r), ⟨hm.1.le, hm.2.le⟩, ?_⟩
  symm
  apply forwardState_run hα a (n+2) r
  intro i hi
  simpa only [show n+2+i+1=n+3+i by omega] using hd i hi

end ContinuedFractionBounds
