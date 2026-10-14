module

public import ContinuedFractionBounds.FiberProfiles
public import ContinuedFractionBounds.DigitWindows

/-! # Sharp thresholds for constant-digit windows -/

@[expose] public section
namespace ContinuedFractionBounds

/-- Exact lower-envelope supremum outside the open target square. -/
noncomputable def sharpLowerWindowThreshold (a L U : ℝ) : ℝ :=
  max (lowerProfile a L) (lowerProfile a U)

/-- Exact upper-envelope infimum outside the open target square. -/
noncomputable def sharpUpperWindowThreshold (a L U : ℝ) : ℝ :=
  min (upperProfile a L) (upperProfile a U)

/-- A sharp lower cutoff is attained with the second coordinate at a target endpoint. -/
theorem sharpLowerWindowThreshold_witness {a L U : ℝ} (ha : 2 ≤ a)
    (hL : L ∈ Set.Icc (0:ℝ) 1) (hU : U ∈ Set.Icc (0:ℝ) 1) :
    ∃ t, (t = L ∨ t = U) ∧ ∃ x ∈ Set.Icc (0:ℝ) 1,
      lower a x t = sharpLowerWindowThreshold a L U := by
  rcases le_total (lowerProfile a L) (lowerProfile a U) with h | h
  · have hp := lowerProfile_optimal ha hU.1 hU.2
    refine ⟨U, Or.inr rfl, lowerProfileWitness a U, hp.1, ?_⟩
    rw [lower_comm, hp.2.1, sharpLowerWindowThreshold, max_eq_right h]
  · have hp := lowerProfile_optimal ha hL.1 hL.2
    refine ⟨L, Or.inl rfl, lowerProfileWitness a L, hp.1, ?_⟩
    rw [lower_comm, hp.2.1, sharpLowerWindowThreshold, max_eq_left h]

/-- A sharp upper cutoff is attained with the second coordinate at a target endpoint. -/
theorem sharpUpperWindowThreshold_witness {a L U : ℝ} (ha : 2 ≤ a)
    (hL : L ∈ Set.Icc (0:ℝ) 1) (hU : U ∈ Set.Icc (0:ℝ) 1) :
    ∃ t, (t = L ∨ t = U) ∧ ∃ x ∈ Set.Icc (0:ℝ) 1,
      upper a x t = sharpUpperWindowThreshold a L U := by
  rcases le_total (upperProfile a L) (upperProfile a U) with h | h
  · have hp := upperProfile_optimal ha hL.1 hL.2
    refine ⟨L, Or.inl rfl, upperProfileWitness a L, hp.1, ?_⟩
    rw [upper_comm, hp.2.1, sharpUpperWindowThreshold, min_eq_left h]
  · have hp := upperProfile_optimal ha hU.1 hU.2
    refine ⟨U, Or.inr rfl, upperProfileWitness a U, hp.1, ?_⟩
    rw [upper_comm, hp.2.1, sharpUpperWindowThreshold, min_eq_right h]

lemma constantLower_pos {a : ℝ} (ha : 1 < a) {r : ℕ} (hr : 0 < r) :
    0 < constantLower a r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have h0 := tailMap_mem_unit ha (tailIter_mem_unit ha k (by norm_num : (0:ℝ) ∈ Set.Icc 0 1))
  have h1 := tailMap_mem_unit ha (tailIter_mem_unit ha k (by norm_num : (1:ℝ) ∈ Set.Icc 0 1))
  simpa only [constantLower, tailIter_succ, lt_min_iff] using And.intro h0.1 h1.1

lemma constantUpper_lt_one {a : ℝ} (ha : 1 < a) {r : ℕ} (hr : 0 < r) :
    constantUpper a r < 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have h0 := tailMap_mem_unit ha (tailIter_mem_unit ha k (by norm_num : (0:ℝ) ∈ Set.Icc 0 1))
  have h1 := tailMap_mem_unit ha (tailIter_mem_unit ha k (by norm_num : (1:ℝ) ∈ Set.Icc 0 1))
  simpa only [constantUpper, tailIter_succ, max_lt_iff] using And.intro h0.2 h1.2

/-- Endpoint profile bounds control every coordinate outside the target interval. -/
lemma profiles_le_window_of_outside {a L U t : ℝ} (ha : 2 ≤ a)
    (hL : 0 ≤ L) (hLb : L ≤ metallic a) (hbU : metallic a ≤ U) (_hU : U ≤ 1)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hout : t ∉ Set.Ioo L U) :
    lowerProfile a t ≤ sharpLowerWindowThreshold a L U ∧
      sharpUpperWindowThreshold a L U ≤ upperProfile a t := by
  have hout' : t ≤ L ∨ U ≤ t := by
    by_cases hl : L < t
    · exact Or.inr (le_of_not_gt (fun hu => hout ⟨hl,hu⟩))
    · exact Or.inl (le_of_not_gt hl)
  rcases hout' with hl | hu
  · have hlo : lowerProfile a t ≤ lowerProfile a L := by
      rcases lt_or_eq_of_le hl with h | rfl
      · exact (lowerProfile_strictMono_below ha ht.1 h hLb).le
      · exact le_rfl
    have hup : upperProfile a L ≤ upperProfile a t := by
      rcases lt_or_eq_of_le hl with h | rfl
      · exact (upperProfile_strictAnti_below ha ht.1 h hLb).le
      · exact le_rfl
    exact ⟨hlo.trans (le_max_left _ _), (min_le_left _ _).trans hup⟩
  · have hlo : lowerProfile a t ≤ lowerProfile a U := by
      rcases lt_or_eq_of_le hu with h | rfl
      · exact (lowerProfile_strictAnti_above ha hbU h ht.2).le
      · exact le_rfl
    have hup : upperProfile a U ≤ upperProfile a t := by
      rcases lt_or_eq_of_le hu with h | rfl
      · exact (upperProfile_strictMono_above ha hbU h ht.2).le
      · exact le_rfl
    exact ⟨hlo.trans (le_max_right _ _), (min_le_right _ _).trans hup⟩

/-- Sharp two-endpoint bounds on the complement of an open target square. -/
theorem sharp_window_complement_bounds {a L U x y : ℝ} (ha : 2 ≤ a)
    (hL : 0 ≤ L) (hLb : L ≤ metallic a) (hbU : metallic a ≤ U) (hU : U ≤ 1)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hout : ¬(x ∈ Set.Ioo L U ∧ y ∈ Set.Ioo L U)) :
    lower a x y ≤ sharpLowerWindowThreshold a L U ∧
      sharpUpperWindowThreshold a L U ≤ upper a x y := by
  by_cases hxi : x ∈ Set.Ioo L U
  · have hyi : y ∉ Set.Ioo L U := fun h => hout ⟨hxi,h⟩
    have hp := profiles_le_window_of_outside ha hL hLb hbU hU hy hyi
    have hlo := ((lowerProfile_optimal ha hy.1 hy.2).2.2 x hx).1
    have hup := ((upperProfile_optimal ha hy.1 hy.2).2.2 x hx).1
    rw [lower_comm, upper_comm]
    exact ⟨hlo.trans hp.1, hp.2.trans hup⟩
  · have hp := profiles_le_window_of_outside ha hL hLb hbU hU hx hxi
    exact ⟨((lowerProfile_optimal ha hx.1 hx.2).2.2 y hy).1.trans hp.1,
      hp.2.trans ((upperProfile_optimal ha hx.1 hx.2).2.2 y hy).1⟩

/-- Both sharp square bounds are attained on its complement. -/
theorem sharp_window_complement_attainment {a L U : ℝ} (ha : 2 ≤ a)
    (hL : L ∈ Set.Icc (0:ℝ) 1) (hU : U ∈ Set.Icc (0:ℝ) 1) :
    (∃ x ∈ Set.Icc (0:ℝ) 1, ∃ y ∈ Set.Icc (0:ℝ) 1,
      ¬(x ∈ Set.Ioo L U ∧ y ∈ Set.Ioo L U) ∧
      lower a x y = sharpLowerWindowThreshold a L U) ∧
    (∃ x ∈ Set.Icc (0:ℝ) 1, ∃ y ∈ Set.Icc (0:ℝ) 1,
      ¬(x ∈ Set.Ioo L U ∧ y ∈ Set.Ioo L U) ∧
      upper a x y = sharpUpperWindowThreshold a L U) := by
  constructor
  · obtain ⟨t,ht,x,hx,he⟩ := sharpLowerWindowThreshold_witness ha hL hU
    refine ⟨x,hx,t,?_,?_,he⟩
    · rcases ht with rfl | rfl <;> assumption
    · rintro ⟨_,hy⟩
      rcases ht with rfl | rfl
      · exact (lt_irrefl _) hy.1
      · exact (lt_irrefl _) hy.2
  · obtain ⟨t,ht,x,hx,he⟩ := sharpUpperWindowThreshold_witness ha hL hU
    refine ⟨x,hx,t,?_,?_,he⟩
    · rcases ht with rfl | rfl <;> assumption
    · rintro ⟨_,hy⟩
      rcases ht with rfl | rfl
      · exact (lt_irrefl _) hy.1
      · exact (lt_irrefl _) hy.2

/-- Exceeding either sharp threshold forces both coordinates into the open target square. -/
theorem sharp_window_forcing {a L U x y : ℝ} (ha : 2 ≤ a)
    (hL : 0 ≤ L) (hLb : L ≤ metallic a) (hbU : metallic a ≤ U) (hU : U ≤ 1)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hsharp : sharpLowerWindowThreshold a L U < lower a x y ∨
      upper a x y < sharpUpperWindowThreshold a L U) :
    x ∈ Set.Ioo L U ∧ y ∈ Set.Ioo L U := by
  by_contra hout
  have hb := sharp_window_complement_bounds ha hL hLb hbU hU hx hy hout
  rcases hsharp with h | h <;> linarith

/-- The lower sharp cutoff lies strictly below the metallic value. -/
theorem sharpLowerWindowThreshold_lt {a L U : ℝ} (ha : 2 ≤ a)
    (hL : 0 ≤ L) (hLb : L < metallic a) (hbU : metallic a < U) (hU : U ≤ 1) :
    sharpLowerWindowThreshold a L U < threshold a := by
  have hL1 := hLb.le.trans ((metallic_lt_one (by linarith : 1 ≤ a)).le)
  have hU0 := (metallic_pos a).le.trans hbU.le
  rw [sharpLowerWindowThreshold, max_lt_iff]
  constructor
  · have hp := lowerProfile_optimal ha hL hL1
    rw [← hp.2.1]
    exact lower_lt_threshold_of_ne (by linarith) hL hL1 hp.1.1 (ne_of_lt hLb)
  · have hp := lowerProfile_optimal ha hU0 hU
    rw [← hp.2.1]
    exact lower_lt_threshold_of_ne (by linarith) hU0 hU hp.1.1 (ne_of_gt hbU)

/-- The upper sharp cutoff lies strictly above the metallic value. -/
theorem threshold_lt_sharpUpperWindowThreshold {a L U : ℝ} (ha : 2 ≤ a)
    (hL : 0 ≤ L) (hLb : L < metallic a) (hbU : metallic a < U) (hU : U ≤ 1) :
    threshold a < sharpUpperWindowThreshold a L U := by
  have hL1 := hLb.le.trans ((metallic_lt_one (by linarith : 1 ≤ a)).le)
  have hU0 := (metallic_pos a).le.trans hbU.le
  rw [sharpUpperWindowThreshold, lt_min_iff]
  constructor
  · have hp := upperProfile_optimal ha hL hL1
    rw [← hp.2.1]
    exact threshold_lt_upper_of_ne (by linarith) hL hL1 hp.1.1 (ne_of_lt hLb)
  · have hp := upperProfile_optimal ha hU0 hU
    rw [← hp.2.1]
    exact threshold_lt_upper_of_ne (by linarith) hU0 hU hp.1.1 (ne_of_gt hbU)

/-- Lower cutoff for an asymmetric open target rectangle. -/
noncomputable def sharpLowerRectangleThreshold (a Lx Ux Ly Uy : ℝ) : ℝ :=
  max (sharpLowerWindowThreshold a Lx Ux) (sharpLowerWindowThreshold a Ly Uy)

/-- Upper cutoff for an asymmetric open target rectangle. -/
noncomputable def sharpUpperRectangleThreshold (a Lx Ux Ly Uy : ℝ) : ℝ :=
  min (sharpUpperWindowThreshold a Lx Ux) (sharpUpperWindowThreshold a Ly Uy)

/-- Four endpoint profile values give bounds on the complement of any open
rectangle whose two coordinate intervals contain the metallic point. -/
theorem sharp_rectangle_complement_bounds {a Lx Ux Ly Uy x y : ℝ} (ha : 2 ≤ a)
    (hLx : 0 ≤ Lx) (hLxb : Lx ≤ metallic a) (hbUx : metallic a ≤ Ux) (hUx : Ux ≤ 1)
    (hLy : 0 ≤ Ly) (hLyb : Ly ≤ metallic a) (hbUy : metallic a ≤ Uy) (hUy : Uy ≤ 1)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hout : ¬(x ∈ Set.Ioo Lx Ux ∧ y ∈ Set.Ioo Ly Uy)) :
    lower a x y ≤ sharpLowerRectangleThreshold a Lx Ux Ly Uy ∧
      sharpUpperRectangleThreshold a Lx Ux Ly Uy ≤ upper a x y := by
  by_cases hxi : x ∈ Set.Ioo Lx Ux
  · have hyi : y ∉ Set.Ioo Ly Uy := fun h => hout ⟨hxi,h⟩
    have hp := profiles_le_window_of_outside ha hLy hLyb hbUy hUy hy hyi
    have hlo := ((lowerProfile_optimal ha hy.1 hy.2).2.2 x hx).1
    have hup := ((upperProfile_optimal ha hy.1 hy.2).2.2 x hx).1
    rw [lower_comm, upper_comm]
    exact ⟨hlo.trans (hp.1.trans (le_max_right _ _)),
      (min_le_right _ _).trans (hp.2.trans hup)⟩
  · have hp := profiles_le_window_of_outside ha hLx hLxb hbUx hUx hx hxi
    exact ⟨((lowerProfile_optimal ha hx.1 hx.2).2.2 y hy).1.trans
        (hp.1.trans (le_max_left _ _)),
      (min_le_left _ _).trans (hp.2.trans ((upperProfile_optimal ha hx.1 hx.2).2.2 y hy).1)⟩

/-- Both bounds on the complement of an asymmetric open rectangle are attained. -/
theorem sharp_rectangle_complement_attainment {a Lx Ux Ly Uy : ℝ} (ha : 2 ≤ a)
    (hLx : Lx ∈ Set.Icc (0:ℝ) 1) (hUx : Ux ∈ Set.Icc (0:ℝ) 1)
    (hLy : Ly ∈ Set.Icc (0:ℝ) 1) (hUy : Uy ∈ Set.Icc (0:ℝ) 1) :
    (∃ x ∈ Set.Icc (0:ℝ) 1, ∃ y ∈ Set.Icc (0:ℝ) 1,
      ¬(x ∈ Set.Ioo Lx Ux ∧ y ∈ Set.Ioo Ly Uy) ∧
      lower a x y = sharpLowerRectangleThreshold a Lx Ux Ly Uy) ∧
    (∃ x ∈ Set.Icc (0:ℝ) 1, ∃ y ∈ Set.Icc (0:ℝ) 1,
      ¬(x ∈ Set.Ioo Lx Ux ∧ y ∈ Set.Ioo Ly Uy) ∧
      upper a x y = sharpUpperRectangleThreshold a Lx Ux Ly Uy) := by
  constructor
  · rcases le_total (sharpLowerWindowThreshold a Lx Ux)
      (sharpLowerWindowThreshold a Ly Uy) with h | h
    · obtain ⟨t,ht,x,hx,he⟩ := sharpLowerWindowThreshold_witness ha hLy hUy
      refine ⟨x,hx,t,?_,?_,?_⟩
      · rcases ht with rfl | rfl <;> assumption
      · rintro ⟨_,hy⟩
        rcases ht with rfl | rfl
        · exact (lt_irrefl _) hy.1
        · exact (lt_irrefl _) hy.2
      · simpa only [sharpLowerRectangleThreshold, max_eq_right h] using he
    · obtain ⟨t,ht,y,hy,he⟩ := sharpLowerWindowThreshold_witness ha hLx hUx
      refine ⟨t,?_,y,hy,?_,?_⟩
      · rcases ht with rfl | rfl <;> assumption
      · rintro ⟨hx,_⟩
        rcases ht with rfl | rfl
        · exact (lt_irrefl _) hx.1
        · exact (lt_irrefl _) hx.2
      · simpa only [sharpLowerRectangleThreshold, max_eq_left h, lower_comm] using he
  · rcases le_total (sharpUpperWindowThreshold a Lx Ux)
      (sharpUpperWindowThreshold a Ly Uy) with h | h
    · obtain ⟨t,ht,y,hy,he⟩ := sharpUpperWindowThreshold_witness ha hLx hUx
      refine ⟨t,?_,y,hy,?_,?_⟩
      · rcases ht with rfl | rfl <;> assumption
      · rintro ⟨hx,_⟩
        rcases ht with rfl | rfl
        · exact (lt_irrefl _) hx.1
        · exact (lt_irrefl _) hx.2
      · simpa only [sharpUpperRectangleThreshold, min_eq_left h, upper_comm] using he
    · obtain ⟨t,ht,x,hx,he⟩ := sharpUpperWindowThreshold_witness ha hLy hUy
      refine ⟨x,hx,t,?_,?_,?_⟩
      · rcases ht with rfl | rfl <;> assumption
      · rintro ⟨_,hy⟩
        rcases ht with rfl | rfl
        · exact (lt_irrefl _) hy.1
        · exact (lt_irrefl _) hy.2
      · simpa only [sharpUpperRectangleThreshold, min_eq_right h] using he

theorem sharp_rectangle_forcing {a Lx Ux Ly Uy x y : ℝ} (ha : 2 ≤ a)
    (hLx : 0 ≤ Lx) (hLxb : Lx ≤ metallic a) (hbUx : metallic a ≤ Ux) (hUx : Ux ≤ 1)
    (hLy : 0 ≤ Ly) (hLyb : Ly ≤ metallic a) (hbUy : metallic a ≤ Uy) (hUy : Uy ≤ 1)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hsharp : sharpLowerRectangleThreshold a Lx Ux Ly Uy < lower a x y ∨
      upper a x y < sharpUpperRectangleThreshold a Lx Ux Ly Uy) :
    x ∈ Set.Ioo Lx Ux ∧ y ∈ Set.Ioo Ly Uy := by
  by_contra hout
  have hb := sharp_rectangle_complement_bounds ha hLx hLxb hbUx hUx
    hLy hLyb hbUy hUy hx hy hout
  rcases hsharp with h | h <;> linarith

/-- Sharp lower coefficient cutoff for a constant-digit cylinder. -/
noncomputable def sharpLowerDigitThreshold (a : ℝ) (r : ℕ) : ℝ :=
  sharpLowerWindowThreshold a (constantLower a r) (constantUpper a r)

/-- Sharp upper coefficient cutoff for a constant-digit cylinder. -/
noncomputable def sharpUpperDigitThreshold (a : ℝ) (r : ℕ) : ℝ :=
  sharpUpperWindowThreshold a (constantLower a r) (constantUpper a r)

lemma constant_window_bounds {a : ℝ} (ha : 1 < a) (r : ℕ) :
    0 ≤ constantLower a r ∧ constantLower a r < metallic a ∧
      metallic a < constantUpper a r ∧ constantUpper a r ≤ 1 := by
  have h0 := tailIter_mem_unit ha r (by norm_num : (0:ℝ) ∈ Set.Icc 0 1)
  have h1 := tailIter_mem_unit ha r (by norm_num : (1:ℝ) ∈ Set.Icc 0 1)
  have hb := metallic_mem_constant_interior ha r
  rw [constantCell_eq_Icc ha, interior_Icc] at hb
  exact ⟨le_min h0.1 h1.1, hb.1, hb.2, max_le h0.2 h1.2⟩

/-- Either sharp coefficient inequality forces independent past and future
constant-digit windows. The past cannot be exhausted; the future length has no
restriction involving the convergent index. -/
theorem sharp_window_digit_window {α : ℝ} {a : ℤ} (hα : Irrational α)
    (ha : 2 ≤ a) (n r s : ℕ) (hd : digit α (n+2) = a)
    (hsharp : max (sharpLowerDigitThreshold a r) (sharpLowerDigitThreshold a s) <
        minimumTriple α n ∨
      maximumTriple α n < min (sharpUpperDigitThreshold a r) (sharpUpperDigitThreshold a s)) :
    r < n+1 ∧ (∀ i < r, digit α (n+1-i) = a) ∧
      (∀ i < s, digit α (n+3+i) = a) := by
  have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha
  have ha1 : (1:ℝ) < a := by linarith
  have hx := past_mem hα n
  have hy := future_mem hα n
  have hr := constant_window_bounds ha1 r
  have hs := constant_window_bounds ha1 s
  rw [actual_minimum_eq hα n, actual_maximum_eq hα n, hd] at hsharp
  have hp := sharp_rectangle_forcing ha' hr.1 hr.2.1.le hr.2.2.1.le hr.2.2.2
    hs.1 hs.2.1.le hs.2.2.1.le hs.2.2.2 ⟨hx.1.le,hx.2⟩ ⟨hy.1.le,hy.2.le⟩ hsharp
  have hpr : past α n ∈ interior (constantCell a r) := by
    rw [constantCell_eq_Icc ha1, interior_Icc]
    exact hp.1
  have hps : future α n ∈ interior (constantCell a s) := by
    rw [constantCell_eq_Icc ha1, interior_Icc]
    exact hp.2
  obtain ⟨u,hu,he⟩ := constant_interior_preimage ha1 r hpr
  obtain ⟨v,hv,he'⟩ := constant_interior_preimage ha1 s hps
  rw [← backwardState_eq_past hα n] at he
  have hback := backward_digits_of_constant_prefix hα ha r (n+1) hu he
  have hfor := forward_digits_of_constant_prefix hα ha s (n+2) hv he'
  refine ⟨hback.1,hback.2,?_⟩
  intro i hi
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hfor i hi

/-- Symmetric specialization with the exact two-endpoint cutoffs. -/
theorem sharp_symmetric_digit_window {α : ℝ} {a : ℤ} (hα : Irrational α)
    (ha : 2 ≤ a) (n r : ℕ) (hd : digit α (n+2) = a)
    (hsharp : sharpLowerDigitThreshold a r < minimumTriple α n ∨
      maximumTriple α n < sharpUpperDigitThreshold a r) :
    r < n+1 ∧ (∀ i < r, digit α (n+1-i) = a) ∧
      (∀ i < r, digit α (n+3+i) = a) := by
  apply sharp_window_digit_window hα ha n r r hd
  simpa only [max_self,min_self] using hsharp

lemma silver_metallic_window_bounds : (7:ℝ)/17 < metallic 2 ∧ metallic 2 < 5/12 := by
  have hb := metallic_pos 2
  have he := metallic_equation 2
  constructor
  · by_contra h
    have hle : metallic 2 ≤ (7:ℝ)/17 := le_of_not_gt h
    have hs := mul_self_le_mul_self hb.le hle
    nlinarith
  · by_contra h
    have hle : (5:ℝ)/12 ≤ metallic 2 := le_of_not_gt h
    have hs := mul_self_le_mul_self (by norm_num : (0:ℝ)≤5/12) hle
    nlinarith

/-- Exact silver cylinder and sharp cutoffs for one required digit. -/
theorem silver_sharp_window_one :
    sharpLowerDigitThreshold 2 1 = 10/29 ∧ sharpUpperDigitThreshold 2 1 = 21/58 := by
  have hb := silver_metallic_window_bounds
  have hlow : (1:ℝ)/3 ≤ metallic 2 := by linarith
  have hhigh : ¬ (1:ℝ)/2 ≤ metallic 2 := by linarith
  norm_num [sharpLowerDigitThreshold,sharpUpperDigitThreshold,
    sharpLowerWindowThreshold,sharpUpperWindowThreshold,constantLower,constantUpper,
    tailIter,tailMap,lowerProfile,upperProfile,hlow,hhigh]

/-- Exact silver cylinder and sharp cutoffs for two required digits. -/
theorem silver_sharp_window_two :
    sharpLowerDigitThreshold 2 2 = 119/338 ∧ sharpUpperDigitThreshold 2 2 = 60/169 := by
  have hb := silver_metallic_window_bounds
  have hlow : (2:ℝ)/5 ≤ metallic 2 := by linarith
  have hhigh : ¬ (3:ℝ)/7 ≤ metallic 2 := by linarith
  norm_num [sharpLowerDigitThreshold,sharpUpperDigitThreshold,
    sharpLowerWindowThreshold,sharpUpperWindowThreshold,constantLower,constantUpper,
    tailIter,tailMap,Function.iterate_succ_apply,lowerProfile,upperProfile,hlow,hhigh]

/-- Exact silver cylinder and sharp cutoffs for three required digits. -/
theorem silver_sharp_window_three :
    sharpLowerDigitThreshold 2 3 = 348/985 ∧ sharpUpperDigitThreshold 2 3 = 697/1970 := by
  have hb := silver_metallic_window_bounds
  have hlow : (7:ℝ)/17 ≤ metallic 2 := hb.1.le
  have hhigh : ¬ (5:ℝ)/12 ≤ metallic 2 := not_le.mpr hb.2
  norm_num [sharpLowerDigitThreshold,sharpUpperDigitThreshold,
    sharpLowerWindowThreshold,sharpUpperWindowThreshold,constantLower,constantUpper,
    tailIter,tailMap,Function.iterate_succ_apply,lowerProfile,upperProfile,hlow,hhigh]

end ContinuedFractionBounds
