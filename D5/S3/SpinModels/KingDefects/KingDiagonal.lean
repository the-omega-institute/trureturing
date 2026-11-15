/- GID: D5/S3/SpinModels/KingDefects/KingDiagonal
   generality: G
   mirror-B: D5/B/S3/SpinModels/KingDefects/KingDiagonal
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Diagonal-defect slot classification and exact counts on king rectangles. -/
/-
admission_basis: escape-witness
escape_witness: diagonalSlotEquiv (the exact diagonal slot classification),
  diagonal_count (the exact count of compatible words).
The dimensions and word lengths are arbitrary. No bounded grid enumeration,
checker, numerical reduction or certified instance is asserted.
-/
import D5.S3.SpinModels.KingDefects.KingDifference

namespace D5.S3.SpinModels.KingDefects.KingDiagonal

open KingGrid KingDifference

private theorem klein_zero (x y : K) : x + y = 0 ↔ x = y := by
  simpa only [IsAddKleinFour.neg_eq_self] using
    (add_eq_zero_iff_eq_neg (a := x) (b := y))

private theorem klein_alphabet (x y t : K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x ≠ y) : t ≠ 0 ∧ t ≠ x ↔ t = y ∨ t = x + y := by
  have h : ∀ x y t : K, x ≠ 0 → y ≠ 0 → x ≠ y →
      (t ≠ 0 ∧ t ≠ x ↔ t = y ∨ t = x + y) := by decide
  exact h x y t hx hy hxy

/-- Four ordinary words, with the two split-slot values recorded separately. -/
structure DiagonalSlots {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M) where
  x : K
  y : K
  U : {i : Fin N // i < i₀} → K
  V : {i : Fin N // i₀ < i} → K
  C : {j : Fin M // j < j₀} → K
  D : {j : Fin M // j₀ < j} → K

/-- The four alphabets and every vertical-horizontal cross exclusion. -/
def SlotValid {N M : ℕ} {i₀ : Fin N} {j₀ : Fin M}
    (w : DiagonalSlots i₀ j₀) : Prop :=
  w.x ≠ 0 ∧ w.y ≠ 0 ∧ w.x ≠ w.y ∧
    (∀ i, w.U i = w.y ∨ w.U i = w.x + w.y) ∧
    (∀ i, w.V i = w.x ∨ w.V i = w.x + w.y) ∧
    (∀ j, w.C j = w.x ∨ w.C j = w.x + w.y) ∧
    (∀ j, w.D j = w.y ∨ w.D j = w.x + w.y) ∧
    (∀ i j, w.U i ≠ w.C j) ∧ (∀ i j, w.U i ≠ w.D j) ∧
    (∀ i j, w.V i ≠ w.C j) ∧ (∀ i j, w.V i ≠ w.D j)

/-- Fill each ordinary slot constantly and split the exceptional row and column. -/
def slotField {N M : ℕ} {i₀ : Fin N} {j₀ : Fin M}
    (w : DiagonalSlots i₀ j₀) : DiffField N M where
  h i j := if h : j < j₀ then w.C ⟨j,h⟩ else
    if h : j₀ < j then w.D ⟨j,h⟩ else if i.val ≤ i₀.val then w.x else w.y
  v i j := if h : i < i₀ then w.U ⟨i,h⟩ else
    if h : i₀ < i then w.V ⟨i,h⟩ else if j.val ≤ j₀.val then w.y else w.x

private theorem diagonal_clear {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M)
    (i : Fin N) (j : Fin M) (h : i ≠ i₀ ∨ j ≠ j₀) :
    BlockAvoids (.D i₀ j₀) i j := by
  simpa [BlockAvoids, not_and_or] using h

private theorem special_block {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M)
    (s : DiffField N M) (hs : RawAdmissible (.D i₀ j₀) s) :
    s.h i₀.castSucc j₀ ≠ 0 ∧ s.h i₀.succ j₀ ≠ 0 ∧
    s.h i₀.castSucc j₀ ≠ s.h i₀.succ j₀ ∧
    s.v i₀ j₀.castSucc = s.h i₀.succ j₀ ∧
    s.v i₀ j₀.succ = s.h i₀.castSucc j₀ := by
  have hd := (hs.2 (.D i₀ j₀)).mpr rfl
  change s.h i₀.castSucc j₀ + s.v i₀ j₀.succ = 0 at hd
  have hr := (klein_zero _ _).mp hd
  have hc := hs.1 i₀ j₀
  rw [hd] at hc
  have hl := (klein_zero _ _).mp hc.symm
  have nz (d : Edge (N + 1) (M + 1)) (hne : d ≠ .D i₀ j₀) :
      edgeValue s d ≠ 0 := mt (hs.2 d).mp hne
  have hx := nz (.H i₀.castSucc j₀) (by simp)
  have hy := nz (.H i₀.succ j₀) (by simp)
  have ha := nz (.A i₀ j₀) (by simp)
  change s.h i₀.castSucc j₀ + s.v i₀ j₀.castSucc ≠ 0 at ha
  rw [hl] at ha
  exact ⟨hx,hy,fun h => ha ((klein_zero _ _).mpr h),hl,hr.symm⟩

private theorem raw_h_ordinary {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M)
    (s : DiffField N M) (hs : RawAdmissible (.D i₀ j₀) s)
    (j : Fin M) (hj : j ≠ j₀) (r : Fin (N + 1)) : s.h r j = s.h 0 j := by
  symm
  exact horizontal_slot_eq _ s hs j 0 r (Fin.zero_le _) (fun i _ _ =>
    diagonal_clear i₀ j₀ i j (Or.inr hj))

private theorem raw_v_ordinary {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M)
    (s : DiffField N M) (hs : RawAdmissible (.D i₀ j₀) s)
    (i : Fin N) (hi : i ≠ i₀) (r : Fin (M + 1)) : s.v i r = s.v i 0 := by
  symm
  exact vertical_slot_eq _ s hs i 0 r (Fin.zero_le _) (fun j _ _ =>
    diagonal_clear i₀ j₀ i j (Or.inl hi))

private theorem raw_h_special {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M)
    (s : DiffField N M) (hs : RawAdmissible (.D i₀ j₀) s)
    (r : Fin (N + 1)) : s.h r j₀ =
      if r.val ≤ i₀.val then s.h i₀.castSucc j₀ else s.h i₀.succ j₀ := by
  split_ifs with h
  · apply horizontal_slot_eq _ s hs j₀ r i₀.castSucc h
    intro i _ hi
    apply diagonal_clear i₀ j₀ i j₀
    left
    intro he
    subst i
    exact (Nat.lt_irrefl _) hi
  · symm
    apply horizontal_slot_eq _ s hs j₀ i₀.succ r (by
      change i₀.val + 1 ≤ r.val
      omega)
    intro i hi _
    apply diagonal_clear i₀ j₀ i j₀
    left
    intro he
    subst i
    change i₀.val + 1 ≤ i₀.val at hi
    omega

private theorem raw_v_special {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M)
    (s : DiffField N M) (hs : RawAdmissible (.D i₀ j₀) s)
    (r : Fin (M + 1)) : s.v i₀ r =
      if r.val ≤ j₀.val then s.v i₀ j₀.castSucc else s.v i₀ j₀.succ := by
  split_ifs with h
  · apply vertical_slot_eq _ s hs i₀ r j₀.castSucc h
    intro j _ hj
    apply diagonal_clear i₀ j₀ i₀ j
    right
    intro he
    subst j
    exact (Nat.lt_irrefl _) hj
  · symm
    apply vertical_slot_eq _ s hs i₀ j₀.succ r (by
      change j₀.val + 1 ≤ r.val
      omega)
    intro j hj _
    apply diagonal_clear i₀ j₀ i₀ j
    right
    intro he
    subst j
    change j₀.val + 1 ≤ j₀.val at hj
    omega

/-- Read ordinary slots on the coordinate axes and the split horizontal values locally. -/
def extractSlots {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M)
    (s : DiffField N M) : DiagonalSlots i₀ j₀ where
  x := s.h i₀.castSucc j₀
  y := s.h i₀.succ j₀
  U i := s.v i.val 0
  V i := s.v i.val 0
  C j := s.h 0 j.val
  D j := s.h 0 j.val

private theorem slot_reconstruction {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M)
    (s : DiffField N M) (hs : RawAdmissible (.D i₀ j₀) s) :
    slotField (extractSlots i₀ j₀ s) = s := by
  apply DiffField.ext
  · funext i j
    dsimp [slotField, extractSlots]
    split_ifs with h₁ h₂
    · exact (raw_h_ordinary i₀ j₀ s hs j (ne_of_lt h₁) i).symm
    · exact (raw_h_ordinary i₀ j₀ s hs j (ne_of_gt h₂) i).symm
    · have hj : j = j₀ := le_antisymm (le_of_not_gt h₂) (le_of_not_gt h₁)
      subst j
      exact (raw_h_special i₀ j₀ s hs i).symm
  · funext i j
    dsimp [slotField, extractSlots]
    split_ifs with h₁ h₂
    · exact (raw_v_ordinary i₀ j₀ s hs i (ne_of_lt h₁) j).symm
    · exact (raw_v_ordinary i₀ j₀ s hs i (ne_of_gt h₂) j).symm
    · have hi : i = i₀ := le_antisymm (le_of_not_gt h₂) (le_of_not_gt h₁)
      subst i
      have he := special_block i₀ j₀ s hs
      rw [raw_v_special i₀ j₀ s hs j, he.2.2.2.1, he.2.2.2.2]

private theorem extract_slotField {N M : ℕ} {i₀ : Fin N} {j₀ : Fin M}
    (w : DiagonalSlots i₀ j₀) : extractSlots i₀ j₀ (slotField w) = w := by
  cases w
  simp only [extractSlots, slotField, lt_self_iff_false, dite_false, Fin.val_castSucc,
    le_refl, ite_true, Fin.val_succ, Nat.add_one_le_iff, ite_false]
  congr 1 <;> funext i <;> simp [i.property, not_lt_of_ge (le_of_lt i.property),
    not_lt_of_ge (le_of_lt i.property).le]

private theorem extract_valid {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M)
    (s : DiffField N M) (hs : RawAdmissible (.D i₀ j₀) s) :
    SlotValid (extractSlots i₀ j₀ s) := by
  obtain ⟨hx,hy,hxy,hl,hr⟩ := special_block i₀ j₀ s hs
  have good (i : Fin N) (j : Fin M) (h : i ≠ i₀ ∨ j ≠ j₀) :=
    goodBlock_of_raw (.D i₀ j₀) s hs i j (diagonal_clear i₀ j₀ i j h)
  refine ⟨hx,hy,hxy,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    have h := good i.val j₀ (Or.inl (ne_of_lt i.property))
    rw [raw_h_special i₀ j₀ s hs i.val.castSucc,
      raw_v_ordinary i₀ j₀ s hs i.val (ne_of_lt i.property) j₀.castSucc] at h
    simp only [Fin.val_castSucc, if_pos (le_of_lt i.property)] at h
    exact (klein_alphabet _ _ _ hx hy hxy).mp ⟨h.2.2.2.1, h.2.2.2.2.symm⟩
  · intro i
    have h := good i.val j₀ (Or.inl (ne_of_gt i.property))
    rw [raw_h_special i₀ j₀ s hs i.val.castSucc,
      raw_v_ordinary i₀ j₀ s hs i.val (ne_of_gt i.property) j₀.castSucc] at h
    simp only [Fin.val_castSucc, if_neg (not_le_of_gt i.property)] at h
    simpa only [extractSlots, add_comm] using
      (klein_alphabet _ _ _ hy hx hxy.symm).mp ⟨h.2.2.2.1, h.2.2.2.2.symm⟩
  · intro j
    have h := good i₀ j.val (Or.inr (ne_of_lt j.property))
    rw [raw_h_ordinary i₀ j₀ s hs j.val (ne_of_lt j.property) i₀.castSucc,
      raw_v_special i₀ j₀ s hs j.val.castSucc] at h
    simp only [Fin.val_castSucc, if_pos (le_of_lt j.property), hl] at h
    simpa only [extractSlots, add_comm] using
      (klein_alphabet _ _ _ hy hx hxy.symm).mp ⟨h.2.2.1, h.2.2.2.2⟩
  · intro j
    have h := good i₀ j.val (Or.inr (ne_of_gt j.property))
    rw [raw_h_ordinary i₀ j₀ s hs j.val (ne_of_gt j.property) i₀.castSucc,
      raw_v_special i₀ j₀ s hs j.val.castSucc] at h
    simp only [Fin.val_castSucc, if_neg (not_le_of_gt j.property), hr] at h
    exact (klein_alphabet _ _ _ hx hy hxy).mp ⟨h.2.2.1, h.2.2.2.2⟩
  all_goals
    intro i j
    have hi : i.val ≠ i₀ := ne_of_lt i.property <|> exact ne_of_gt i.property
    have hj : j.val ≠ j₀ := ne_of_lt j.property <|> exact ne_of_gt j.property
    have h := good i.val j.val (Or.inl hi)
    rw [raw_h_ordinary i₀ j₀ s hs j.val hj i.val.castSucc,
      raw_v_ordinary i₀ j₀ s hs i.val hi j.val.castSucc] at h
    exact h.2.2.2.2.symm

private theorem slot_good {N M : ℕ} {i₀ : Fin N} {j₀ : Fin M}
    (w : DiagonalSlots i₀ j₀) (hw : SlotValid w)
    (i : Fin N) (j : Fin M) (h : i ≠ i₀ ∨ j ≠ j₀) :
    (slotField w).h i.castSucc j = (slotField w).h i.succ j ∧
    (slotField w).v i j.castSucc = (slotField w).v i j.succ ∧
    (slotField w).h i.castSucc j ≠ 0 ∧ (slotField w).v i j.castSucc ≠ 0 ∧
    (slotField w).h i.castSucc j ≠ (slotField w).v i j.castSucc := by
  obtain ⟨hx,hy,hxy,hU,hV,hC,hD,hUC,hUD,hVC,hVD⟩ := hw
  have hU' (i) := (klein_alphabet _ _ _ hx hy hxy).mpr (hU i)
  have hV' (i) : w.V i ≠ 0 ∧ w.V i ≠ w.y :=
    (klein_alphabet _ _ _ hy hx hxy.symm).mpr (by simpa [add_comm] using hV i)
  have hC' (j) : w.C j ≠ 0 ∧ w.C j ≠ w.y :=
    (klein_alphabet _ _ _ hy hx hxy.symm).mpr (by simpa [add_comm] using hC j)
  have hD' (j) := (klein_alphabet _ _ _ hx hy hxy).mpr (hD j)
  have hi : i.val < i₀.val ∨ i = i₀ ∨ i₀.val < i.val := by
    rcases lt_trichotomy i i₀ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hj : j.val < j₀.val ∨ j = j₀ ∨ j₀.val < j.val := by
    rcases lt_trichotomy j j₀ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rcases hi with hi | rfl | hi <;> rcases hj with hj | rfl | hj
  all_goals simp only [slotField, Fin.val_castSucc, Fin.val_succ]
  all_goals simp_all [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val,
    show ∀ a b : ℕ, a < b → ¬ b < a by omega,
    show ∀ a b : ℕ, a < b → a + 1 ≤ b by omega,
    show ∀ a b : ℕ, a < b → ¬ b + 1 ≤ a by omega]

private theorem slot_special {N M : ℕ} {i₀ : Fin N} {j₀ : Fin M}
    (w : DiagonalSlots i₀ j₀) :
    (slotField w).h i₀.castSucc j₀ = w.x ∧
    (slotField w).h i₀.succ j₀ = w.y ∧
    (slotField w).v i₀ j₀.castSucc = w.y ∧
    (slotField w).v i₀ j₀.succ = w.x := by simp [slotField]

private theorem slot_raw {N M : ℕ} {i₀ : Fin N} {j₀ : Fin M}
    (w : DiagonalSlots i₀ j₀) (hw : SlotValid w) :
    RawAdmissible (.D i₀ j₀) (slotField w) := by
  have hz : w.x + w.y ≠ 0 := mt (klein_zero _ _).mp hw.2.2.1
  have hnU (i) : w.U i ≠ 0 := by rcases hw.2.2.2.1 i with h | h <;> rw [h]; exact hw.2.1; exact hz
  have hnV (i) : w.V i ≠ 0 := by rcases hw.2.2.2.2.1 i with h | h <;> rw [h]; exact hw.1; exact hz
  have hnC (j) : w.C j ≠ 0 := by rcases hw.2.2.2.2.2.1 j with h | h <;> rw [h]; exact hw.1; exact hz
  have hnD (j) : w.D j ≠ 0 := by rcases hw.2.2.2.2.2.2.1 j with h | h <;> rw [h]; exact hw.2.1; exact hz
  have hs := slot_special w
  have self (x : K) : x + x = 0 := IsAddKleinFour.add_self x
  constructor
  · intro i j
    by_cases he : i = i₀ ∧ j = j₀
    · rcases he with ⟨rfl,rfl⟩
      simp only [hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,self]
    · have h := slot_good w hw i j (not_and_or.mp he)
      rw [← h.1, ← h.2.1]
      exact add_comm _ _
  · intro e
    cases e with
    | H i j =>
      have hn : (slotField w).h i j ≠ 0 := by
        dsimp [slotField]
        split_ifs <;> first | apply hnC | apply hnD | exact hw.1 | exact hw.2.1
      simp [edgeValue, hn]
    | V i j =>
      have hn : (slotField w).v i j ≠ 0 := by
        dsimp [slotField]
        split_ifs <;> first | apply hnU | apply hnV | exact hw.1 | exact hw.2.1
      simp [edgeValue, hn]
    | D i j =>
      by_cases he : i = i₀ ∧ j = j₀
      · rcases he with ⟨rfl,rfl⟩
        simp [edgeValue, hs.1, hs.2.2.2, self]
      · have h := slot_good w hw i j (not_and_or.mp he)
        have hn : edgeValue (slotField w) (.D i j) ≠ 0 := by
          dsimp [edgeValue]
          rw [← h.2.1]
          exact mt (klein_zero _ _).mp h.2.2.2.2
        simp [hn, he]
    | A i j =>
      have hn : edgeValue (slotField w) (.A i j) ≠ 0 := by
        by_cases he : i = i₀ ∧ j = j₀
        · rcases he with ⟨rfl,rfl⟩
          simpa only [edgeValue, hs.1, hs.2.2.1] using hz
        · have h := slot_good w hw i j (not_and_or.mp he)
          exact mt (klein_zero _ _).mp h.2.2.2.2
      simp [hn]

/-- Exact classification by an ordered nonzero unequal pair and four compatible words. -/
def diagonalSlotEquiv {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M) :
    {s : DiffField N M // RawAdmissible (.D i₀ j₀) s} ≃
      {w : DiagonalSlots i₀ j₀ // SlotValid w} where
  toFun s := ⟨extractSlots i₀ j₀ s.val, extract_valid i₀ j₀ s.val s.property⟩
  invFun w := ⟨slotField w.val, slot_raw w.val w.property⟩
  left_inv s := Subtype.ext (slot_reconstruction i₀ j₀ s.val s.property)
  right_inv w := Subtype.ext (extract_slotField w.val)

#print axioms diagonalSlotEquiv

end D5.S3.SpinModels.KingDefects.KingDiagonal
