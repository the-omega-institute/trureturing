/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/KingDiagonal
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/KingDiagonal
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Diagonal-defect slot classification and exact counts on king rectangles. -/
/-
admission_basis: open-problem-resolution (#30641; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229571.result, HardinA229573.result, HardinA229574.result, HardinA229575.result, HardinA229576.result, HardinA229577.result, HardinA229578.result)
klein_alphabet: proof_shape=bind-only; consumers=KingDiagonal.extract_valid,KingDiagonal.slot_good
DiagonalSlots: proof_shape=bind-only; consumers=KingDiagonal.SlotValid,KingDiagonal.diagonalSlotEquiv,KingDiagonal.diagonal_count,KingDiagonal.extractSlots,KingDiagonal.extract_slotField,KingDiagonal.extract_valid,KingDiagonal.normalizedEquiv,KingDiagonal.normalizedSlots,KingDiagonal.normalized_recover,KingDiagonal.normalized_valid,KingDiagonal.slotField,KingDiagonal.slot_good,KingDiagonal.slot_raw,KingDiagonal.slot_special,KingDiagonal.slotsWord,KingDiagonal.word_recover
SlotValid: proof_shape=bind-only; consumers=KingDiagonal.diagonalSlotEquiv,KingDiagonal.diagonal_count,KingDiagonal.extract_valid,KingDiagonal.normalizedEquiv,KingDiagonal.normalized_recover,KingDiagonal.normalized_valid,KingDiagonal.slot_good,KingDiagonal.slot_raw
slotField: proof_shape=bind-only; consumers=KingDiagonal.diagonalSlotEquiv,KingDiagonal.extract_slotField,KingDiagonal.slot_good,KingDiagonal.slot_raw,KingDiagonal.slot_reconstruction,KingDiagonal.slot_special
diagonal_clear: proof_shape=bind-only; consumers=KingDiagonal.extract_valid,KingDiagonal.raw_h_ordinary,KingDiagonal.raw_h_special,KingDiagonal.raw_v_ordinary,KingDiagonal.raw_v_special
special_block: proof_shape=bind-only; consumers=KingDiagonal.extract_valid,KingDiagonal.slot_reconstruction
raw_h_ordinary: proof_shape=bind-only; consumers=KingDiagonal.extract_valid,KingDiagonal.slot_reconstruction
raw_v_ordinary: proof_shape=bind-only; consumers=KingDiagonal.extract_valid,KingDiagonal.slot_reconstruction
raw_h_special: proof_shape=bind-only; consumers=KingDiagonal.extract_valid,KingDiagonal.slot_reconstruction
raw_v_special: proof_shape=bind-only; consumers=KingDiagonal.extract_valid,KingDiagonal.slot_reconstruction
extractSlots: proof_shape=bind-only; consumers=KingDiagonal.diagonalSlotEquiv,KingDiagonal.extract_slotField,KingDiagonal.extract_valid,KingDiagonal.slot_reconstruction
slot_reconstruction: proof_shape=bind-only; consumers=KingDiagonal.diagonalSlotEquiv
extract_slotField: proof_shape=bind-only; consumers=KingDiagonal.diagonalSlotEquiv
extract_valid: proof_shape=bind-only; consumers=KingDiagonal.diagonalSlotEquiv
slot_good: proof_shape=bind-only; consumers=KingDiagonal.slot_raw
slot_special: proof_shape=bind-only; consumers=KingDiagonal.slot_raw
slot_raw: proof_shape=bind-only; consumers=KingDiagonal.diagonalSlotEquiv
diagonalSlotEquiv: proof_shape=bind-only; consumers=KingDiagonal.diagonal_count
WordIndex: proof_shape=bind-only; consumers=KingDiagonal.F_add,KingDiagonal.SlotsIndex,KingDiagonal.WordCompatible,KingDiagonal.diagonal_count,KingDiagonal.intersection_card,KingDiagonal.leftRule,KingDiagonal.left_card,KingDiagonal.rightRule,KingDiagonal.right_card,KingDiagonal.word_card,KingDiagonal.word_card_add,KingDiagonal.word_cover
WordCompatible: proof_shape=bind-only; consumers=KingDiagonal.F_add,KingDiagonal.diagonal_count,KingDiagonal.normalizedEquiv,KingDiagonal.normalized_valid,KingDiagonal.word_card,KingDiagonal.word_card_add,KingDiagonal.word_cover
leftRule: proof_shape=bind-only; consumers=KingDiagonal.intersection_card,KingDiagonal.left_card,KingDiagonal.word_card_add,KingDiagonal.word_cover
rightRule: proof_shape=bind-only; consumers=KingDiagonal.intersection_card,KingDiagonal.right_card,KingDiagonal.word_card_add,KingDiagonal.word_cover
word_cover: proof_shape=bind-only; consumers=KingDiagonal.word_card_add
unary_card: proof_shape=bind-only; consumers=KingDiagonal.left_card,KingDiagonal.right_card
left_card: proof_shape=bind-only; consumers=KingDiagonal.word_card_add
right_card: proof_shape=bind-only; consumers=KingDiagonal.word_card_add
intersection_card: proof_shape=bind-only; consumers=KingDiagonal.word_card_add
card_or_add_inter: proof_shape=bind-only; consumers=KingDiagonal.word_card_add
emptyIndicator: proof_shape=bind-only; consumers=KingDiagonal.F,KingDiagonal.F_add,KingDiagonal.F_piecewise,KingDiagonal.indicator_corners,KingDiagonal.sum_F,KingDiagonal.word_card,KingDiagonal.word_card_add
F: proof_shape=bind-only; consumers=KingDiagonal.F_add,KingDiagonal.F_piecewise,KingDiagonal.N_D_closed,KingDiagonal.N_D_two_columns,KingDiagonal.diagonal_count,KingDiagonal.sum_F,KingDiagonal.word_card
word_card_add: proof_shape=bind-only; consumers=KingDiagonal.F_add,KingDiagonal.word_card
word_card: proof_shape=bind-only; consumers=KingDiagonal.F_add,KingDiagonal.diagonal_count
SlotsIndex: proof_shape=bind-only; consumers=KingDiagonal.diagonal_count,KingDiagonal.normalizedEquiv,KingDiagonal.normalizedSlots,KingDiagonal.normalized_valid,KingDiagonal.slotsWord,KingDiagonal.word_recover
normalizedSlots: proof_shape=bind-only; consumers=KingDiagonal.normalizedEquiv,KingDiagonal.normalized_recover,KingDiagonal.normalized_valid,KingDiagonal.word_recover
third_ne: proof_shape=bind-only; consumers=KingDiagonal.normalized_valid,KingDiagonal.word_recover
normalized_valid: proof_shape=bind-only; consumers=KingDiagonal.normalizedEquiv
slotsWord: proof_shape=bind-only; consumers=KingDiagonal.normalizedEquiv,KingDiagonal.normalized_recover,KingDiagonal.word_recover
normalized_recover: proof_shape=bind-only; consumers=KingDiagonal.normalizedEquiv
word_recover: proof_shape=bind-only; consumers=KingDiagonal.normalizedEquiv
normalizedEquiv: proof_shape=bind-only; consumers=KingDiagonal.diagonal_count
diagonal_count: proof_shape=bind-only; consumers=KingDiagonal.N_D_closed,KingDiagonal.N_D_two_columns
F_piecewise: proof_shape=bind-only; consumers=KingDiagonal.N_D_two_columns
F_add: proof_shape=bind-only; consumers=KingDiagonal.sum_F
geometric_two: proof_shape=bind-only; consumers=KingDiagonal.geometric_two_reverse,KingDiagonal.sum_A
geometric_two_reverse: proof_shape=bind-only; consumers=KingDiagonal.sum_A
Aterm: proof_shape=bind-only; consumers=KingDiagonal.sum_A,KingDiagonal.sum_F
sum_A: proof_shape=bind-only; consumers=KingDiagonal.sum_F
indicator_corners: proof_shape=bind-only; consumers=KingDiagonal.sum_F
sum_F: proof_shape=bind-only; consumers=KingDiagonal.N_D_closed
N_D_closed: proof_shape=bind-only; consumers=KingClosedForm.closed_form,KingClosedForm.width_three
N_D_two_columns: proof_shape=bind-only; consumers=KingClosedForm.width_two
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Ring.GeomSum

/-!
A defect in block `(i₀,j₀)` splits its horizontal slot into `x,y` and its vertical
slot into `y,x`. Every other slot is constant, with the four alphabets in `SlotValid`.
The indices are finite intervals, so words on empty sides remain in the same model.

For a fixed ordered pair, `true` records the third colour `x+y`. Cross exclusions
force either all vertical words or all horizontal words to omit that colour.
The two classes have independent coordinates; their intersection is the constant
assignment, present exactly under `emptyIndicator`. Their union gives `F`.

`N_D` uses step counts: its actual rectangle has `N+1` rows and `M+1` columns.
`N_D_closed` is an integer identity and the two thin boundary identities use naturals.
-/

namespace D5.S3.StatisticalMechanics.Potts.KingDefects.KingDiagonal

open KingGrid KingDifference

attribute [local instance] Classical.propDecidable

private theorem klein_alphabet (x y t : K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x ≠ y) : t ≠ 0 ∧ t ≠ x ↔ t = y ∨ t = x+y := by
  have hm : t ∈ ({x+y,x,y,0} : Finset K) := by
    rw [IsAddKleinFour.eq_finset_univ hx hy hxy]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  constructor
  · rintro ⟨ht0,htx⟩
    rcases hm with h | h | h | h
    · exact Or.inr h
    · exact (htx h).elim
    · exact Or.inl h
    · exact (ht0 h).elim
  · rintro (rfl | rfl)
    · exact ⟨hy,hxy.symm⟩
    · exact ⟨mt (KingDifference.add_eq_zero x y).mp hxy, by simpa using hy⟩

/-- Four ordinary words, with the two split-slot values recorded separately. -/
@[ext] private structure DiagonalSlots {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M) where
  x : K
  y : K
  U : {i : Fin N // i < i₀} → K
  V : {i : Fin N // i₀ < i} → K
  C : {j : Fin M // j < j₀} → K
  D : {j : Fin M // j₀ < j} → K

/-- The four alphabets and every vertical-horizontal cross exclusion. -/
private def SlotValid {N M : ℕ} {i₀ : Fin N} {j₀ : Fin M}
    (w : DiagonalSlots i₀ j₀) : Prop :=
  w.x ≠ 0 ∧ w.y ≠ 0 ∧ w.x ≠ w.y ∧
    (∀ i, w.U i = w.y ∨ w.U i = w.x + w.y) ∧
    (∀ i, w.V i = w.x ∨ w.V i = w.x + w.y) ∧
    (∀ j, w.C j = w.x ∨ w.C j = w.x + w.y) ∧
    (∀ j, w.D j = w.y ∨ w.D j = w.x + w.y) ∧
    (∀ i j, w.U i ≠ w.C j) ∧ (∀ i j, w.U i ≠ w.D j) ∧
    (∀ i j, w.V i ≠ w.C j) ∧ (∀ i j, w.V i ≠ w.D j)

/-- Fill each ordinary slot constantly and split the exceptional row and column. -/
private def slotField {N M : ℕ} {i₀ : Fin N} {j₀ : Fin M}
    (w : DiagonalSlots i₀ j₀) : DiffField N M where
  h i j := if h : j < j₀ then w.C ⟨j,h⟩ else
    if h : j₀ < j then w.D ⟨j,h⟩ else if i.val ≤ i₀.val then w.x else w.y
  v i j := if h : i < i₀ then w.U ⟨i,h⟩ else
    if h : i₀ < i then w.V ⟨i,h⟩ else if j.val ≤ j₀.val then w.y else w.x

private theorem diagonal_clear {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M)
    (i : Fin N) (j : Fin M) (h : i ≠ i₀ ∨ j ≠ j₀) :
    BlockAvoids (.D i₀ j₀) i j := by
  refine ⟨by simp, by simp, ?_, by simp, by simp, by simp⟩
  intro he
  have he' := Edge.D.inj he
  exact h.elim (fun hi => hi he'.1) (fun hj => hj he'.2)

private theorem special_block {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M)
    (s : DiffField N M) (hs : RawAdmissible (.D i₀ j₀) s) :
    s.h i₀.castSucc j₀ ≠ 0 ∧ s.h i₀.succ j₀ ≠ 0 ∧
    s.h i₀.castSucc j₀ ≠ s.h i₀.succ j₀ ∧
    s.v i₀ j₀.castSucc = s.h i₀.succ j₀ ∧
    s.v i₀ j₀.succ = s.h i₀.castSucc j₀ := by
  have hd := (hs.2 (.D i₀ j₀)).mpr rfl
  change s.h i₀.castSucc j₀ + s.v i₀ j₀.succ = 0 at hd
  have hr := (KingDifference.add_eq_zero _ _).mp hd
  have hc := hs.1 i₀ j₀
  rw [hd] at hc
  have hl := (KingDifference.add_eq_zero _ _).mp hc.symm
  have nz (d : Edge (N + 1) (M + 1)) (hne : d ≠ .D i₀ j₀) :
      edgeValue s d ≠ 0 := mt (hs.2 d).mp hne
  have hx := nz (.H i₀.castSucc j₀) (by simp)
  have hy := nz (.H i₀.succ j₀) (by simp)
  have ha := nz (.A i₀ j₀) (by simp)
  change s.h i₀.castSucc j₀ + s.v i₀ j₀.castSucc ≠ 0 at ha
  rw [hl] at ha
  exact ⟨hx,hy,fun h => ha ((KingDifference.add_eq_zero _ _).mpr h),hl,hr.symm⟩

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
private def extractSlots {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M)
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
    split_ifs with h₁ h₂ h₃
    · exact (raw_h_ordinary i₀ j₀ s hs j (ne_of_lt h₁) i).symm
    · exact (raw_h_ordinary i₀ j₀ s hs j (ne_of_gt h₂) i).symm
    all_goals
      have hj : j = j₀ := le_antisymm (le_of_not_gt h₂) (le_of_not_gt h₁)
      subst j
      simpa only [h₃, ite_true, ite_false] using (raw_h_special i₀ j₀ s hs i).symm
  · funext i j
    dsimp [slotField, extractSlots]
    split_ifs with h₁ h₂ h₃
    · exact (raw_v_ordinary i₀ j₀ s hs i (ne_of_lt h₁) j).symm
    · exact (raw_v_ordinary i₀ j₀ s hs i (ne_of_gt h₂) j).symm
    all_goals
      have hi : i = i₀ := le_antisymm (le_of_not_gt h₂) (le_of_not_gt h₁)
      subst i
      have he := special_block i₀ j₀ s hs
      simpa only [h₃, ite_true, ite_false, he.2.2.2.1, he.2.2.2.2] using
        (raw_v_special i₀ j₀ s hs j).symm

private theorem extract_slotField {N M : ℕ} {i₀ : Fin N} {j₀ : Fin M}
    (w : DiagonalSlots i₀ j₀) : extractSlots i₀ j₀ (slotField w) = w := by
  cases w
  simp only [extractSlots, slotField, lt_self_iff_false, dite_false, Fin.val_castSucc,
    le_refl, ite_true, Fin.val_succ, Nat.add_one_le_iff, ite_false]
  congr 1 <;> funext i <;> simp [i.property, not_lt_of_ge (le_of_lt i.property)]

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
    have hi : i.val.val ≤ i₀.val := Nat.le_of_lt i.property
    simp only [Fin.val_castSucc, ite_eq_left hi] at h
    exact (klein_alphabet _ _ _ hx hy hxy).mp ⟨h.2.2.2.1, h.2.2.2.2.symm⟩
  · intro i
    have h := good i.val j₀ (Or.inl (ne_of_gt i.property))
    rw [raw_h_special i₀ j₀ s hs i.val.castSucc,
      raw_v_ordinary i₀ j₀ s hs i.val (ne_of_gt i.property) j₀.castSucc] at h
    have hi : ¬ i.val.val ≤ i₀.val := Nat.not_le_of_lt i.property
    simp only [Fin.val_castSucc, ite_eq_right hi] at h
    simpa only [extractSlots, add_comm] using
      (klein_alphabet _ _ _ hy hx hxy.symm).mp ⟨h.2.2.2.1, h.2.2.2.2.symm⟩
  · intro j
    have h := good i₀ j.val (Or.inr (ne_of_lt j.property))
    rw [raw_h_ordinary i₀ j₀ s hs j.val (ne_of_lt j.property) i₀.castSucc,
      raw_v_special i₀ j₀ s hs j.val.castSucc] at h
    have hj : j.val.val ≤ j₀.val := Nat.le_of_lt j.property
    simp only [Fin.val_castSucc, ite_eq_left hj, hl] at h
    simpa only [extractSlots, add_comm] using
      (klein_alphabet _ _ _ hy hx hxy.symm).mp ⟨h.2.2.1, h.2.2.2.2⟩
  · intro j
    have h := good i₀ j.val (Or.inr (ne_of_gt j.property))
    rw [raw_h_ordinary i₀ j₀ s hs j.val (ne_of_gt j.property) i₀.castSucc,
      raw_v_special i₀ j₀ s hs j.val.castSucc] at h
    have hj : ¬ j.val.val ≤ j₀.val := Nat.not_le_of_lt j.property
    simp only [Fin.val_castSucc, ite_eq_right hj, hr] at h
    exact (klein_alphabet _ _ _ hx hy hxy).mp ⟨h.2.2.1, h.2.2.2.2⟩
  all_goals
    intro i j
    have hi : i.val ≠ i₀ := by first | exact ne_of_lt i.property | exact ne_of_gt i.property
    have hj : j.val ≠ j₀ := by first | exact ne_of_lt j.property | exact ne_of_gt j.property
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
  rcases lt_trichotomy i i₀ with hi | rfl | hi <;>
    rcases lt_trichotomy j j₀ with hj | rfl | hj
  · simp only [slotField, dite_eq_left hi, dite_eq_left hj]
    exact ⟨True.intro,True.intro,(hC' ⟨j,hj⟩).1,(hU' ⟨i,hi⟩).1,(hUC ⟨i,hi⟩ ⟨j,hj⟩).symm⟩
  · have ht : i.val ≤ i₀.val := Nat.le_of_lt hi
    have hb : i.val + 1 ≤ i₀.val := hi
    simp only [slotField, dite_eq_left hi, lt_self_iff_false, dite_false,
      Fin.val_castSucc, Fin.val_succ, ite_eq_left ht, ite_eq_left hb]
    exact ⟨True.intro,True.intro,hx,(hU' ⟨i,hi⟩).1,(hU' ⟨i,hi⟩).2.symm⟩
  · simp only [slotField, dite_eq_left hi, dite_eq_right (not_lt_of_gt hj), dite_eq_left hj]
    exact ⟨True.intro,True.intro,(hD' ⟨j,hj⟩).1,(hU' ⟨i,hi⟩).1,(hUD ⟨i,hi⟩ ⟨j,hj⟩).symm⟩
  · have hl : j.val ≤ j₀.val := Nat.le_of_lt hj
    have hr : j.val + 1 ≤ j₀.val := hj
    simp only [slotField, dite_eq_left hj, lt_self_iff_false, dite_false,
      Fin.val_castSucc, Fin.val_succ, ite_eq_left hl, ite_eq_left hr]
    exact ⟨True.intro,True.intro,(hC' ⟨j,hj⟩).1,hy,(hC' ⟨j,hj⟩).2⟩
  · exact False.elim (h.elim (fun hn => hn rfl) (fun hn => hn rfl))
  · have hl : ¬ j.val ≤ j₀.val := Nat.not_le_of_lt hj
    have hr : ¬ j.val + 1 ≤ j₀.val := by omega
    simp only [slotField, dite_eq_right (not_lt_of_gt hj), dite_eq_left hj,
      lt_self_iff_false, dite_false, Fin.val_castSucc, Fin.val_succ,
      ite_eq_right hl, ite_eq_right hr]
    exact ⟨True.intro,True.intro,(hD' ⟨j,hj⟩).1,hx,(hD' ⟨j,hj⟩).2⟩
  · simp only [slotField, dite_eq_right (not_lt_of_gt hi), dite_eq_left hi, dite_eq_left hj]
    exact ⟨True.intro,True.intro,(hC' ⟨j,hj⟩).1,(hV' ⟨i,hi⟩).1,(hVC ⟨i,hi⟩ ⟨j,hj⟩).symm⟩
  · have ht : ¬ i.val ≤ i₀.val := Nat.not_le_of_lt hi
    have hb : ¬ i.val + 1 ≤ i₀.val := by omega
    simp only [slotField, dite_eq_right (not_lt_of_gt hi), dite_eq_left hi,
      lt_self_iff_false, dite_false, Fin.val_castSucc, Fin.val_succ,
      ite_eq_right ht, ite_eq_right hb]
    exact ⟨True.intro,True.intro,hy,(hV' ⟨i,hi⟩).1,(hV' ⟨i,hi⟩).2.symm⟩
  · simp only [slotField, dite_eq_right (not_lt_of_gt hi), dite_eq_left hi,
      dite_eq_right (not_lt_of_gt hj), dite_eq_left hj]
    exact ⟨True.intro,True.intro,(hD' ⟨j,hj⟩).1,(hV' ⟨i,hi⟩).1,(hVD ⟨i,hi⟩ ⟨j,hj⟩).symm⟩

private theorem slot_special {N M : ℕ} {i₀ : Fin N} {j₀ : Fin M}
    (w : DiagonalSlots i₀ j₀) :
    (slotField w).h i₀.castSucc j₀ = w.x ∧
    (slotField w).h i₀.succ j₀ = w.y ∧
    (slotField w).v i₀ j₀.castSucc = w.y ∧
    (slotField w).v i₀ j₀.succ = w.x := by simp [slotField]

private theorem slot_raw {N M : ℕ} {i₀ : Fin N} {j₀ : Fin M}
    (w : DiagonalSlots i₀ j₀) (hw : SlotValid w) :
    RawAdmissible (.D i₀ j₀) (slotField w) := by
  have hz : w.x + w.y ≠ 0 := mt (KingDifference.add_eq_zero _ _).mp hw.2.2.1
  have hnU (i) : w.U i ≠ 0 := by
    rcases hw.2.2.2.1 i with h | h
    · rw [h]; exact hw.2.1
    · rw [h]; exact hz
  have hnV (i) : w.V i ≠ 0 := by
    rcases hw.2.2.2.2.1 i with h | h
    · rw [h]; exact hw.1
    · rw [h]; exact hz
  have hnC (j) : w.C j ≠ 0 := by
    rcases hw.2.2.2.2.2.1 j with h | h
    · rw [h]; exact hw.1
    · rw [h]; exact hz
  have hnD (j) : w.D j ≠ 0 := by
    rcases hw.2.2.2.2.2.2.1 j with h | h
    · rw [h]; exact hw.2.1
    · rw [h]; exact hz
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
          exact mt (KingDifference.add_eq_zero _ _).mp h.2.2.2.2
        simp [hn, he]
    | A i j =>
      have hn : edgeValue (slotField w) (.A i j) ≠ 0 := by
        by_cases he : i = i₀ ∧ j = j₀
        · rcases he with ⟨rfl,rfl⟩
          simpa only [edgeValue, hs.1, hs.2.2.1] using hz
        · have h := slot_good w hw i j (not_and_or.mp he)
          exact mt (KingDifference.add_eq_zero _ _).mp h.2.2.2.2
      simp [hn]

/-- Exact classification by an ordered nonzero unequal pair and four compatible words. -/
private def diagonalSlotEquiv {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M) :
    {s : DiffField N M // RawAdmissible (.D i₀ j₀) s} ≃
      {w : DiagonalSlots i₀ j₀ // SlotValid w} where
  toFun s := ⟨extractSlots i₀ j₀ s.val, extract_valid i₀ j₀ s.val s.property⟩
  invFun w := ⟨slotField w.val, slot_raw w.val w.property⟩
  left_inv s := Subtype.ext (slot_reconstruction i₀ j₀ s.val s.property)
  right_inv w := Subtype.ext (extract_slotField w.val)

#print axioms diagonalSlotEquiv

/-- Word positions in the four ordinary slot families. -/
private abbrev WordIndex (A B C D : Type) := A ⊕ B ⊕ C ⊕ D

/-- `true` denotes the third colour; `false` denotes the family's other colour. -/
private def WordCompatible {A B C D : Type} (f : WordIndex A B C D → Bool) : Prop :=
  (∀ a c, f (.inl a) = false ∨ f (.inr (.inr (.inl c))) = false) ∧
  (∀ b d, f (.inr (.inl b)) = false ∨ f (.inr (.inr (.inr d))) = false) ∧
  (∀ a d, f (.inl a) ≠ f (.inr (.inr (.inr d)))) ∧
  (∀ b c, f (.inr (.inl b)) ≠ f (.inr (.inr (.inl c))))

private def leftRule (A B C D : Type) : WordIndex A B C D → Bool → Prop
  | .inl _, b => b = false
  | .inr (.inl _), b => b = false
  | .inr (.inr (.inl _)), b => Nonempty B → b = true
  | .inr (.inr (.inr _)), b => Nonempty A → b = true

private def rightRule (A B C D : Type) : WordIndex A B C D → Bool → Prop
  | .inl _, b => Nonempty D → b = true
  | .inr (.inl _), b => Nonempty C → b = true
  | .inr (.inr (.inl _)), b => b = false
  | .inr (.inr (.inr _)), b => b = false

private theorem word_cover {A B C D : Type} (f : WordIndex A B C D → Bool) :
    WordCompatible f ↔ (∀ i, leftRule A B C D i (f i)) ∨
      (∀ i, rightRule A B C D i (f i)) := by
  classical
  constructor
  · rintro ⟨hAC,hBD,hAD,hBC⟩
    by_cases h : (∀ a, f (.inl a) = false) ∧ (∀ b, f (.inr (.inl b)) = false)
    · left
      intro i
      rcases i with a | b | c | d
      · exact h.1 a
      · exact h.2 b
      · rintro ⟨b⟩
        have hn := hBC b c
        rw [h.2 b] at hn
        cases he : f (.inr (.inr (.inl c))) <;> simp_all
      · rintro ⟨a⟩
        have hn := hAD a d
        rw [h.1 a] at hn
        cases he : f (.inr (.inr (.inr d))) <;> simp_all
    · have hCD : (∀ c, f (.inr (.inr (.inl c))) = false) ∧
          (∀ d, f (.inr (.inr (.inr d))) = false) := by
        have hh : (∃ a, f (.inl a) ≠ false) ∨
            (∃ b, f (.inr (.inl b)) ≠ false) := by
          simpa only [not_and_or, not_forall] using h
        rcases hh with ⟨a,ha⟩ | ⟨b,hb⟩
        · have ha' : f (.inl a) = true := by cases he : f (.inl a) <;> simp_all
          constructor
          · intro c; exact (hAC a c).resolve_left ha
          · intro d
            have hn := hAD a d
            rw [ha'] at hn
            cases he : f (.inr (.inr (.inr d))) <;> simp_all
        · have hb' : f (.inr (.inl b)) = true := by
            cases he : f (.inr (.inl b)) <;> simp_all
          constructor
          · intro c
            have hn := hBC b c
            rw [hb'] at hn
            cases he : f (.inr (.inr (.inl c))) <;> simp_all
          · intro d; exact (hBD b d).resolve_left hb
      right
      intro i
      rcases i with a | b | c | d
      · rintro ⟨d⟩
        have hn := hAD a d
        rw [hCD.2 d] at hn
        cases he : f (.inl a) <;> simp_all
      · rintro ⟨c⟩
        have hn := hBC b c
        rw [hCD.1 c] at hn
        cases he : f (.inr (.inl b)) <;> simp_all
      · exact hCD.1 c
      · exact hCD.2 d
  · intro h
    rcases h with h | h
    · have ha (a) := h (.inl a)
      have hb (b) := h (.inr (.inl b))
      have hc (c) := h (.inr (.inr (.inl c)))
      have hd (d) := h (.inr (.inr (.inr d)))
      dsimp [leftRule] at ha hb hc hd
      refine ⟨fun a c => Or.inl (ha a), fun b d => Or.inl (hb b), ?_, ?_⟩
      · intro a d; simp [ha a, hd d ⟨a⟩]
      · intro b c; simp [hb b, hc c ⟨b⟩]
    · have ha (a) := h (.inl a)
      have hb (b) := h (.inr (.inl b))
      have hc (c) := h (.inr (.inr (.inl c)))
      have hd (d) := h (.inr (.inr (.inr d)))
      dsimp [rightRule] at ha hb hc hd
      refine ⟨fun a c => Or.inr (hc c), fun b d => Or.inr (hd d), ?_, ?_⟩
      · intro a d; simp [ha a ⟨d⟩, hd d]
      · intro b c; simp [hb b ⟨c⟩, hc c]

private theorem unary_card {I : Type} [Fintype I] (p : I → Bool → Prop) :
    Nat.card {f : I → Bool // ∀ i, p i (f i)} =
      ∏ i, Nat.card {b : Bool // p i b} := by
  classical
  rw [Nat.card_congr (Equiv.subtypePiEquivPi)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_pi]

private theorem left_card (A B C D : Type) [Finite A] [Finite B]
    [Fintype C] [Fintype D] :
    Nat.card {f : WordIndex A B C D → Bool // ∀ i, leftRule A B C D i (f i)} =
      (if Nonempty B then 1 else 2) ^ Fintype.card C *
      (if Nonempty A then 1 else 2) ^ Fintype.card D := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  let _ : Fintype B := Fintype.ofFinite B
  rw [unary_card]
  simp only [Fintype.prod_sum_type, leftRule]
  have hb (P : Prop) : Nat.card {b : Bool // P → b = true} = if P then 1 else 2 := by
    by_cases h : P <;> simp [h, Nat.card_eq_fintype_card]
  simp only [hb]
  simp [Nat.card_eq_fintype_card]

private theorem right_card (A B C D : Type) [Fintype A] [Fintype B]
    [Finite C] [Finite D] :
    Nat.card {f : WordIndex A B C D → Bool // ∀ i, rightRule A B C D i (f i)} =
      (if Nonempty D then 1 else 2) ^ Fintype.card A *
      (if Nonempty C then 1 else 2) ^ Fintype.card B := by
  classical
  let _ : Fintype C := Fintype.ofFinite C
  let _ : Fintype D := Fintype.ofFinite D
  rw [unary_card]
  simp only [Fintype.prod_sum_type, rightRule]
  have hb (P : Prop) : Nat.card {b : Bool // P → b = true} = if P then 1 else 2 := by
    by_cases h : P <;> simp [h, Nat.card_eq_fintype_card]
  simp only [hb]
  simp [Nat.card_eq_fintype_card]

private theorem intersection_card (A B C D : Type) :
    Nat.card {f : WordIndex A B C D → Bool //
      (∀ i, leftRule A B C D i (f i)) ∧ (∀ i, rightRule A B C D i (f i))} =
    if (Nonempty A → ¬ Nonempty D) ∧ (Nonempty B → ¬ Nonempty C) then 1 else 0 := by
  classical
  have he (f : WordIndex A B C D → Bool) :
      ((∀ i, leftRule A B C D i (f i)) ∧ (∀ i, rightRule A B C D i (f i))) ↔
      f = (fun _ => false) ∧
        (Nonempty A → ¬ Nonempty D) ∧ (Nonempty B → ¬ Nonempty C) := by
    constructor
    · rintro ⟨hL,hR⟩
      have hf : f = (fun _ => false) := by
        funext i
        rcases i with a | b | c | d
        · exact hL (.inl a)
        · exact hL (.inr (.inl b))
        · exact hR (.inr (.inr (.inl c)))
        · exact hR (.inr (.inr (.inr d)))
      refine ⟨hf, ?_, ?_⟩
      · rintro ⟨a⟩ ⟨d⟩
        have hh := hL (.inr (.inr (.inr d)))
        have hh' : f (.inr (.inr (.inr d))) = true := hh ⟨a⟩
        simp [hf] at hh'
      · rintro ⟨b⟩ ⟨c⟩
        have hh := hL (.inr (.inr (.inl c)))
        have hh' : f (.inr (.inr (.inl c))) = true := hh ⟨b⟩
        simp [hf] at hh'
    · rintro ⟨rfl,hAD,hBC⟩
      constructor <;> intro i <;> rcases i with a | b | c | d
      all_goals dsimp [leftRule, rightRule]
      all_goals first | exact fun hn => False.elim (hAD ⟨a⟩ hn) |
        exact fun hn => False.elim (hAD hn ⟨d⟩) |
        exact fun hn => False.elim (hBC ⟨b⟩ hn) |
        exact fun hn => False.elim (hBC hn ⟨c⟩)
  simp_rw [he]
  by_cases h : (Nonempty A → ¬ Nonempty D) ∧ (Nonempty B → ¬ Nonempty C)
  · have hp : ((Nonempty A → ¬ Nonempty D) ∧ (Nonempty B → ¬ Nonempty C)) = True :=
      propext (iff_true_intro h)
    simp only [hp, and_true, ite_true]
    simp [Nat.card_eq_fintype_card]
  · have hp : ((Nonempty A → ¬ Nonempty D) ∧ (Nonempty B → ¬ Nonempty C)) = False :=
      propext (iff_false_intro h)
    simp only [hp, and_false, ite_false]
    simp

private theorem card_or_add_inter {I : Type} [Finite I] (p q : I → Prop) :
    Nat.card {i // p i ∨ q i} + Nat.card {i // p i ∧ q i} =
      Nat.card {i // p i} + Nat.card {i // q i} := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← Finset.filter_or, ← Finset.filter_and] using
      Finset.card_union_add_card_inter (Finset.univ.filter p) (Finset.univ.filter q)

/-- The zero-length indicator preserves all empty-word cases. -/
private def emptyIndicator (a b c d : ℕ) : ℕ :=
  if (a = 0 ∨ d = 0) ∧ (b = 0 ∨ c = 0) then 1 else 0

/-- Two classes according to which direction omits the third colour. -/
private def F (a b c d : ℕ) : ℕ :=
  (if b = 0 then 2^c else 1) * (if a = 0 then 2^d else 1) +
    (if d = 0 then 2^a else 1) * (if c = 0 then 2^b else 1) -
    emptyIndicator a b c d

private theorem word_card_add (A B C D : Type) [Fintype A] [Fintype B]
    [Fintype C] [Fintype D] :
    Nat.card {f : WordIndex A B C D → Bool // WordCompatible f} +
      emptyIndicator (Fintype.card A) (Fintype.card B) (Fintype.card C) (Fintype.card D) =
    (if Fintype.card B = 0 then 2 ^ Fintype.card C else 1) *
      (if Fintype.card A = 0 then 2 ^ Fintype.card D else 1) +
    (if Fintype.card D = 0 then 2 ^ Fintype.card A else 1) *
      (if Fintype.card C = 0 then 2 ^ Fintype.card B else 1) := by
  classical
  have h := card_or_add_inter
    (fun f : WordIndex A B C D → Bool => ∀ i, leftRule A B C D i (f i))
    (fun f : WordIndex A B C D → Bool => ∀ i, rightRule A B C D i (f i))
  simp_rw [← word_cover] at h
  rw [intersection_card, left_card, right_card] at h
  have emp (I : Type) [Fintype I] : Fintype.card I = 0 ↔ ¬ Nonempty I := by
    simp [Fintype.card_eq_zero_iff]
  simp only [emptyIndicator, emp]
  by_cases hA : Nonempty A <;> by_cases hB : Nonempty B <;>
    by_cases hC : Nonempty C <;> by_cases hD : Nonempty D
  all_goals simpa only [hA,hB,hC,hD, not_true_eq_false, not_false_eq_true,
    true_or, false_or, or_true, or_false, true_and, false_and, and_true, and_false,
    false_implies, implies_true, true_implies, ite_true, ite_false, one_pow, one_mul,
    mul_one] using h

private theorem word_card (A B C D : Type) [Fintype A] [Fintype B]
    [Fintype C] [Fintype D] :
    Nat.card {f : WordIndex A B C D → Bool // WordCompatible f} =
      F (Fintype.card A) (Fintype.card B) (Fintype.card C) (Fintype.card D) := by
  have h := word_card_add A B C D
  unfold F
  omega

private abbrev SlotsIndex {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M) :=
  WordIndex {i : Fin N // i < i₀} {i : Fin N // i₀ < i}
    {j : Fin M // j < j₀} {j : Fin M // j₀ < j}

private def normalizedSlots {N M : ℕ} {i₀ : Fin N} {j₀ : Fin M}
    (p : NZPair) (f : SlotsIndex i₀ j₀ → Bool) : DiagonalSlots i₀ j₀ where
  x := p.val.1
  y := p.val.2
  U i := if f (.inl i) then p.val.1 + p.val.2 else p.val.2
  V i := if f (.inr (.inl i)) then p.val.1 + p.val.2 else p.val.1
  C j := if f (.inr (.inr (.inl j))) then p.val.1 + p.val.2 else p.val.1
  D j := if f (.inr (.inr (.inr j))) then p.val.1 + p.val.2 else p.val.2

private theorem third_ne (p : NZPair) :
    p.val.1 + p.val.2 ≠ p.val.1 ∧ p.val.1 + p.val.2 ≠ p.val.2 := by
  constructor
  · intro h
    have hh : p.val.1 + p.val.2 = p.val.1 + 0 := by simpa using h
    exact p.property.2.1 (add_left_cancel hh)
  · intro h
    have hh : p.val.1 + p.val.2 = 0 + p.val.2 := by simpa using h
    exact p.property.1 (add_right_cancel hh)

private theorem normalized_valid {N M : ℕ} {i₀ : Fin N} {j₀ : Fin M}
    (p : NZPair) (f : SlotsIndex i₀ j₀ → Bool) :
    SlotValid (normalizedSlots p f) ↔ WordCompatible f := by
  obtain ⟨hzx,hzy⟩ := third_ne p
  have hxy := p.property.2.2
  have ac (u c : Bool) :
      ((if u then p.val.1 + p.val.2 else p.val.2) ≠
        (if c then p.val.1 + p.val.2 else p.val.1)) ↔ u = false ∨ c = false := by
    cases u <;> cases c <;> simp [hxy.symm, hzx, hzy.symm]
  have bd (v d : Bool) :
      ((if v then p.val.1 + p.val.2 else p.val.1) ≠
        (if d then p.val.1 + p.val.2 else p.val.2)) ↔ v = false ∨ d = false := by
    cases v <;> cases d <;> simp [hxy, hzx.symm, hzy]
  have ad (u d : Bool) :
      ((if u then p.val.1 + p.val.2 else p.val.2) ≠
        (if d then p.val.1 + p.val.2 else p.val.2)) ↔ u ≠ d := by
    cases u <;> cases d <;> simp [hzy, hzy.symm]
  have bc (v c : Bool) :
      ((if v then p.val.1 + p.val.2 else p.val.1) ≠
        (if c then p.val.1 + p.val.2 else p.val.1)) ↔ v ≠ c := by
    cases v <;> cases c <;> simp [hzx, hzx.symm]
  have alphabet (b : Bool) (x y : K) : (if b then x + y else y) = y ∨
      (if b then x + y else y) = x + y := by cases b <;> simp
  have alphabet' (b : Bool) (x y : K) : (if b then x + y else x) = x ∨
      (if b then x + y else x) = x + y := by cases b <;> simp
  simp only [SlotValid, normalizedSlots, alphabet, alphabet', ac, bd, ad, bc,
    WordCompatible]
  have hx := p.property.1
  have hy := p.property.2.1
  tauto

private def slotsWord {N M : ℕ} {i₀ : Fin N} {j₀ : Fin M}
    (w : DiagonalSlots i₀ j₀) : SlotsIndex i₀ j₀ → Bool
  | .inl i => decide (w.U i = w.x + w.y)
  | .inr (.inl i) => decide (w.V i = w.x + w.y)
  | .inr (.inr (.inl j)) => decide (w.C j = w.x + w.y)
  | .inr (.inr (.inr j)) => decide (w.D j = w.x + w.y)

private theorem normalized_recover {N M : ℕ} {i₀ : Fin N} {j₀ : Fin M}
    (w : DiagonalSlots i₀ j₀) (hw : SlotValid w) :
    normalizedSlots ⟨(w.x,w.y),hw.1,hw.2.1,hw.2.2.1⟩ (slotsWord w) = w := by
  have recov (x z t : K) (ht : t = x ∨ t = z) :
      (if decide (t = z) then z else x) = t := by
    simp only [decide_eq_true_eq]
    by_cases h : t = z
    · rw [ite_eq_left h]
      exact h.symm
    · rw [ite_eq_right h]
      exact (ht.resolve_right h).symm
  apply DiagonalSlots.ext
  · rfl
  · rfl
  all_goals funext i
  · exact recov _ _ _ (hw.2.2.2.1 i)
  · exact recov _ _ _ (hw.2.2.2.2.1 i)
  · exact recov _ _ _ (hw.2.2.2.2.2.1 i)
  · exact recov _ _ _ (hw.2.2.2.2.2.2.1 i)

private theorem word_recover {N M : ℕ} {i₀ : Fin N} {j₀ : Fin M}
    (p : NZPair) (f : SlotsIndex i₀ j₀ → Bool) :
    slotsWord (normalizedSlots p f) = f := by
  obtain ⟨hzx,hzy⟩ := third_ne p
  funext i
  rcases i with a | b | c | d
  all_goals dsimp [slotsWord, normalizedSlots]
  all_goals split <;> simp_all

private def normalizedEquiv {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M) :
    NZPair × {f : SlotsIndex i₀ j₀ → Bool // WordCompatible f} ≃
      {w : DiagonalSlots i₀ j₀ // SlotValid w} where
  toFun q := ⟨normalizedSlots q.1 q.2.val, (normalized_valid q.1 q.2.val).mpr q.2.property⟩
  invFun w := (⟨(w.val.x,w.val.y),w.property.1,w.property.2.1,w.property.2.2.1⟩,
    ⟨slotsWord w.val, by
      apply (normalized_valid ⟨(w.val.x,w.val.y),
        w.property.1,w.property.2.1,w.property.2.2.1⟩ _).mp
      rw [normalized_recover w.val w.property]
      exact w.property⟩)
  left_inv q := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext (word_recover q.1 q.2.val)
  right_inv w := Subtype.ext (normalized_recover w.val w.property)

/-- The exact per-position count, including every empty side. -/
private theorem diagonal_count {N M : ℕ} (i₀ : Fin N) (j₀ : Fin M) :
    N_e (.D i₀ j₀ : Edge (N + 1) (M + 1)) =
      6 * F i₀.val (N - 1 - i₀.val) j₀.val (M - 1 - j₀.val) := by
  rw [N_e, Nat.card_congr (diagonalSlotEquiv i₀ j₀),
    ← Nat.card_congr (normalizedEquiv i₀ j₀), Nat.card_prod, nz_pair_card, word_card]
  have hlt {L : ℕ} (r : Fin L) : Fintype.card {i : Fin L // i < r} = r.val := by
    rw [Fintype.card_of_subtype (Finset.Iio r) (by simp), Fin.card_Iio]
  have hgt {L : ℕ} (r : Fin L) :
      Fintype.card {i : Fin L // r < i} = L - 1 - r.val := by
    rw [Fintype.card_of_subtype (Finset.Ioi r) (by simp), Fin.card_Ioi]
  rw [hlt,hgt,hlt,hgt]

#print axioms diagonal_count

/-- The support count in the exhaustive piecewise form, with empty sides retained. -/
private theorem F_piecewise (a b c d : ℕ) :
    F a b c d =
      if a + b = 0 then 2 ^ (c + d) else
      if c + d = 0 then 2 ^ (a + b) else
      if a = 0 then 2^d + 1 + (if c = 0 then 2^b - 2 else 0) else
      if b = 0 then 2^c + 1 + (if d = 0 then 2^a - 2 else 0) else
      2 + (if c = 0 then 2^b - 1 else 0) + (if d = 0 then 2^a - 1 else 0) := by
  have lb (t : ℕ) : 1 ≤ 2^t := Nat.one_le_pow t 2 (by omega)
  have lb' (t : ℕ) (ht : t ≠ 0) : 2 ≤ 2^t := by
    calc
      2 = 2^1 := by norm_num
      _ ≤ 2^t := Nat.pow_le_pow_right (by omega) (by omega)
  have ha := lb a
  have hb := lb b
  have hc := lb c
  have hd := lb d
  have ha' := lb' a
  have hb' := lb' b
  have hc' := lb' c
  have hd' := lb' d
  by_cases za : a = 0 <;> by_cases zb : b = 0 <;>
    by_cases zc : c = 0 <;> by_cases zd : d = 0
  all_goals simp [F, emptyIndicator, pow_add, za, zb, zc, zd]
  all_goals omega

private theorem F_add (a b c d : ℕ) :
    F a b c d + emptyIndicator a b c d =
      (if b = 0 then 2^c else 1) * (if a = 0 then 2^d else 1) +
      (if d = 0 then 2^a else 1) * (if c = 0 then 2^b else 1) := by
  have h := word_card_add (Fin a) (Fin b) (Fin c) (Fin d)
  rw [word_card] at h
  simpa only [Fintype.card_fin] using h

private theorem geometric_two (r : ℕ) :
    (∑ i : Fin r, (2 : ℤ)^i.val) = 2^r - 1 := by
  simpa only [Fin.sum_univ_eq_sum_range, show (2 : ℤ) - 1 = 1 by norm_num, mul_one]
    using geom_sum_mul (2 : ℤ) r

private theorem geometric_two_reverse (r : ℕ) :
    (∑ i : Fin r, (2 : ℤ)^(r - 1 - i.val)) = 2^r - 1 := by
  have h := Equiv.sum_comp (Fin.revPerm (n := r)) (fun i : Fin r => (2 : ℤ)^i.val)
  simpa only [Fin.revPerm_apply, Fin.val_rev, geometric_two, Nat.sub_sub, Nat.add_comm] using h

private def Aterm {N M : ℕ} (i : Fin N) (j : Fin M) : ℤ :=
  (if N - 1 - i.val = 0 then 2^j.val else 1) *
    (if i.val = 0 then 2^(M - 1 - j.val) else 1)

private theorem sum_A (n M : ℕ) :
    (∑ i : Fin (n + 2), ∑ j : Fin M, Aterm i j) =
      (n : ℤ) * M + 2 * (2^M - 1) := by
  have hterm (i : Fin (n + 2)) (j : Fin M) :
      Aterm i j = 1 + (if i = 0 then (2 : ℤ)^(M - 1 - j.val) - 1 else 0) +
        (if i = Fin.last (n + 1) then (2 : ℤ)^j.val - 1 else 0) := by
    have hi := i.isLt
    by_cases h0 : i = 0 <;> by_cases h1 : i = Fin.last (n + 1)
    all_goals simp only [Fin.ext_iff, Fin.val_zero, Fin.val_last] at h0 h1
    all_goals simp [Aterm, h0, h1, Fin.ext_iff, show n + 2 - 1 = n + 1 by omega,
      show (n + 1 - i.val = 0 ↔ i.val = n + 1) by omega]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, geometric_two,
    geometric_two_reverse]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private theorem indicator_corners (n m : ℕ) (i : Fin (n + 2)) (j : Fin (m + 2)) :
    (emptyIndicator i.val (n + 1 - i.val) j.val (m + 1 - j.val) : ℤ) =
      (if i = 0 ∧ j = 0 then 1 else 0) +
        (if i = Fin.last (n + 1) ∧ j = Fin.last (m + 1) then 1 else 0) := by
  have hi := i.isLt
  have hj := j.isLt
  have hi' : n + 1 - i.val = 0 ↔ i.val = n + 1 := by omega
  have hj' : m + 1 - j.val = 0 ↔ j.val = m + 1 := by omega
  unfold emptyIndicator
  simp only [hi',hj',Fin.ext_iff, Fin.val_zero, Fin.val_last]
  split_ifs <;> norm_num <;> omega

private theorem sum_F (n m : ℕ) :
    (∑ i : Fin (n + 2), ∑ j : Fin (m + 2),
      (F i.val (n + 1 - i.val) j.val (m + 1 - j.val) : ℤ)) =
      2^(n+3) + 2^(m+3) + 2*(n+1)*(m+1) - 8 := by
  have point (i : Fin (n + 2)) (j : Fin (m + 2)) :
      (F i.val (n + 1 - i.val) j.val (m + 1 - j.val) : ℤ) +
        emptyIndicator i.val (n + 1 - i.val) j.val (m + 1 - j.val) =
      Aterm i j + Aterm j i := by
    have h := F_add i.val (n + 1 - i.val) j.val (m + 1 - j.val)
    have hc := congrArg (fun t : ℕ => (t : ℤ)) h
    push_cast at hc
    simpa [Aterm, Nat.add_sub_cancel] using hc
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun j _ => point i j))
  simp only [Finset.sum_add_distrib] at h
  have hind : (∑ i : Fin (n + 2), ∑ j : Fin (m + 2),
      (emptyIndicator i.val (n + 1 - i.val) j.val (m + 1 - j.val) : ℤ)) = 2 := by
    simp_rw [indicator_corners]
    simp [Finset.sum_add_distrib, ite_and]
  rw [hind, sum_A, Finset.sum_comm (f := fun i j => Aterm j i), sum_A] at h
  push_cast at h
  have hn : (2 : ℤ)^(n+3) = 2 * 2^(n+2) := by rw [pow_succ]; ring
  have hm : (2 : ℤ)^(m+3) = 2 * 2^(m+2) := by rw [pow_succ]; ring
  rw [hn,hm]
  linear_combination h

/-- The sum over all descending diagonal positions in dimensions at least three. -/
theorem N_D_closed (N M : ℕ) (hN : 2 ≤ N) (hM : 2 ≤ M) :
    (N_D N M : ℤ) = 6 * ((2 : ℤ)^(N+1) + 2^(M+1) +
      2*(N-1)*(M-1) - 8) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N-2, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 2 := ⟨M-2, by omega⟩
  simp only [N_D]
  simp_rw [diagonal_count]
  push_cast
  simp only [← Finset.mul_sum]
  rw [sum_F]
  ring

/-- The transposed two-column boundary has the same empty-side count. -/
theorem N_D_two_columns (N : ℕ) : N_D N 1 = 6 * (N * 2^(N-1)) := by
  unfold N_D
  simp only [Fin.sum_univ_one]
  have point (i : Fin N) : N_e (.D i (0 : Fin 1) : Edge (N+1) 2) = 6*2^(N-1) := by
    rw [diagonal_count, F_piecewise]
    have hi := i.isLt
    have hab : i.val + (N - 1 - i.val) = N - 1 := by omega
    simp only [Fin.val_zero, Nat.sub_self, Nat.zero_add, hab, ite_true]
    by_cases h : N - 1 = 0 <;> simp [h]
  simp_rw [point]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id]
  ring

#print axioms F_piecewise
#print axioms N_D_closed
#print axioms N_D_two_columns

end D5.S3.StatisticalMechanics.Potts.KingDefects.KingDiagonal
