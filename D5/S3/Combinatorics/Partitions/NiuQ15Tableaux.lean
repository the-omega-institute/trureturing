/- GID: D5/S3/Combinatorics/Partitions/NiuQ15Tableaux
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/NiuQ15Tableaux
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.SetTheory.Cardinal.Finite]
   utility: none
   digest: Largest-label deletion and prefix rotation for standard tableaux. -/

/- admission_basis: escape-witness (preregistration #32036)
   Direct frozen dependencies: none.
   size_eraseRowEnd | proof_shape: bind-only | escape_witness: none
     Consumers: standardTableauDeleteLast and card_standardTableau_eq_shiftedCount.
   card_standardTableau_eq_sum | proof_shape: content
     escape_witness: standardTableauDeleteLast constructs the bijection by removing the maximal
     label and reinserting it at the chosen corner.
     Consumer: card_standardTableau_eq_shiftedCount.
   card_standardTableau_of_size_zero | proof_shape: content
     escape_witness: a Unique instance is constructed for strictly increasing bijections
     between the two empty carriers.
     Consumer: card_standardTableau_eq_shiftedCount.
   size_rectangle | proof_shape: bind-only | escape_witness: none
     Consumers: rectangleRowMajor and zeroShapeReadout_fails.
   firstDescent_le_width | proof_shape: content
     escape_witness: firstDescent_ge_iff_prefix identifies every label before the descent.
     Consumers: card_rectangle_tail_of_width_lt and rectangleOddEntryProbability_eq_sum.
   card_rectangle_tail | proof_shape: content
     escape_witness: rectangleTailRotation constructs the bijection for the actual survival event.
     Consumer: rectangleTailProbability_eq.
   card_rectangle_tail_of_width_lt | proof_shape: content
     escape_witness: firstDescent_le_width rules out a tableau in the above-width event.
     Consumer: rectangleTailProbability_eq.
   rectangle_card_pos | proof_shape: content
     escape_witness: rectangleRowMajor constructs an actual tableau for every width.
     Consumers: rectangleTailProbability_eq and zeroCoefficientReadout_fails.
   card_rectangle_tail_eq_point_add_next | proof_shape: content
     escape_witness: explicit bijections identify the two parts of the split survival subtype.
     Consumer: rectangleTailPartition. -/

module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-! Standard tableaux of straight shapes, maximum-cell deletion and rectangle rotation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

public section

namespace NiuQ15

open scoped BigOperators

/-- A diagram with rows numbered from the top, allowing trailing zero lengths. -/
structure RowShape (k : ℕ) where
  rows : Fin k → ℕ
  antitone_rows : Antitone rows

/-- Cells carry the inherited coordinatewise partial order. -/
@[expose] def Cell {k : ℕ} (shape : RowShape k) :=
  {p : Fin k × ℕ // p.2 < shape.rows p.1}

instance instPartialOrderCell {k : ℕ} (shape : RowShape k) : PartialOrder (Cell shape) :=
  inferInstanceAs (PartialOrder {p : Fin k × ℕ // p.2 < shape.rows p.1})

private local instance {k : ℕ} (shape : RowShape k) : DecidableEq (Cell shape) :=
  inferInstanceAs (DecidableEq {p : Fin k × ℕ // p.2 < shape.rows p.1})

private def cellsEquivSigma {k : ℕ} (shape : RowShape k) :
    Cell shape ≃ Σ i : Fin k, Fin (shape.rows i) where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨(x.1, x.2.val), x.2.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

private local instance {k : ℕ} (shape : RowShape k) : Fintype (Cell shape) :=
  Fintype.ofEquiv _ (cellsEquivSigma shape).symm

@[expose] def size {k : ℕ} (shape : RowShape k) : ℕ := ∑ i, shape.rows i

private theorem card_cells {k : ℕ} (shape : RowShape k) :
    Fintype.card (Cell shape) = size shape := by
  rw [Fintype.card_congr (cellsEquivSigma shape), Fintype.card_sigma]
  simp [size]

/-- Bijective zero-based labels, strictly increasing along comparable cells. -/
abbrev Labeling (P : Type*) [Preorder P] (m : ℕ) :=
  {e : P ≃ Fin m // StrictMono e}

private local instance {P : Type*} [Preorder P] [Finite P] {m : ℕ} : Finite (Labeling P m) := by
  infer_instance

private noncomputable local instance {P : Type*} [Preorder P] [Finite P] {m : ℕ} :
    Fintype (Labeling P m) := Fintype.ofFinite _

@[expose] def StandardTableau {k : ℕ} (shape : RowShape k) :=
  Labeling (Cell shape) (size shape)

@[no_expose] noncomputable instance instFintypeStandardTableau {k : ℕ} (shape : RowShape k) :
    Fintype (StandardTableau shape) := by
  exact (inferInstance : Fintype (Labeling (Cell shape) (size shape)))

section LastLabel

variable {P : Type*} [PartialOrder P] {m : ℕ}

/-- The carrier obtained by removing a specified element. -/
private abbrev Without (a : P) := {x : P // x ≠ a}

private def lastCell (t : Labeling P (m + 1)) : P := t.1.symm (Fin.last m)

private theorem lastCell_maximal (t : Labeling P (m + 1)) : ∀ x, ¬lastCell t < x := by
  intro x hx
  have h := t.2 hx
  change t.1 (t.1.symm (Fin.last m)) < t.1 x at h
  rw [Equiv.apply_symm_apply] at h
  exact (Fin.le_last _).not_gt h

private def restrictLast (a : P) (t : {t : Labeling P (m + 1) // lastCell t = a}) :
    Labeling (Without a) m := by
  have ha : t.1.1 a = Fin.last m := by
    exact (congrArg (fun x : P => t.1.1 x) t.2).symm.trans
      (t.1.1.apply_symm_apply (Fin.last m))
  refine ⟨(t.1.1.subtypeEquiv (q := fun x => x ≠ Fin.last m)
    (fun x => by rw [← ha, t.1.1.injective.ne_iff])).trans
    (finSuccAboveEquiv (Fin.last m)).symm, ?_⟩
  intro x y hxy
  simp only [Equiv.trans_apply, finSuccAboveEquiv_symm_apply_last]
  exact t.1.2 (show x.1 < y.1 from hxy)

private def insertLast [DecidableEq P] (a : P) (ha : ∀ x, ¬a < x)
    (t : Labeling (Without a) m) : {t : Labeling P (m + 1) // lastCell t = a} := by
  let e := ((Equiv.optionSubtypeNe a).symm.trans (Equiv.optionCongr t.1)).trans
    (finSuccEquivLast (n := m)).symm
  have eat : e a = Fin.last m := by simp [e]
  have erest (x : P) (hx : x ≠ a) : e x = (t.1 ⟨x, hx⟩).castSucc := by
    simp [e, Equiv.optionSubtypeNe_symm_of_ne hx]
  refine ⟨⟨e, ?_⟩, ?_⟩
  · intro x y hxy
    have hx : x ≠ a := fun hx => ha y (hx ▸ hxy)
    rw [erest x hx]
    by_cases hy : y = a
    · rw [hy, eat]
      exact Fin.castSucc_lt_last _
    · rw [erest y hy]
      exact Fin.castSucc_lt_castSucc_iff.mpr (t.2 (show (⟨x, hx⟩ : Without a) < ⟨y, hy⟩ from hxy))
  · exact e.symm_apply_eq.mpr eat.symm

private theorem restrictLast_label (a : P)
    (t : {t : Labeling P (m + 1) // lastCell t = a}) (x : Without a) :
    ((restrictLast a t).1 x).castSucc = t.1.1 x.1 := by
  apply Fin.ext
  simp [restrictLast, finSuccAboveEquiv_symm_apply_last]

private theorem insertLast_label [DecidableEq P] (a : P) (ha : ∀ x, ¬a < x)
    (t : Labeling (Without a) m) (x : Without a) :
    (insertLast a ha t).1.1 x.1 = (t.1 x).castSucc := by
  simp [insertLast, Equiv.optionSubtypeNe_symm_of_ne x.2]

/-- Restrict to all cells except the cell carrying the largest label, with insertion inverse. -/
private def deleteFixedLast [DecidableEq P] (a : P) (ha : ∀ x, ¬a < x) :
    {t : Labeling P (m + 1) // lastCell t = a} ≃ Labeling (Without a) m where
  toFun := restrictLast a
  invFun := insertLast a ha
  left_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change (insertLast a ha (restrictLast a t)).1.1 x = t.1.1 x
    by_cases hx : x = a
    · subst x
      simpa [insertLast] using (t.1.1.apply_symm_apply (Fin.last m)).symm.trans
        (congrArg (fun x : P => t.1.1 x) t.2)
    · exact (insertLast_label a ha (restrictLast a t) ⟨x, hx⟩).trans
        (restrictLast_label a t ⟨x, hx⟩)
  right_inv t := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Fin.castSucc_injective
    exact (restrictLast_label a (insertLast a ha t) x).trans (insertLast_label a ha t x)

/-- The largest label selects a maximal cell and gives a labeling with that cell removed. -/
private def deleteLast [DecidableEq P] :
    Labeling P (m + 1) ≃ Σ a : {a : P // ∀ x, ¬a < x}, Labeling (Without a.1) m :=
  (Equiv.sigmaFiberEquiv (fun t : Labeling P (m + 1) =>
    (⟨lastCell t, lastCell_maximal t⟩ : {a : P // ∀ x, ¬a < x}))).symm.trans
      (Equiv.sigmaCongrRight fun a =>
        (Equiv.subtypeEquivRight fun _ => ⟨congrArg Subtype.val, Subtype.ext⟩).trans
          (deleteFixedLast a.1 a.2))

end LastLabel

section RemovableRows

variable {k : ℕ} (shape : RowShape k)

/-- The row is nonempty, and its end has no cell below it. -/
@[expose] def RemovableRow :=
  {i : Fin k // 0 < shape.rows i ∧ ∀ j, i < j → shape.rows j < shape.rows i}

noncomputable instance instFintypeRemovableRow : Fintype (RemovableRow shape) := by
  unfold RemovableRow
  exact Fintype.ofFinite _

private def endCell (i : RemovableRow shape) : Cell shape :=
  ⟨(i.1, shape.rows i.1 - 1), Nat.sub_lt i.2.1 Nat.one_pos⟩

private theorem endCell_maximal (i : RemovableRow shape) (x : Cell shape) :
    ¬endCell shape i < x := by
  intro h
  have hr : i.1 ≤ x.1.1 := h.le.1
  have hc : shape.rows i.1 - 1 ≤ x.1.2 := h.le.2
  have hmem := x.2
  rcases hr.eq_or_lt with heq | hlt
  · have hcol : shape.rows i.1 - 1 = x.1.2 := by
      rw [← heq] at hmem
      omega
    exact h.ne (Subtype.ext (Prod.ext heq hcol))
  · have hlen := i.2.2 x.1.1 hlt
    omega

private theorem maximal_is_rowEnd (a : Cell shape) (ha : ∀ x, ¬a < x) :
    a.1.2 = shape.rows a.1.1 - 1 := by
  have hmem := a.2
  by_contra h
  let right : Cell shape := ⟨(a.1.1, a.1.2 + 1), by change a.1.2 + 1 < shape.rows a.1.1; omega⟩
  exact ha right (lt_of_le_not_ge ⟨le_rfl, Nat.le_succ _⟩
    (fun hx => Nat.not_succ_le_self _ hx.2))

private theorem maximal_row_removable (a : Cell shape) (ha : ∀ x, ¬a < x) :
    0 < shape.rows a.1.1 ∧ ∀ j, a.1.1 < j → shape.rows j < shape.rows a.1.1 := by
  have hmem := a.2
  have hend := maximal_is_rowEnd shape a ha
  refine ⟨by omega, fun j hj => ?_⟩
  by_contra! h
  let below : Cell shape := ⟨(j, a.1.2), by change a.1.2 < shape.rows j; omega⟩
  exact ha below (lt_of_le_not_ge ⟨hj.le, le_rfl⟩ (fun hx => hj.not_ge hx.1))

/-- The maximal cells of the product order are exactly the removable row ends. -/
private def maximalCellsEquivRemovable : {a : Cell shape // ∀ x, ¬a < x} ≃ RemovableRow shape where
  toFun a := ⟨a.1.1.1, maximal_row_removable shape a.1 a.2⟩
  invFun i := ⟨endCell shape i, endCell_maximal shape i⟩
  left_inv a := Subtype.ext (Subtype.ext (Prod.ext rfl (maximal_is_rowEnd shape a.1 a.2).symm))
  right_inv _ := rfl

/-- Remove the last cell in a removable row, retaining the same row index type. -/
@[expose] def eraseRowEnd (i : RemovableRow shape) : RowShape k where
  rows j := if j = i.1 then shape.rows j - 1 else shape.rows j
  antitone_rows := by
    intro a b hab
    rcases hab.eq_or_lt with heq | hlt
    · subst b
      exact le_rfl
    · by_cases hi : a = i.1
      · subst a
        have hb := i.2.2 b hlt
        have hne : b ≠ i.1 := hlt.ne.symm
        simpa [hne] using Nat.le_sub_one_of_lt hb
      · simp only [ite_eq_right hi]
        split
        · exact (Nat.sub_le _ _).trans (shape.antitone_rows hab)
        · exact shape.antitone_rows hab

private theorem eraseRowEnd_mem_iff (i : RemovableRow shape) (x : Fin k × ℕ) :
    x.2 < (eraseRowEnd shape i).rows x.1 ↔
      x.2 < shape.rows x.1 ∧ x ≠ (endCell shape i).1 := by
  rcases x with ⟨j, c⟩
  by_cases h : j = i.1
  · subst j
    simp [eraseRowEnd, endCell]
    have hp := i.2.1
    omega
  · simp [eraseRowEnd, endCell, h]

/-- Deleting a maximal cell in the ambient order gives the shortened row shape. -/
private def eraseCellsOrderIso (i : RemovableRow shape) :
    Without (endCell shape i) ≃o Cell (eraseRowEnd shape i) where
  toFun x := ⟨x.1.1, (eraseRowEnd_mem_iff shape i x.1.1).mpr
    ⟨x.1.2, fun h => x.2 (Subtype.ext h)⟩⟩
  invFun x :=
    let h := (eraseRowEnd_mem_iff shape i x.1).mp x.2
    ⟨⟨x.1, h.1⟩, fun he => h.2 (congrArg Subtype.val he)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem size_eraseRowEnd (i : RemovableRow shape) :
    size (eraseRowEnd shape i) + 1 = size shape := by
  let e := (Equiv.optionCongr (eraseCellsOrderIso shape i).toEquiv).symm.trans
    (Equiv.optionSubtypeNe (endCell shape i))
  simpa only [Fintype.card_option, card_cells] using Fintype.card_congr e

private def relabel {α β : Type*} [Preorder α] [Preorder β] {m n : ℕ}
    (e : α ≃o β) (h : m = n) : Labeling α m ≃ Labeling β n :=
  (Equiv.equivCongr e.toEquiv (Fin.castOrderIso h).toEquiv).subtypeEquiv
    (fun f => ⟨fun hf => (Fin.castOrderIso h).strictMono.comp (hf.comp e.symm.strictMono),
      fun hf x y hxy => (Fin.castOrderIso h).lt_iff_lt.mp (by
        simpa using hf (e.strictMono hxy))⟩)

/-- A nonempty standard tableau is uniquely a removable row and a tableau of the
shortened shape. The forward map removes the cell carrying the largest label. -/
private noncomputable def standardTableauDeleteLast (h : 0 < size shape) :
    StandardTableau shape ≃ Σ i : RemovableRow shape, StandardTableau (eraseRowEnd shape i) := by
  let m := size shape - 1
  have hm : size shape = m + 1 := by dsimp [m]; omega
  refine (relabel (OrderIso.refl (Cell shape)) hm).trans (deleteLast.trans ?_)
  refine ((Equiv.sigmaCongrLeft (β := fun a : {a : Cell shape // ∀ x, ¬a < x} =>
    Labeling (Without a.1) m) (maximalCellsEquivRemovable shape).symm).symm).trans ?_
  refine Equiv.sigmaCongrRight fun i => relabel (eraseCellsOrderIso shape i) ?_
  have hsize := size_eraseRowEnd shape i
  omega

theorem card_standardTableau_eq_sum (h : 0 < size shape) :
    Fintype.card (StandardTableau shape) =
      ∑ i : RemovableRow shape, Fintype.card (StandardTableau (eraseRowEnd shape i)) := by
  rw [Fintype.card_congr (standardTableauDeleteLast shape h), Fintype.card_sigma]

end RemovableRows

theorem card_standardTableau_of_size_zero {k : ℕ} (shape : RowShape k) (h : size shape = 0) :
    Fintype.card (StandardTableau shape) = 1 := by
  classical
  have : IsEmpty (Cell shape) := Fintype.card_eq_zero_iff.mp ((card_cells shape).trans h)
  have : IsEmpty (Fin (size shape)) := by rw [h]; infer_instance
  let empty : StandardTableau shape :=
    ⟨Equiv.equivOfIsEmpty _ _, fun x => isEmptyElim x⟩
  have : Unique (StandardTableau shape) :=
    ⟨⟨empty⟩, fun t => Subtype.ext (Equiv.ext fun x => isEmptyElim x)⟩
  exact Fintype.card_unique

section Prefix

variable {P : Type*} [PartialOrder P] {r m : ℕ} {initial : P → Prop}

/-- The prescribed prefix runs through the cells in their prescribed order. -/
private abbrev WithPrefix (e : Fin r ≃o {x : P // initial x}) (m : ℕ) :=
  {t : Labeling P (r + m) // ∀ j, t.1 (e j).1 = j.castAdd m}

private def suffixLabels (r m : ℕ) : Fin m ≃ {i : Fin (r + m) // r ≤ i.val} where
  toFun i := ⟨i.natAdd r, Nat.le_add_right r i.val⟩
  invFun i := ⟨i.1.val - r, by have := i.1.isLt; omega⟩
  left_inv i := Fin.ext (Nat.add_sub_cancel_left r i.val)
  right_inv i := Subtype.ext (Fin.ext (Nat.add_sub_of_le i.2))

private theorem outside_prefix_iff (e : Fin r ≃o {x : P // initial x})
    (t : WithPrefix e m) (x : P) : ¬initial x ↔ r ≤ (t.1.1 x).val := by
  constructor
  · intro hx
    by_contra! hlt
    let j : Fin r := ⟨(t.1.1 x).val, hlt⟩
    have heq : t.1.1 (e j).1 = t.1.1 x := (t.2 j).trans (Fin.ext rfl)
    exact hx (t.1.1.injective heq ▸ (e j).2)
  · intro h hx
    let j := e.symm ⟨x, hx⟩
    have heq : (e j).1 = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
    have hlabel := t.2 j
    rw [heq] at hlabel
    have hval : (t.1.1 x).val = j.val := congrArg Fin.val hlabel
    have hlt := j.isLt
    omega

private def restrictPrefix (e : Fin r ≃o {x : P // initial x})
    (t : WithPrefix e m) : Labeling {x : P // ¬initial x} m :=
  ⟨(t.1.1.subtypeEquiv (outside_prefix_iff e t)).trans (suffixLabels r m).symm, by
    intro x y hxy
    have h := t.1.2 (show x.1 < y.1 from hxy)
    have hx := (outside_prefix_iff e t x.1).mp x.2
    have hy := (outside_prefix_iff e t y.1).mp y.2
    change (t.1.1 x.1).val - r < (t.1.1 y.1).val - r
    omega⟩

private theorem restrictPrefix_label (e : Fin r ≃o {x : P // initial x})
    (t : WithPrefix e m) (x : {x : P // ¬initial x}) :
    ((restrictPrefix e t).1 x).natAdd r = t.1.1 x.1 := by
  exact congrArg Subtype.val ((suffixLabels r m).apply_symm_apply
    ⟨t.1.1 x.1, (outside_prefix_iff e t x.1).mp x.2⟩)

private def paste [DecidablePred initial] (e : Fin r ≃o {x : P // initial x})
    (t : Labeling {x : P // ¬initial x} m) : P ≃ Fin (r + m) :=
  ((Equiv.sumCompl initial).symm.trans (Equiv.sumCongr e.symm.toEquiv t.1)).trans finSumFinEquiv

private theorem paste_first [DecidablePred initial] (e : Fin r ≃o {x : P // initial x})
    (t : Labeling {x : P // ¬initial x} m) (x : P) (hx : initial x) :
    paste e t x = (e.symm ⟨x, hx⟩).castAdd m := by simp [paste, hx]

private theorem paste_rest [DecidablePred initial] (e : Fin r ≃o {x : P // initial x})
    (t : Labeling {x : P // ¬initial x} m) (x : P) (hx : ¬initial x) :
    paste e t x = (t.1 ⟨x, hx⟩).natAdd r := by simp [paste, hx]

private def insertPrefix [DecidablePred initial] (e : Fin r ≃o {x : P // initial x})
    (lower : ∀ ⦃x y⦄, x ≤ y → initial y → initial x)
    (t : Labeling {x : P // ¬initial x} m) : WithPrefix e m := by
  refine ⟨⟨paste e t, ?_⟩, fun j => ?_⟩
  · intro x y hxy
    by_cases hy : initial y
    · have hx := lower hxy.le hy
      rw [paste_first e t x hx, paste_first e t y hy]
      exact Fin.strictMono_castAdd _ (e.symm.strictMono (show
        (⟨x, hx⟩ : {x : P // initial x}) < ⟨y, hy⟩ from hxy))
    · rw [paste_rest e t y hy]
      by_cases hx : initial x
      · rw [paste_first e t x hx]
        change (e.symm ⟨x, hx⟩).val < r + (t.1 ⟨y, hy⟩).val
        exact lt_of_lt_of_le (e.symm ⟨x, hx⟩).isLt (Nat.le_add_right _ _)
      · rw [paste_rest e t x hx]
        exact Fin.natAdd_lt_natAdd_iff r |>.mpr
          (t.2 (show (⟨x, hx⟩ : {x : P // ¬initial x}) < ⟨y, hy⟩ from hxy))
  · rw [paste_first e t _ (e j).2]
    exact congrArg (Fin.castAdd m) (e.symm_apply_apply j)

/-- A fixed initial segment on a lower set can be deleted and reinserted. -/
private def deletePrefix [DecidablePred initial] (e : Fin r ≃o {x : P // initial x})
    (lower : ∀ ⦃x y⦄, x ≤ y → initial y → initial x) :
    WithPrefix e m ≃ Labeling {x : P // ¬initial x} m where
  toFun := restrictPrefix e
  invFun := insertPrefix e lower
  left_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change paste e (restrictPrefix e t) x = t.1.1 x
    by_cases hx : initial x
    · rw [paste_first e _ x hx]
      exact (t.2 (e.symm ⟨x, hx⟩)).symm.trans
        (congrArg (fun y : {x : P // initial x} => t.1.1 y.1) (e.apply_symm_apply ⟨x, hx⟩))
    · rw [paste_rest e _ x hx]
      exact restrictPrefix_label e t ⟨x, hx⟩
  right_inv t := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply (Fin.strictMono_natAdd r).injective
    exact (restrictPrefix_label e (insertPrefix e lower t) x).trans (paste_rest e t x.1 x.2)

end Prefix

section Rectangle

/-- A rectangle with k + 1 rows, so its first row always has an index. -/
@[expose] def rectangle (k n : ℕ) : RowShape (k + 1) :=
  ⟨fun _ => n, fun _ _ _ => le_rfl⟩

theorem size_rectangle (k n : ℕ) : size (rectangle k n) = (k + 1) * n := by
  simp [size, rectangle, Nat.mul_comm]

private def topPrefix {k n : ℕ} (r : ℕ) (x : Cell (rectangle k n)) : Prop :=
  x.1.1 = 0 ∧ x.1.2 < r

private local instance {k n : ℕ} (r : ℕ) : DecidablePred (@topPrefix k n r) :=
  fun x => inferInstanceAs (Decidable (x.1.1 = 0 ∧ x.1.2 < r))

private theorem topPrefix_lower {k n r : ℕ} {x y : Cell (rectangle k n)}
    (h : x ≤ y) (hy : topPrefix r y) : topPrefix r x := by
  have hrow : x.1.1 ≤ y.1.1 := h.1
  have hcol : x.1.2 ≤ y.1.2 := h.2
  exact ⟨Fin.le_zero_iff.mp (hy.1 ▸ hrow), hcol.trans_lt hy.2⟩

private def topPrefixOrder {k n r : ℕ} (hr : r ≤ n) :
    Fin r ≃o {x : Cell (rectangle k n) // topPrefix r x} where
  toFun j := ⟨⟨(0, j.val), j.isLt.trans_le hr⟩, rfl, j.isLt⟩
  invFun x := ⟨x.1.1.2, x.2.2⟩
  left_inv _ := rfl
  right_inv x := Subtype.ext (Subtype.ext (Prod.ext x.2.1.symm rfl))
  map_rel_iff' := ⟨fun h => h.2, fun h => ⟨le_rfl, h⟩⟩

/-- Rotating the complement of the top-row prefix shortens the bottom row. -/
@[expose] def rotatedShape (k n r : ℕ) : RowShape (k + 1) where
  rows i := if i = Fin.last k then n - r else n
  antitone_rows := by
    intro i j hij
    by_cases hi : i = Fin.last k
    · have hj : j = i := le_antisymm (hi ▸ Fin.le_last j) hij
      rw [hj]
    · change (if j = Fin.last k then n - r else n) ≤ (if i = Fin.last k then n - r else n)
      rw [ite_eq_right hi]
      split
      · exact Nat.sub_le _ _
      · exact le_rfl

private theorem rev_eq_last_iff {k : ℕ} (i : Fin (k + 1)) :
    i.rev = Fin.last k ↔ i = 0 := by
  rw [← Fin.rev_zero k, Fin.rev_inj]

private theorem rotate_mem {k n r : ℕ} {i : Fin (k + 1)} {j : ℕ}
    (hj : j < n) (h : ¬(i = 0 ∧ j < r)) :
    n - 1 - j < (rotatedShape k n r).rows i.rev := by
  change n - 1 - j < (if i.rev = Fin.last k then n - r else n)
  by_cases hi : i = 0
  · have hr : r ≤ j := Nat.le_of_not_lt (fun hlt => h ⟨hi, hlt⟩)
    rw [ite_eq_left ((rev_eq_last_iff i).mpr hi)]
    omega
  · rw [ite_eq_right (mt (rev_eq_last_iff i).mp hi)]
    omega

private theorem rotated_mem_lt {k n r : ℕ} (x : Cell (rotatedShape k n r)) : x.1.2 < n := by
  refine x.2.trans_le ?_
  change (if x.1.1 = Fin.last k then n - r else n) ≤ n
  split
  · exact Nat.sub_le _ _
  · exact le_rfl

/-- The coordinate reflection reverses the partial order on all surviving cells. -/
private def rotateCells {k n r : ℕ} :
    ({x : Cell (rectangle k n) // ¬topPrefix r x})ᵒᵈ ≃o Cell (rotatedShape k n r) where
  toFun x := ⟨(x.1.1.1.rev, n - 1 - x.1.1.2), rotate_mem x.1.2 x.2⟩
  invFun x := ⟨⟨(x.1.1.rev, n - 1 - x.1.2), by
    have hx := rotated_mem_lt x
    change n - 1 - x.1.2 < n
    omega⟩, by
    intro h
    have hrow : x.1.1.rev = 0 := h.1
    have hcol : n - 1 - x.1.2 < r := h.2
    have hlen := x.2
    change x.1.2 < (if x.1.1 = Fin.last k then n - r else n) at hlen
    rw [ite_eq_left (by simpa using congrArg Fin.rev hrow)] at hlen
    omega⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.rev_rev _
    · have hx : x.1.1.2 < n := x.1.2
      change n - 1 - (n - 1 - x.1.1.2) = x.1.1.2
      omega
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.rev_rev _
    · have hx := rotated_mem_lt x
      change n - 1 - (n - 1 - x.1.2) = x.1.2
      omega
  map_rel_iff' := by
    intro x y
    have hx : x.1.1.2 < n := x.1.2
    have hy : y.1.1.2 < n := y.1.2
    change (x.1.1.1.rev ≤ y.1.1.1.rev ∧ n - 1 - x.1.1.2 ≤ n - 1 - y.1.1.2) ↔
      (y.1.1.1 ≤ x.1.1.1 ∧ y.1.1.2 ≤ x.1.1.2)
    rw [Fin.rev_le_rev]
    exact and_congr_right (fun _ => by omega)

private theorem size_rectangle_split {k n r : ℕ} (hr : r ≤ n) :
    size (rectangle k n) = r + size (rotatedShape k n r) := by
  let e := (Equiv.sumCompl (@topPrefix k n r)).symm.trans
    ((topPrefixOrder hr).symm.toEquiv.sumCongr (rotateCells (k := k) (n := n) (r := r)).toEquiv)
  simpa only [Fintype.card_sum, Fintype.card_fin, card_cells] using Fintype.card_congr e

private def reverseLabeling {P : Type*} [Preorder P] (m : ℕ) :
    Labeling P m ≃ Labeling Pᵒᵈ m :=
  (Equiv.equivCongr (OrderDual.toDual : P ≃ Pᵒᵈ) (@Fin.revPerm m)).subtypeEquiv
    (fun _ => ⟨fun hf _ _ h => Fin.rev_lt_rev.mpr (hf h),
      fun hf _ _ h => Fin.rev_lt_rev.mp (hf (show _ < _ from h))⟩)

/-- A rectangle with its first r labels in the top-row prefix is equivalent to
the straight shape obtained by rotating the complement. -/
private def rectanglePrefixRotation {k n r : ℕ} (hr : r ≤ n) :
    {t : StandardTableau (rectangle k n) //
      ∀ j : Fin r, (t.1 ((topPrefixOrder hr) j).1).val = j.val} ≃
      StandardTableau (rotatedShape k n r) := by
  let h := size_rectangle_split (k := k) hr
  let e := relabel (OrderIso.refl (Cell (rectangle k n))) h
  refine (e.subtypeEquiv (q := fun u =>
    ∀ j : Fin r, u.1 ((topPrefixOrder hr) j).1 = j.castAdd (size (rotatedShape k n r)))
    (fun t => ⟨fun ht j => Fin.ext (ht j), fun ht j => congrArg Fin.val (ht j)⟩)).trans ?_
  exact (deletePrefix (topPrefixOrder hr) (fun _ _ hxy hy => topPrefix_lower hxy hy)).trans
    ((reverseLabeling _).trans (relabel rotateCells rfl))

@[expose] def secondRowFirst {k n : ℕ} (hn : 0 < n) : Cell (rectangle (k + 1) n) :=
  ⟨(1, 0), hn⟩

/-- In zero-based labels this is the label in the second row's first cell. -/
@[expose] def firstDescent {k n : ℕ} (hn : 0 < n)
    (t : StandardTableau (rectangle (k + 1) n)) : ℕ :=
  (t.1 (secondRowFirst hn)).val

private theorem above_secondRowFirst {k n : ℕ} (hn : 0 < n)
    (t : StandardTableau (rectangle (k + 1) n)) (x : Cell (rectangle (k + 1) n))
    (h : (t.1 x).val < firstDescent hn t) : x.1.1 = 0 := by
  by_contra hrow
  have hx : secondRowFirst hn ≤ x := by
    refine ⟨?_, Nat.zero_le _⟩
    have hval : x.1.1.val ≠ 0 := fun h => hrow (Fin.ext h)
    change 1 ≤ x.1.1.val
    omega
  exact (t.2.monotone hx).not_gt h

private theorem firstDescent_ge_iff_prefix {k n r : ℕ} (hn : 0 < n) (hr : r ≤ n)
    (t : StandardTableau (rectangle (k + 1) n)) :
    r ≤ firstDescent hn t ↔
      ∀ j : Fin r, (t.1 ((topPrefixOrder hr) j).1).val = j.val := by
  constructor
  · intro h
    have identify (j : ℕ) (hj : j < r) :
        (t.1 ((topPrefixOrder hr) ⟨j, hj⟩).1).val = j := by
      induction j using Nat.strong_induction_on with
      | h j ih =>
        let a : Cell (rectangle (k + 1) n) := ((topPrefixOrder hr) ⟨j, hj⟩).1
        let i : Fin (size (rectangle (k + 1) n)) :=
          ⟨j, (hj.trans_le h).trans (t.1 (secondRowFirst hn)).isLt⟩
        let x := t.1.symm i
        have hx : (t.1 x).val = j := congrArg Fin.val (t.1.apply_symm_apply i)
        have hrow : x.1.1 = 0 := above_secondRowFirst hn t x (hx ▸ (hj.trans_le h))
        rcases lt_trichotomy x.1.2 j with hlt | heq | hgt
        · let b : Cell (rectangle (k + 1) n) :=
            ((topPrefixOrder hr) ⟨x.1.2, hlt.trans hj⟩).1
          have hbx : b = x := Subtype.ext (Prod.ext hrow.symm rfl)
          have hlabel : (t.1 b).val = x.1.2 := ih _ hlt (hlt.trans hj)
          rw [hbx, hx] at hlabel
          omega
        · have hax : a = x := Subtype.ext (Prod.ext hrow.symm heq.symm)
          exact (congrArg (fun x => (t.1 x).val) hax).trans hx
        · have hax : a < x := lt_of_le_not_ge ⟨hrow.symm.le, hgt.le⟩
            (fun hxa => hgt.not_ge hxa.2)
          have hlabel : (t.1 a).val < j :=
            (show (t.1 a).val < (t.1 x).val from t.2 hax).trans_le hx.le
          let b : Cell (rectangle (k + 1) n) :=
            ((topPrefixOrder hr) ⟨(t.1 a).val, hlabel.trans hj⟩).1
          have heq : (t.1 b).val = (t.1 a).val := ih _ hlabel (hlabel.trans hj)
          have hba : b = a := t.1.injective (Fin.ext heq)
          have hcols : (t.1 a).val = j := congrArg (fun x : Cell _ => x.1.2) hba
          omega
    exact fun j => identify j.val j.isLt
  · intro h
    by_contra! hn'
    let j : Fin r := ⟨firstDescent hn t, hn'⟩
    have heq : ((topPrefixOrder hr) j).1 = secondRowFirst hn := t.1.injective (Fin.ext (h j))
    have hrows := congrArg (fun x : Cell (rectangle (k + 1) n) => x.1.1) heq
    exact Fin.zero_ne_one hrows

/-- The event D ≥ r has the same cardinality as the straight shape with r
cells removed from the end of its bottom row. -/
private def rectangleTailRotation {k n r : ℕ} (hn : 0 < n) (hr : r ≤ n) :
    {t : StandardTableau (rectangle (k + 1) n) // r ≤ firstDescent hn t} ≃
    StandardTableau (rotatedShape (k + 1) n r) :=
  (Equiv.subtypeEquivRight (firstDescent_ge_iff_prefix hn hr)).trans (rectanglePrefixRotation hr)

private def rectangleCellsEquivProd (k n : ℕ) :
    Cell (rectangle k n) ≃ Fin (k + 1) × Fin n where
  toFun x := (x.1.1, ⟨x.1.2, x.2⟩)
  invFun x := ⟨(x.1, x.2.val), x.2.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The row-major labeling is a standard tableau, even for the empty rectangle. -/
private def rectangleRowMajor (k n : ℕ) : StandardTableau (rectangle k n) := by
  refine ⟨((rectangleCellsEquivProd k n).trans finProdFinEquiv).trans
    (finCongr (size_rectangle k n).symm), ?_⟩
  intro x y hxy
  change x.1.2 + n * x.1.1.val < y.1.2 + n * y.1.1.val
  have hr : x.1.1 ≤ y.1.1 := hxy.le.1
  have hc : x.1.2 ≤ y.1.2 := hxy.le.2
  rcases hr.eq_or_lt with heq | hlt
  · rw [heq]
    exact Nat.add_lt_add_right (lt_of_le_of_ne hc (fun h =>
      hxy.ne (Subtype.ext (Prod.ext heq h)))) _
  · have hn : 0 < n := Nat.zero_lt_of_lt x.2
    exact Nat.add_lt_add_of_le_of_lt hc (Nat.mul_lt_mul_of_pos_left hlt hn)

theorem firstDescent_le_width {k n : ℕ} (hn : 0 < n)
    (t : StandardTableau (rectangle (k + 1) n)) : firstDescent hn t ≤ n := by
  by_contra! h
  let i : Fin (size (rectangle (k + 1) n)) := ⟨n, h.trans (t.1 (secondRowFirst hn)).isLt⟩
  let x := t.1.symm i
  have hx : (t.1 x).val = n := congrArg Fin.val (t.1.apply_symm_apply i)
  have hrow : x.1.1 = 0 := above_secondRowFirst hn t x (by rwa [hx])
  let j : Fin n := ⟨x.1.2, x.2⟩
  have hprefix := (firstDescent_ge_iff_prefix hn le_rfl t).mp h.le j
  have heq : ((topPrefixOrder le_rfl) j).1 = x := Subtype.ext (Prod.ext hrow.symm rfl)
  exact (ne_of_lt x.2)
    (hprefix.symm.trans ((congrArg (fun c => (t.1 c).val) heq).trans hx))

theorem card_rectangle_tail {k n r : ℕ} (hn : 0 < n) (hr : r ≤ n) :
    Nat.card {t : StandardTableau (rectangle (k + 1) n) // r ≤ firstDescent hn t} =
      Fintype.card (StandardTableau (rotatedShape (k + 1) n r)) := by
  rw [Nat.card_congr (rectangleTailRotation hn hr), Nat.card_eq_fintype_card]

theorem card_rectangle_tail_of_width_lt {k n r : ℕ} (hn : 0 < n) (hr : n < r) :
    Nat.card {t : StandardTableau (rectangle (k + 1) n) // r ≤ firstDescent hn t} = 0 := by
  have : IsEmpty {t : StandardTableau (rectangle (k + 1) n) // r ≤ firstDescent hn t} :=
    ⟨fun t => hr.not_ge (t.2.trans (firstDescent_le_width hn t.1))⟩
  exact Nat.card_of_isEmpty

theorem rectangle_card_pos (k n : ℕ) : 0 < Fintype.card (StandardTableau (rectangle k n)) :=
  Fintype.card_pos_iff.mpr ⟨rectangleRowMajor k n⟩

/-- The two consecutive tail events differ by exactly the point event. -/
theorem card_rectangle_tail_eq_point_add_next {k n : ℕ} (hn : 0 < n) (r : ℕ) :
    Nat.card {t : StandardTableau (rectangle (k + 1) n) // r ≤ firstDescent hn t} =
      Nat.card {t : StandardTableau (rectangle (k + 1) n) // firstDescent hn t = r} +
      Nat.card {t : StandardTableau (rectangle (k + 1) n) // r + 1 ≤ firstDescent hn t} := by
  let Tail := {t : StandardTableau (rectangle (k + 1) n) // r ≤ firstDescent hn t}
  let point (t : Tail) := firstDescent hn t.1 = r
  let first : {t : Tail // point t} ≃
      {t : StandardTableau (rectangle (k + 1) n) // firstDescent hn t = r} :=
    ⟨fun t => ⟨t.1.1, t.2⟩, fun t => ⟨⟨t.1, t.2.ge⟩, t.2⟩, fun _ => rfl, fun _ => rfl⟩
  let rest : {t : Tail // ¬point t} ≃
      {t : StandardTableau (rectangle (k + 1) n) // r + 1 ≤ firstDescent hn t} := {
    toFun t := ⟨t.1.1, by
      have hle := t.1.2
      have hne : firstDescent hn t.1.1 ≠ r := t.2
      omega⟩
    invFun t := ⟨⟨t.1, (Nat.le_succ r).trans t.2⟩, (Nat.lt_of_succ_le t.2).ne.symm⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  let (t : Tail) : Decidable (point t) := inferInstanceAs (Decidable (_ = _))
  exact (Nat.card_congr ((Equiv.sumCompl point).symm.trans (first.sumCongr rest))).trans
    Nat.card_sum

end Rectangle
end NiuQ15
