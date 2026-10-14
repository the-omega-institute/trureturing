/- GID: D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux01
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Tau Ceti suppliers for finite-group and Young-diagram identities. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license; the complete license is retained in Library/FiniteGroups/tauceti2026nksuppliers.md.
Modified in trureturing: relocate names into the file namespace, prune unused declarations,
inline type aliases, reuse pinned owners, and adapt the pinned Mathlib APIs.
Authors: The Tau Ceti contributors.
Repository: https://github.com/TauCetiProject/TauCeti
Revision: 5a9ceb62c81b6e1f2784d7f739938686a87ca278
Source files:
  TauCeti/Combinatorics/Young/Diagram.lean
  TauCeti/Combinatorics/Young/OfRowLens.lean
  TauCeti/Combinatorics/Young/SemistandardTableau.lean
  TauCeti/Combinatorics/Young/Tableau.lean
Retirement: when the Mathlib revision pinned in `lake-manifest.json` contains a declaration equivalent to a ported one, its clients use that declaration and the port is deleted.
admission_basis: escape-witness
escape_witness: D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.card_filter_le_sum_take_rowLens
Direct frozen dependencies:
  D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.rowLen_zero
    declaration statement_id: sha256:efaaa12164c1db0e709c1a0104797eb3bf77e2e3e1442c2b671f377ce75a429f.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16827
Declaration classification:
YoungDiagram.getD_rowLens — proof_shape: bind-only;
  consumer: SchurPolynomial04.hsymmPart_eq_sum_kostkaNumber_smul_schurPoly.
YoungDiagram.mergeSort_rowLens — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungDiagram.sort_coe_rowLens.
YoungDiagram.sort_coe_rowLens — proof_shape: bind-only;
  consumer: YoungTableaux04.shapePartition_parts_sort.
YoungDiagram.sum_range_rowLen_eq_card_filter_fst — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungDiagram.card_eq_sum_range_rowLen.
YoungDiagram.card_eq_sum_range_rowLen — proof_shape: bind-only;
  consumer: D5.S3.Quantum.Matrix.Schur.RectangularDualCauchy.NKBetaPermutation.cell_sign.
YoungDiagram.card_filter_cells — proof_shape: bind-only;
  consumer: YoungTableaux03.SemistandardYoungTableau.content_recut.
YoungDiagram.sum_take_rowLens_eq_card_filter_fst — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungDiagram.card_filter_le_sum_take_rowLens.
YoungDiagram.card_filter_fst_lt_filter_snd_eq — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungDiagram.card_filter_le_sum_take_rowLens.
YoungDiagram.card_filter_le_sum_take_rowLens — proof_shape: content;
  consumer: YoungTableaux02.YoungTableau.card_filter_lt_le_card_filter_rowIndex_lt.
YoungDiagram.rowLen_le_of_le — proof_shape: bind-only;
  consumer: SchurPolynomial04.hsymm_mul_diagramSchurPoly.
YoungDiagram.le_of_forall_rowLen_le — proof_shape: bind-only;
  consumer: YoungTableaux04.YoungDiagram.InterlacedBy.le.
YoungDiagram.le_rowLen_of_forall_mem — proof_shape: bind-only;
  consumer: YoungTableaux05.BoundedSSYT.interlacedBy_restrictShape.
YoungDiagram.finite_Iic — proof_shape: bind-only;
  consumer: YoungTableaux04.YoungDiagram.interlacingShapes.
YoungDiagram.mem_iff_of_colLen_le_one — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungDiagram.cells_eq_of_colLen_le_one.
YoungDiagram.cells_eq_of_colLen_le_one — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungDiagram.card_eq_rowLen_of_colLen_le_one.
YoungDiagram.card_eq_rowLen_of_colLen_le_one — proof_shape: bind-only;
  consumer: SchurPolynomial03.BoundedSSYT.rowMultisetEquiv.
YoungDiagram.ofRowLensFin — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungDiagram.colLen_zero_ofRowLensFin_le.
YoungDiagram.rowLen_ofRowLensFin — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungDiagram.ofRowLensFin_rowLen.
YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungDiagram.colLen_zero_ofRowLensFin_le.
YoungDiagram.colLen_zero_ofRowLensFin_le — proof_shape: bind-only;
  consumer: D5.S3.Quantum.Matrix.Schur.MatrixSchurPolynomial.NKSchurMatrix.Shape.diagram_height.
YoungDiagram.ofRowLensFin_rowLen — proof_shape: bind-only;
  consumer: D5.S3.Quantum.Matrix.Schur.RectangularDualCauchy.NKScalarSchur.scalar_diagonal.
SemistandardYoungTableau.entry_le_of_le — proof_shape: bind-only;
  consumer: YoungTableaux05.BoundedSSYT.restrictShape.
YoungTableau.rowIndex — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungTableau.card_filter_colIndex_comp_lt_and_rowIndex_eq_le.
YoungTableau.colIndex — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungTableau.card_filter_colIndex_comp_lt_and_rowIndex_eq_le.
YoungTableau.rowIndex_def — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungTableau.card_filter_rowIndex_lt.
YoungTableau.colIndex_def — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungTableau.colIndex_apply.
YoungTableau.rowIndex_apply — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungTableau.card_filter_rowIndex_lt.
YoungTableau.colIndex_apply — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungTableau.exists_rowIndex_colIndex.
YoungTableau.rowIndex_colIndex_injective — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungTableau.card_filter_colIndex_lt_and_rowIndex_eq.
YoungTableau.rowFiberEquiv — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungTableau.card_filter_rowIndex_eq.
YoungTableau.colFiberEquiv — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungTableau.card_filter_colIndex_eq.
YoungTableau.rowIndex_colIndex_mem — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungTableau.colIndex_lt_rowLen.
YoungTableau.colIndex_lt_rowLen — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungTableau.card_filter_colIndex_lt_and_rowIndex_eq.
YoungTableau.rowIndex_lt_colLen_zero — proof_shape: bind-only;
  consumer: YoungTableaux02.YoungTableau.rowFilling.
YoungTableau.exists_rowIndex_colIndex — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungTableau.card_filter_colIndex_lt_and_rowIndex_eq.
YoungTableau.card_filter_rowIndex_eq — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungTableau.card_filter_colIndex_comp_lt_and_rowIndex_eq_le.
YoungTableau.card_filter_colIndex_eq — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungTableau.exists_ne_and_apply_eq_of_lt_colLen.
YoungTableau.exists_ne_and_apply_eq_of_lt_colLen — proof_shape: bind-only;
  consumer: WeylSpecht13.YoungTableau.permTensorActionAlgHom_youngSymmetrizerOver_eq_zero.
YoungTableau.card_filter_rowIndex_lt — proof_shape: bind-only;
  consumer: YoungTableaux02.YoungTableau.card_filter_lt_le_card_filter_rowIndex_lt.
YoungTableau.card_filter_colIndex_lt_and_rowIndex_eq — proof_shape: bind-only;
  consumer: YoungTableaux01.YoungTableau.sum_card_filter_colIndex_comp_lt_and_rowIndex_eq.
YoungTableau.card_filter_colIndex_comp_lt_and_rowIndex_eq_le — proof_shape: bind-only;
  consumer: YoungTableaux02.YoungTableau.colIndex_lt_rowLen_of_injective.
YoungTableau.sum_card_filter_colIndex_comp_lt_and_rowIndex_eq — proof_shape: bind-only;
  consumer: YoungTableaux02.YoungTableau.colIndex_lt_rowLen_of_injective.
-/

import D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01
import Mathlib.Combinatorics.Young.SemistandardTableau
import Mathlib.Data.List.GetD

namespace D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01

open D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01
open D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.YoungDiagram
open _root_.YoungDiagram
open scoped BigOperators

namespace YoungDiagram

theorem getD_rowLens (μ : YoungDiagram) (i : ℕ) : μ.rowLens.getD i 0 = μ.rowLen i := by
  by_cases hi : i < μ.rowLens.length
  · rw [List.getD_eq_getElem _ _ hi, _root_.YoungDiagram.get_rowLens]
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi),
      D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts.rowLen_zero μ i
        (le_of_eq_of_le _root_.YoungDiagram.length_rowLens.symm (Nat.le_of_not_lt hi))]

@[simp]
private theorem mergeSort_rowLens (μ : YoungDiagram) :
    μ.rowLens.mergeSort (fun a b => decide (b ≤ a)) = μ.rowLens :=
  List.mergeSort_eq_self _ μ.rowLens_sorted.pairwise

theorem sort_coe_rowLens (μ : YoungDiagram) :
    (↑μ.rowLens : Multiset ℕ).sort (· ≥ ·) = μ.rowLens := by
  rw [Multiset.coe_sort]
  exact mergeSort_rowLens μ

theorem sum_range_rowLen_eq_card_filter_fst (μ : YoungDiagram) (k : ℕ) :
    ∑ i ∈ Finset.range k, μ.rowLen i = (μ.cells.filter fun c => c.1 < k).card := by
  symm
  calc
    (μ.cells.filter fun c => c.1 < k).card =
        ∑ i ∈ Finset.range k,
          ((μ.cells.filter fun c => c.1 < k).filter fun c => c.1 = i).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter] at hc
      exact Finset.mem_range.mpr hc.2
    _ = ∑ i ∈ Finset.range k, μ.rowLen i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [μ.rowLen_eq_card]
      congr 1
      ext c
      have hik : i < k := Finset.mem_range.mp hi
      simp only [Finset.mem_filter, _root_.YoungDiagram.mem_cells,
        _root_.YoungDiagram.mem_row_iff]
      aesop

theorem card_eq_sum_range_rowLen (μ : _root_.YoungDiagram) {N : ℕ} (hN : μ.colLen 0 ≤ N) :
    μ.card = ∑ i ∈ Finset.range N, μ.rowLen i := by
  rw [sum_range_rowLen_eq_card_filter_fst]
  refine (congrArg Finset.card (Finset.filter_true_of_mem fun c hc => ?_)).symm
  exact lt_of_lt_of_le ((_root_.YoungDiagram.mem_iff_lt_colLen.mp hc).trans_le
    (μ.colLen_anti 0 c.snd c.snd.zero_le)) hN

theorem card_filter_cells (μ : _root_.YoungDiagram) (p : ℕ × ℕ → Prop) [DecidablePred p] {N : ℕ}
    (hN : μ.colLen 0 ≤ N) :
    (μ.cells.filter p).card
      = ∑ i ∈ Finset.range N, ((Finset.range (μ.rowLen i)).filter fun j => p (i, j)).card := by
  have hcells : μ.cells.filter p
      = (Finset.range N).biUnion fun i =>
          ((Finset.range (μ.rowLen i)).filter fun j => p (i, j)).image fun j => (i, j) := by
    ext c
    obtain ⟨i, j⟩ := c
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
      _root_.YoungDiagram.mem_cells, Prod.mk.injEq]
    constructor
    · rintro ⟨hij, hp⟩
      refine ⟨i, lt_of_lt_of_le (lt_of_lt_of_le (_root_.YoungDiagram.mem_iff_lt_colLen.mp hij)
        (μ.colLen_anti 0 j j.zero_le)) hN, j, ⟨?_, hp⟩, rfl, rfl⟩
      exact _root_.YoungDiagram.mem_iff_lt_rowLen.mp hij
    · rintro ⟨i', -, j', ⟨hj', hp⟩, rfl, rfl⟩
      exact ⟨_root_.YoungDiagram.mem_iff_lt_rowLen.mpr hj', hp⟩
  rw [hcells, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun i _ =>
      Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.snd h
  · intro y _ z _ hyz
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    rintro c ⟨j, -, rfl⟩ ⟨j', -, hj'⟩
    exact hyz (congrArg Prod.fst hj').symm

theorem sum_take_rowLens_eq_card_filter_fst (μ : YoungDiagram) (k : ℕ) :
    (μ.rowLens.take k).sum = (μ.cells.filter fun c => c.1 < k).card := by
  rw [_root_.YoungDiagram.rowLens, ← List.map_take, List.take_range, sum_list_range,
    ← sum_range_rowLen_eq_card_filter_fst]
  have hsub : Finset.range (min k (μ.colLen 0)) ⊆ Finset.range k := fun i hi =>
    Finset.mem_range.mpr (lt_min_iff.mp (Finset.mem_range.mp hi)).1
  refine Finset.sum_subset hsub fun i hi hi' => ?_
  exact D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts.rowLen_zero μ i
    (by simpa [lt_min_iff, Finset.mem_range.mp hi] using Finset.mem_range.not.mp hi')

private theorem card_filter_fst_lt_filter_snd_eq (lam : YoungDiagram) (k j : ℕ) :
    (((lam.cells.filter fun c => c.1 < k)).filter fun c => c.2 = j).card
      = min k (lam.colLen j) := by
  have himg : (((lam.cells.filter fun c => c.1 < k)).filter fun c => c.2 = j)
      = (Finset.range (min k (lam.colLen j))).image fun i => (i, j) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, lt_min_iff,
      _root_.YoungDiagram.mem_cells]
    constructor
    · rintro ⟨⟨hc, hk⟩, hj⟩
      refine ⟨c.1, ⟨hk, ?_⟩, ?_⟩
      · exact _root_.YoungDiagram.mem_iff_lt_colLen.mp (hj ▸ hc)
      · rw [← hj]
    · rintro ⟨i, ⟨hik, hicol⟩, rfl⟩
      exact ⟨⟨_root_.YoungDiagram.mem_iff_lt_colLen.mpr hicol, hik⟩, rfl⟩
  rw [himg, Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.fst h, Finset.card_range]

theorem card_filter_le_sum_take_rowLens {α : Type*} [Fintype α] (lam : YoungDiagram)
    (r : α → ℕ) (f : α → ℕ × ℕ) (hmem : ∀ a, f a ∈ lam.cells) (hinj : Function.Injective f)
    (hcol : ∀ a b, r a = r b → (f a).2 = (f b).2 → a = b) (k : ℕ) :
    (Finset.univ.filter fun a => r a < k).card ≤ (lam.rowLens.take k).sum := by
  classical
  rw [sum_take_rowLens_eq_card_filter_fst]
  -- Every column index in sight is smaller than the length of the top row.
  have hlt : ∀ c ∈ lam.cells, c.2 ∈ Finset.range (lam.rowLen 0) := by
    intro c hc
    refine Finset.mem_range.mpr (lt_of_lt_of_le ?_ (lam.rowLen_anti 0 c.1 c.1.zero_le))
    exact _root_.YoungDiagram.mem_iff_lt_rowLen.mp ((_root_.YoungDiagram.mem_cells c).mp hc)
  -- Split both sides into their columns.
  rw [Finset.card_eq_sum_card_fiberwise (f := fun a => (f a).2)
      (t := Finset.range (lam.rowLen 0)) fun a _ => hlt _ (hmem a),
    Finset.card_eq_sum_card_fiberwise (f := fun c : ℕ × ℕ => c.2)
      (t := Finset.range (lam.rowLen 0)) fun c hc =>
      hlt c (Finset.mem_filter.mp hc).1]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [card_filter_fst_lt_filter_snd_eq lam k j]
  have hfib : ∀ a ∈ ((Finset.univ.filter fun a => r a < k).filter fun a => (f a).2 = j : Finset α),
      r a < k ∧ (f a).2 = j := by
    intro a ha
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
  -- In a fixed column, the elements are separated by their rows, and they fit in the column.
  refine le_min (le_of_le_of_eq ?_ (Finset.card_range k))
    (le_of_le_of_eq ?_ lam.colLen_eq_card.symm)
  · refine Finset.card_le_card_of_injOn r (fun a ha => ?_) fun a ha b hb hab => ?_
    · exact Finset.mem_range.mpr (hfib a ha).1
    · exact hcol a b hab (((hfib a ha).2).trans (hfib b hb).2.symm)
  · refine Finset.card_le_card_of_injOn f (fun a ha => ?_) hinj.injOn
    exact _root_.YoungDiagram.mem_col_iff.mpr
      ⟨(_root_.YoungDiagram.mem_cells _).mp (hmem a), (hfib a ha).2⟩

theorem rowLen_le_of_le {μ ν : YoungDiagram} (h : ν ≤ μ) (i : ℕ) : ν.rowLen i ≤ μ.rowLen i := by
  rcases Nat.eq_zero_or_pos (ν.rowLen i) with h0 | h0
  · omega
  · have hmem : ((i, ν.rowLen i - 1) : ℕ × ℕ) ∈ ν :=
      _root_.YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have := _root_.YoungDiagram.mem_iff_lt_rowLen.mp (h hmem)
    omega

theorem le_of_forall_rowLen_le {μ ν : YoungDiagram} (h : ∀ i, ν.rowLen i ≤ μ.rowLen i) : ν ≤ μ := by
  rintro ⟨i, j⟩ hc
  exact _root_.YoungDiagram.mem_iff_lt_rowLen.mpr
    ((_root_.YoungDiagram.mem_iff_lt_rowLen.mp hc).trans_le (h i))

theorem le_rowLen_of_forall_mem {ν : YoungDiagram} {i k : ℕ}
    (h : ∀ j < k, ((i, j) : ℕ × ℕ) ∈ ν) : k ≤ ν.rowLen i := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Nat.zero_le _
  · have := _root_.YoungDiagram.mem_iff_lt_rowLen.mp (h (k - 1) (by omega))
    omega

theorem finite_Iic (μ : YoungDiagram) : (Set.Iic μ).Finite := by
  have hinj : Set.InjOn _root_.YoungDiagram.cells (Set.Iic μ) :=
    fun _ _ _ _ h => _root_.YoungDiagram.ext h
  refine Set.Finite.of_finite_image ?_ hinj
  refine Set.Finite.subset (μ.cells.powerset : Finset (Finset (ℕ × ℕ))).finite_toSet ?_
  rintro s ⟨ξ, hξ, rfl⟩
  exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr fun c hc => Set.mem_Iic.mp hξ hc)

theorem mem_iff_of_colLen_le_one {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) {i j : ℕ} :
    (i, j) ∈ μ ↔ i = 0 ∧ j < μ.rowLen 0 := by
  grind [_root_.YoungDiagram.mem_cells, _root_.YoungDiagram.mem_iff_lt_colLen,
    _root_.YoungDiagram.mem_iff_lt_rowLen, μ.colLen_anti 0 j (Nat.zero_le _)]

private theorem cells_eq_of_colLen_le_one {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) :
    μ.cells = {0} ×ˢ Finset.range (μ.rowLen 0) := by
  ext ⟨i, j⟩
  simp [_root_.YoungDiagram.mem_cells, mem_iff_of_colLen_le_one h, eq_comm, and_comm]

theorem card_eq_rowLen_of_colLen_le_one {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) :
    μ.card = μ.rowLen 0 := by
  simp [_root_.YoungDiagram.card, cells_eq_of_colLen_le_one h]
end YoungDiagram

namespace YoungDiagram
variable {n : ℕ}

def ofRowLensFin (f : Fin n → ℕ) (hf : Antitone f) : _root_.YoungDiagram :=
  _root_.YoungDiagram.ofRowLens (List.ofFn f) hf.sortedGE_ofFn

@[simp]
theorem rowLen_ofRowLensFin (f : Fin n → ℕ) (hf : Antitone f) (i : Fin n) :
    (ofRowLensFin f hf).rowLen i = f i := by
  have h : (i : ℕ) < (List.ofFn f).length := by simp
  simpa [ofRowLensFin] using
    _root_.YoungDiagram.rowLen_ofRowLens (w := List.ofFn f) (hw := hf.sortedGE_ofFn) ⟨i, h⟩

@[simp]
theorem rowLen_ofRowLensFin_eq_zero_of_le (f : Fin n → ℕ) (hf : Antitone f) {i : ℕ} (hi : n ≤ i) :
    (ofRowLensFin f hf).rowLen i = 0 := by
  by_contra h
  have hmem : ((i, 0) : ℕ × ℕ) ∈ ofRowLensFin f hf :=
    _root_.YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h)
  grind [ofRowLensFin, _root_.YoungDiagram.mem_ofRowLens, List.length_ofFn]

theorem colLen_zero_ofRowLensFin_le (f : Fin n → ℕ) (hf : Antitone f) :
    (ofRowLensFin f hf).colLen 0 ≤ n := by
  by_contra h
  have hmem : ((n, 0) : ℕ × ℕ) ∈ ofRowLensFin f hf :=
    _root_.YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_le h)
  grind [_root_.YoungDiagram.mem_iff_lt_rowLen, rowLen_ofRowLensFin_eq_zero_of_le]

theorem ofRowLensFin_rowLen (μ : _root_.YoungDiagram) (hμ : μ.colLen 0 ≤ n) :
    ofRowLensFin (fun i : Fin n => μ.rowLen i) (fun _ _ h => μ.rowLen_anti _ _ h) = μ := by
  refine rowLen_injective (funext fun i => ?_)
  by_cases hi : i < n
  · simpa using rowLen_ofRowLensFin _ _ ⟨i, hi⟩
  · grind [rowLen_ofRowLensFin_eq_zero_of_le,
      D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts.rowLen_zero]
end YoungDiagram

namespace SemistandardYoungTableau
variable {μ : YoungDiagram}

theorem entry_le_of_le (T : SemistandardYoungTableau μ) {i₁ i₂ j₁ j₂ : ℕ} (hi : i₁ ≤ i₂)
    (hj : j₁ ≤ j₂) (hc : ((i₂, j₂) : ℕ × ℕ) ∈ μ) : T i₁ j₁ ≤ T i₂ j₂ :=
  (T.row_weak_of_le hj (μ.up_left_mem hi le_rfl hc)).trans (T.col_weak hi hc)
end SemistandardYoungTableau

section

namespace YoungTableau
variable {μ : YoungDiagram}

def rowIndex (t : (↥μ.cells ≃ Fin μ.card)) (k : Fin μ.card) : ℕ := (t.symm k : ℕ × ℕ).1

def colIndex (t : (↥μ.cells ≃ Fin μ.card)) (k : Fin μ.card) : ℕ := (t.symm k : ℕ × ℕ).2

theorem rowIndex_def (t : (↥μ.cells ≃ Fin μ.card)) (k : Fin μ.card) :
    rowIndex t k = (t.symm k : ℕ × ℕ).1 := by
  rw [rowIndex]

theorem colIndex_def (t : (↥μ.cells ≃ Fin μ.card)) (k : Fin μ.card) :
    colIndex t k = (t.symm k : ℕ × ℕ).2 := by
  rw [colIndex]
@[simp]
theorem rowIndex_apply (t : (↥μ.cells ≃ Fin μ.card)) (c : ↥μ.cells) :
    rowIndex t (t c) = (c : ℕ × ℕ).1 := by
  rw [rowIndex_def, Equiv.symm_apply_apply]
@[simp]
theorem colIndex_apply (t : (↥μ.cells ≃ Fin μ.card)) (c : ↥μ.cells) :
    colIndex t (t c) = (c : ℕ × ℕ).2 := by
  rw [colIndex_def, Equiv.symm_apply_apply]

theorem rowIndex_colIndex_injective (t : (↥μ.cells ≃ Fin μ.card)) :
    Function.Injective fun k => (rowIndex t k, colIndex t k) := by
  intro k l h
  simp only [rowIndex_def, colIndex_def, Prod.mk.injEq] at h
  exact t.symm.injective (Subtype.ext (Prod.ext h.1 h.2))

private def rowFiberEquiv (t : (↥μ.cells ≃ Fin μ.card)) (i : ℕ) :
    {k : Fin μ.card // rowIndex t k = i} ≃ ↥(μ.row i) :=
  -- the two predicates are given explicitly: inferring them from `Iff.rfl` would state the source
  -- subtype through the unfolding of `rowIndex` rather than through `rowIndex` itself
  (Equiv.subtypeEquiv (p := fun k => rowIndex t k = i) (q := fun c : ↥μ.cells => (↑c : ℕ × ℕ).1 = i)
      t.symm fun _ => Iff.rfl).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ μ.cells) fun c => c.1 = i).trans <|
      Equiv.subtypeEquivRight fun _ => by
        rw [YoungDiagram.mem_row_iff, YoungDiagram.mem_cells]

private def colFiberEquiv (t : (↥μ.cells ≃ Fin μ.card)) (j : ℕ) :
    {k : Fin μ.card // colIndex t k = j} ≃ ↥(μ.col j) :=
  -- as for `rowFiberEquiv`, the two predicates are given explicitly
  (Equiv.subtypeEquiv (p := fun k => colIndex t k = j) (q := fun c : ↥μ.cells => (↑c : ℕ × ℕ).2 = j)
      t.symm fun _ => Iff.rfl).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ μ.cells) fun c => c.2 = j).trans <|
      Equiv.subtypeEquivRight fun _ => by
        rw [YoungDiagram.mem_col_iff, YoungDiagram.mem_cells]

private theorem rowIndex_colIndex_mem (t : (↥μ.cells ≃ Fin μ.card)) (x : Fin μ.card) :
    (rowIndex t x, colIndex t x) ∈ μ := by
  rw [rowIndex_def, colIndex_def]
  simp

private theorem colIndex_lt_rowLen (t : (↥μ.cells ≃ Fin μ.card)) (x : Fin μ.card) :
    colIndex t x < μ.rowLen (rowIndex t x) :=
  YoungDiagram.mem_iff_lt_rowLen.mp (rowIndex_colIndex_mem t x)

theorem rowIndex_lt_colLen_zero (t : (↥μ.cells ≃ Fin μ.card)) (x : Fin μ.card) :
    rowIndex t x < μ.colLen 0 :=
  (YoungDiagram.mem_iff_lt_colLen.mp (rowIndex_colIndex_mem t x)).trans_le
    (μ.colLen_anti 0 _ (Nat.zero_le _))

private theorem exists_rowIndex_colIndex (t : (↥μ.cells ≃ Fin μ.card)) {i j : ℕ} (h : (i, j) ∈ μ) :
    ∃ x, rowIndex t x = i ∧ colIndex t x = j :=
  ⟨t ⟨(i, j), (YoungDiagram.mem_cells _).mpr h⟩, by simp, by simp⟩

theorem card_filter_rowIndex_eq (t : (↥μ.cells ≃ Fin μ.card)) (i : ℕ) :
    (Finset.univ.filter fun y => rowIndex t y = i).card = μ.rowLen i := by
  rw [← Fintype.card_subtype, Fintype.card_congr (rowFiberEquiv t i), Fintype.card_coe]
  exact (YoungDiagram.rowLen_eq_card μ).symm

private theorem card_filter_colIndex_eq (t : (↥μ.cells ≃ Fin μ.card)) (j : ℕ) :
    (Finset.univ.filter fun y => colIndex t y = j).card = μ.colLen j := by
  rw [← Fintype.card_subtype, Fintype.card_congr (colFiberEquiv t j), Fintype.card_coe]
  exact (YoungDiagram.colLen_eq_card μ).symm

theorem exists_ne_and_apply_eq_of_lt_colLen (t : (↥μ.cells ≃ Fin μ.card)) {α : Type*} [Fintype α]
    {j : ℕ} (hn : Fintype.card α < μ.colLen j) (p : Fin μ.card → α) :
    ∃ a b : Fin μ.card, colIndex t a = j ∧ colIndex t b = j ∧ a ≠ b ∧ p a = p b := by
  classical
  have hcard : Fintype.card {ℓ : Fin μ.card // colIndex t ℓ = j} = μ.colLen j := by
    rw [Fintype.card_subtype]
    exact card_filter_colIndex_eq t j
  obtain ⟨a, b, hab, hpab⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun ℓ : {ℓ : Fin μ.card // colIndex t ℓ = j} => p ℓ)
      (by rw [hcard]; exact hn)
  exact ⟨a, b, a.2, b.2, fun h => hab (Subtype.ext h), hpab⟩

theorem card_filter_rowIndex_lt (t : (↥μ.cells ≃ Fin μ.card)) (k : ℕ) :
    (Finset.univ.filter fun x => rowIndex t x < k).card = (μ.rowLens.take k).sum := by
  classical
  rw [D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.sum_take_rowLens_eq_card_filter_fst]
  refine Finset.card_bij (fun x _ => ((t.symm x : ↥μ.cells) : ℕ × ℕ)) (fun x hx => ?_)
    (fun x _ y _ h => t.symm.injective (Subtype.ext h)) fun c hc => ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, rowIndex_def] at hx
    exact Finset.mem_filter.mpr ⟨(t.symm x).2, hx⟩
  · rw [Finset.mem_filter] at hc
    refine ⟨t ⟨c, hc.1⟩, ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, rowIndex_apply] using hc.2
    · rw [Equiv.symm_apply_apply]

private theorem card_filter_colIndex_lt_and_rowIndex_eq (t : (↥μ.cells ≃ Fin μ.card)) (i k : ℕ) :
    (Finset.univ.filter fun y => colIndex t y < k ∧ rowIndex t y = i).card
      = min (μ.rowLen i) k := by
  have hinj : Set.InjOn (colIndex t)
      ↑(Finset.univ.filter fun y => colIndex t y < k ∧ rowIndex t y = i) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact rowIndex_colIndex_injective t (Prod.ext (ha.2.trans hb.2.symm) hab)
  have himg : (Finset.univ.filter fun y => colIndex t y < k ∧ rowIndex t y = i).image
      (colIndex t) = (Finset.range (μ.rowLen i)).filter fun j => j < k := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨hy2 ▸ colIndex_lt_rowLen t y, hy1⟩
    · rintro ⟨hj1, hj2⟩
      obtain ⟨y, hy1, hy2⟩ :=
        exists_rowIndex_colIndex t (YoungDiagram.mem_iff_lt_rowLen.mpr hj1)
      exact ⟨y, ⟨hy2 ▸ hj2, hy1⟩, hy2⟩
  have hrange : ((Finset.range (μ.rowLen i)).filter fun j => j < k)
      = Finset.range (min (μ.rowLen i) k) := by
    ext j
    simp
  rw [← Finset.card_image_of_injOn hinj, himg, hrange, Finset.card_range]

theorem card_filter_colIndex_comp_lt_and_rowIndex_eq_le (t : (↥μ.cells ≃ Fin μ.card))
    {u : Fin μ.card → Fin μ.card}
    (hu : Function.Injective fun x => (rowIndex t x, colIndex t (u x))) (i k : ℕ) :
    (Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).card
      ≤ min (μ.rowLen i) k := by
  refine le_min ?_ ?_
  · rw [← card_filter_rowIndex_eq t i]
    refine Finset.card_le_card fun y hy => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.2
  · have hinj : Set.InjOn (fun y => colIndex t (u y))
        ↑(Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i) := by
      intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hu (Prod.ext (ha.2.trans hb.2.symm) hab)
    calc (Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).card
        = ((Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).image
            fun y => colIndex t (u y)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range k).card := by
            refine Finset.card_le_card fun j hj => ?_
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hj
            obtain ⟨y, ⟨hy1, _⟩, rfl⟩ := hj
            exact Finset.mem_range.mpr hy1
      _ = k := Finset.card_range k

theorem sum_card_filter_colIndex_comp_lt_and_rowIndex_eq (t : (↥μ.cells ≃ Fin μ.card))
    (u : Equiv.Perm (Fin μ.card)) (k : ℕ) :
    ∑ i ∈ Finset.image (rowIndex t) Finset.univ,
        (Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).card
      = ∑ i ∈ Finset.image (rowIndex t) Finset.univ, min (μ.rowLen i) k := by
  have hmemS : ∀ y : Fin μ.card, rowIndex t y ∈ Finset.image (rowIndex t) Finset.univ :=
    fun y => Finset.mem_image_of_mem _ (Finset.mem_univ y)
  have h1 : (Finset.univ.filter fun y => colIndex t (u y) < k).card
      = ∑ i ∈ Finset.image (rowIndex t) Finset.univ,
          (Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := rowIndex t)
      (t := Finset.image (rowIndex t) Finset.univ) fun y _ => hmemS y]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.filter_filter]
  have h2 : (Finset.univ.filter fun y => colIndex t y < k).card
      = ∑ i ∈ Finset.image (rowIndex t) Finset.univ,
          (Finset.univ.filter fun y => colIndex t y < k ∧ rowIndex t y = i).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := rowIndex t)
      (t := Finset.image (rowIndex t) Finset.univ) fun y _ => hmemS y]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.filter_filter]
  have h3 : (Finset.univ.filter fun y => colIndex t (u y) < k).card
      = (Finset.univ.filter fun y => colIndex t y < k).card :=
    Finset.card_equiv u fun i => by simp
  rw [← h1, h3, h2]
  exact Finset.sum_congr rfl fun i _ => card_filter_colIndex_lt_and_rowIndex_eq t i k
variable {n : ℕ}
end YoungTableau
end

end D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01
