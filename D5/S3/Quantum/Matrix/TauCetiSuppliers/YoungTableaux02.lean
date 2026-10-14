/- GID: D5/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/TauCetiSuppliers/YoungTableaux02
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
Copyright (c) 2026 Kevin Gomez. All rights reserved.
PartitionYoungDiagram author: Kevin Gomez.
Mathlib revision: 3b531c35df33d6bbe64b4e87dec056211d3a5676
Mathlib blob: ac23c7777b7fe62455d359a79c1cab5d0e7b8fe0
Source files:
  TauCeti/Combinatorics/Young/Tableau.lean
  TauCeti/Combinatorics/Young/Dominance.lean
  TauCeti/Combinatorics/Young/StandardTableau/Basic.lean
  TauCeti/Combinatorics/Young/StandardTableau/Reading.lean
  TauCeti/Compat/PartitionYoungDiagram.lean
  TauCeti/Combinatorics/Young/Kostka.lean
Retirement: when the Mathlib revision pinned in `lake-manifest.json` contains a declaration equivalent to a ported one, its clients use that declaration and the port is deleted.
admission_basis: escape-witness
escape_witness: D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.le_entry
Direct frozen dependencies:
  D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.rowLen_zero
    declaration statement_id: sha256:efaaa12164c1db0e709c1a0104797eb3bf77e2e3e1442c2b671f377ce75a429f.
  D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts.rowLens_sum
    declaration statement_id: sha256:ade544a7169cf7900d9485f566fd666f1311bcc62ebaf0cb3c8f19d8a4ed976e.
  D5/S3/Combinatorics/TwoLayerSolidPartitions.youngPartition
    declaration statement_id: sha256:0395c8d3ea7f78b248591b3337e223abe154192be434c949e2cbfa6d466771bd.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16827
Diagram/partition maps use
  D5.S3.Combinatorics.TwoLayerSolidPartitions.youngPartition and its inverse.
Declaration classification:
YoungTableau.colIndex_lt_rowLen_of_injective — proof_shape: bind-only;
  consumer: WeylSpecht08.YoungTableau.mem_mul_of_not_rowMeetsColumnTwice.
YoungTableau.card_filter_lt_le_card_filter_rowIndex_lt — proof_shape: bind-only;
  consumer: YoungTableaux02.YoungTableau.sum_take_rowLens_le_of_injective.
YoungTableau.rowFilling — proof_shape: bind-only;
  consumer: YoungTableaux02.YoungTableau.val_rowFilling.
YoungTableau.val_rowFilling — proof_shape: bind-only;
  consumer: WeylSpecht13.YoungTableau.repr_symmetrizer_tensorPowerBasis_eq_card_rowSubgroup.
YoungTableau.relabel — proof_shape: bind-only;
  consumer: YoungTableaux02.YoungTableau.colIndex_relabel.
YoungTableau.relabel_apply — proof_shape: bind-only;
  consumer: WeylSpecht09.YoungTableau.rowYoungConjugator_relabel.
YoungTableau.relabel_symm_apply — proof_shape: bind-only;
  consumer: YoungTableaux02.YoungTableau.colIndex_relabel.
YoungTableau.rowIndex_relabel — proof_shape: bind-only;
  consumer: WeylSpecht07.YoungTableau.rowSubgroup_relabel.
YoungTableau.colIndex_relabel — proof_shape: bind-only;
  consumer: WeylSpecht07.YoungTableau.colSubgroup_relabel.
YoungTableau.relabelPerm — proof_shape: bind-only;
  consumer: YoungTableaux02.YoungTableau.exists_relabel_eq.
YoungTableau.relabel_relabelPerm — proof_shape: bind-only;
  consumer: YoungTableaux02.YoungTableau.exists_relabel_eq.
YoungTableau.exists_relabel_eq — proof_shape: bind-only;
  consumer:
    WeylSpecht10.YoungTableau.exists_asAlgebraHom_columnAntisymmetrizer_single_eq_sign_smul.
YoungTableau.nonempty — proof_shape: bind-only;
  consumer: WeylSpecht09.YoungTableau.tabloid_surjective.
YoungTableau.sum_take_rowLens_le_of_injective — proof_shape: bind-only;
  consumer: WeylSpecht11.sum_take_rowLens_le_of_transportedColumnAntisymmetrizer_ne_zero.
StandardYoungTableau — proof_shape: bind-only;
  consumer: YoungTableaux02.StandardYoungTableau.rowSuperstandard.
YoungDiagram.readingIndex — proof_shape: bind-only;
  consumer: YoungTableaux02.StandardYoungTableau.rowSuperstandard.
YoungDiagram.readingIndex_lt_card — proof_shape: bind-only;
  consumer: YoungTableaux02.StandardYoungTableau.rowSuperstandard.
YoungDiagram.readingIndex_lt_readingIndex_of_fst_lt — proof_shape: bind-only;
  consumer: YoungTableaux02.StandardYoungTableau.rowSuperstandard.
YoungDiagram.readingIndex_lt_readingIndex_of_snd_lt — proof_shape: bind-only;
  consumer: YoungTableaux02.StandardYoungTableau.rowSuperstandard.
YoungDiagram.eq_of_readingIndex_eq — proof_shape: bind-only;
  consumer: YoungTableaux02.StandardYoungTableau.rowSuperstandard.
StandardYoungTableau.rowSuperstandard — proof_shape: bind-only;
  consumer:
    D5.S3.Quantum.Matrix.Schur.UnitaryPolynomialRepresentations.NKWeylPolynomial.polynomial_weyl.
YoungDiagram.sum_rowLens_eq_card — proof_shape: bind-only;
  consumer: SchurPolynomial04.hsymmPart_eq_sum_kostkaNumber_smul_schurPoly.
YoungDiagram.card_transpose — proof_shape: bind-only;
  consumer: D5.S3.Quantum.Matrix.Schur.RectangularDualCauchy.NKBetaParity.exponent_sum.
YoungDiagram.rowLens_ofPartition_eq_sort_parts — proof_shape: bind-only;
  consumer: SchurPolynomial04.hsymmPart_eq_sum_kostkaNumber_smul_schurPoly.
YoungDiagram.card_ofPartition — proof_shape: bind-only;
  consumer: SchurPolynomial02.isHomogeneous_schurPoly.
YoungDiagram.ofPartition_toPartition — proof_shape: bind-only;
  consumer: SchurPolynomial04.card_weight_eq_sum_partition.
YoungDiagram.toPartition_ofPartition — proof_shape: bind-only;
  consumer: WeylSpecht14.sum_spechtChar_mul_char_permutationModule_eq_zero.
SemistandardYoungTableau.content — proof_shape: bind-only;
  consumer: YoungTableaux02.SemistandardYoungTableau.content_apply.
SemistandardYoungTableau.content_apply — proof_shape: bind-only;
  consumer: YoungTableaux02.SemistandardYoungTableau.content_highestWeight.
SemistandardYoungTableau.support_content — proof_shape: bind-only;
  consumer: YoungTableaux02.SemistandardYoungTableau.finite_content_eq.
SemistandardYoungTableau.le_entry — proof_shape: content;
  consumer: YoungTableaux02.BoundedSSYT.isEmpty_of_lt_colLen.
SemistandardYoungTableau.filter_entry_lt_subset_filter_fst_lt — proof_shape: content;
  consumer: YoungTableaux02.SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen.
SemistandardYoungTableau.sum_content_eq_card_filter — proof_shape: bind-only;
  consumer: YoungTableaux02.SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen.
SemistandardYoungTableau.sum_content_eq_card — proof_shape: bind-only;
  consumer: SchurPolynomial02.BoundedSSYT.sum_weight.
SemistandardYoungTableau.sum_content_le_sum_take_rowLens — proof_shape: content;
  consumer: YoungTableaux02.sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero.
SemistandardYoungTableau.content_highestWeight — proof_shape: bind-only;
  consumer: YoungTableaux02.diagramKostkaNumber_rowLen.
SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen — proof_shape: content;
  consumer: YoungTableaux02.diagramKostkaNumber_rowLen.
SemistandardYoungTableau.finite_content_eq — proof_shape: bind-only;
  consumer: YoungTableaux02.diagramKostkaNumber_ne_zero_iff.
BoundedSSYT — proof_shape: bind-only;
  consumer: YoungTableaux02.BoundedSSYT.entry_lt.
BoundedSSYT.entry_lt — proof_shape: bind-only;
  consumer: YoungTableaux02.BoundedSSYT.isEmpty_of_lt_colLen.
BoundedSSYT.isEmpty_of_lt_colLen — proof_shape: content;
  consumer: SchurPolynomial02.diagramSchurPoly_eq_zero_of_lt_colLen.
BoundedSSYT.instUniqueBotYoungDiagram — proof_shape: bind-only;
  consumer: SchurPolynomial02.diagramSchurPoly_bot.
finite_boundedSSYT — proof_shape: bind-only;
  consumer: YoungTableaux02.instFintypeBoundedSSYT.
instFintypeBoundedSSYT — proof_shape: bind-only;
  consumer:
    D5.S3.Quantum.Matrix.Schur.MatrixSchurPolynomial.NKSchurMatrix.dimension_eq_tableau_card.
diagramKostkaNumber — proof_shape: bind-only;
  consumer: YoungTableaux02.diagramKostkaNumber_def.
diagramKostkaNumber_def — proof_shape: bind-only;
  consumer: YoungTableaux02.diagramKostkaNumber_ne_zero_iff.
diagramKostkaNumber_ne_zero_iff — proof_shape: bind-only;
  consumer: YoungTableaux02.sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero.
diagramKostkaNumber_rowLen — proof_shape: content;
  consumer: SchurPolynomial02.coeff_diagramSchurPoly_rowLenWeight.
sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero — proof_shape: content;
  consumer: YoungTableaux03.dominates_of_kostkaNumber_ne_zero.
-/

import D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01
import D5.S3.Combinatorics.TwoLayerSolidPartitions

namespace D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02

open D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01
open D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01
open D5.S3.Quantum.Matrix.TauCetiSuppliers.AlgebraGroups01.YoungDiagram
open D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram
open D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungTableau
open _root_.YoungDiagram
open scoped BigOperators

section
namespace YoungTableau
variable {μ : YoungDiagram}

theorem colIndex_lt_rowLen_of_injective (t : (↥μ.cells ≃ Fin μ.card)) (u : Equiv.Perm (Fin μ.card))
    (hu : Function.Injective fun x => (rowIndex t x, colIndex t (u x))) (x : Fin μ.card) :
    colIndex t (u x) < μ.rowLen (rowIndex t x) := by
  have hmemS : ∀ y : Fin μ.card, rowIndex t y ∈ Finset.image (rowIndex t) Finset.univ :=
    fun y => Finset.mem_image_of_mem _ (Finset.mem_univ y)
  -- The row-wise upper bounds add up to the total, so each is an equality.
  have hi := (Finset.sum_eq_sum_iff_of_le fun i _ =>
      card_filter_colIndex_comp_lt_and_rowIndex_eq_le t hu i (μ.rowLen (rowIndex t x))).mp
    (sum_card_filter_colIndex_comp_lt_and_rowIndex_eq t u (μ.rowLen (rowIndex t x)))
    (rowIndex t x) (hmemS x)
  rw [min_self] at hi
  -- a subset of the row with the same cardinality is the whole row
  have hsub : (Finset.univ.filter fun y =>
        colIndex t (u y) < μ.rowLen (rowIndex t x) ∧ rowIndex t y = rowIndex t x)
      ⊆ Finset.univ.filter fun y => rowIndex t y = rowIndex t x := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.2
  have hEq := Finset.eq_of_subset_of_card_le hsub
    (le_of_eq (by rw [card_filter_rowIndex_eq t (rowIndex t x), hi]))
  have hx : x ∈ Finset.univ.filter fun y =>
      colIndex t (u y) < μ.rowLen (rowIndex t x) ∧ rowIndex t y = rowIndex t x := by
    rw [hEq]
    simp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact hx.1

private theorem card_filter_lt_le_card_filter_rowIndex_lt (t : (↥μ.cells ≃ Fin μ.card)) {p : Fin μ.card → ℕ}
    (hp : Function.Injective fun x => (p x, colIndex t x)) (m : ℕ) :
    (Finset.univ.filter fun x => p x < m).card ≤
      (Finset.univ.filter fun x => rowIndex t x < m).card := by
  rw [card_filter_rowIndex_lt]
  refine D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.card_filter_le_sum_take_rowLens μ p
    (fun x => ((t.symm x : ↥μ.cells) : ℕ × ℕ)) (fun x => (t.symm x).2)
    (fun x y hxy => t.symm.injective (Subtype.ext hxy)) (fun x y hv hc => ?_) m
  exact hp (Prod.ext hv (by simpa only [colIndex_def] using hc))
variable {n : ℕ}

def rowFilling (t : (↥μ.cells ≃ Fin μ.card)) (hn : μ.colLen 0 ≤ n) (x : Fin μ.card) : Fin n :=
  ⟨rowIndex t x, (rowIndex_lt_colLen_zero t x).trans_le hn⟩
@[simp]
theorem val_rowFilling (t : (↥μ.cells ≃ Fin μ.card)) (hn : μ.colLen 0 ≤ n) (x : Fin μ.card) :
    (rowFilling t hn x : ℕ) = rowIndex t x :=
  (rfl)

def relabel (σ : Equiv.Perm (Fin μ.card)) (t : (↥μ.cells ≃ Fin μ.card)) : (↥μ.cells ≃ Fin μ.card) :=
  t.trans σ
@[simp]
theorem relabel_apply (σ : Equiv.Perm (Fin μ.card)) (t : (↥μ.cells ≃ Fin μ.card)) (c : ↥μ.cells) :
    relabel σ t c = σ (t c) :=
  (rfl)
@[simp]
private theorem relabel_symm_apply (σ : Equiv.Perm (Fin μ.card)) (t : (↥μ.cells ≃ Fin μ.card)) (k : Fin μ.card) :
    (relabel σ t).symm k = t.symm (σ⁻¹ k) := by
  rw [relabel, Equiv.symm_trans_apply, Equiv.Perm.inv_def]

@[simp]
theorem rowIndex_relabel (σ : Equiv.Perm (Fin μ.card)) (t : (↥μ.cells ≃ Fin μ.card)) (k : Fin μ.card) :
    rowIndex (relabel σ t) k = rowIndex t (σ⁻¹ k) := by
  rw [rowIndex_def, rowIndex_def, relabel_symm_apply]

@[simp]
theorem colIndex_relabel (σ : Equiv.Perm (Fin μ.card)) (t : (↥μ.cells ≃ Fin μ.card)) (k : Fin μ.card) :
    colIndex (relabel σ t) k = colIndex t (σ⁻¹ k) := by
  rw [colIndex_def, colIndex_def, relabel_symm_apply]

def relabelPerm (t t' : (↥μ.cells ≃ Fin μ.card)) : Equiv.Perm (Fin μ.card) :=
  t.symm.trans t'
@[simp]
theorem relabel_relabelPerm (t t' : (↥μ.cells ≃ Fin μ.card)) : relabel (relabelPerm t t') t = t' := by
  rw [relabel, relabelPerm, ← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]

theorem exists_relabel_eq (t t' : (↥μ.cells ≃ Fin μ.card)) : ∃ σ, relabel σ t = t' :=
  ⟨relabelPerm t t', relabel_relabelPerm t t'⟩

theorem nonempty (μ : YoungDiagram) : Nonempty ((↥μ.cells ≃ Fin μ.card)) :=
  ⟨μ.cells.equivFin⟩
end YoungTableau
end

section
namespace YoungTableau
variable {lam m : YoungDiagram}

theorem sum_take_rowLens_le_of_injective (t : (↥lam.cells ≃ Fin lam.card)) (s : (↥m.cells ≃ Fin m.card))
    (σ : Fin m.card ≃ Fin lam.card)
    (h : ∀ x y, rowIndex s x = rowIndex s y → colIndex t (σ x) = colIndex t (σ y) → x = y)
    (k : ℕ) : (m.rowLens.take k).sum ≤ (lam.rowLens.take k).sum := by
  classical
  have hp : Function.Injective fun y => (rowIndex s (σ.symm y), colIndex t y) := by
    intro x y hxy
    have hr := congrArg (Prod.fst : ℕ × ℕ → ℕ) hxy
    have hc := congrArg (Prod.snd : ℕ × ℕ → ℕ) hxy
    have hh := h (σ.symm x) (σ.symm y) hr
      (by simpa only [Equiv.apply_symm_apply] using hc)
    exact σ.symm.injective hh
  have hcount : (Finset.univ.filter fun y => rowIndex s (σ.symm y) < k).card =
      (Finset.univ.filter fun x => rowIndex s x < k).card :=
    Finset.card_equiv σ.symm fun y => by simp
  simpa only [hcount, card_filter_rowIndex_lt] using
    card_filter_lt_le_card_filter_rowIndex_lt t hp k
end YoungTableau
end

section

structure StandardYoungTableau (μ : YoungDiagram) where

  toTableau : (↥μ.cells ≃ Fin μ.card)

  row_strict' : ∀ {i j₁ j₂ : ℕ} (h : j₁ < j₂) (hcell : (i, j₂) ∈ μ),
    toTableau ⟨(i, j₁), μ.up_left_mem (by rfl) h.le hcell⟩ < toTableau ⟨(i, j₂), hcell⟩

  col_strict' : ∀ {i₁ i₂ j : ℕ} (h : i₁ < i₂) (hcell : (i₂, j) ∈ μ),
    toTableau ⟨(i₁, j), μ.up_left_mem h.le (by rfl) hcell⟩ < toTableau ⟨(i₂, j), hcell⟩
namespace StandardYoungTableau
end StandardYoungTableau
end

open scoped Nat
namespace YoungDiagram
variable {μ : YoungDiagram}

private def readingIndex (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ :=
  (∑ i ∈ Finset.range c.1, μ.rowLen i) + c.2

private theorem readingIndex_lt_card {c : ℕ × ℕ} (hc : c ∈ μ) : readingIndex μ c < μ.card := by
  have hsucc : ∑ i ∈ Finset.range (c.1 + 1), μ.rowLen i ≤ μ.card := by
    rw [sum_range_rowLen_eq_card_filter_fst]
    exact Finset.card_filter_le _ _
  rw [Finset.sum_range_succ] at hsucc
  have hrow := _root_.YoungDiagram.mem_iff_lt_rowLen.mp hc
  rw [readingIndex]
  omega

private theorem readingIndex_lt_readingIndex_of_fst_lt {c d : ℕ × ℕ} (hc : c ∈ μ) (h : c.1 < d.1) :
    readingIndex μ c < readingIndex μ d := by
  have hsub : Finset.range (c.1 + 1) ⊆ Finset.range d.1 := by
    rw [Finset.range_subset_range]
    omega
  have hmono : ∑ i ∈ Finset.range (c.1 + 1), μ.rowLen i ≤ ∑ i ∈ Finset.range d.1, μ.rowLen i :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_range_succ] at hmono
  have hrow := _root_.YoungDiagram.mem_iff_lt_rowLen.mp hc
  rw [readingIndex, readingIndex]
  omega

private theorem readingIndex_lt_readingIndex_of_snd_lt {c d : ℕ × ℕ} (hrow : c.1 = d.1) (h : c.2 < d.2) :
    readingIndex μ c < readingIndex μ d := by
  rw [readingIndex, readingIndex, hrow]
  omega

private theorem eq_of_readingIndex_eq {c d : ℕ × ℕ} (hc : c ∈ μ) (hd : d ∈ μ)
    (h : readingIndex μ c = readingIndex μ d) : c = d := by
  rcases lt_trichotomy c.1 d.1 with hfst | hfst | hfst
  · exact absurd h (readingIndex_lt_readingIndex_of_fst_lt hc hfst).ne
  · rcases lt_trichotomy c.2 d.2 with hsnd | hsnd | hsnd
    · exact absurd h (readingIndex_lt_readingIndex_of_snd_lt hfst hsnd).ne
    · exact Prod.ext hfst hsnd
    · exact absurd h (readingIndex_lt_readingIndex_of_snd_lt hfst.symm hsnd).ne'
  · exact absurd h (readingIndex_lt_readingIndex_of_fst_lt hd hfst).ne'
end YoungDiagram
section
namespace StandardYoungTableau
variable {μ : YoungDiagram}

noncomputable def rowSuperstandard (μ : YoungDiagram) : StandardYoungTableau μ where
  toTableau :=
    Equiv.ofBijective
      (fun c => ⟨D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungDiagram.readingIndex μ c.1, D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungDiagram.readingIndex_lt_card c.2⟩)
      ((Fintype.bijective_iff_injective_and_card _).mpr
        ⟨fun c d hcd =>
          Subtype.ext (D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungDiagram.eq_of_readingIndex_eq c.2 d.2 (congrArg Fin.val hcd)),
          by simp⟩)
  row_strict' := fun {i j₁ j₂} h _ =>
    Fin.lt_def.mpr (D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungDiagram.readingIndex_lt_readingIndex_of_snd_lt
      (μ := μ) (c := (i, j₁)) (d := (i, j₂)) rfl h)
  col_strict' := fun {i₁ i₂ j} h hcell =>
    Fin.lt_def.mpr (D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.YoungDiagram.readingIndex_lt_readingIndex_of_fst_lt
      (c := (i₁, j)) (d := (i₂, j)) (μ.up_left_mem h.le (le_refl j) hcell) h)
end StandardYoungTableau
end

namespace YoungDiagram
theorem sum_rowLens_eq_card (mu : YoungDiagram) : mu.rowLens.sum = mu.card := by
  exact D5.S1.Words.Compositions.ZeroPrependedFirstSumsOddParts.rowLens_sum mu
@[simp] theorem card_transpose (mu : YoungDiagram) : mu.transpose.card = mu.card := by
  unfold YoungDiagram.card YoungDiagram.transpose
  simp

@[simp]
theorem rowLens_ofPartition_eq_sort_parts {n : ℕ} (p : Nat.Partition n) :
    ((D5.S3.Combinatorics.TwoLayerSolidPartitions.youngPartition n).symm p).1.rowLens =
      p.parts.sort (· ≥ ·) := by
  change (ofRowLens (p.parts.sort (· ≥ ·))
    (Multiset.pairwise_sort _ _).sortedGE).rowLens = _
  apply rowLens_ofRowLens_eq_self
  intro x hx
  exact p.parts_pos ((Multiset.mem_sort _).mp hx)
@[simp]
theorem card_ofPartition {n : ℕ} (p : Nat.Partition n) :
    ((D5.S3.Combinatorics.TwoLayerSolidPartitions.youngPartition n).symm p).1.card = n :=
  ((D5.S3.Combinatorics.TwoLayerSolidPartitions.youngPartition n).symm p).2
@[simp]
theorem ofPartition_toPartition {n : ℕ} {μ : YoungDiagram} (h : μ.card = n) :
    ((D5.S3.Combinatorics.TwoLayerSolidPartitions.youngPartition n).symm
      (D5.S3.Combinatorics.TwoLayerSolidPartitions.youngPartition n ⟨μ, h⟩)).1 = μ :=
  congrArg Subtype.val
    ((D5.S3.Combinatorics.TwoLayerSolidPartitions.youngPartition n).symm_apply_apply ⟨μ, h⟩)
@[simp]
theorem toPartition_ofPartition {n : ℕ} {p : Nat.Partition n} :
    D5.S3.Combinatorics.TwoLayerSolidPartitions.youngPartition n
      ((D5.S3.Combinatorics.TwoLayerSolidPartitions.youngPartition n).symm p) = p :=
  (D5.S3.Combinatorics.TwoLayerSolidPartitions.youngPartition n).apply_symm_apply p
end YoungDiagram
namespace Nat.Partition
end Nat.Partition

namespace SemistandardYoungTableau
variable {μ : YoungDiagram}

noncomputable def content (T : _root_.SemistandardYoungTableau μ) : ℕ →₀ ℕ :=
  (μ.cells.val.map fun c => T c.1 c.2).toFinsupp

theorem content_apply (T : _root_.SemistandardYoungTableau μ) (i : ℕ) :
    content T i = (μ.cells.filter fun c => T c.1 c.2 = i).card := by
  rw [content, Multiset.toFinsupp_apply, Multiset.count_map]
  simp [Finset.card, Finset.filter_val, eq_comm]

@[simp]
theorem support_content (T : _root_.SemistandardYoungTableau μ) :
    (content T).support = μ.cells.image fun c => T c.1 c.2 := by
  rw [content, Multiset.toFinsupp_support, Multiset.toFinset_map, Finset.val_toFinset]

theorem le_entry (T : _root_.SemistandardYoungTableau μ) {i j : ℕ} (h : (i, j) ∈ μ) :
    i ≤ T i j := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    have hm : (m, j) ∈ μ := μ.up_left_mem (Nat.le_succ m) le_rfl h
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih hm) (T.col_strict (Nat.lt_succ_self m) h))

private theorem filter_entry_lt_subset_filter_fst_lt (T : _root_.SemistandardYoungTableau μ) (k : ℕ) :
    (μ.cells.filter fun c => T c.1 c.2 < k) ⊆ μ.cells.filter fun c => c.1 < k := by
  intro c hc
  rw [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, lt_of_le_of_lt (le_entry T (by simpa using hc.1)) hc.2⟩

private theorem sum_content_eq_card_filter (T : _root_.SemistandardYoungTableau μ) (k : ℕ) :
    ∑ i ∈ Finset.range k, content T i = (μ.cells.filter fun c => T c.1 c.2 < k).card := by
  symm
  calc
    (μ.cells.filter fun c => T c.1 c.2 < k).card =
        ∑ i ∈ Finset.range k,
          ((μ.cells.filter fun c => T c.1 c.2 < k).filter fun c => T c.1 c.2 = i).card := by
      refine Finset.card_eq_sum_card_fiberwise fun c hc => ?_
      simp only [Finset.mem_coe, Finset.mem_filter] at hc
      exact Finset.mem_range.mpr hc.2
    _ = ∑ i ∈ Finset.range k, content T i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i < k := Finset.mem_range.mp hi
      rw [content_apply]
      refine congrArg Finset.card (Finset.ext fun c => ?_)
      simp only [Finset.mem_filter, and_assoc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.2 ▸ hik, h.2⟩⟩

theorem sum_content_eq_card {T : _root_.SemistandardYoungTableau μ} {N : ℕ}
    (hN : ∀ c ∈ μ.cells, T c.1 c.2 < N) :
    ∑ i ∈ Finset.range N, content T i = μ.card := by
  rw [sum_content_eq_card_filter, Finset.filter_true_of_mem hN]

private theorem sum_content_le_sum_take_rowLens (T : _root_.SemistandardYoungTableau μ) (k : ℕ) :
    ∑ i ∈ Finset.range k, content T i ≤ (μ.rowLens.take k).sum := by
  rw [sum_content_eq_card_filter, D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.sum_take_rowLens_eq_card_filter_fst]
  exact Finset.card_le_card (filter_entry_lt_subset_filter_fst_lt T k)

@[simp]
private theorem content_highestWeight (μ : YoungDiagram) :
    ⇑(content (_root_.SemistandardYoungTableau.highestWeight μ)) = μ.rowLen := by
  funext i
  rw [content_apply, μ.rowLen_eq_card]
  refine congrArg Finset.card (Finset.ext fun c => ?_)
  simp only [_root_.YoungDiagram.mem_row_iff,
    _root_.SemistandardYoungTableau.highestWeight_apply]
  aesop

private theorem eq_highestWeight_of_content_eq_rowLen {T : _root_.SemistandardYoungTableau μ}
    (h : ⇑(content T) = μ.rowLen) : T = _root_.SemistandardYoungTableau.highestWeight μ := by
  have key : ∀ i j : ℕ, (i, j) ∈ μ → T i j = i := by
    intro i j hij
    have hcards : (μ.cells.filter fun c => T c.1 c.2 < i + 1).card =
        (μ.cells.filter fun c => c.1 < i + 1).card := by
      rw [← sum_content_eq_card_filter, ← D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux01.YoungDiagram.sum_range_rowLen_eq_card_filter_fst]
      exact Finset.sum_congr rfl fun k _ => congrFun h k
    have hsets := Finset.eq_of_subset_of_card_le
      (filter_entry_lt_subset_filter_fst_lt T (i + 1)) hcards.ge
    have hmem : ((i, j) : ℕ × ℕ) ∈ μ.cells.filter fun c => T c.1 c.2 < i + 1 := by
      rw [hsets, Finset.mem_filter]
      exact ⟨hij, Nat.lt_succ_self i⟩
    exact le_antisymm (Nat.lt_succ_iff.mp (Finset.mem_filter.mp hmem).2) (le_entry T hij)
  ext i j
  by_cases hij : (i, j) ∈ μ
  · rw [key i j hij, _root_.SemistandardYoungTableau.highestWeight_apply, if_pos hij]
  · rw [T.zeros hij, _root_.SemistandardYoungTableau.highestWeight_apply, if_neg hij]

private instance finite_content_eq (μ : YoungDiagram) (w : ℕ → ℕ) :
    Finite {T : _root_.SemistandardYoungTableau μ // ⇑(content T) = w} := by
  by_cases hne : Nonempty {T : _root_.SemistandardYoungTableau μ // ⇑(content T) = w}
  swap
  · rw [not_nonempty_iff] at hne
    infer_instance
  obtain ⟨T₀, hT₀⟩ := hne.some
  have hmem : ∀ T : _root_.SemistandardYoungTableau μ, ⇑(content T) = w →
      ∀ c ∈ μ.cells, T c.1 c.2 ∈ μ.cells.image fun d => T₀ d.1 d.2 := by
    intro T hT c hc
    rw [← support_content T₀, DFunLike.coe_injective (hT₀.trans hT.symm), support_content T]
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  refine Finite.of_injective
    (fun (T : {T : _root_.SemistandardYoungTableau μ // ⇑(content T) = w}) (c : ↥μ.cells) =>
      (⟨T.1 (c : ℕ × ℕ).1 (c : ℕ × ℕ).2, hmem T.1 T.2 _ c.2⟩ :
        ↥(μ.cells.image fun d => T₀ d.1 d.2))) fun T T' hTT' => ?_
  refine Subtype.ext (_root_.SemistandardYoungTableau.ext fun i j => ?_)
  by_cases hij : (i, j) ∈ μ
  · exact congrArg Subtype.val (congrFun hTT' ⟨(i, j), hij⟩)
  · rw [T.1.zeros hij, T'.1.zeros hij]
end SemistandardYoungTableau
section

abbrev BoundedSSYT (n : ℕ) (μ : YoungDiagram) : Type :=
  {T : _root_.SemistandardYoungTableau μ // ∀ i c : ℕ, (i, c) ∈ μ → T i c < n}
namespace BoundedSSYT
variable {n : ℕ} {μ : YoungDiagram}

theorem entry_lt (T : BoundedSSYT n μ) {i c : ℕ} (h : (i, c) ∈ μ) : T.1 i c < n :=
  T.2 i c h

theorem isEmpty_of_lt_colLen (h : n < μ.colLen 0) : IsEmpty (BoundedSSYT n μ) := by
  refine ⟨fun T => absurd (entry_lt T (YoungDiagram.mem_iff_lt_colLen.mpr h)) (not_lt.mpr ?_)⟩
  exact D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.le_entry T.1 (YoungDiagram.mem_iff_lt_colLen.mpr h)

instance instUniqueBotYoungDiagram (n : ℕ) : Unique (BoundedSSYT n (⊥ : YoungDiagram)) where
  default := ⟨_root_.SemistandardYoungTableau.highestWeight ⊥, fun _ _ hic => absurd hic (by simp)⟩
  uniq T := Subtype.ext <| _root_.SemistandardYoungTableau.ext fun _ _ => by
    rw [T.1.zeros (by simp), _root_.SemistandardYoungTableau.highestWeight_apply,
      if_neg (by simp)]
end BoundedSSYT

private instance finite_boundedSSYT (n : ℕ) (μ : YoungDiagram) : Finite (BoundedSSYT n μ) := by
  refine Finite.of_injective (β := μ.cells → Fin n)
    (fun T x => ⟨T.1 x.1.1 x.1.2, T.2 _ _ ((YoungDiagram.mem_cells _).mp x.2)⟩) ?_
  rintro ⟨T, hT⟩ ⟨T', hT'⟩ h
  refine Subtype.ext (_root_.SemistandardYoungTableau.ext fun i c => ?_)
  by_cases hc : (i, c) ∈ μ
  · exact congrArg Fin.val (congrFun h ⟨(i, c), (YoungDiagram.mem_cells _).mpr hc⟩)
  · rw [T.zeros hc, T'.zeros hc]
noncomputable instance instFintypeBoundedSSYT (n : ℕ) (μ : YoungDiagram) : Fintype (BoundedSSYT n μ) := .ofFinite _

noncomputable def diagramKostkaNumber (μ : YoungDiagram) (w : ℕ → ℕ) : ℕ :=
  Nat.card {T : _root_.SemistandardYoungTableau μ // ⇑(D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.content T) = w}

theorem diagramKostkaNumber_def (μ : YoungDiagram) (w : ℕ → ℕ) :
    diagramKostkaNumber μ w =
      Nat.card
        {T : _root_.SemistandardYoungTableau μ // ⇑(D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.content T) = w} :=
  (rfl)

private theorem diagramKostkaNumber_ne_zero_iff {μ : YoungDiagram} {w : ℕ → ℕ} :
    diagramKostkaNumber μ w ≠ 0 ↔
      ∃ T : _root_.SemistandardYoungTableau μ, ⇑(D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.content T) = w := by
  rw [diagramKostkaNumber_def, Nat.card_ne_zero]
  exact ⟨fun h => h.1.elim fun T => ⟨T.1, T.2⟩, fun ⟨T, hT⟩ => ⟨⟨⟨T, hT⟩⟩, inferInstance⟩⟩

@[simp]
theorem diagramKostkaNumber_rowLen (μ : YoungDiagram) : diagramKostkaNumber μ μ.rowLen = 1 := by
  rw [diagramKostkaNumber_def, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun T T' => Subtype.ext ?_⟩,
    ⟨⟨_root_.SemistandardYoungTableau.highestWeight μ,
      D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.content_highestWeight μ⟩⟩⟩
  rw [D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen T.2,
    D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen T'.2]

theorem sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero {μ : YoungDiagram} {w : ℕ → ℕ}
    (h : diagramKostkaNumber μ w ≠ 0) (k : ℕ) :
    ∑ i ∈ Finset.range k, w i ≤ (μ.rowLens.take k).sum := by
  obtain ⟨T, hT⟩ := diagramKostkaNumber_ne_zero_iff.mp h
  calc
    ∑ i ∈ Finset.range k, w i = ∑ i ∈ Finset.range k, D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.content T i :=
      Finset.sum_congr rfl fun i _ => (congrFun hT i).symm
    _ ≤ (μ.rowLens.take k).sum := D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02.SemistandardYoungTableau.sum_content_le_sum_take_rowLens T k
end

end D5.S3.Quantum.Matrix.TauCetiSuppliers.YoungTableaux02
