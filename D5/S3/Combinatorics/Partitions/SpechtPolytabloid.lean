/- GID: D5/S3/Combinatorics/Partitions/SpechtPolytabloid
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtPolytabloid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal partition-indexed rational polytabloid Specht modules and their complex scalar extensions. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Complete license and source attribution:
Library/FiniteGroups/tauceti2026spechtpolytabloids.md.
Authors of the ported constructions and proofs: The Tau Ceti contributors

PORT of selected declarations at TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
Changes: repository namespace, import selection, comment selection and local universe
qualification only. All selected proof bodies are preserved; no third-party theorem
is reproved. Retire each port when OUR lake-manifest.json-pinned Mathlib supplies an
equivalent declaration with the same hypotheses and conclusions, checked at that pin.

WIP SOURCE ONLY. No native elaboration, axiom closure, Reg audit, statement projection,
firstfreeze or CI is claimed. The same-label ordinary trace/Frobenius comparison and
the full weighted HSW ordinary-character application remain open. This construction
is independent of the desired coefficient: column antisymmetrizers act on left cosets
of the consecutive-block Young subgroup; their polytabloid span is stable by relabeling.
The source nonvanishing proof uses injectivity of column permutations on the tabloid,
proved from the trivial intersection of the row and column groups. No arbitrary
character relabeling or bridge hypothesis is introduced.

Candidate admission: genuine representation constructions and the polytabloid
nonvanishing proof, subject to per-declaration and native live-dependency review.
Bind-only organization is consumed by these constructions and proofs; it supplies
no independent admission witness. Exact source selections and uses are in the Library
note. No open-problem-resolution admission is claimed: an ordinary-trace-specific
current preregistration/echo has not been established. Caller owns issue handling.
utility: none: these are unbounded constructions and general structural proofs,
not a finite enumeration, checker, numerical reduction or certified instance.
-/
import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Data.Finite.Perm
import Mathlib.Data.List.Sort
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Data.Complex.Basic

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid

open scoped BigOperators

namespace YoungDiagram
@[simp]
private theorem mergeSort_rowLens (μ : YoungDiagram) :
    μ.rowLens.mergeSort (fun a b => decide (b ≤ a)) = μ.rowLens :=
  List.mergeSort_eq_self _ μ.rowLens_sorted.pairwise

theorem sort_coe_rowLens (μ : YoungDiagram) :
    (↑μ.rowLens : Multiset ℕ).sort (· ≥ ·) = μ.rowLens := by
  rw [Multiset.coe_sort]
  exact mergeSort_rowLens μ
end YoungDiagram

namespace TauCeti
def shapePartition (μ : YoungDiagram) : μ.card.Partition :=
  μ.toPartition rfl

@[simp]
theorem shapePartition_parts (μ : YoungDiagram) :
    (shapePartition μ).parts = μ.rowLens := by
  rfl

theorem shapePartition_parts_sort (μ : YoungDiagram) :
    (shapePartition μ).parts.sort (· ≥ ·) = μ.rowLens := by
  rw [shapePartition_parts, YoungDiagram.sort_coe_rowLens]

abbrev YoungTableau (μ : YoungDiagram) : Type := ↥μ.cells ≃ Fin μ.card
namespace YoungTableau
variable {μ : YoungDiagram}
def rowIndex (t : YoungTableau μ) (k : Fin μ.card) : ℕ := (t.symm k : ℕ × ℕ).1

def colIndex (t : YoungTableau μ) (k : Fin μ.card) : ℕ := (t.symm k : ℕ × ℕ).2

theorem rowIndex_def (t : YoungTableau μ) (k : Fin μ.card) :
    rowIndex t k = (t.symm k : ℕ × ℕ).1 := by
  rw [rowIndex]

theorem colIndex_def (t : YoungTableau μ) (k : Fin μ.card) :
    colIndex t k = (t.symm k : ℕ × ℕ).2 := by
  rw [colIndex]

@[simp]
theorem rowIndex_apply (t : YoungTableau μ) (c : ↥μ.cells) :
    rowIndex t (t c) = (c : ℕ × ℕ).1 := by
  rw [rowIndex_def, Equiv.symm_apply_apply]

theorem rowIndex_colIndex_injective (t : YoungTableau μ) :
    Function.Injective fun k => (rowIndex t k, colIndex t k) := by
  intro k l h
  simp only [rowIndex_def, colIndex_def, Prod.mk.injEq] at h
  exact t.symm.injective (Subtype.ext (Prod.ext h.1 h.2))

def relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) : YoungTableau μ :=
  t.trans σ

@[simp]
theorem relabel_apply (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) (c : ↥μ.cells) :
    relabel σ t c = σ (t c) :=
  (rfl)

@[simp]
theorem relabel_symm_apply (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) (k : Fin μ.card) :
    (relabel σ t).symm k = t.symm (σ⁻¹ k) := by
  rw [relabel, Equiv.symm_trans_apply, Equiv.Perm.inv_def]

@[simp]
theorem colIndex_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) (k : Fin μ.card) :
    colIndex (relabel σ t) k = colIndex t (σ⁻¹ k) := by
  rw [colIndex_def, colIndex_def, relabel_symm_apply]

theorem nonempty (μ : YoungDiagram) : Nonempty (YoungTableau μ) :=
  ⟨μ.cells.equivFin⟩

end YoungTableau

variable {α ι κ : Type*}
def fiberSubgroup (f : α → ι) : Subgroup (Equiv.Perm α) where
  carrier := {σ | ∀ a, f (σ a) = f a}
  mul_mem' hσ hτ a := (hσ _).trans (hτ a)
  one_mem' _ := rfl
  inv_mem' {σ} hσ a := by
    have h := hσ (σ⁻¹ a)
    rwa [Equiv.Perm.inv_def, Equiv.apply_symm_apply, eq_comm] at h

@[simp]
theorem mem_fiberSubgroup {f : α → ι} {σ : Equiv.Perm α} :
    σ ∈ fiberSubgroup f ↔ ∀ a, f (σ a) = f a :=
  Iff.rfl

theorem fiberSubgroup_map_conj {f : α → ι} {g : α → κ} (e : Equiv.Perm α)
    (h : ∀ a b, f a = f b ↔ g (e a) = g (e b)) :
    (fiberSubgroup f).map (MulAut.conj e).toMonoidHom = fiberSubgroup g := by
  ext σ
  rw [Subgroup.mem_map_equiv, mem_fiberSubgroup, mem_fiberSubgroup]
  constructor
  · intro hσ a
    have hfa : f (e.symm (σ a)) = f (e.symm a) := by
      simpa only [MulAut.conj_symm_apply, Equiv.Perm.coe_mul, Function.comp_apply,
        Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using hσ (e.symm a)
    have ha := (h (e.symm (σ a)) (e.symm a)).mp hfa
    simpa only [MulAut.conj_symm_apply, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using ha
  · intro hσ a
    apply (h _ _).mpr
    simpa only [MulAut.conj_symm_apply, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using hσ (e a)

theorem fiberSubgroup_inf (f : α → ι) (g : α → κ) :
    fiberSubgroup f ⊓ fiberSubgroup g = fiberSubgroup fun a => (f a, g a) := by
  ext σ
  simp [Subgroup.mem_inf, Prod.ext_iff, forall_and]

theorem fiberSubgroup_eq_bot_of_injective {f : α → ι} (hf : Function.Injective f) :
    fiberSubgroup f = ⊥ :=
  eq_bot_iff.mpr fun _ hσ => Subgroup.mem_bot.mpr (Equiv.ext fun a => hf (hσ a))

open Equiv
noncomputable def youngBlocksEquiv {n : ℕ} (μ : n.Partition) :
    (Σ i : Fin (μ.parts.sort (· ≥ ·)).length,
      Fin ((μ.parts.sort (· ≥ ·)).get i)) ≃ Fin n :=
  finSigmaFinEquiv.trans <| finCongr <| by
    simp_rw [List.get_eq_getElem]
    rw [Fin.sum_univ_getElem, ← Multiset.sum_coe, Multiset.sort_eq, μ.parts_sum]

noncomputable def youngBlock {n : ℕ} (μ : n.Partition) (j : Fin n) :
    Fin (μ.parts.sort (· ≥ ·)).length :=
  ((youngBlocksEquiv μ).symm j).1

@[simp]
theorem youngBlock_youngBlocksEquiv {n : ℕ} (μ : n.Partition)
    (x : Σ i : Fin (μ.parts.sort (· ≥ ·)).length,
      Fin ((μ.parts.sort (· ≥ ·)).get i)) :
    youngBlock μ (youngBlocksEquiv μ x) = x.1 := by
  simp [youngBlock]

noncomputable def youngSubgroup {n : ℕ} (μ : n.Partition) :
    Subgroup (Equiv.Perm (Fin n)) :=
  (MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ (youngBlock μ)).unop

private theorem mem_youngSubgroup_stabilizer_iff {n : ℕ} (μ : n.Partition)
    (σ : Equiv.Perm (Fin n)) :
    σ ∈ youngSubgroup μ ↔
      DomMulAct.mk σ ∈
        MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ (youngBlock μ) :=
  Iff.rfl

@[simp]
theorem mem_youngSubgroup_iff {n : ℕ} (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    σ ∈ youngSubgroup μ ↔ youngBlock μ ∘ σ = youngBlock μ := by
  rw [mem_youngSubgroup_stabilizer_iff]
  exact DomMulAct.mem_stabilizer_iff

theorem youngSubgroup_eq_fiberSubgroup {n : ℕ} (μ : n.Partition) :
    youngSubgroup μ = fiberSubgroup (youngBlock μ) := by
  ext σ
  rw [mem_youngSubgroup_iff, mem_fiberSubgroup]
  simp only [funext_iff, Function.comp_apply]

namespace YoungTableau
variable {μ : YoungDiagram}
def rowSubgroup (t : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) :=
  fiberSubgroup (rowIndex t)

def colSubgroup (t : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) :=
  fiberSubgroup (colIndex t)

@[simp]
theorem mem_rowSubgroup {t : YoungTableau μ} {σ : Equiv.Perm (Fin μ.card)} :
    σ ∈ rowSubgroup t ↔ ∀ k, rowIndex t (σ k) = rowIndex t k :=
  mem_fiberSubgroup

@[simp]
theorem mem_colSubgroup {t : YoungTableau μ} {σ : Equiv.Perm (Fin μ.card)} :
    σ ∈ colSubgroup t ↔ ∀ k, colIndex t (σ k) = colIndex t k :=
  mem_fiberSubgroup

theorem rowSubgroup_def (t : YoungTableau μ) :
    rowSubgroup t = fiberSubgroup (rowIndex t) := by
  ext σ
  rw [mem_rowSubgroup, mem_fiberSubgroup]

theorem colSubgroup_def (t : YoungTableau μ) :
    colSubgroup t = fiberSubgroup (colIndex t) := by
  ext σ
  rw [mem_colSubgroup, mem_fiberSubgroup]

theorem rowSubgroup_inf_colSubgroup_eq_bot (t : YoungTableau μ) :
    rowSubgroup t ⊓ colSubgroup t = ⊥ := by
  rw [rowSubgroup_def, colSubgroup_def, fiberSubgroup_inf]
  exact fiberSubgroup_eq_bot_of_injective (rowIndex_colIndex_injective t)

private abbrev rowBlocks (l : List ℕ) : Type :=
  Σ i : Fin l.length, Fin (l.get i)

private noncomputable def rowCellsEquiv (μ : YoungDiagram) :
    rowBlocks μ.rowLens ≃ ↥μ.cells where
  toFun x := ⟨(x.1, x.2), by
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, ← YoungDiagram.get_rowLens]
    exact x.2.2⟩
  invFun c :=
    ⟨⟨c.1.1, by
      rw [YoungDiagram.length_rowLens]
      exact (_root_.YoungDiagram.mem_iff_lt_colLen.mp c.2).trans_le
        (μ.colLen_anti 0 c.1.2 c.1.2.zero_le)⟩,
      ⟨c.1.2, by
        have hj := _root_.YoungDiagram.mem_iff_lt_rowLen.mp c.2
        rw [← YoungDiagram.get_rowLens] at hj
        exact hj⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def sortedBlocksEquivRows (μ : YoungDiagram) :
    rowBlocks ((shapePartition μ).parts.sort (· ≥ ·)) ≃ rowBlocks μ.rowLens :=
  Equiv.cast (congrArg rowBlocks (shapePartition_parts_sort μ))

private theorem cast_rowBlocks_fst {l₁ l₂ : List ℕ} (h : l₁ = l₂)
    (x : rowBlocks l₁) :
    ((Equiv.cast (congrArg rowBlocks h) x).1 : ℕ) = x.1 := by
  subst l₂
  rfl

private theorem sortedBlocksEquivRows_fst (μ : YoungDiagram)
    (x : rowBlocks ((shapePartition μ).parts.sort (· ≥ ·))) :
    ((sortedBlocksEquivRows μ x).1 : ℕ) = x.1 :=
  cast_rowBlocks_fst (shapePartition_parts_sort μ) x

noncomputable def rowYoungConjugator {μ : YoungDiagram} (t : YoungTableau μ) :
    Equiv.Perm (Fin μ.card) :=
  (youngBlocksEquiv (shapePartition μ)).symm |>.trans <|
    (sortedBlocksEquivRows μ).trans ((rowCellsEquiv μ).trans t)

@[simp]
theorem rowIndex_rowYoungConjugator {μ : YoungDiagram} (t : YoungTableau μ)
    (k : Fin μ.card) :
    rowIndex t (rowYoungConjugator t k) =
      youngBlock (shapePartition μ) k := by
  let x := (youngBlocksEquiv (shapePartition μ)).symm k
  have hk : youngBlocksEquiv (shapePartition μ) x = k :=
    Equiv.apply_symm_apply _ k
  rw [← hk, youngBlock_youngBlocksEquiv]
  simp only [rowYoungConjugator, Equiv.trans_apply, rowIndex_apply, rowCellsEquiv,
    Equiv.symm_apply_apply, x]
  exact sortedBlocksEquivRows_fst μ x

@[simp]
theorem rowYoungConjugator_relabel {μ : YoungDiagram} (σ : Equiv.Perm (Fin μ.card))
    (t : YoungTableau μ) :
    rowYoungConjugator (relabel σ t) = σ * rowYoungConjugator t := by
  have h : relabel σ t = t.trans σ := Equiv.ext fun c => relabel_apply σ t c
  simp only [rowYoungConjugator, Equiv.Perm.mul_def, Equiv.trans_assoc, h]

theorem youngSubgroup_map_conj_eq_rowSubgroup {μ : YoungDiagram} (t : YoungTableau μ) :
    (youngSubgroup (shapePartition μ)).map
        (MulAut.conj (rowYoungConjugator t)).toMonoidHom = rowSubgroup t := by
  rw [youngSubgroup_eq_fiberSubgroup, rowSubgroup_def]
  apply fiberSubgroup_map_conj
  intro a b
  simp only [rowIndex_rowYoungConjugator]
  exact Fin.ext_iff
end YoungTableau

open MulAction
open scoped Pointwise
variable {G : Type*} [Group G]
@[simp]
theorem stabilizer_quotientGroup_mk (H : Subgroup G) (s : G) :
    stabilizer G ((s : G ⧸ H)) = MulAut.conj s • H := by
  have hs : ((s : G) : G ⧸ H) = s • ((1 : G) : G ⧸ H) := by
    rw [Quotient.smul_coe, smul_eq_mul, mul_one]
  rw [hs, stabilizer_smul_eq_stabilizer_map_conj, stabilizer_quotient]

  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_symm_apply, MulAut.conj_apply, inv_inv]

noncomputable abbrev permutationModule {n : ℕ} (μ : n.Partition) :
    Rep ℚ (Equiv.Perm (Fin n)) :=
  Rep.ofMulAction ℚ (Equiv.Perm (Fin n))
    (Equiv.Perm (Fin n) ⧸ youngSubgroup μ)
variable {k : Type*} [CommSemiring k] (χ : G →* k) (H : Subgroup G) [Fintype H]
noncomputable def subgroupCharSum : MonoidAlgebra k G :=
  ∑ h : H, χ (h : G) • MonoidAlgebra.of k G (h : G)

theorem subgroupCharSum_def :
    subgroupCharSum χ H = ∑ h : H, χ (h : G) • MonoidAlgebra.of k G (h : G) :=
  (rfl)

@[simp]
theorem subgroupCharSum_coeff [DecidablePred (· ∈ H)] (g : G) :
    (subgroupCharSum χ H).coeff g = if g ∈ H then χ g else 0 := by
  rw [subgroupCharSum_def, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single,
    smul_eq_mul]
  by_cases hg : g ∈ H
  · rw [ite_eq_left hg, Finset.sum_eq_single (⟨g, hg⟩ : H)]
    · rw [Finsupp.single_eq_same, mul_one]
    · exact fun h _ hh => by
        rw [Finsupp.single_eq_of_ne' fun e => hh (Subtype.ext e), mul_zero]
    · simp
  · rw [ite_eq_right hg]
    exact Finset.sum_eq_zero fun h _ => by
      rw [Finsupp.single_eq_of_ne' fun e : (h : G) = g => hg (e ▸ h.property), mul_zero]

universe u v
def signLinearCharacter (k : Type u) [Ring k] (α : Type v) [DecidableEq α] [Fintype α] :
    Equiv.Perm α →* kˣ :=
  (Units.map (Int.castRingHom k).toMonoidHom).comp Equiv.Perm.sign

variable {k : Type u} [Ring k] {α : Type v} [DecidableEq α] [Fintype α]
@[simp]
theorem coe_signLinearCharacter_apply (σ : Equiv.Perm α) :
    (signLinearCharacter k α σ : k) = ((Equiv.Perm.sign σ : ℤ) : k) :=

  (rfl)

namespace YoungTableau
variable {μ : YoungDiagram}
noncomputable section
local instance decidablePredMemColSubgroup (t : YoungTableau μ) :
    DecidablePred (· ∈ colSubgroup t) :=
  Classical.decPred _

noncomputable def columnAntisymmetrizer (t : YoungTableau μ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)) :=
  ∑ q : colSubgroup t,
    ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
      MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card)) q

theorem columnAntisymmetrizer_def (t : YoungTableau μ) :
    columnAntisymmetrizer t =
      ∑ q : colSubgroup t,
        ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
          MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card)) q :=
  (rfl)

theorem columnAntisymmetrizer_eq_subgroupCharSum (t : YoungTableau μ) :
    columnAntisymmetrizer t =
      subgroupCharSum ((Units.coeHom ℚ).comp (signLinearCharacter ℚ (Fin μ.card)))
        (colSubgroup t) := by
  rw [columnAntisymmetrizer_def, subgroupCharSum_def]
  simp

@[simp]
theorem columnAntisymmetrizer_coeff (t : YoungTableau μ) (σ : Equiv.Perm (Fin μ.card)) :
    (columnAntisymmetrizer t).coeff σ =
      if σ ∈ colSubgroup t then ((Equiv.Perm.sign σ : ℤ) : ℚ) else 0 := by
  rw [columnAntisymmetrizer_eq_subgroupCharSum, subgroupCharSum_coeff]
  simp

private theorem coeff_conj (g h : G) (x : MonoidAlgebra ℚ G) :
    (MonoidAlgebra.single g (1 : ℚ) * x * MonoidAlgebra.single g⁻¹ 1).coeff h =
      x.coeff (g⁻¹ * h * g) := by
  simp [mul_assoc]
variable (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ)
theorem colSubgroup_relabel :
    colSubgroup (relabel σ t) = (colSubgroup t).map (MulAut.conj σ).toMonoidHom := by
  rw [colSubgroup_def, colSubgroup_def]
  exact (fiberSubgroup_map_conj σ fun _ _ => by simp).symm

theorem mem_colSubgroup_relabel {τ : Equiv.Perm (Fin μ.card)} :
    τ ∈ colSubgroup (relabel σ t) ↔ σ⁻¹ * τ * σ ∈ colSubgroup t := by
  rw [colSubgroup_relabel, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

@[simp]
theorem columnAntisymmetrizer_relabel :
    columnAntisymmetrizer (relabel σ t) =
      MonoidAlgebra.single σ 1 * columnAntisymmetrizer t * MonoidAlgebra.single σ⁻¹ 1 := by
  ext τ
  rw [coeff_conj, columnAntisymmetrizer_coeff, columnAntisymmetrizer_coeff]
  have hsign : Equiv.Perm.sign (σ⁻¹ * τ * σ) = Equiv.Perm.sign τ := by
    rw [map_mul, map_mul, Equiv.Perm.sign_inv, mul_right_comm, Int.units_mul_self, one_mul]
  by_cases h : σ⁻¹ * τ * σ ∈ colSubgroup t
  · rw [ite_eq_left h, ite_eq_left ((mem_colSubgroup_relabel σ t).mpr h), hsign]
  · rw [ite_eq_right h, ite_eq_right fun hτ => h ((mem_colSubgroup_relabel σ t).mp hτ)]

end
end YoungTableau

namespace YoungTableau
variable {μ : YoungDiagram}
attribute [local instance] decidablePredMemColSubgroup
noncomputable def tabloid (t : YoungTableau μ) :
    Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ) :=
  QuotientGroup.mk (rowYoungConjugator t)

theorem tabloid_def (t : YoungTableau μ) :
    tabloid t = QuotientGroup.mk (rowYoungConjugator t) :=
  (rfl)

@[simp]
theorem tabloid_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    tabloid (relabel σ t) = σ • tabloid t := by
  rw [tabloid_def, tabloid_def, rowYoungConjugator_relabel, MulAction.Quotient.smul_coe,
    smul_eq_mul]

@[simp]
theorem smul_tabloid_eq_self_iff {t : YoungTableau μ} {σ : Equiv.Perm (Fin μ.card)} :
    σ • tabloid t = tabloid t ↔ σ ∈ rowSubgroup t := by

  have h : MulAction.stabilizer (Equiv.Perm (Fin μ.card)) (tabloid t) = rowSubgroup t := by
    rw [tabloid_def, stabilizer_quotientGroup_mk]
    exact youngSubgroup_map_conj_eq_rowSubgroup t
  rw [← h, MulAction.mem_stabilizer_iff]

@[simp]
theorem smul_tabloid_eq_iff {t : YoungTableau μ} {σ τ : Equiv.Perm (Fin μ.card)} :
    σ • tabloid t = τ • tabloid t ↔ σ⁻¹ * τ ∈ rowSubgroup t := by
  rw [← smul_tabloid_eq_self_iff, mul_smul, inv_smul_eq_iff, eq_comm]

theorem smul_tabloid_injective (t : YoungTableau μ) :
    Function.Injective fun q : colSubgroup t => (q : Equiv.Perm (Fin μ.card)) • tabloid t := by
  intro q r h
  have hrow : (q : Equiv.Perm (Fin μ.card))⁻¹ * r ∈ rowSubgroup t := smul_tabloid_eq_iff.mp h
  have hcol : (q : Equiv.Perm (Fin μ.card))⁻¹ * r ∈ colSubgroup t :=
    mul_mem (inv_mem q.2) r.2
  have hmem : (q : Equiv.Perm (Fin μ.card))⁻¹ * r ∈ rowSubgroup t ⊓ colSubgroup t :=
    Subgroup.mem_inf.mpr ⟨hrow, hcol⟩
  rw [rowSubgroup_inf_colSubgroup_eq_bot t, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact Subtype.ext hmem

noncomputable def polytabloid (t : YoungTableau μ) :
    (permutationModule (shapePartition μ)).V :=
  (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t)
    (MonoidAlgebra.single (tabloid t) 1)

theorem polytabloid_eq_sum (t : YoungTableau μ) :
    polytabloid t =
      ∑ q : colSubgroup t,
        ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
          MonoidAlgebra.single ((q : Equiv.Perm (Fin μ.card)) • tabloid t) (1 : ℚ) := by
  rw [polytabloid, columnAntisymmetrizer_def]
  simp [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single]

@[simp]
theorem polytabloid_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    polytabloid (relabel σ t) =
      (permutationModule (shapePartition μ)).ρ σ (polytabloid t) := by
  rw [polytabloid, polytabloid, columnAntisymmetrizer_relabel, map_mul, map_mul,
    Representation.asAlgebraHom_single_one, Representation.asAlgebraHom_single_one,
    tabloid_relabel]
  simp only [Module.End.mul_apply, Representation.ofMulAction_single, smul_smul,
    inv_mul_cancel, one_smul]

@[simp]
theorem polytabloid_coeff_smul_tabloid (t : YoungTableau μ) (q : colSubgroup t) :
    (polytabloid t).coeff ((q : Equiv.Perm (Fin μ.card)) • tabloid t) =
      ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) := by
  classical
  rw [polytabloid_eq_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Finset.sum_eq_single q]
  · simp [MonoidAlgebra.coeff_single]
  · intro r _ hr
    have hne : (r : Equiv.Perm (Fin μ.card)) • tabloid t ≠
        (q : Equiv.Perm (Fin μ.card)) • tabloid t := fun h =>
      hr (smul_tabloid_injective t h)
    simp [MonoidAlgebra.coeff_single, hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

@[simp]
theorem polytabloid_coeff_tabloid (t : YoungTableau μ) :
    (polytabloid t).coeff (tabloid t) = 1 := by
  have h := polytabloid_coeff_smul_tabloid t 1
  simpa using h

@[simp]
theorem polytabloid_ne_zero (t : YoungTableau μ) : polytabloid t ≠ 0 := by
  intro h
  have := polytabloid_coeff_tabloid t
  rw [h] at this
  simp at this

end YoungTableau

open YoungTableau

noncomputable def spechtSubrepresentation (μ : YoungDiagram) :
    Subrepresentation (permutationModule (shapePartition μ)).ρ where
  toSubmodule := Submodule.span ℚ (Set.range (polytabloid (μ := μ)))
  apply_mem_toSubmodule σ _ hv := by

    have h : Submodule.span ℚ (Set.range (polytabloid (μ := μ))) ≤
        (Submodule.span ℚ (Set.range (polytabloid (μ := μ)))).comap
          ((permutationModule (shapePartition μ)).ρ σ) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      exact Submodule.subset_span ⟨relabel σ t, polytabloid_relabel σ t⟩
    exact h hv

theorem polytabloid_mem_spechtSubrepresentation (t : YoungTableau μ) :
    polytabloid t ∈ spechtSubrepresentation μ :=
  Submodule.subset_span ⟨t, rfl⟩

@[simp]
theorem spechtSubrepresentation_ne_bot (μ : YoungDiagram) : spechtSubrepresentation μ ≠ ⊥ := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  intro h
  have hmem : polytabloid t ∈ (⊥ : Subrepresentation (permutationModule (shapePartition μ)).ρ) :=
    h ▸ polytabloid_mem_spechtSubrepresentation t
  exact polytabloid_ne_zero t (Submodule.mem_bot ℚ |>.mp hmem)

instance (μ : YoungDiagram) :
    FiniteDimensional ℚ (spechtSubrepresentation μ).toSubmodule :=
  FiniteDimensional.finiteDimensional_submodule _

noncomputable abbrev spechtModule {n : ℕ} (μ : n.Partition) :
    FDRep ℚ (Equiv.Perm (Fin n)) :=
  FDRep.of ((spechtSubrepresentation (YoungDiagram.ofPartition μ)).toRepresentation.comp
    (finCongr (YoungDiagram.card_ofPartition μ).symm).permCongrHom.toMonoidHom)
end TauCeti

namespace Representation
open TensorProduct
universe u v w x
noncomputable section
variable {G : Type w} {V : Type x} [Monoid G]
variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
variable [AddCommMonoid V] [Module R V]
def _root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange (A : Type v) [Semiring A] [Algebra R A]
    (ρ : _root_.Representation R G V) : _root_.Representation A G (A ⊗[R] V) :=
  ((Module.End.baseChangeHom R A V :
      Module.End R V →ₐ[R] Module.End A (A ⊗[R] V)) :
    Module.End R V →* Module.End A (A ⊗[R] V)).comp ρ
end
end Representation

namespace TauCeti
variable {n : ℕ}
noncomputable def spechtModuleℂ (μ : n.Partition) : FDRep ℂ (Equiv.Perm (Fin n)) :=
  FDRep.of (Representation.baseChange ℂ (spechtModule μ).ρ)
end TauCeti

end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
