/- GID: D5/S3/Combinatorics/Partitions/SpechtSubmoduleTheorem
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtSubmoduleTheorem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: James submodule dichotomy and irreducibility for the literal polytabloid span. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected A17.2PORT from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
Changes: selected declarations/comments, repository namespaces, existing D5 suppliers,
and definitionally equivalent normalization at private supplier boundaries.
License, immutable locators, consumers and retirement rule:
Library/FiniteGroups/tauceti2026spechtpolytabloids.md.
SOURCE ONLY: no elaboration, axiom report, validated Reg, freeze or full HSW result.
These are necessary supplier proofs, not an independent novelty/admission claim.
utility: none: unbounded structural representation theory, no finite computation.
-/
import D5.S3.Combinatorics.Partitions.SpechtTabloidForm
import D5.S3.FiniteGroups.FiniteCharacterAlgebra
import Mathlib.RepresentationTheory.Submodule

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
open scoped BigOperators

namespace TauCeti
namespace YoungTableau
variable {μ : YoungDiagram}
@[simp]
theorem colIndex_apply (t : YoungTableau μ) (c : ↥μ.cells) :
    colIndex t (t c) = (c : ℕ × ℕ).2 := by
  rw [colIndex_def, Equiv.symm_apply_apply]

def rowFiberEquiv (t : YoungTableau μ) (i : ℕ) :
    {k : Fin μ.card // rowIndex t k = i} ≃ ↥(μ.row i) :=


  (Equiv.subtypeEquiv (p := fun k => rowIndex t k = i) (q := fun c : ↥μ.cells => (↑c : ℕ × ℕ).1 = i)
      t.symm fun _ => Iff.rfl).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ μ.cells) fun c => c.1 = i).trans <|
      Equiv.subtypeEquivRight fun _ => by
        rw [YoungDiagram.mem_row_iff, YoungDiagram.mem_cells]

theorem rowIndex_colIndex_mem (t : YoungTableau μ) (x : Fin μ.card) :
    (rowIndex t x, colIndex t x) ∈ μ := by
  rw [rowIndex_def, colIndex_def]
  simp

theorem colIndex_lt_rowLen (t : YoungTableau μ) (x : Fin μ.card) :
    colIndex t x < μ.rowLen (rowIndex t x) :=
  YoungDiagram.mem_iff_lt_rowLen.mp (rowIndex_colIndex_mem t x)

theorem exists_rowIndex_colIndex (t : YoungTableau μ) {i j : ℕ} (h : (i, j) ∈ μ) :
    ∃ x, rowIndex t x = i ∧ colIndex t x = j :=
  ⟨t ⟨(i, j), (YoungDiagram.mem_cells _).mpr h⟩, by simp, by simp⟩

theorem card_filter_rowIndex_eq (t : YoungTableau μ) (i : ℕ) :
    (Finset.univ.filter fun y => rowIndex t y = i).card = μ.rowLen i := by
  rw [← Fintype.card_subtype, Fintype.card_congr (rowFiberEquiv t i), Fintype.card_coe]
  exact (YoungDiagram.rowLen_eq_card μ).symm

private theorem card_filter_colIndex_lt_and_rowIndex_eq (t : YoungTableau μ) (i k : ℕ) :
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

private theorem card_filter_colIndex_comp_lt_and_rowIndex_eq_le (t : YoungTableau μ)
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

private theorem sum_card_filter_colIndex_comp_lt_and_rowIndex_eq (t : YoungTableau μ)
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

theorem colIndex_lt_rowLen_of_injective (t : YoungTableau μ) (u : Equiv.Perm (Fin μ.card))
    (hu : Function.Injective fun x => (rowIndex t x, colIndex t (u x))) (x : Fin μ.card) :
    colIndex t (u x) < μ.rowLen (rowIndex t x) := by
  have hmemS : ∀ y : Fin μ.card, rowIndex t y ∈ Finset.image (rowIndex t) Finset.univ :=
    fun y => Finset.mem_image_of_mem _ (Finset.mem_univ y)

  have hi := (Finset.sum_eq_sum_iff_of_le fun i _ =>
      card_filter_colIndex_comp_lt_and_rowIndex_eq_le t hu i (μ.rowLen (rowIndex t x))).mp
    (sum_card_filter_colIndex_comp_lt_and_rowIndex_eq t u (μ.rowLen (rowIndex t x)))
    (rowIndex t x) (hmemS x)
  rw [min_self] at hi

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

@[simp]
theorem rowIndex_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) (k : Fin μ.card) :
    rowIndex (relabel σ t) k = rowIndex t (σ⁻¹ k) := by
  rw [rowIndex_def, rowIndex_def, relabel_symm_apply]

def relabelPerm (t t' : YoungTableau μ) : Equiv.Perm (Fin μ.card) :=
  t.symm.trans t'

@[simp]
theorem relabel_relabelPerm (t t' : YoungTableau μ) : relabel (relabelPerm t t') t = t' := by
  rw [relabel, relabelPerm, ← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]

theorem exists_relabel_eq (t t' : YoungTableau μ) : ∃ σ, relabel σ t = t' :=
  ⟨relabelPerm t t', relabel_relabelPerm t t'⟩

end YoungTableau
variable {α ι : Type*}
theorem swap_mem_fiberSubgroup [DecidableEq α] {f : α → ι} {x y : α} (h : f x = f y) :
    Equiv.swap x y ∈ fiberSubgroup f := by
  rw [mem_fiberSubgroup]
  intro a
  rcases eq_or_ne a x with rfl | hax
  · rw [Equiv.swap_apply_left, h]
  · rcases eq_or_ne a y with rfl | hay
    · rw [Equiv.swap_apply_right, h]
    · rw [Equiv.swap_apply_of_ne_of_ne hax hay]

namespace YoungTableau
variable {μ : YoungDiagram}
theorem swap_mem_rowSubgroup {t : YoungTableau μ} {x y : Fin μ.card}
    (h : rowIndex t x = rowIndex t y) : Equiv.swap x y ∈ rowSubgroup t := by
  rw [rowSubgroup_def]
  exact swap_mem_fiberSubgroup h

theorem swap_mem_colSubgroup {t : YoungTableau μ} {x y : Fin μ.card}
    (h : colIndex t x = colIndex t y) : Equiv.swap x y ∈ colSubgroup t := by
  rw [colSubgroup_def]
  exact swap_mem_fiberSubgroup h
def RowMeetsColumnTwice (t s : YoungTableau μ) : Prop :=
  ∃ x y, x ≠ y ∧ rowIndex t x = rowIndex t y ∧ colIndex s x = colIndex s y

theorem rowMeetsColumnTwice_def (t s : YoungTableau μ) :
    RowMeetsColumnTwice t s ↔
      ∃ x y, x ≠ y ∧ rowIndex t x = rowIndex t y ∧ colIndex s x = colIndex s y :=
  Iff.rfl

@[simp]
theorem rowMeetsColumnTwice_relabel_iff (t : YoungTableau μ) (σ : Equiv.Perm (Fin μ.card)) :
    RowMeetsColumnTwice t (relabel σ t) ↔
      ∃ x y, x ≠ y ∧ rowIndex t x = rowIndex t y ∧
        colIndex t (σ⁻¹ x) = colIndex t (σ⁻¹ y) := by
  simp only [rowMeetsColumnTwice_def, colIndex_relabel]

theorem rowMeetsColumnTwice_relabel_left_iff (t s : YoungTableau μ)
    (σ : Equiv.Perm (Fin μ.card)) :
    RowMeetsColumnTwice (relabel σ t) s ↔ RowMeetsColumnTwice t (relabel σ⁻¹ s) := by
  simp only [rowMeetsColumnTwice_def, rowIndex_relabel, colIndex_relabel, inv_inv]
  constructor
  · rintro ⟨x, y, hxy, hrow, hcol⟩
    exact ⟨σ⁻¹ x, σ⁻¹ y, fun h => hxy (σ⁻¹.injective h), hrow, by simpa using hcol⟩
  · rintro ⟨x, y, hxy, hrow, hcol⟩
    exact ⟨σ x, σ y, fun h => hxy (σ.injective h), by simpa using hrow, hcol⟩

open scoped Pointwise
theorem mem_mul_of_not_rowMeetsColumnTwice {t : YoungTableau μ} {σ : Equiv.Perm (Fin μ.card)}
    (h : ¬RowMeetsColumnTwice t (relabel σ t)) :
    σ ∈ (rowSubgroup t : Set (Equiv.Perm (Fin μ.card))) *
      (colSubgroup t : Set (Equiv.Perm (Fin μ.card))) := by
  rw [rowMeetsColumnTwice_relabel_iff] at h

  have hu : Function.Injective fun x => (rowIndex t x, colIndex t (σ⁻¹ x)) := by
    intro a b hab
    rw [Prod.mk.injEq] at hab
    by_contra hne
    exact h ⟨a, b, hne, hab.1, hab.2⟩

  have hcell : ∀ x, (rowIndex t x, colIndex t (σ⁻¹ x)) ∈ μ := fun x =>
    YoungDiagram.mem_iff_lt_rowLen.mpr (colIndex_lt_rowLen_of_injective t σ⁻¹ hu x)
  set g : Fin μ.card → Fin μ.card := fun x =>
    t ⟨(rowIndex t x, colIndex t (σ⁻¹ x)), (YoungDiagram.mem_cells _).mpr (hcell x)⟩ with hg
  have hgrow : ∀ x, rowIndex t (g x) = rowIndex t x := fun x => by rw [hg]; simp
  have hgcol : ∀ x, colIndex t (g x) = colIndex t (σ⁻¹ x) := fun x => by rw [hg]; simp
  have hginj : Function.Injective g := by
    intro a b hab
    exact hu (Prod.ext ((hgrow a).symm.trans (by rw [hab, hgrow]))
      ((hgcol a).symm.trans (by rw [hab, hgcol])))

  set p : Equiv.Perm (Fin μ.card) :=
    Equiv.ofBijective g (Finite.injective_iff_bijective.mp hginj) with hp
  have hpapply : ∀ x, p x = g x := fun x => by
    rw [hp, Equiv.coe_ofBijective]
  have hprow : p ∈ rowSubgroup t := mem_rowSubgroup.mpr fun k => by rw [hpapply, hgrow]
  have hpinv : ∀ k, p (p⁻¹ k) = k := fun k => by
    rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  have hqcol : σ⁻¹ * p⁻¹ ∈ colSubgroup t := by
    refine mem_colSubgroup.mpr fun k => ?_
    rw [Equiv.Perm.mul_apply]
    have h1 := (hgcol (p⁻¹ k)).symm
    rwa [← hpapply, hpinv] at h1
  have hfac : σ⁻¹ = (σ⁻¹ * p⁻¹) * p := by
    rw [inv_mul_cancel_right]
  refine Set.mem_mul.mpr ⟨p⁻¹, inv_mem hprow, (σ⁻¹ * p⁻¹)⁻¹, inv_mem hqcol, ?_⟩
  rw [← mul_inv_rev, ← hfac, inv_inv]

end YoungTableau
variable {k G : Type*} [CommSemiring k] [Group G] (χ : G →* k) (H : Subgroup G) [Fintype H]
@[simp]
theorem subgroupCharSum_mul_single (p : H) :
    subgroupCharSum χ H * MonoidAlgebra.single (p : G) 1 =
      χ ((p : G)⁻¹) • subgroupCharSum χ H := by
  rw [subgroupCharSum_def, ← MonoidAlgebra.of_apply, Finset.sum_mul, Finset.smul_sum]
  simp_rw [smul_mul_assoc, ← (MonoidAlgebra.of k G).map_mul]
  apply Fintype.sum_equiv (Equiv.mulRight p)
  intro h
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul, smul_smul]
  rw [mul_left_comm, map_mul_eq_one χ (inv_mul_cancel (p : G)), mul_one]

end TauCeti
namespace Representation
variable {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]
theorem asAlgebraHom_eq_zero_of_mul_single_eq_neg
    (h2inj : Function.Injective fun w : V ↦ (2 : ℕ) • w)
    (ρ : Representation k G V) {a : MonoidAlgebra k G} {g : G} {v : V} (hfix : ρ g v = v)
    (hneg : a * MonoidAlgebra.single g 1 = -a) :
    ρ.asAlgebraHom a v = 0 := by

  have key : ρ.asAlgebraHom a v = -(ρ.asAlgebraHom a v) := by
    conv_lhs => rw [← hfix]
    rw [← Representation.asAlgebraHom_single_one ρ, ← Module.End.mul_apply, ← map_mul, hneg,
      map_neg, LinearMap.neg_apply]

  refine h2inj ?_
  simp only [two_nsmul, add_zero]
  nth_rewrite 1 [key]
  exact neg_add_cancel _

end Representation
namespace TauCeti
section Semiring
variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V] (χ : G →* k) (H : Subgroup G) [Fintype H]
theorem asAlgebraHom_subgroupCharSum_apply (ρ : Representation k G V) (v : V) :
    ρ.asAlgebraHom (subgroupCharSum χ H) v = ∑ h : H, χ (h : G) • ρ (h : G) v := by
  rw [subgroupCharSum_def, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun h _ => by
    rw [map_smul, LinearMap.smul_apply, MonoidAlgebra.of_apply,
      Representation.asAlgebraHom_single_one]

end Semiring
section Ring
variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V] (χ : G →* k) (H : Subgroup G) [Fintype H]
theorem asAlgebraHom_subgroupCharSum_apply_eq_zero
    (h2inj : Function.Injective fun w : V => (2 : ℕ) • w) (ρ : Representation k G V) {p : G}
    (hp : p ∈ H) (hχ : χ p⁻¹ = -1) {v : V} (hfix : ρ p v = v) :
    ρ.asAlgebraHom (subgroupCharSum χ H) v = 0 :=
  Representation.asAlgebraHom_eq_zero_of_mul_single_eq_neg h2inj ρ hfix
    (by rw [subgroupCharSum_mul_single χ H ⟨p, hp⟩, hχ, neg_one_smul])

end Ring
namespace YoungTableau
variable {μ : YoungDiagram}
attribute [local instance] decidablePredMemColSubgroup
@[simp]
theorem mul_columnAntisymmetrizer_right (t : YoungTableau μ) (q : colSubgroup t) :
    columnAntisymmetrizer t * MonoidAlgebra.single (q : Equiv.Perm (Fin μ.card)) 1 =
      ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
        columnAntisymmetrizer t := by
  rw [columnAntisymmetrizer_eq_subgroupCharSum, subgroupCharSum_mul_single]
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
    coe_signLinearCharacter_apply, Equiv.Perm.sign_inv]

theorem asAlgebraHom_columnAntisymmetrizer_apply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ρ : Representation ℚ (Equiv.Perm (Fin μ.card)) V) (t : YoungTableau μ) (v : V) :
    ρ.asAlgebraHom (columnAntisymmetrizer t) v =
      ∑ q : colSubgroup t,
        ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) • ρ q v := by
  rw [columnAntisymmetrizer_eq_subgroupCharSum, asAlgebraHom_subgroupCharSum_apply]
  simp
theorem tabloid_surjective : Function.Surjective (tabloid (μ := μ)) := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  intro q
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨relabel (σ * (rowYoungConjugator t)⁻¹) t, ?_⟩
  rw [tabloid_def, rowYoungConjugator_relabel, inv_mul_cancel_right]

theorem polytabloid_def (t : YoungTableau μ) :
    polytabloid t =
      (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t)
        (MonoidAlgebra.single (tabloid t) 1) :=
  (rfl)

end YoungTableau
open YoungTableau
variable {μ : YoungDiagram}
noncomputable abbrev permutationModuleBasis {n : ℕ} (μ : n.Partition) :
    Module.Basis (Equiv.Perm (Fin n) ⧸ youngSubgroup μ) ℚ
      (permutationModule μ).V :=
  MonoidAlgebra.basis (Equiv.Perm (Fin n) ⧸ youngSubgroup μ) ℚ
@[simp]
theorem spechtSubrepresentation_toSubmodule (μ : YoungDiagram) :
    (spechtSubrepresentation μ).toSubmodule =
      Submodule.span ℚ (Set.range (polytabloid (μ := μ))) :=
  (rfl)

theorem spechtSubrepresentation_eq_span_orbit (t : YoungTableau μ) :
    (spechtSubrepresentation μ).toSubmodule =
      Submodule.span ℚ
        (Set.range fun σ : Equiv.Perm (Fin μ.card) =>
          (permutationModule (shapePartition μ)).ρ σ (polytabloid t)) := by
  rw [spechtSubrepresentation_toSubmodule]
  congr 1
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨t', rfl⟩
    obtain ⟨σ, rfl⟩ := exists_relabel_eq t t'
    exact ⟨σ, (polytabloid_relabel σ t).symm⟩
  · rintro _ ⟨σ, rfl⟩
    exact ⟨relabel σ t, polytabloid_relabel σ t⟩
theorem asAlgebraHom_columnAntisymmetrizer_single_eq_zero {lam : YoungDiagram}
    (t : YoungTableau lam) (μ : lam.card.Partition)
    (q : Equiv.Perm (Fin lam.card) ⧸ youngSubgroup μ) {p : Equiv.Perm (Fin lam.card)}
    (hp : p ∈ colSubgroup t) (hsign : Equiv.Perm.sign p = -1) (hfix : p • q = q) :
    (permutationModule μ).ρ.asAlgebraHom (columnAntisymmetrizer t)
      (MonoidAlgebra.single q 1) = 0 := by
  have hfix' : (permutationModule μ).ρ p (MonoidAlgebra.single q (1 : ℚ)) =
      MonoidAlgebra.single q 1 := by
    rw [Representation.ofMulAction_single, hfix]

  have : HasUniqueDiv (permutationModule μ) := .of_module_rat _
  rw [columnAntisymmetrizer_eq_subgroupCharSum]
  exact asAlgebraHom_subgroupCharSum_apply_eq_zero _ _ (nsmul_right_injective two_ne_zero) _ hp
    (by simp [hsign]) hfix'

namespace YoungTableau
attribute [local instance] decidablePredMemColSubgroup
private theorem exists_asAlgebraHom_columnAntisymmetrizer_single_eq_sign_smul
    (s t : YoungTableau μ) (h : ¬ RowMeetsColumnTwice s t) :
    ∃ q : Equiv.Perm (Fin μ.card),
      (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t)
        (MonoidAlgebra.single (tabloid s) 1)
          = ((Equiv.Perm.sign q : ℤ) : ℚ) • polytabloid t := by



  obtain ⟨σ, rfl⟩ := exists_relabel_eq t s
  rw [rowMeetsColumnTwice_relabel_left_iff] at h
  obtain ⟨p, hp, q, hq, hpq⟩ := Set.mem_mul.mp (mem_mul_of_not_rowMeetsColumnTwice h)
  have hσ : σ = q⁻¹ * p⁻¹ := by rw [← mul_inv_rev, hpq, inv_inv]
  refine ⟨q, ?_⟩
  have htab : MonoidAlgebra.single (tabloid (relabel σ t)) (1 : ℚ) =
      (permutationModule (shapePartition μ)).ρ q⁻¹
        (MonoidAlgebra.single (tabloid t) 1) := by
    rw [Representation.ofMulAction_single, tabloid_relabel, hσ, mul_smul,
      smul_tabloid_eq_self_iff.mpr (inv_mem (SetLike.mem_coe.mp hp))]
  rw [htab, ← Representation.asAlgebraHom_single_one (permutationModule (shapePartition μ)).ρ,
    ← Module.End.mul_apply, ← map_mul,
    mul_columnAntisymmetrizer_right t ⟨q⁻¹, inv_mem (SetLike.mem_coe.mp hq)⟩,
    Equiv.Perm.sign_inv, map_smul, LinearMap.smul_apply, ← polytabloid_def]

theorem exists_eq_smul_polytabloid_single (t : YoungTableau μ)
    (T : Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ)) :
    ∃ κ : ℚ, (κ = 0 ∨ κ = 1 ∨ κ = -1) ∧
      (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t)
          (MonoidAlgebra.single T 1) = κ • polytabloid t := by
  obtain ⟨s, rfl⟩ := tabloid_surjective T
  by_cases h : RowMeetsColumnTwice s t
  ·

    obtain ⟨x, y, hxy, hrow, hcol⟩ := (rowMeetsColumnTwice_def _ _).mp h
    exact ⟨0, Or.inl rfl, by
      rw [zero_smul]
      exact asAlgebraHom_columnAntisymmetrizer_single_eq_zero t (shapePartition μ) (tabloid s)
        (swap_mem_colSubgroup hcol) (Equiv.Perm.sign_swap hxy)
        (smul_tabloid_eq_self_iff.mpr (swap_mem_rowSubgroup hrow))⟩
  · obtain ⟨q, hq⟩ := exists_asAlgebraHom_columnAntisymmetrizer_single_eq_sign_smul s t h
    exact ⟨_, Or.inr (by rcases Int.units_eq_one_or (Equiv.Perm.sign q) with h | h <;> simp [h]),
      hq⟩

theorem exists_eq_smul_polytabloid (t : YoungTableau μ)
    (v : (permutationModule (shapePartition μ)).V) :
    ∃ κ : ℚ,
      (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t) v =
        κ • polytabloid t := by
  have hv : v ∈ Submodule.span ℚ (Set.range (permutationModuleBasis (shapePartition μ))) := by
    rw [Module.Basis.span_eq]
    exact Submodule.mem_top
  have hspan : (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t) v ∈
      Submodule.span ℚ {polytabloid t} := by
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨T, rfl⟩ := hw
      obtain ⟨κ, -, hκ⟩ := exists_eq_smul_polytabloid_single t T
      rw [MonoidAlgebra.basis_apply, hκ]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  obtain ⟨κ, hκ⟩ := Submodule.mem_span_singleton.mp hspan
  exact ⟨κ, hκ.symm⟩

theorem tabloidForm_asAlgebraHom_columnAntisymmetrizer (t : YoungTableau μ)
    (v w : (permutationModule (shapePartition μ)).V) :
    tabloidForm (shapePartition μ)
        ((permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t) v) w =
      tabloidForm (shapePartition μ) v
        ((permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t) w) := by
  rw [asAlgebraHom_columnAntisymmetrizer_apply, asAlgebraHom_columnAntisymmetrizer_apply,
    map_sum, LinearMap.sum_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.inv (colSubgroup t)) _ _ fun q => ?_
  rw [map_smul, LinearMap.smul_apply, map_smul]
  simp only [Equiv.inv_apply, InvMemClass.coe_inv, Equiv.Perm.sign_inv, smul_eq_mul]
  rw [permutationForm_ofMulAction_left]

end YoungTableau
theorem spechtSubrepresentation_le_or_le_orthogonal (μ : YoungDiagram)
    (U : Subrepresentation (permutationModule (shapePartition μ)).ρ) :
    spechtSubrepresentation μ ≤ U ∨
      U ≤ orthogonalSubrepresentation (spechtSubrepresentation μ) := by
  by_cases hex : ∃ (t : YoungTableau μ) (v : (permutationModule (shapePartition μ)).V),
      v ∈ U.toSubmodule ∧
      (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t) v ≠ 0
  · obtain ⟨t, v, hvU, hne⟩ := hex
    refine Or.inl ?_
    obtain ⟨κ, hκ⟩ := exists_eq_smul_polytabloid t v
    have hκ0 : κ ≠ 0 := by
      rintro rfl
      exact hne (by rw [hκ, zero_smul])

    have hmem : polytabloid t ∈ U.toSubmodule := by
      have hsmul : κ • polytabloid t ∈ U.toSubmodule :=
        hκ ▸ Representation.asAlgebraHom_mem_of_forall_mem _ U.toSubmodule
          (fun g _ hv => U.apply_mem_toSubmodule g hv) v hvU (columnAntisymmetrizer t)
      have := U.toSubmodule.smul_mem κ⁻¹ hsmul
      rwa [smul_smul, inv_mul_cancel₀ hκ0, one_smul] at this

    change (spechtSubrepresentation μ).toSubmodule ≤ U.toSubmodule
    rw [spechtSubrepresentation_eq_span_orbit t]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨σ, rfl⟩
    exact U.apply_mem_toSubmodule σ hmem
  · push Not at hex
    refine Or.inr ?_
    change U.toSubmodule ≤ (orthogonalSubrepresentation (spechtSubrepresentation μ)).toSubmodule
    rw [toSubmodule_orthogonalSubrepresentation]
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [spechtSubrepresentation_toSubmodule] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      rw [polytabloid_def, tabloidForm_asAlgebraHom_columnAntisymmetrizer, hex t v hv,
        map_zero]
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul r x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

theorem isAtom_spechtSubrepresentation (μ : YoungDiagram) :
    IsAtom (spechtSubrepresentation μ) := by
  refine ⟨spechtSubrepresentation_ne_bot μ, fun U hU => ?_⟩
  rcases spechtSubrepresentation_le_or_le_orthogonal μ U with hle | hle
  · exact absurd (le_antisymm hU.le hle) hU.ne
  · exact le_bot_iff.mp
      ((isCompl_orthogonalSubrepresentation_permutationModule (shapePartition μ)
        (spechtSubrepresentation μ)).disjoint hU.le hle)

end TauCeti

end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
