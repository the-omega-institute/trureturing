/- GID: D5/S3/Combinatorics/Partitions/SpechtTabloidForm
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtTabloidForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The positive tabloid pairing and its invariant orthogonal complement. -/

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
import D5.S3.Combinatorics.Partitions.SpechtPolytabloid
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.RepresentationTheory.Submodule

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
open scoped BigOperators

namespace TauCeti
open LinearMap (BilinForm)
section Semiring
variable (k : Type*) [CommSemiring k] (X : Type*)
noncomputable def permutationForm : BilinForm k (MonoidAlgebra k X) :=
  Finsupp.lsum k (fun x : X => LinearMap.toSpanSingleton k (MonoidAlgebra k X →ₗ[k] k)
      (Finsupp.lapply x ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

variable {k X}
theorem permutationForm_apply (v w : MonoidAlgebra k X) :
    permutationForm k X v w = v.coeff.sum fun x a => a * w.coeff x := by
  simp [permutationForm, Finsupp.sum, LinearMap.toSpanSingleton_apply]

theorem permutationForm_comm (v w : MonoidAlgebra k X) :
    permutationForm k X v w = permutationForm k X w v := by
  classical
  have h₁ : (v.coeff.sum fun x a => a * w.coeff x) =
      ∑ x ∈ v.coeff.support ∪ w.coeff.support, v.coeff x * w.coeff x :=
    Finsupp.sum_of_support_subset _ Finset.subset_union_left _ (by simp)
  have h₂ : (w.coeff.sum fun x a => a * v.coeff x) =
      ∑ x ∈ v.coeff.support ∪ w.coeff.support, w.coeff x * v.coeff x :=
    Finsupp.sum_of_support_subset _ Finset.subset_union_right _ (by simp)
  rw [permutationForm_apply, permutationForm_apply, h₁, h₂]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

theorem permutationForm_isSymm : (permutationForm k X).IsSymm :=
  ⟨fun v w => permutationForm_comm v w⟩

theorem permutationForm_isRefl : (permutationForm k X).IsRefl :=
  permutationForm_isSymm.isRefl

end Semiring
section Ordered
variable {k : Type*} [CommSemiring k] [LinearOrder k] [IsStrictOrderedRing k] [ExistsAddOfLE k] {X : Type*}
theorem permutationForm_self_pos {v : MonoidAlgebra k X} (hv : v ≠ 0) :
    0 < permutationForm k X v v := by
  rw [permutationForm_apply, Finsupp.sum]
  refine Finset.sum_pos (fun x hx => mul_self_pos.mpr (Finsupp.mem_support_iff.mp hx)) ?_
  exact Finsupp.support_nonempty_iff.mpr (by simpa using hv)

@[simp]
theorem permutationForm_self_eq_zero_iff {v : MonoidAlgebra k X} :
    permutationForm k X v v = 0 ↔ v = 0 := by
  refine ⟨fun h => by_contra fun hv => ?_, fun h => by simp [h]⟩
  exact (permutationForm_self_pos hv).ne' h

theorem permutationForm_restrict_nondegenerate (W : Submodule k (MonoidAlgebra k X)) :
    ((permutationForm k X).restrict W).Nondegenerate := by
  have key : ∀ v : W, permutationForm k X v v = 0 → v = 0 := fun v h =>
    Submodule.coe_eq_zero.mp (permutationForm_self_eq_zero_iff.mp h)
  exact ⟨fun v hv => key v (by simpa using hv v), fun v hv => key v (by simpa using hv v)⟩

end Ordered
section MulAction
variable {k : Type*} [CommSemiring k] {G X : Type*} [Group G] [MulAction G X]
@[simp]
theorem permutationForm_ofMulAction_invariant (g : G) (v w : MonoidAlgebra k X) :
    permutationForm k X (Representation.ofMulAction k G X g v)
        (Representation.ofMulAction k G X g w) = permutationForm k X v w := by
  have hcoeff : (Representation.ofMulAction k G X g v).coeff =
      Finsupp.mapDomain (g • ·) v.coeff := by
    simp [Representation.ofMulAction_def]
  rw [permutationForm_apply, permutationForm_apply, hcoeff,
    Finsupp.sum_mapDomain_index_inj (MulAction.injective g)]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [Representation.coeff_ofMulAction, inv_smul_smul]

theorem permutationForm_ofMulAction_left (g : G) (v w : MonoidAlgebra k X) :
    permutationForm k X (Representation.ofMulAction k G X g v) w =
      permutationForm k X v (Representation.ofMulAction k G X g⁻¹ w) := by
  conv_lhs => rw [← Representation.self_inv_apply (Representation.ofMulAction k G X) g w]
  exact permutationForm_ofMulAction_invariant g v _

theorem ofMulAction_mem_orthogonal {W : Submodule k (MonoidAlgebra k X)}
    (hW : ∀ g : G, ∀ v ∈ W, Representation.ofMulAction k G X g v ∈ W) (g : G)
    {v : MonoidAlgebra k X} (hv : v ∈ (permutationForm k X).orthogonal W) :
    Representation.ofMulAction k G X g v ∈ (permutationForm k X).orthogonal W := by
  intro u hu
  rw [permutationForm_comm, permutationForm_ofMulAction_left, permutationForm_comm]
  exact hv _ (hW g⁻¹ u hu)

noncomputable def orthogonalSubrepresentation
    (σ : Subrepresentation (Representation.ofMulAction k G X)) :
    Subrepresentation (Representation.ofMulAction k G X) where
  toSubmodule := (permutationForm k X).orthogonal σ.toSubmodule
  apply_mem_toSubmodule g _ hv :=
    ofMulAction_mem_orthogonal (fun g' _ hu => σ.apply_mem_toSubmodule g' hu) g hv

@[simp]
theorem toSubmodule_orthogonalSubrepresentation
    (σ : Subrepresentation (Representation.ofMulAction k G X)) :
    (orthogonalSubrepresentation σ).toSubmodule =
      (permutationForm k X).orthogonal σ.toSubmodule :=


  (rfl)

end MulAction
section OrderedField
variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] {G X : Type*} [Group G] [MulAction G X] [Finite X]
theorem isCompl_orthogonalSubrepresentation
    (σ : Subrepresentation (Representation.ofMulAction k G X)) :
    IsCompl σ (orthogonalSubrepresentation σ) := by
  have : Module.Finite k (MonoidAlgebra k X) := Module.Finite.of_basis (MonoidAlgebra.basis X k)
  have h : IsCompl σ.toSubmodule ((permutationForm k X).orthogonal σ.toSubmodule) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate permutationForm_isRefl
      (permutationForm_restrict_nondegenerate σ.toSubmodule)
  constructor
  · rw [disjoint_iff]
    exact Subrepresentation.toSubmodule_injective h.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subrepresentation.toSubmodule_injective h.sup_eq_top

end OrderedField
variable {n : ℕ} (μ : n.Partition)
noncomputable abbrev tabloidForm :
    BilinForm ℚ (MonoidAlgebra ℚ (Equiv.Perm (Fin n) ⧸ youngSubgroup μ)) :=
  permutationForm ℚ (Equiv.Perm (Fin n) ⧸ youngSubgroup μ)
theorem isCompl_orthogonalSubrepresentation_permutationModule
    (σ : Subrepresentation (permutationModule μ).ρ) :
    IsCompl σ (orthogonalSubrepresentation σ) :=
  isCompl_orthogonalSubrepresentation σ

end TauCeti

end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
