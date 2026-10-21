/- GID: D5/S3/FiniteGroups/ComplexCharacterAbelianProducts
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/ComplexCharacterAbelianProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Irreducibility survives restriction past an abelian direct factor. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19389

admission_basis: escape-witness
Direct frozen dependencies: none.
Module escape_witness: degreesProdAbelian
Scalar action of the abelian factor extends first-factor invariant subspaces to full invariant subspaces.
central_action_scalar | proof_shape: bind-only | escape_witness: none | consumer: firstFactorSubrepresentationOrderIso
firstFactorSubrepresentationOrderIso | proof_shape: bind-only | escape_witness: none | consumer: irreducible_firstFactor
irreducible_firstFactor | proof_shape: bind-only | escape_witness: none | consumer: degreesProdAbelian
degreesProdAbelian | proof_shape: content | escape_witness: degreesProdAbelian | consumer: BahturinCentronePereiraPeakGroups.BCP31.result
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import D5.S3.FiniteGroups.FiniteCharacterAlgebra

namespace D5.S3.FiniteGroups.ComplexCharacterAbelianProducts
open Representation

variable {k B A V : Type*} [Field k] [IsAlgClosed k]
  [Group B] [CommGroup A] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A central element acts as a scalar in a finite-dimensional irreducible representation. -/
theorem central_action_scalar {G : Type*} [Monoid G]
    (ρ : Representation k G V) [ρ.IsIrreducible] (z : G)
    (hz : ∀ g, z * g = g * z) :
    ∃ c : k, ρ z = c • (LinearMap.id : V →ₗ[k] V) := by
  let f : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := ρ z
      isIntertwining' := by
        intro g
        change ρ z * ρ g = ρ g * ρ z
        rw [← map_mul, ← map_mul, hz] }
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective f
  refine ⟨c, ?_⟩
  have h := Representation.IntertwiningMap.ext_iff.mp hc
  exact h.symm

/-- For an abelian second factor, a subspace invariant under the first factor is invariant
under the whole product of an irreducible representation. -/
private def firstFactorSubrepresentationOrderIso
    (ρ : Representation k (B × A) V) [ρ.IsIrreducible] :
    Subrepresentation (ρ.comp (MonoidHom.inl B A)) ≃o Subrepresentation ρ where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨c, hc⟩ := central_action_scalar ρ (1, g.2) (by
          intro h
          apply Prod.ext <;> simp [mul_comm])
        have hfac : ρ g = ρ (1, g.2) * ρ (g.1, 1) := by
          rw [← map_mul]
          congr 1
          apply Prod.ext <;> simp
        rw [hfac, Module.End.mul_apply, hc]
        exact S.toSubmodule.smul_mem c (S.apply_mem_toSubmodule g.1 hv) }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g v hv => S.apply_mem_toSubmodule (g, 1) hv }
  left_inv S := by apply Subrepresentation.toSubmodule_injective; rfl
  right_inv S := by apply Subrepresentation.toSubmodule_injective; rfl
  map_rel_iff' := by rfl

/-- Restriction to the first factor of an irreducible representation remains irreducible
when the second factor is abelian. -/
private theorem irreducible_firstFactor
    (ρ : Representation k (B × A) V) [ρ.IsIrreducible] :
    Representation.IsIrreducible (ρ.comp (MonoidHom.inl B A)) := by
  exact (firstFactorSubrepresentationOrderIso ρ).isSimpleOrder_iff.mpr inferInstance

open CategoryTheory

/-- An abelian direct factor leaves the degrees of simple complex representations unchanged. -/
theorem degreesProdAbelian (B A : Type) [Group B] [CommGroup A] :
    {d : ℕ | ∃ X : FDRep ℂ (B × A), Simple X ∧ Module.finrank ℂ X = d} =
      {d : ℕ | ∃ X : FDRep ℂ B, Simple X ∧ Module.finrank ℂ X = d} := by
  ext d
  constructor
  · rintro ⟨X, hX, hd⟩
    haveI := hX
    haveI : Representation.IsIrreducible X.ρ :=
      D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple X
    let Y : FDRep ℂ B := FDRep.of (X.ρ.comp (MonoidHom.inl B A))
    haveI : Representation.IsIrreducible Y.ρ := irreducible_firstFactor X.ρ
    exact ⟨Y, D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.simple_of_isIrreducible Y, hd⟩
  · rintro ⟨X, hX, hd⟩
    haveI := hX
    haveI : Representation.IsIrreducible X.ρ :=
      D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple X
    let Y : FDRep ℂ (B × A) := FDRep.of (X.ρ.comp (MonoidHom.fst B A))
    have hf : Function.Surjective (MonoidHom.fst B A) := fun b => ⟨(b, 1), rfl⟩
    haveI : Representation.IsIrreducible Y.ρ :=
      (D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.isIrreducible_comp_surjective_iff
        (MonoidHom.fst B A) hf X.ρ).mpr inferInstance
    exact ⟨Y, D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.simple_of_isIrreducible Y, hd⟩

end D5.S3.FiniteGroups.ComplexCharacterAbelianProducts
