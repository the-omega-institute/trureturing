/- GID: D5/S3/Combinatorics/Partitions/SpechtYoungMultiplicity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtYoungMultiplicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual rational Specht to Young intertwiner dimensions have dominance zeros and diagonal one. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected A17.2PORT from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
Changes: selected declarations, namespaces, exact D5 supplier qualifications and
explicit normalization at missing source convenience interfaces. Immutable locators,
license, consumers and retirement against OUR Mathlib pin are recorded in
Library/FiniteGroups/tauceti2026spechtpolytabloids.md.
SOURCE ONLY: no native elaboration, axiom closure, proof-term liveness, admission,
validated Reg, emission, freeze, deposit, PR or CI is claimed. Unfinished audit:
https://github.com/the-omega-institute/trureturing/issues/24542.
Necessary Young-rule construction for the full ordinary HSW theorem; not standalone
firstfreeze content. Young/Kostka equality and both weighted ordinary sums remain open.
utility: none: general unbounded partitions and representation spaces, no enumeration.
-/
import D5.S3.Combinatorics.Partitions.SpechtYoungDominance
import Batteries.Tactic.OpenPrivate

open private D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype
  D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.coe_subtype
  D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.coe_toRepresentation_asAlgebraHom_apply
  from D5.S3.FiniteGroups.FiniteCharacterAlgebra

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators

namespace TauCeti
open YoungTableau
variable {lam : YoungDiagram}
noncomputable def spechtMultiplicity (lam : YoungDiagram) (μ : lam.card.Partition) : ℕ :=
  Module.finrank ℚ
    (Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
      (permutationModule μ).ρ)

@[simp]
theorem spechtMultiplicity_eq_zero_of_not_dominates (μ : lam.card.Partition)
    (h : ¬Dominates (shapePartition lam) μ) : spechtMultiplicity lam μ = 0 := by
  have : Subsingleton
      (Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
        (permutationModule μ).ρ) :=
    ⟨fun f g => sub_eq_zero.mp
      (intertwiningMap_eq_zero_of_not_dominates μ h (f - g))⟩
  exact Module.finrank_zero_of_subsingleton

private theorem exists_intertwiningMap_eq_smul_subtype
    (f : Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
      (permutationModule (shapePartition lam)).ρ) :
    ∃ κ : ℚ, f = κ • D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype (spechtSubrepresentation lam) := by
  obtain ⟨t⟩ := YoungTableau.nonempty lam
  obtain ⟨v, hv, hbv⟩ :=
    exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid t
  let v' : (spechtSubrepresentation lam).toSubmodule := ⟨v, hv⟩
  let et : (spechtSubrepresentation lam).toSubmodule :=
    ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩
  have hmap : f
      ((spechtSubrepresentation lam).toRepresentation.asAlgebraHom
        (columnAntisymmetrizer t) v') =
      (permutationModule (shapePartition lam)).ρ.asAlgebraHom
        (columnAntisymmetrizer t) (f v') :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ f).map_smul'
      (columnAntisymmetrizer t) v'
  have hbet :
      (spechtSubrepresentation lam).toRepresentation.asAlgebraHom
          (columnAntisymmetrizer t) v' = et := by
    apply Subtype.ext
    simpa only [v', et, D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.coe_toRepresentation_asAlgebraHom_apply] using hbv
  obtain ⟨κ, hκ⟩ := exists_eq_smul_polytabloid t (f v')
  refine ⟨κ, ?_⟩
  have het : f et = κ • (et : (permutationModule (shapePartition lam)).V) := by
    rw [← hbet, hmap, hκ]
    simpa only [et] using congrArg
      (fun x : (spechtSubrepresentation lam).toSubmodule =>
        κ • (x : (permutationModule (shapePartition lam)).V)) hbet.symm
  have hspan : Submodule.span ℚ
      (Set.range fun σ : Equiv.Perm (Fin lam.card) =>
        (spechtSubrepresentation lam).toRepresentation σ et) = ⊤ := by
    apply Submodule.map_injective_of_injective
      (spechtSubrepresentation lam).toSubmodule.injective_subtype
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span]
    have himage : (spechtSubrepresentation lam).toSubmodule.subtype ''
        Set.range (fun σ : Equiv.Perm (Fin lam.card) =>
          (spechtSubrepresentation lam).toRepresentation σ et) =
        Set.range (fun σ : Equiv.Perm (Fin lam.card) =>
          (permutationModule (shapePartition lam)).ρ σ (polytabloid t)) := by
      ext x
      constructor
      · rintro ⟨y, ⟨σ, rfl⟩, rfl⟩
        exact ⟨σ, rfl⟩
      · rintro ⟨σ, rfl⟩
        exact ⟨_, ⟨σ, rfl⟩, rfl⟩
    rw [himage]
    exact (spechtSubrepresentation_eq_span_orbit t).symm
  apply Representation.IntertwiningMap.ext
  refine (Submodule.linearMap_eq_iff_of_span_eq_top _ _ hspan).2 ?_
  rintro ⟨_, ⟨σ, rfl⟩⟩
  have hf := Representation.IntertwiningMap.isIntertwining
    (spechtSubrepresentation lam).toRepresentation
    (permutationModule (shapePartition lam)).ρ f σ et
  rw [het] at hf
  simpa only [Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.smul_apply, D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.coe_subtype,
    Subrepresentation.toRepresentation, LinearMap.restrict_apply, map_smul] using hf

private noncomputable def scalarToSpechtIntertwiningMap (lam : YoungDiagram) :
    ℚ →ₗ[ℚ] Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
      (permutationModule (shapePartition lam)).ρ where
  toFun κ := κ • D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype (spechtSubrepresentation lam)
  map_add' κ ν := by rw [add_smul]
  map_smul' κ ν := by rw [smul_eq_mul, mul_smul, RingHom.id_apply]

private theorem scalarToSpechtIntertwiningMap_injective (lam : YoungDiagram) :
    Function.Injective (scalarToSpechtIntertwiningMap lam) := by
  intro κ ν hκν
  obtain ⟨t⟩ := YoungTableau.nonempty lam
  let et : (spechtSubrepresentation lam).toSubmodule :=
    ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩
  have happ : κ • (polytabloid t : (permutationModule (shapePartition lam)).V) =
      ν • (polytabloid t : (permutationModule (shapePartition lam)).V) := by
    simpa only [scalarToSpechtIntertwiningMap,
      LinearMap.coe_mk, AddHom.coe_mk, Representation.IntertwiningMap.smul_apply,
      D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.coe_subtype, et] using
      DFunLike.congr_fun hκν et
  have hpoly : (polytabloid t : (permutationModule (shapePartition lam)).V) ≠ 0 :=
    polytabloid_ne_zero t
  have hsub : (κ - ν) • (polytabloid t : (permutationModule (shapePartition lam)).V) = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr happ
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hpoly)

noncomputable def spechtSelfMultiplicityEquiv (lam : YoungDiagram) :
    ℚ ≃ₗ[ℚ] Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
      (permutationModule (shapePartition lam)).ρ :=
  LinearEquiv.ofBijective (scalarToSpechtIntertwiningMap lam)
    ⟨scalarToSpechtIntertwiningMap_injective lam,
      fun f => by
        obtain ⟨κ, hκ⟩ := exists_intertwiningMap_eq_smul_subtype f
        exact ⟨κ, hκ.symm⟩⟩

@[simp]
theorem spechtMultiplicity_self (lam : YoungDiagram) :
    spechtMultiplicity lam (shapePartition lam) = 1 := by
  rw [spechtMultiplicity, ← (spechtSelfMultiplicityEquiv lam).finrank_eq]
  exact Module.finrank_self ℚ

end TauCeti

end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
