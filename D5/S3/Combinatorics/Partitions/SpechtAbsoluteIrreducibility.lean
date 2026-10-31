/- GID: D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational Specht intertwining endomorphisms are scalars. -/

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
import D5.S3.Combinatorics.Partitions.SpechtSubmoduleTheorem
import Mathlib.RepresentationTheory.Intertwining

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
open scoped BigOperators

namespace TauCeti
open YoungTableau
namespace YoungTableau
variable {lam : YoungDiagram}
theorem exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid (t : YoungTableau lam) :
    ∃ e ∈ (spechtSubrepresentation lam).toSubmodule,
      (permutationModule (shapePartition lam)).ρ.asAlgebraHom (columnAntisymmetrizer t) e =
        polytabloid t := by
  have hc : IsCompl (spechtSubrepresentation lam)
      (orthogonalSubrepresentation (spechtSubrepresentation lam)) :=
    isCompl_orthogonalSubrepresentation_permutationModule (shapePartition lam) _
  have hstable : ∀ (σ : Subrepresentation (permutationModule (shapePartition lam)).ρ)
      (g : Equiv.Perm (Fin lam.card)), ∀ v ∈ σ.toSubmodule,
      (permutationModule (shapePartition lam)).ρ g v ∈ σ.toSubmodule :=
    fun σ g _ hv => σ.apply_mem_toSubmodule g hv

  have hsup : MonoidAlgebra.single (tabloid t) (1 : ℚ) ∈
      (spechtSubrepresentation lam).toSubmodule ⊔
        (orthogonalSubrepresentation (spechtSubrepresentation lam)).toSubmodule := by
    have h := congrArg Subrepresentation.toSubmodule hc.sup_eq_top
    rw [Subrepresentation.toSubmodule_sup, _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_top] at h
    rw [h]
    exact Submodule.mem_top
  obtain ⟨e, he, w, hw, hsum⟩ := Submodule.mem_sup.mp hsup
  refine ⟨e, he, ?_⟩

  have hmemS : (permutationModule (shapePartition lam)).ρ.asAlgebraHom (columnAntisymmetrizer t) e ∈
      (spechtSubrepresentation lam).toSubmodule :=
    Representation.asAlgebraHom_mem_of_forall_mem _ _ (hstable _) e he _
  have hmemW : (permutationModule (shapePartition lam)).ρ.asAlgebraHom (columnAntisymmetrizer t) w ∈
      (orthogonalSubrepresentation (spechtSubrepresentation lam)).toSubmodule :=
    Representation.asAlgebraHom_mem_of_forall_mem _ _ (hstable _) w hw _

  have hadd : (permutationModule (shapePartition lam)).ρ.asAlgebraHom (columnAntisymmetrizer t) e +
      (permutationModule (shapePartition lam)).ρ.asAlgebraHom (columnAntisymmetrizer t) w =
      polytabloid t := by
    rw [← map_add, hsum, polytabloid_def]
  have hmemW' : (permutationModule (shapePartition lam)).ρ.asAlgebraHom
      (columnAntisymmetrizer t) w ∈ (spechtSubrepresentation lam).toSubmodule := by
    have : (permutationModule (shapePartition lam)).ρ.asAlgebraHom (columnAntisymmetrizer t) w =
        polytabloid t -
          (permutationModule (shapePartition lam)).ρ.asAlgebraHom (columnAntisymmetrizer t) e := by
      rw [← hadd]
      exact (add_sub_cancel_left _ _).symm
    rw [this]
    exact Submodule.sub_mem _ (polytabloid_mem_spechtSubrepresentation t) hmemS
  have hdisj : Disjoint (spechtSubrepresentation lam).toSubmodule
      (orthogonalSubrepresentation (spechtSubrepresentation lam)).toSubmodule :=
    disjoint_iff.mpr (by
      rw [← Subrepresentation.toSubmodule_inf, hc.inf_eq_bot, _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_bot])
  rw [← hadd, Submodule.disjoint_def.mp hdisj _ hmemW' hmemW, add_zero]

end YoungTableau
variable {mu : YoungDiagram}
private theorem intertwiningMap_eq_smul_one_of_apply_polytabloid_eq
    (t : YoungTableau mu)
    (f : Representation.IntertwiningMap
      (spechtSubrepresentation mu).toRepresentation
      (spechtSubrepresentation mu).toRepresentation)
    (kappa : ℚ)
    (h : f ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩ =
      kappa • ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩) :
    f = kappa • 1 := by
  let et : (spechtSubrepresentation mu).toSubmodule :=
    ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩
  let orbit : Set (spechtSubrepresentation mu).toSubmodule :=
    Set.range fun sigma : Equiv.Perm (Fin mu.card) =>
      (spechtSubrepresentation mu).toRepresentation sigma et
  have hspan : Submodule.span ℚ orbit = ⊤ := by
    apply Submodule.map_injective_of_injective
      (spechtSubrepresentation mu).toSubmodule.injective_subtype
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span]
    have himage : (spechtSubrepresentation mu).toSubmodule.subtype '' orbit =
        Set.range (fun sigma : Equiv.Perm (Fin mu.card) =>
          (permutationModule (shapePartition mu)).ρ sigma (polytabloid t)) := by
      ext x
      constructor
      · rintro ⟨y, ⟨sigma, rfl⟩, rfl⟩
        exact ⟨sigma, rfl⟩
      · rintro ⟨sigma, rfl⟩
        exact ⟨_, ⟨sigma, rfl⟩, rfl⟩
    rw [himage]
    exact (spechtSubrepresentation_eq_span_orbit t).symm
  apply Representation.IntertwiningMap.ext
  refine (Submodule.linearMap_eq_iff_of_span_eq_top _ _ hspan).2 ?_
  rintro ⟨_, ⟨sigma, rfl⟩⟩
  have hf := Representation.IntertwiningMap.isIntertwining
    (spechtSubrepresentation mu).toRepresentation
    (spechtSubrepresentation mu).toRepresentation f sigma et
  have het : f et = kappa • et := by simpa only [et] using h
  rw [het] at hf
  simpa only [Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.smul_apply,
    Representation.IntertwiningMap.coe_one, id_eq, map_smul] using hf

private theorem algebraMap_intertwiningMap_injective {G V : Type*} [Monoid G] [AddCommGroup V]
    [Module ℚ V] {rho : Representation ℚ G V} {v : V} (hv : v ≠ 0) :
    Function.Injective (algebraMap ℚ (Representation.IntertwiningMap rho rho)) := by
  intro q r hqr
  have happ : q • v = r • v := by
    simpa only [Representation.IntertwiningMap.algebraMap_apply,
      Representation.IntertwiningMap.smul_apply, Representation.IntertwiningMap.coe_one,
      id_eq] using congrArg (fun F => F v) hqr
  have hsub : (q - r) • v = 0 := by rw [sub_smul, happ, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hv)

private theorem algebraMap_intertwiningMap_spechtSubrepresentation_injective
    (mu : YoungDiagram) :
    Function.Injective
      (algebraMap ℚ (Representation.IntertwiningMap
        (spechtSubrepresentation mu).toRepresentation
        (spechtSubrepresentation mu).toRepresentation)) := by
  obtain ⟨t⟩ := YoungTableau.nonempty mu
  refine algebraMap_intertwiningMap_injective
    (v := (⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩ :
      (spechtSubrepresentation mu).toSubmodule)) ?_
  simpa only [ne_eq, Submodule.mk_eq_zero] using polytabloid_ne_zero t

theorem algebraMap_intertwiningMap_spechtSubrepresentation_bijective (mu : YoungDiagram) :
    Function.Bijective
      (algebraMap ℚ (Representation.IntertwiningMap
        (spechtSubrepresentation mu).toRepresentation
        (spechtSubrepresentation mu).toRepresentation)) := by
  have hcoe (a : MonoidAlgebra ℚ (Equiv.Perm (Fin mu.card)))
      (x : (spechtSubrepresentation mu).toSubmodule) :
      (((spechtSubrepresentation mu).toRepresentation.asAlgebraHom a x :
        (spechtSubrepresentation mu).toSubmodule) :
        (permutationModule (shapePartition mu)).V) =
        (permutationModule (shapePartition mu)).ρ.asAlgebraHom a x := by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
        simpa only [map_add, LinearMap.add_apply, Submodule.coe_add] using
          congrArg₂ (fun u v => u + v) ha hb
    | single g r =>
        simp only [Representation.asAlgebraHom_single]
        congr 1
  constructor
  · exact algebraMap_intertwiningMap_spechtSubrepresentation_injective mu
  · intro f
    obtain ⟨t⟩ := YoungTableau.nonempty mu
    obtain ⟨v, hv, hbv⟩ :=
      exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid t
    let v' : (spechtSubrepresentation mu).toSubmodule := ⟨v, hv⟩
    have hmap : f
        ((spechtSubrepresentation mu).toRepresentation.asAlgebraHom
          (columnAntisymmetrizer t) v') =
        (spechtSubrepresentation mu).toRepresentation.asAlgebraHom
          (columnAntisymmetrizer t) (f v') :=
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _ f).map_smul'
        (columnAntisymmetrizer t) v'
    obtain ⟨kappa, hkappa⟩ := exists_eq_smul_polytabloid t (f v' : _)
    have hpoly : f ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩ =
        kappa • ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩ := by
      apply Subtype.ext
      have hmap' := congrArg Subtype.val hmap
      have hbv' : (spechtSubrepresentation mu).toRepresentation.asAlgebraHom
          (columnAntisymmetrizer t) v' =
          ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩ := by
        apply Subtype.ext
        simpa only [hcoe] using hbv
      rw [hbv'] at hmap'
      exact hmap'.trans (by
        simpa only [hcoe,
          Submodule.coe_smul] using hkappa)
    refine ⟨kappa, ?_⟩
    have hfscalar := intertwiningMap_eq_smul_one_of_apply_polytabloid_eq t f kappa hpoly
    rw [hfscalar]
    rfl

theorem algebraMap_intertwiningMap_spechtModule_bijective {n : ℕ} (mu : n.Partition) :
    Function.Bijective
      (algebraMap ℚ (Representation.IntertwiningMap (spechtModule mu).ρ (spechtModule mu).ρ)) := by
  constructor
  · obtain ⟨t⟩ := YoungTableau.nonempty (YoungDiagram.ofPartition mu)
    let et : (spechtModule mu).V :=
      ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩
    refine algebraMap_intertwiningMap_injective (v := et) ?_
    intro het

    refine polytabloid_ne_zero t ?_
    simpa only [et, ZeroMemClass.coe_zero] using congrArg
      (fun v : (spechtModule mu).V =>
        ((v : (spechtSubrepresentation (YoungDiagram.ofPartition mu)).toSubmodule) :
          (permutationModule (shapePartition (YoungDiagram.ofPartition mu))).V)) het
  · intro f
    let e := (finCongr (YoungDiagram.card_ofPartition mu).symm).permCongrHom
    let f' : Representation.IntertwiningMap
        (spechtSubrepresentation (YoungDiagram.ofPartition mu)).toRepresentation
        (spechtSubrepresentation (YoungDiagram.ofPartition mu)).toRepresentation :=
      { toLinearMap := f.toLinearMap
        isIntertwining' g := by
          have hf := f.isIntertwining' (e.symm g)
          simpa only [spechtModule, FDRep.of_ρ', MonoidHom.comp_apply,
            MulEquiv.coe_toMonoidHom, e, MulEquiv.apply_symm_apply] using hf }
    obtain ⟨q, hq⟩ :=
      (algebraMap_intertwiningMap_spechtSubrepresentation_bijective
        (YoungDiagram.ofPartition mu)).surjective f'
    refine ⟨q, ?_⟩
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x

    change q • x = f x
    have hx := DFunLike.congr_fun hq x
    change q • x = f x at hx
    exact hx

private noncomputable def spechtModuleScalarAlgEquiv {n : ℕ} (mu : n.Partition) :
    ℚ ≃ₐ[ℚ] Representation.IntertwiningMap (spechtModule mu).ρ (spechtModule mu).ρ := by
  apply AlgEquiv.ofBijective (Algebra.ofId ℚ _)
  have hfun : ⇑(Algebra.ofId ℚ
      (Representation.IntertwiningMap (spechtModule mu).ρ (spechtModule mu).ρ)) =
      ⇑(algebraMap ℚ
        (Representation.IntertwiningMap (spechtModule mu).ρ (spechtModule mu).ρ)) := by
    funext q
    exact Algebra.ofId_apply
      (Representation.IntertwiningMap (spechtModule mu).ρ (spechtModule mu).ρ) q
  rw [hfun]
  exact algebraMap_intertwiningMap_spechtModule_bijective mu

noncomputable def spechtModuleIntertwiningEndAlgEquiv {n : ℕ} (mu : n.Partition) :
    Representation.IntertwiningMap (spechtModule mu).ρ (spechtModule mu).ρ ≃ₐ[ℚ] ℚ :=
  (spechtModuleScalarAlgEquiv mu).symm

end TauCeti

end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
