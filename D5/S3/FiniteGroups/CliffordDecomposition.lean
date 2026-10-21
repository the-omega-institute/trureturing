/- GID: D5/S3/FiniteGroups/CliffordDecomposition
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/CliffordDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite character theory: CliffordDecomposition. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19389

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. The complete license and immutable sources are in Library/FiniteGroups/tauceti2026finitecharacters.md.
Authors: The Tau Ceti contributors

This port uses repository namespaces and the pinned Mathlib API.

Replace these ports by direct imports when the repository’s pinned Mathlib supplies
equivalent declarations with the same hypotheses and conclusions.

admission_basis: escape-witness
Direct frozen dependencies: none.
Module escape_witness: FDRep.clifford_restrict_iso
The isotypic components are identified with the conjugation orbit and assembled into the restriction isomorphism.
Representation.fdRepIsoConjSubrep | proof_shape: bind-only | escape_witness: none | consumer: Representation.toSkeleton_fdRepOf_conjSubrep, TauCeti.componentLinearEquiv
Representation.toSkeleton_fdRepOf_conjSubrep | proof_shape: bind-only | escape_witness: none | consumer: Representation.componentClassMap_conjSubrepIsotypicComponent, Representation.submoduleClassToSkeleton_mem_orbit
Representation.submoduleClassToSkeleton | proof_shape: bind-only | escape_witness: none | consumer: Representation.componentClassMap, Representation.componentClassMap_conjSubrepIsotypicComponent, Representation.submoduleClassToSkeleton_injective, Representation.submoduleClassToSkeleton_mem_orbit, Representation.submoduleClassToSkeleton_mk
Representation.submoduleClassToSkeleton_mk | proof_shape: bind-only | escape_witness: none | consumer: Representation.componentClassMap_conjSubrepIsotypicComponent, Representation.submoduleClassToSkeleton_injective, Representation.submoduleClassToSkeleton_mem_orbit
Representation.submoduleClassToSkeleton_injective | proof_shape: bind-only | escape_witness: none | consumer: Representation.componentClassMap_injective
Representation.componentClassMap | proof_shape: bind-only | escape_witness: none | consumer: Representation.componentClassMap_conjSubrepIsotypicComponent, Representation.componentClassMap_injective, Representation.componentOrbitMap, Representation.componentOrbitMap_surjective
Representation.componentClassMap_injective | proof_shape: bind-only | escape_witness: none | consumer: Representation.componentOrbitMap_injective
Representation.componentClassMap_conjSubrepIsotypicComponent | proof_shape: bind-only | escape_witness: none | consumer: Representation.componentOrbitMap_surjective, Representation.isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent
Representation.submoduleClassToSkeleton_mem_orbit | proof_shape: bind-only | escape_witness: none | consumer: Representation.componentClassMap_mem_orbit
Representation.componentClassMap_mem_orbit | proof_shape: bind-only | escape_witness: none | consumer: Representation.componentOrbitMap
Representation.componentOrbitMap | proof_shape: bind-only | escape_witness: none | consumer: Representation.componentOrbitMap_injective, Representation.componentOrbitMap_surjective, Representation.componentsEquivOrbit, Representation.isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent
Representation.componentOrbitMap_injective | proof_shape: bind-only | escape_witness: none | consumer: Representation.componentsEquivOrbit
Representation.componentOrbitMap_surjective | proof_shape: bind-only | escape_witness: none | consumer: Representation.componentsEquivOrbit
Representation.componentsEquivOrbit | proof_shape: bind-only | escape_witness: none | consumer: Representation.componentsEquivOrbit_apply, Representation.isotypicComponentsEquivQuotientInertia, Representation.isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent
Representation.componentsEquivOrbit_apply | proof_shape: bind-only | escape_witness: none | consumer: Representation.isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent
Representation.isotypicComponentsEquivQuotientInertia | proof_shape: bind-only | escape_witness: none | consumer: Representation.isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent, Representation.isotypicComponentsEquivQuotientInertia_symm_mk, TauCeti.componentLinearEquiv, TauCeti.finite_quotient_inertia, TauCeti.restrictLinearEquivPi
Representation.isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent | proof_shape: bind-only | escape_witness: none | consumer: Representation.isotypicComponentsEquivQuotientInertia_symm_mk
Representation.isotypicComponentsEquivQuotientInertia_symm_mk | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.componentLinearEquiv
TauCeti.isUnit_natCard_subgroup | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.frobenius_reciprocity_classFunction, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_ind_ind_mackey, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.natCast_finrank_hom_indFDRep_mackey_erase
LinearMap.trace_pi_of_apply_eq | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.trace_ind_eq_sum_rightCosets
LinearMap.trace_pi_of_apply_eq_dependent | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.char_ofModule'_pi
TauCeti.Representation.ofModule'_apply | proof_shape: bind-only | escape_witness: none | consumer: Representation.char_ofModule'_asModule
TauCeti.Representation.asAlgebraHom_ofModule' | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.asAlgebraHom_ofModule'_apply
TauCeti.Representation.asAlgebraHom_ofModule'_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.ofModule'AsModuleEquiv
TauCeti.Representation.ofModule'AsModuleEquiv | proof_shape: bind-only | escape_witness: none | consumer: FDRep.clifford_restrict_iso_of_isAtom
TauCeti.Representation.char_ofModule'_pi | proof_shape: bind-only | escape_witness: none | consumer: FDRep.character_cliffordSum
Representation.char_ofModule'_asModule | proof_shape: bind-only | escape_witness: none | consumer: FDRep.character_cliffordSum
TauCeti.IsSemisimpleModule.linearEquivIsotypicComponents | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.restrictLinearEquivPi
FDRep.cliffordSum | proof_shape: bind-only | escape_witness: none | consumer: FDRep.character_cliffordSum, FDRep.clifford_restrict_iso, FDRep.clifford_restrict_iso_of_isAtom, FDRep.finrank_cliffordSum, D5.S3.FiniteGroups.FrobeniusCharacterDegrees.degree_dvd_or_index_dvd_of_fixedPointFree, D5.S3.FiniteGroups.FrobeniusCharacterDegrees.restriction_trivial_of_clifford_constituent_trivial, D5.S3.FiniteGroups.InducedCharacterFormula.FDRep.clifford_restrict_finrank
FDRep.finrank_cliffordSum | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.InducedCharacterFormula.FDRep.clifford_restrict_finrank
FDRep.character_cliffordSum | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.FrobeniusCharacterDegrees.restriction_trivial_of_clifford_constituent_trivial
TauCeti.componentLinearEquiv | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.restrictLinearEquivPi
TauCeti.finite_quotient_inertia | proof_shape: bind-only | escape_witness: none | consumer: FDRep.clifford_restrict_iso_of_isAtom
TauCeti.restrictLinearEquivPi | proof_shape: bind-only | escape_witness: none | consumer: FDRep.clifford_restrict_iso_of_isAtom
FDRep.clifford_restrict_iso_of_isAtom | proof_shape: content | escape_witness: D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep | consumer: FDRep.clifford_restrict_iso
FDRep.clifford_restrict_iso | proof_shape: content | escape_witness: FDRep.clifford_restrict_iso | consumer: D5.S3.FiniteGroups.InducedCharacterFormula.FDRep.clifford_restrict_finrank
-/

import D5.S3.FiniteGroups.CliffordConstituents
import D5.S3.FiniteGroups.FiniteCharacterAlgebra
namespace D5.S3.FiniteGroups.CliffordDecomposition
namespace FDRep
end FDRep
namespace LinearMap
end LinearMap
namespace Representation
end Representation
namespace TauCeti
end TauCeti
namespace TauCeti.IsSemisimpleModule
end TauCeti.IsSemisimpleModule
namespace TauCeti.Representation
end TauCeti.Representation
section UpstreamSource5_0
open CategoryTheory
open scoped _root_.MonoidAlgebra
universe u v
namespace Representation
open _root_.Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation _root_.D5.S3.FiniteGroups.CliffordConstituents.Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.Representation
section OrbitIndex
variable {k : Type u} {G : Type v} [Field k] [Group G]
  {V : Type u} [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)
private noncomputable def fdRepIsoConjSubrep [FiniteDimensional k V]
    (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    FDRep.of (conjSubrep ρ g σ).toRepresentation ≅
      (conjNormalFDRepFunctor g).obj (FDRep.of σ.toRepresentation) :=
  fdRepIsoOfAsModuleLinearEquiv
    (_root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.asModuleLinearEquivOfEquiv (conjSubrepEquiv ρ g σ).symm)
private theorem toSkeleton_fdRepOf_conjSubrep [FiniteDimensional k V]
    (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    toSkeleton (FDRep.of (conjSubrep ρ g σ).toRepresentation) =
      g • toSkeleton (FDRep.of σ.toRepresentation) := by
  rw [smul_toSkeleton]
  exact toSkeleton_eq_toSkeleton_iff.mpr ⟨fdRepIsoConjSubrep ρ g σ⟩
variable [FiniteDimensional k V]
private noncomputable def submoduleClassToSkeleton :
    SimpleSubmoduleClasses k[N]
        (_root_.Representation.asModule (ρ.comp N.subtype)) →
      Skeleton (FDRep k N) :=
  SimpleSubmoduleClasses.lift
    (fun T _ ↦ toSkeleton (FDRep.of
      (Subrepresentation.subrepresentationSubmoduleOrderIso.symm T).toRepresentation))
    (by
      intro T U _ _ e
      apply (toSkeleton_fdRepOf_toRepresentation_eq_iff _ _).mpr
      obtain ⟨e⟩ := e
      exact ⟨(LinearEquiv.ofEq _ _
          (OrderIso.apply_symm_apply
            Subrepresentation.subrepresentationSubmoduleOrderIso T)).trans e
        |>.trans
        (LinearEquiv.ofEq _ _
          (OrderIso.apply_symm_apply
            Subrepresentation.subrepresentationSubmoduleOrderIso U).symm)⟩)
omit [N.Normal] in
@[simp]
private theorem submoduleClassToSkeleton_mk
    (T : Submodule k[N] (_root_.Representation.asModule (ρ.comp N.subtype)))
    [IsSimpleModule k[N] T] :
    submoduleClassToSkeleton ρ (.mk T) =
      toSkeleton (FDRep.of
        (Subrepresentation.subrepresentationSubmoduleOrderIso.symm T).toRepresentation) :=
  by
    rw [submoduleClassToSkeleton, SimpleSubmoduleClasses.lift_mk]
omit [N.Normal] in
private theorem submoduleClassToSkeleton_injective :
    Function.Injective (submoduleClassToSkeleton (N := N) ρ) := by
  intro C
  induction C using SimpleSubmoduleClasses.ind with
  | mk T hT =>
    intro D
    induction D using SimpleSubmoduleClasses.ind with
    | mk U hU =>
      intro h
      rw [SimpleSubmoduleClasses.mk_eq_mk_iff]
      have h' :
          toSkeleton (FDRep.of
              (Subrepresentation.subrepresentationSubmoduleOrderIso.symm T).toRepresentation) =
            toSkeleton (FDRep.of
              (Subrepresentation.subrepresentationSubmoduleOrderIso.symm U).toRepresentation) := by
        simpa only [submoduleClassToSkeleton_mk] using h
      obtain ⟨e⟩ := (toSkeleton_fdRepOf_toRepresentation_eq_iff _ _).mp h'
      exact ⟨(LinearEquiv.ofEq _ _
          (OrderIso.apply_symm_apply
            Subrepresentation.subrepresentationSubmoduleOrderIso T).symm).trans e
        |>.trans (LinearEquiv.ofEq _ _
          (OrderIso.apply_symm_apply
            Subrepresentation.subrepresentationSubmoduleOrderIso U))⟩
private noncomputable def componentClassMap
    (c : isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) :
    Skeleton (FDRep k N) :=
  submoduleClassToSkeleton ρ
    ((simpleSubmoduleClassesEquiv k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))).symm c)
omit [N.Normal] in
private theorem componentClassMap_injective :
    Function.Injective (componentClassMap (N := N) ρ) := by
  intro c d h
  apply (simpleSubmoduleClassesEquiv k[N]
    (_root_.Representation.asModule (ρ.comp N.subtype))).symm.injective
  exact submoduleClassToSkeleton_injective ρ h
private theorem componentClassMap_conjSubrepIsotypicComponent [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    componentClassMap ρ (conjSubrepIsotypicComponent ρ σ hσ g) =
      g • toSkeleton (FDRep.of σ.toRepresentation) := by
  let _ : IsSimpleModule k[N] (conjSubrep ρ g σ).asSubmodule :=
    _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.isSimpleModule_asSubmodule_iff.mpr (isAtom_conjSubrep_iff.mpr hσ)
  let ec := simpleSubmoduleClassesEquiv k[N]
    (_root_.Representation.asModule (ρ.comp N.subtype))
  have hclass :
      ec.symm (conjSubrepIsotypicComponent ρ σ hσ g) =
        SimpleSubmoduleClasses.mk (conjSubrep ρ g σ).asSubmodule :=
    (ec.symm_apply_eq).mpr rfl
  rw [componentClassMap, hclass, submoduleClassToSkeleton_mk]
  calc
    _ = toSkeleton (FDRep.of (conjSubrep ρ g σ).toRepresentation) :=
      (toSkeleton_fdRepOf_toRepresentation_eq_iff _ _).mpr <| by
        exact ⟨LinearEquiv.ofEq _ _
          (OrderIso.apply_symm_apply
            Subrepresentation.subrepresentationSubmoduleOrderIso _)⟩
    _ = _ := toSkeleton_fdRepOf_conjSubrep ρ g σ
private theorem submoduleClassToSkeleton_mem_orbit [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ)
    (C : SimpleSubmoduleClasses k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) :
    submoduleClassToSkeleton ρ C ∈
      MulAction.orbit G (toSkeleton (FDRep.of σ.toRepresentation)) := by
  induction C using SimpleSubmoduleClasses.ind with
  | mk T hT =>
    obtain ⟨g, ⟨e⟩⟩ := exists_nonempty_linearEquiv_asSubmodule_conjSubrep ρ hσ T
    rw [MulAction.mem_orbit_iff]
    refine ⟨g, ?_⟩
    exact (toSkeleton_fdRepOf_conjSubrep ρ g σ).symm.trans <| by
      rw [submoduleClassToSkeleton_mk]
      apply (toSkeleton_fdRepOf_toRepresentation_eq_iff _ _).mpr
      exact ⟨e.symm.trans (LinearEquiv.ofEq _ _
        (OrderIso.apply_symm_apply
          Subrepresentation.subrepresentationSubmoduleOrderIso _).symm)⟩
private theorem componentClassMap_mem_orbit [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ)
    (c : isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) :
    componentClassMap ρ c ∈
      MulAction.orbit G (toSkeleton (FDRep.of σ.toRepresentation)) :=
  submoduleClassToSkeleton_mem_orbit ρ hσ _
private noncomputable def componentOrbitMap [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) →
      MulAction.orbit G (toSkeleton (FDRep.of σ.toRepresentation)) :=
  fun c ↦ ⟨componentClassMap ρ c, componentClassMap_mem_orbit ρ hσ c⟩
private theorem componentOrbitMap_injective [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    Function.Injective (componentOrbitMap ρ hσ) := by
  intro c d h
  apply componentClassMap_injective ρ
  exact congrArg Subtype.val h
private theorem componentOrbitMap_surjective [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    Function.Surjective (componentOrbitMap ρ hσ) := by
  rintro ⟨x, hx⟩
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hx
  refine ⟨conjSubrepIsotypicComponent ρ σ hσ g, Subtype.ext ?_⟩
  exact (componentClassMap_conjSubrepIsotypicComponent ρ σ hσ g).trans hg
private noncomputable def componentsEquivOrbit [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) ≃
      MulAction.orbit G (toSkeleton (FDRep.of σ.toRepresentation)) :=
  Equiv.ofBijective (componentOrbitMap ρ hσ)
    ⟨componentOrbitMap_injective ρ hσ, componentOrbitMap_surjective ρ hσ⟩
@[simp]
private theorem componentsEquivOrbit_apply [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ)
    (c : isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) :
    componentsEquivOrbit ρ hσ c = componentOrbitMap ρ hσ c := by
  rfl
private noncomputable def isotypicComponentsEquivQuotientInertia [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) :
    isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) ≃
      G ⧸ (MulAction.stabilizer G (toSkeleton (FDRep.of σ.toRepresentation))) :=
  (componentsEquivOrbit ρ hσ).trans
    (MulAction.orbitEquivQuotientStabilizer G
      (toSkeleton (FDRep.of σ.toRepresentation)))
@[simp]
private theorem isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent
    [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    isotypicComponentsEquivQuotientInertia ρ σ hσ
        (conjSubrepIsotypicComponent ρ σ hσ g) =
      QuotientGroup.mk g := by
  let eo := MulAction.orbitEquivQuotientStabilizer G
    (toSkeleton (FDRep.of σ.toRepresentation))
  simp only [isotypicComponentsEquivQuotientInertia]
  have horbit :
      componentsEquivOrbit ρ hσ (conjSubrepIsotypicComponent ρ σ hσ g) =
        (MulAction.orbitEquivQuotientStabilizer G
          (toSkeleton (FDRep.of σ.toRepresentation))).symm (QuotientGroup.mk g) := by
    apply Subtype.ext
    rw [componentsEquivOrbit_apply]
    simpa only [componentOrbitMap,
      MulAction.orbitEquivQuotientStabilizer_symm_apply] using
      componentClassMap_conjSubrepIsotypicComponent ρ σ hσ g
  exact (congrArg eo horbit).trans (eo.apply_symm_apply (QuotientGroup.mk g))
@[simp]
private theorem isotypicComponentsEquivQuotientInertia_symm_mk [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    (isotypicComponentsEquivQuotientInertia ρ σ hσ).symm (QuotientGroup.mk g) =
      conjSubrepIsotypicComponent ρ σ hσ g := by
  rw [Equiv.symm_apply_eq]
  exact (isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent ρ σ hσ g).symm
end OrbitIndex
end Representation
end UpstreamSource5_0
section UpstreamSource5_2
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti
theorem isUnit_natCard_subgroup {k : Type*} {G : Type*} [Semiring k] [Group G]
    (S : Subgroup G) (hG : IsUnit (Nat.card G : k)) : IsUnit (Nat.card S : k) := by
  have h : IsUnit ((Nat.card S : k) * (S.index : k)) := by
    rwa [← Nat.cast_mul, S.card_mul_index]
  exact ((Nat.cast_commute _ _).isUnit_mul_iff.mp h).1
end TauCeti
end UpstreamSource5_2
section UpstreamSource5_5
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti
universe u v w
variable {k : Type u} {ι : Type v} {M : Type w}
  [CommRing k] [Fintype ι]
  [AddCommGroup M] [Module k M] [Module.Free k M] [Module.Finite k M]
open scoped Classical in
theorem _root_.D5.S3.FiniteGroups.CliffordDecomposition.LinearMap.trace_pi_of_apply_eq (T : (ι → M) →ₗ[k] (ι → M)) (σ : ι → ι)
    (f : ι → M →ₗ[k] M) (hT : ∀ x i, T x i = f i (x (σ i))) :
    LinearMap.trace k (ι → M) T =
      ∑ i : ι, if σ i = i then LinearMap.trace k M (f i) else 0 := by
  let b := Module.Free.chooseBasis k M
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex k M)
  let B := Pi.basis fun _ : ι => b
  rw [LinearMap.trace_eq_matrix_trace k B, Matrix.trace]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : σ i = i
  · simp only [hi, ↓reduceIte]
    rw [LinearMap.trace_eq_matrix_trace k b, Matrix.trace]
    apply Finset.sum_congr rfl
    intro j _
    simp [LinearMap.toMatrix_apply, B, b, hT, hi]
  · simp only [hi, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro j _
    simp [LinearMap.toMatrix_apply, B, b, hT, hi]
open scoped Classical in
private theorem _root_.D5.S3.FiniteGroups.CliffordDecomposition.LinearMap.trace_pi_of_apply_eq_dependent {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)] [∀ i, Module.Free k (M i)]
    [∀ i, Module.Finite k (M i)]
    (T : ((i : ι) → M i) →ₗ[k] ((i : ι) → M i)) (f : ∀ i, M i →ₗ[k] M i)
    (hT : ∀ x i, T x i = f i (x i)) :
    LinearMap.trace k ((i : ι) → M i) T = ∑ i, LinearMap.trace k (M i) (f i) := by
  let b (i : ι) := Module.Free.chooseBasis k (M i)
  let _ (i : ι) : Fintype (Module.Free.ChooseBasisIndex k (M i)) := Fintype.ofFinite _
  let B : Module.Basis (Σ i, Module.Free.ChooseBasisIndex k (M i)) k ((i : ι) → M i) :=
    Pi.basis b
  rw [LinearMap.trace_eq_matrix_trace k B, Matrix.trace, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.trace_eq_matrix_trace k (b i), Matrix.trace]
  apply Finset.sum_congr rfl
  intro j _
  simp [LinearMap.toMatrix_apply, B, b, hT]
end TauCeti
end UpstreamSource5_5
section UpstreamSource5_6
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti
namespace Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation
open scoped _root_.MonoidAlgebra
section Semiring
variable {k G : Type*} [CommSemiring k] [Monoid G]
variable (M : Type*) [AddCommMonoid M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
@[simp]
private theorem ofModule'_apply (g : G) (x : M) :
    _root_.Representation.ofModule' (k := k) (G := G) M g x = MonoidAlgebra.single g (1 : k) • x :=
  rfl
private theorem asAlgebraHom_ofModule' :
    (_root_.Representation.ofModule' (k := k) (G := G) M).asAlgebraHom = Algebra.lsmul k k M := by
  rw [_root_.Representation.asAlgebraHom_def, _root_.Representation.ofModule']
  exact (MonoidAlgebra.lift k (Module.End k M) G).apply_symm_apply _
@[simp]
private theorem asAlgebraHom_ofModule'_apply (r : k[G]) (x : M) :
    (_root_.Representation.ofModule' (k := k) (G := G) M).asAlgebraHom r x = r • x := by
  rw [asAlgebraHom_ofModule']
  rfl
private noncomputable def ofModule'AsModuleEquiv :
    (_root_.Representation.ofModule' (k := k) (G := G) M).asModule ≃ₗ[k[G]] M :=
  (_root_.Representation.ofModule' (k := k) (G := G) M).asModuleEquiv.toAddEquiv.toLinearEquiv
    (fun r x => by
      change (_root_.Representation.ofModule' (k := k) (G := G) M).asModuleEquiv (r • x) =
        r • (_root_.Representation.ofModule' (k := k) (G := G) M).asModuleEquiv x
      rw [_root_.Representation.asModuleEquiv_map_smul, asAlgebraHom_ofModule'_apply])
end Semiring
section Character
variable {k G : Type*} [Field k] [Monoid G]
@[simp]
private theorem char_ofModule'_pi {ι : Type*} [Fintype ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module k (M i)] [∀ i, Module k[G] (M i)] [∀ i, IsScalarTower k k[G] (M i)]
    [∀ i, FiniteDimensional k (M i)] (g : G) :
    (_root_.Representation.ofModule' (k := k) (G := G) ((i : ι) → M i)).character g =
      ∑ i, (_root_.Representation.ofModule' (k := k) (G := G) (M i)).character g :=
  _root_.D5.S3.FiniteGroups.CliffordDecomposition.LinearMap.trace_pi_of_apply_eq_dependent _ _ fun _ _ => rfl
@[simp]
private theorem _root_.D5.S3.FiniteGroups.CliffordDecomposition.Representation.char_ofModule'_asModule {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : _root_.Representation k G V) (g : G) :
    (_root_.Representation.ofModule' (k := k) (G := G) ρ.asModule).character g = ρ.character g := by
  have h : _root_.Representation.ofModule' (k := k) (G := G) ρ.asModule g =
      ρ.asModuleEquiv.symm.conj (ρ g) := by
    ext x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
      _root_.Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply,
      ofModule'_apply, MonoidAlgebra.of_apply]
  rw [_root_.Representation.character, h, LinearMap.trace_conj', _root_.Representation.character]
end Character
end Representation
end TauCeti
end UpstreamSource5_6
section UpstreamSource5_7
namespace TauCeti.IsSemisimpleModule
variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
  [DecidableEq (isotypicComponents R M)]
private noncomputable def linearEquivIsotypicComponents : M ≃ₗ[R] Π₀ c : isotypicComponents R M, c.1 :=
  .symm <| ((sSupIndep_iff _).mp <| sSupIndep_isotypicComponents R M).linearEquiv <|
    (sSup_eq_iSup' _).symm.trans <| sSup_isotypicComponents R M
variable {R M}
end TauCeti.IsSemisimpleModule
end UpstreamSource5_7
section UpstreamSource5_8
open CategoryTheory
open scoped _root_.MonoidAlgebra
universe u v
namespace FDRep
open _root_.FDRep
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti
noncomputable def cliffordSum {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] (V : FDRep k N) [Finite (G ⧸ (MulAction.stabilizer G (toSkeleton V)))]
    (e : ℕ) : FDRep k N :=
  _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.ofShrink <| Representation.ofModule' (k := k) (G := N)
    ((q : G ⧸ (MulAction.stabilizer G (toSkeleton V))) → Fin e →
      _root_.Representation.asModule ((conjNormalFDRepFunctor (Quotient.out q)).obj V).ρ)
@[simp]
theorem finrank_cliffordSum {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] (V : FDRep k N) [Finite (G ⧸ (MulAction.stabilizer G (toSkeleton V)))] (e : ℕ) :
    Module.finrank k ((_root_.D5.S3.FiniteGroups.CliffordDecomposition.FDRep.cliffordSum V) e) =
      Nat.card (G ⧸ (MulAction.stabilizer G (toSkeleton V))) * e * Module.finrank k V := by
  classical
  let _ : Fintype (G ⧸ (MulAction.stabilizer G (toSkeleton V))) := Fintype.ofFinite _
  rw [cliffordSum, finrank_ofShrink, Module.finrank_pi_fintype]
  simp_rw [Module.finrank_pi_fintype,
    (_root_.Representation.asModuleEquiv _).finrank_eq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (∑ _q : G ⧸ (MulAction.stabilizer G (toSkeleton V)), e * Module.finrank k V) = _
  simp [Nat.card_eq_fintype_card, mul_assoc]
@[simp]
theorem character_cliffordSum {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] (V : FDRep k N) [Finite (G ⧸ (MulAction.stabilizer G (toSkeleton V)))]
    (e : ℕ) (x : N) :
    ((_root_.D5.S3.FiniteGroups.CliffordDecomposition.FDRep.cliffordSum V) e).character x =
      (e : k) * ∑ᶠ q : G ⧸ (MulAction.stabilizer G (toSkeleton V)),
        ((conjNormalFDRepFunctor (Quotient.out q)).obj V).character x := by
  let _ : Fintype (G ⧸ (MulAction.stabilizer G (toSkeleton V))) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, cliffordSum, character_ofShrink, Finset.mul_sum]
  simp only [Representation.char_ofModule'_pi, _root_.D5.S3.FiniteGroups.CliffordDecomposition.Representation.char_ofModule'_asModule,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [FDRep.character, _root_.Representation.character]
end FDRep
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti
private noncomputable def componentLinearEquiv
    {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G]
    {X : Type u} [AddCommGroup X] [Module k X] {N : Subgroup G} [N.Normal]
    (ρ : Representation k G X) [FiniteDimensional k X] [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (e : ℕ)
    (hcommon : ∀ τ : Subrepresentation (ρ.comp N.subtype), IsAtom τ →
      Module.finrank k
        (τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) = e)
    (q : G ⧸ (MulAction.stabilizer G (toSkeleton (FDRep.of σ.toRepresentation)))) :
    (((_root_.D5.S3.FiniteGroups.CliffordDecomposition.Representation.isotypicComponentsEquivQuotientInertia ρ) σ hσ).symm q).1 ≃ₗ[k[N]]
      Fin e → _root_.Representation.asModule
        ((conjNormalFDRepFunctor (Quotient.out q)).obj (FDRep.of σ.toRepresentation)).ρ := by
  let g : G := Quotient.out q
  have hq : QuotientGroup.mk g = q := Quotient.out_eq' q
  have hc : ((_root_.D5.S3.FiniteGroups.CliffordDecomposition.Representation.isotypicComponentsEquivQuotientInertia ρ) σ hσ).symm q =
      (_root_.D5.S3.FiniteGroups.CliffordConstituents.Representation.conjSubrepIsotypicComponent ρ) σ hσ g := by
    rw [← hq]
    exact (_root_.D5.S3.FiniteGroups.CliffordDecomposition.Representation.isotypicComponentsEquivQuotientInertia_symm_mk ρ) σ hσ g
  let τ := Representation.conjSubrep ρ g σ
  have hτ : IsAtom τ := Representation.isAtom_conjSubrep_iff.mpr hσ
  let _ : IsSimpleModule k[N] τ.asSubmodule :=
    _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.isSimpleModule_asSubmodule_iff.mpr hτ
  let _ : FiniteDimensional k τ.asSubmodule :=
    Module.Finite.of_injective (τ.asSubmodule.subtype.restrictScalars k) Subtype.val_injective
  let eComponent := (nonempty_linearEquiv_isotypicComponent
    (k := k) (A := k[N])
    (M := _root_.Representation.asModule (ρ.comp N.subtype)) (S := τ.asSubmodule)).some
  have hmultiplicity : Module.finrank k
      (τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) = e :=
    hcommon τ hτ
  rw [hmultiplicity] at eComponent
  let i := _root_.D5.S3.FiniteGroups.CliffordDecomposition.Representation.fdRepIsoConjSubrep ρ g σ
  let iRep := (nonempty_fdRepIso_iff.mp ⟨i⟩).some
  let eConj : τ.asSubmodule ≃ₗ[k[N]] _root_.Representation.asModule
      ((conjNormalFDRepFunctor g).obj (FDRep.of σ.toRepresentation)).ρ :=
    (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.asModuleEquivAsSubmodule τ).symm.trans
      (Representation.asModuleLinearEquivOfEquiv iRep)
  rw [hc, _root_.D5.S3.FiniteGroups.CliffordConstituents.Representation.coe_conjSubrepIsotypicComponent]
  simpa only [τ, g] using
    eComponent.trans (LinearEquiv.piCongrRight fun _ ↦ eConj)
private theorem finite_quotient_inertia {k : Type u} {G : Type v} [Field k] [Group G] {X : Type u}
    [AddCommGroup X] [Module k X] {N : Subgroup G} [N.Normal] (ρ : Representation k G X)
    [FiniteDimensional k X] [ρ.IsIrreducible] (σ : Subrepresentation (ρ.comp N.subtype))
    (hσ : IsAtom σ) : Finite (G ⧸ (MulAction.stabilizer G (toSkeleton (FDRep.of σ.toRepresentation)))) :=
  have : IsNoetherian k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) :=
    isNoetherian_of_tower k inferInstance
  .of_equiv _ ((_root_.D5.S3.FiniteGroups.CliffordDecomposition.Representation.isotypicComponentsEquivQuotientInertia ρ) σ hσ)
private noncomputable def restrictLinearEquivPi {k : Type u} {G : Type v} [Field k] [IsAlgClosed k]
    [Group G] {X : Type u} [AddCommGroup X] [Module k X] {N : Subgroup G} [N.Normal]
    (ρ : Representation k G X) [FiniteDimensional k X] [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (e : ℕ)
    (hcommon : ∀ τ : Subrepresentation (ρ.comp N.subtype), IsAtom τ → Module.finrank k
      (τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) = e) :
    _root_.Representation.asModule (ρ.comp N.subtype) ≃ₗ[k[N]]
      ((q : G ⧸ (MulAction.stabilizer G (toSkeleton (FDRep.of σ.toRepresentation)))) → Fin e → _root_.Representation.asModule
        ((conjNormalFDRepFunctor (Quotient.out q)).obj (FDRep.of σ.toRepresentation)).ρ) :=
  let M := _root_.Representation.asModule (ρ.comp N.subtype)
  have : IsSemisimpleModule k[N] M :=
    (_root_.Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp
      (Representation.isSemisimpleRepresentation_comp_subtype ρ)
  have : IsNoetherian k[N] M := isNoetherian_of_tower k inferInstance
  let _ : Fintype (isotypicComponents k[N] M) := Fintype.ofFinite _
  IsSemisimpleModule.linearEquivIsotypicComponents k[N] M ≪≫ₗ DFinsupp.linearEquivFunOnFintype ≪≫ₗ
    .piCongrLeft' k[N] (fun c ↦ c.1) ((_root_.D5.S3.FiniteGroups.CliffordDecomposition.Representation.isotypicComponentsEquivQuotientInertia ρ) σ hσ) ≪≫ₗ
    .piCongrRight (componentLinearEquiv ρ σ hσ e hcommon)
end TauCeti
namespace FDRep
open _root_.FDRep
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti
private theorem clifford_restrict_iso_of_isAtom {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] [IsAlgClosed k]
    (W : FDRep k G) [Simple W] (σ : Subrepresentation (W.ρ.comp N.subtype))
    (hσ : IsAtom σ) :
    ∃ hfinite : Finite (G ⧸ (MulAction.stabilizer G (toSkeleton (FDRep.of σ.toRepresentation)))),
      let _ := hfinite
      ∃ e : ℕ, e ≠ 0 ∧
        Nonempty (((Action.res (FGModuleCat k) (N).subtype).obj W) ≅ cliffordSum (FDRep.of σ.toRepresentation) e) := by
  have : Representation.IsIrreducible W.ρ := _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple W
  obtain ⟨e, he, hcommon⟩ := _root_.D5.S3.FiniteGroups.CliffordConstituents.Representation.exists_forall_finrank_linearMap_eq (N := N) W.ρ
  have hfinite := finite_quotient_inertia W.ρ σ hσ
  refine ⟨hfinite, e, he.ne', nonempty_fdRepIso_iff.mpr ⟨?_⟩⟩
  have hres : FDRep.ρ ((Action.res (FGModuleCat k) N.subtype).obj W) = W.ρ.comp N.subtype := rfl
  rw [hres, cliffordSum]
  exact (Representation.equivOfAsModuleLinearEquiv (restrictLinearEquivPi W.ρ σ hσ e hcommon ≪≫ₗ
    (Representation.ofModule'AsModuleEquiv _).symm)).trans (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.ofShrinkEquiv _).symm
theorem clifford_restrict_iso {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] [IsAlgClosed k]
    (W : FDRep k G) [Simple W] :
    ∃ (V : FDRep k N) (_ : Simple V) (hfinite : Finite (G ⧸ (MulAction.stabilizer G (toSkeleton V)))),
      let _ := hfinite
      ∃ e : ℕ, e ≠ 0 ∧ Nonempty (((Action.res (FGModuleCat k) (N).subtype).obj W) ≅ (_root_.D5.S3.FiniteGroups.CliffordDecomposition.FDRep.cliffordSum V) e) := by
  classical
  let _ : Representation.IsIrreducible W.ρ := _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple W
  obtain ⟨σ, hσ, -⟩ :=
    Representation.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep (N := N) W.ρ
  let V : FDRep k N := FDRep.of σ.toRepresentation
  let _ : Representation.IsIrreducible V.ρ :=
    Representation.isIrreducible_toRepresentation_of_isAtom hσ
  let _ : Simple V := _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.simple_of_isIrreducible V
  obtain ⟨hfinite, e, he, h⟩ := (_root_.D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso_of_isAtom W) σ hσ
  exact ⟨V, inferInstance, hfinite, e, he, h⟩
end FDRep
end UpstreamSource5_8
end D5.S3.FiniteGroups.CliffordDecomposition
