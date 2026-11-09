/- GID: D5/S3/FiniteGroups/GroupAlgebra/FiniteIndexProjectivity
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/FiniteIndexProjectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Coinduced, mathlib/module/Mathlib.RepresentationTheory.Rep.Iso, mathlib/module/Mathlib.GroupTheory.Index]
   utility: none
   digest: Projectivity is detected on a finite-index subgroup whose index is a unit. -/

import Mathlib.Algebra.Module.ULift
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Tactic

/-!
The coefficient ring, group and module have independent universes. Only the coset space is
finite. The integral relative trace is a generalization of
the finite-group, field-valued construction in OriginalDProjective.coset_trace; that frozen
source is not changed or imported. Restriction preservation is reused from Mathlib.
No literature novelty or computational utility is claimed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.FiniteIndexProjectivity

open CategoryTheory
open scoped BigOperators MonoidAlgebra

universe uR uG uV uW uP uw

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]

/- This normalization helper uses the existing intertwiner/group-algebra equivalence.
   Its only consumer is projective_restrict. -/
private def moduleCongr
    {W : Type uW} [AddCommGroup W] [Module R W]
    (rho : Representation R G V) (sigma : Representation R G W)
    (e : V ≃ₗ[R] W)
    (he : ∀ g, e.toLinearMap.comp (rho g) = (sigma g).comp e.toLinearMap) :
    rho.asModule ≃ₗ[R[G]] sigma.asModule := by
  let f : rho.asModule →ₗ[R[G]] sigma.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule rho sigma
      { toLinearMap := e.toLinearMap, isIntertwining' := he }
  exact
    { f with
      invFun := fun w => rho.asModuleEquiv.symm (e.symm (sigma.asModuleEquiv w))
      left_inv := fun v => by
        apply rho.asModuleEquiv.injective
        exact e.symm_apply_apply (rho.asModuleEquiv v)
      right_inv := fun w => by
        apply sigma.asModuleEquiv.injective
        exact e.apply_symm_apply (sigma.asModuleEquiv w) }

private def liftRepresentation (rho : Representation R G V) :
    Representation R G (ULift.{uw} V) where
  toFun g := ULift.moduleEquiv.symm.toLinearMap.comp
    ((rho g).comp ULift.moduleEquiv.toLinearMap)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [LinearMap.comp_apply]

/- No finite-index or unit hypothesis is needed in this direction. The universe lift permits
   the existing res/coind adjunction and supplies Small for the module/category conversion. -/
private theorem projective_restrict (rho : Representation R G V) (H : Subgroup G)
    (hproj : Module.Projective R[G] rho.asModule) :
    Module.Projective R[H] (Representation.asModule (rho.comp H.subtype)) := by
  letI : Module.Projective R[G] rho.asModule := hproj
  let rho' : Representation R G (ULift.{max uG (max uR uV)} V) :=
    liftRepresentation rho
  let eUp : V ≃ₗ[R] ULift.{max uG (max uR uV)} V := ULift.moduleEquiv.symm
  let eG : rho.asModule ≃ₗ[R[G]] rho'.asModule :=
    moduleCongr rho rho' eUp (by intro g; ext v; rfl)
  letI : Module.Projective R[G] rho'.asModule := Module.Projective.of_equiv' eG
  let A : Rep.{max uG (max uR uV)} R G := Rep.of rho'
  let E := Rep.equivalenceModuleMonoidAlgebra (k := R) (G := G)
  have hmod : CategoryTheory.Projective (ModuleCat.of R[G] rho'.asModule) :=
    ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of R[G] rho'.asModule)
  have hinv : CategoryTheory.Projective (E.inverse.obj (E.functor.obj A)) :=
    E.inverse.projective_obj_of_projective hmod
  have hA : CategoryTheory.Projective A :=
    CategoryTheory.Projective.of_iso (E.unitIso.app A).symm hinv
  let AH := (Rep.resFunctor.{max uG (max uR uV)} H.subtype).obj A
  letI : (Rep.resFunctor.{max uG (max uR uV)} (k := R)
      H.subtype).PreservesProjectiveObjects :=
    (Rep.resFunctor H.subtype).preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (Rep.resCoindAdjunction.{max uR uV, uR, uG, uG} R H.subtype)
  have hAH : CategoryTheory.Projective AH :=
    (Rep.resFunctor H.subtype).projective_obj_of_projective hA
  let EH := Rep.equivalenceModuleMonoidAlgebra (k := R) (G := H)
  have hHmod : CategoryTheory.Projective
      (ModuleCat.of R[H] (Representation.asModule (rho'.comp H.subtype))) :=
    EH.functor.projective_obj_of_projective hAH
  letI : CategoryTheory.Projective
      (ModuleCat.of R[H] (Representation.asModule (rho'.comp H.subtype))) := hHmod
  letI : Module.Projective R[H] (Representation.asModule (rho'.comp H.subtype)) :=
    ModuleCat.projective_of_module_projective
      (ModuleCat.of R[H] (Representation.asModule (rho'.comp H.subtype)))
  let eH : Representation.asModule (rho'.comp H.subtype) ≃ₗ[R[H]]
      Representation.asModule (rho.comp H.subtype) :=
    moduleCongr (rho'.comp H.subtype) (rho.comp H.subtype) eUp.symm
      (by intro h; ext v; rfl)
  exact Module.Projective.of_equiv' eH

/- The section is obtained from the given restricted module's projectivity. No section or
   coefficient-module freeness is assumed. P may be in a different universe from V. -/
private theorem restricted_section
    (rho : Representation R G V) (H : Subgroup G)
    (hproj : Module.Projective R[H] (Representation.asModule (rho.comp H.subtype)))
    {P : Type uP} [AddCommGroup P] [Module R P] [Module R[G] P]
    [IsScalarTower R R[G] P]
    (f : P →ₗ[R[G]] rho.asModule) (hf : Function.Surjective f) :
    ∃ s : rho.asModule →ₗ[R] P, (∀ v, f (s v) = v) ∧
      ∀ (h : H) (v : rho.asModule),
        s (MonoidAlgebra.single (h : G) (1 : R) • v) =
          MonoidAlgebra.single (h : G) (1 : R) • s v := by
  let sigma : Representation R G P := Representation.ofModule' P
  let rhoH : Representation R H V := rho.comp H.subtype
  let sigmaH : Representation R H P := sigma.comp H.subtype
  let fR : P →ₗ[R] V := rho.asModuleEquiv.toLinearMap.comp (f.restrictScalars R)
  have hcomm (g : G) : fR.comp (sigma g) = (rho g).comp fR := by
    ext p
    change rho.asModuleEquiv (f (MonoidAlgebra.single g (1 : R) • p)) =
      rho g (rho.asModuleEquiv (f p))
    rw [f.map_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_single]
    simp only [one_smul]
  let fH : sigmaH.asModule →ₗ[R[H]] rhoH.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule sigmaH rhoH
      { toLinearMap := fR, isIntertwining' := fun h => hcomm h }
  have hfH : Function.Surjective fH := by
    intro v
    obtain ⟨p, hp⟩ := hf (rho.asModuleEquiv.symm (rhoH.asModuleEquiv v))
    refine ⟨sigmaH.asModuleEquiv.symm p, ?_⟩
    change rho.asModuleEquiv (f p) = rhoH.asModuleEquiv v
    rw [hp, rho.asModuleEquiv.apply_symm_apply]
  letI : Module.Projective R[H] rhoH.asModule := hproj
  obtain ⟨sH, hsH⟩ := Module.projective_lifting_property fH
    (LinearMap.id : rhoH.asModule →ₗ[R[H]] rhoH.asModule) hfH
  let t := (Representation.IntertwiningMap.equivLinearMapAsModule rhoH sigmaH).symm sH
  let s : rho.asModule →ₗ[R] P := t.toLinearMap.comp rho.asModuleEquiv.toLinearMap
  refine ⟨s, ?_, ?_⟩
  · intro v
    have h := DFunLike.congr_fun hsH (rhoH.asModuleEquiv.symm (rho.asModuleEquiv v))
    change rho.asModuleEquiv (f (s v)) = rho.asModuleEquiv v at h
    exact rho.asModuleEquiv.injective h
  · intro h v
    have hh := Representation.IntertwiningMap.isIntertwining
      rhoH sigmaH t h (rho.asModuleEquiv v)
    change t (rho.asModuleEquiv (MonoidAlgebra.single (h : G) (1 : R) • v)) =
      MonoidAlgebra.single (h : G) (1 : R) • t (rho.asModuleEquiv v)
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single_one]
    exact hh

/- Integral relative trace on actual left cosets gH. The relation g ~ gh is used to descend
   g * s(g^-1 * -); left translation of cosets gives the nonabelian covariance below. -/
private theorem finite_coset_trace
    (rho : Representation R G V) (H : Subgroup G) [H.FiniteIndex]
    {P : Type uP} [AddCommGroup P] [Module R P] [Module R[G] P]
    [IsScalarTower R R[G] P]
    (f : P →ₗ[R[G]] rho.asModule) (s : rho.asModule →ₗ[R] P)
    (hs : ∀ v, f (s v) = v)
    (hc : ∀ (h : H) (v : rho.asModule),
      s (MonoidAlgebra.single (h : G) (1 : R) • v) =
        MonoidAlgebra.single (h : G) (1 : R) • s v) :
    ∃ T : rho.asModule →ₗ[R[G]] P, ∀ v, f (T v) = H.index • v := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let aV : G → (rho.asModule →ₗ[R] rho.asModule) :=
    MonoidAlgebra.GroupSMul.linearMap R rho.asModule
  let aP : G → (P →ₗ[R] P) := MonoidAlgebra.GroupSMul.linearMap R P
  let A (g : G) : rho.asModule →ₗ[R] P := (aP g).comp (s.comp (aV g⁻¹))
  have hrep (g : G) (h : H) : A (g * h) = A g := by
    apply LinearMap.ext
    intro v
    change MonoidAlgebra.single (g * h) (1 : R) •
        s (MonoidAlgebra.single ((g * h)⁻¹) (1 : R) • v) =
      MonoidAlgebra.single g (1 : R) • s (MonoidAlgebra.single g⁻¹ (1 : R) • v)
    have hinner : MonoidAlgebra.single ((g * h)⁻¹) (1 : R) • v =
        MonoidAlgebra.single ((h⁻¹ : H) : G) (1 : R) •
          (MonoidAlgebra.single g⁻¹ (1 : R) • v) := by
      rw [← mul_smul, MonoidAlgebra.single_mul_single, one_mul]
      simp only [mul_inv_rev, Subgroup.coe_inv]
    rw [hinner, hc h⁻¹, ← mul_smul, MonoidAlgebra.single_mul_single, one_mul]
    simp only [Subgroup.coe_inv, mul_inv_cancel_right]
  let B : (G ⧸ H) → (rho.asModule →ₗ[R] P) :=
    @Quotient.lift G _ (QuotientGroup.leftRel H) A (by
      intro a b hab
      simpa only [mul_inv_cancel_left] using
        (hrep a ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab⟩).symm)
  have hcov (x : G) (q : G ⧸ H) (v : rho.asModule) :
      B (x • q) (aV x v) = aP x (B q v) := by
    refine Quotient.inductionOn q ?_
    intro g
    change MonoidAlgebra.single (x * g) (1 : R) •
        s (MonoidAlgebra.single ((x * g)⁻¹) (1 : R) •
          (MonoidAlgebra.single x (1 : R) • v)) =
      MonoidAlgebra.single x (1 : R) •
        (MonoidAlgebra.single g (1 : R) • s (MonoidAlgebra.single g⁻¹ (1 : R) • v))
    simp only [← mul_smul, MonoidAlgebra.single_mul_single,
      mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  have hB (q : G ⧸ H) (v : rho.asModule) : f (B q v) = v := by
    refine Quotient.inductionOn q ?_
    intro g
    change f (MonoidAlgebra.single g (1 : R) •
      s (MonoidAlgebra.single g⁻¹ (1 : R) • v)) = v
    rw [f.map_smul, hs]
    simp only [← mul_smul, MonoidAlgebra.single_mul_single, one_mul,
      mul_inv_cancel, ← MonoidAlgebra.one_def, one_smul]
  let T : rho.asModule →ₗ[R] P := ∑ q : G ⧸ H, B q
  have hT (x : G) (v : rho.asModule) : T (aV x v) = aP x (T v) := by
    simp only [T, LinearMap.sum_apply, map_sum]
    symm
    exact Fintype.sum_bijective (fun q : G ⧸ H => x • q) (MulAction.bijective x)
      _ _ (fun q => (hcov x q v).symm)
  refine ⟨MonoidAlgebra.equivariantOfLinearOfComm T hT, ?_⟩
  intro v
  change f (T v) = H.index • v
  simp only [T, LinearMap.sum_apply, map_sum, hB, Finset.sum_const, Finset.card_univ]
  rw [Fintype.card_eq_nat_card, ← H.index_eq_card]

/-- Over an arbitrary commutative ring, restriction to a finite-index subgroup detects
projectivity when the natural-number index is a unit in the coefficient ring. No finiteness,
normality, generation, presentation or nontriviality assumption is imposed on G, H or V. -/
theorem projective_iff_projective_restrict_of_isUnit_index
    (rho : Representation R G V) (H : Subgroup G) [H.FiniteIndex]
    (hunit : IsUnit (H.index : R)) :
    Module.Projective R[G] rho.asModule ↔
      Module.Projective R[H] (Representation.asModule (rho.comp H.subtype)) := by
  constructor
  · exact projective_restrict rho H
  · intro hproj
    apply Module.Projective.of_lifting_property''
    intro f hf
    obtain ⟨s, hs, hc⟩ := restricted_section rho H hproj f hf
    obtain ⟨T, hT⟩ := finite_coset_trace rho H f s hs hc
    let c : R := ↑(hunit.unit⁻¹)
    have hcancel : c * (H.index : R) = 1 := hunit.val_inv_mul
    refine ⟨c • T, ?_⟩
    apply LinearMap.ext
    intro v
    change f (c • T v) = v
    rw [f.map_smul_of_tower, hT, ← Nat.cast_smul_eq_nsmul R,
      smul_smul, hcancel, one_smul]

end D5.S3.FiniteGroups.GroupAlgebra.FiniteIndexProjectivity
