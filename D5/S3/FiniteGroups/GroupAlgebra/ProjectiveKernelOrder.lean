/- GID: D5/S3/FiniteGroups/GroupAlgebra/ProjectiveKernelOrder
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/ProjectiveKernelOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Coinduced,
     mathlib/module/Mathlib.RepresentationTheory.Rep.Iso,
     mathlib/module/Mathlib.LinearAlgebra.Dual.Lemmas]
   utility: none
   digest: A finite subgroup acting trivially on a nonzero projective representation has unit cardinal.
-/

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.FiniteGroups.GroupAlgebra.ProjectiveKernelOrder

open CategoryTheory
open scoped BigOperators MonoidAlgebra

universe uk uG uV

/- The augmentation is the unique intertwiner from the left regular representation to the
   trivial representation.  The coefficient formula below is the arithmetic input used at the
   end of the obstruction. -/
private noncomputable def augmentationMap {k : Type uk} [Field k] {H : Type uG} [Group H] :
    Rep.of (Representation.leftRegular k H) ⟶ Rep.of (Representation.trivial k H k) :=
  Rep.ofHom ((Representation.leftRegularMapEquiv (Representation.trivial k H k)).symm 1)

private theorem augmentationMap_apply {k : Type uk} [Field k] {H : Type uG} [Group H]
    (x : k[H]) :
    (augmentationMap (k := k) (H := H)).hom x =
      x.coeff.linearCombination k (fun _ => (1 : k)) := by
  induction x using MonoidAlgebra.induction_on with
  | of g => simp [augmentationMap, Representation.leftRegularMapEquiv_symm_single]
  | add x y hx hy => simp [hx, hy]
  | smul r x hx => simp [hx]

private theorem augmentationMap_surjective {k : Type uk} [Field k] {H : Type uG} [Group H] :
    Function.Surjective (augmentationMap (k := k) (H := H)).hom := by
  intro r
  refine ⟨MonoidAlgebra.single (1 : H) r, ?_⟩
  simp [augmentationMap, ← MonoidAlgebra.smul_single]

/-- If a nonzero representation is projective and a finite subgroup acts trivially, then the
cardinality of that subgroup is a unit in the coefficient field. -/
theorem isUnit_natCard_of_projective_of_isTrivial
    {k : Type uk} [Field k] {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module k V] [Nontrivial V]
    (H : Subgroup G) [Finite H] (rho : Representation k G V)
    (hproj : Module.Projective k[G] rho.asModule)
    (htriv : Representation.IsTrivial (rho.comp H.subtype)) :
    IsUnit (Nat.card H : k) := by
  classical
  letI : Representation.IsTrivial (rho.comp H.subtype) := htriv
  let A : Rep.{uV} k G := Rep.of rho
  let E := Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)
  have hmodcat : CategoryTheory.Projective (ModuleCat.of k[G] rho.asModule) :=
    ModuleCat.projective_of_categoryTheory_projective
  have hinv : CategoryTheory.Projective (E.inverse.obj (E.functor.obj A)) :=
    E.inverse.projective_obj_of_projective hmodcat
  have hA : CategoryTheory.Projective A := by
    exact CategoryTheory.Projective.of_iso (E.unitIso A).symm hinv
  let AH : Rep.{uV} k H := (Rep.resFunctor H.subtype).obj A
  have hAH : CategoryTheory.Projective AH := by
    exact (Rep.resFunctor H.subtype).projective_obj_of_projective hA
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := exists_ne 0
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hv
  let i : Rep.of (Representation.trivial k H k) ⟶ AH :=
    Rep.ofHom
      { toLinearMap := LinearMap.toSpanSingleton k V v
        isIntertwining' := by
          intro h
          ext r
          simp [Representation.isTrivial_apply (rho.comp H.subtype) h] }
  let p : AH ⟶ Rep.of (Representation.trivial k H k) :=
    Rep.ofHom
      { toLinearMap := φ
        isIntertwining' := by
          intro h
          ext x
          simp [Representation.isTrivial_apply (rho.comp H.subtype) h] }
  have hip : i ≫ p = 𝟙 _ := by
    ext r
    simp [i, p, hφ]
  letI : CategoryTheory.Projective (Rep.of (Representation.trivial k H k)) := by
    refine ⟨fun {E X} f e _ => ?_⟩
    obtain ⟨g, hg⟩ := hAH.factors (p ≫ f) e
    refine ⟨i ≫ g, ?_⟩
    rw [Category.assoc, hg, ← Category.assoc, hip, Category.id_comp]
  let aug := augmentationMap (k := k) (H := H)
  letI : Epi aug := (Rep.epi_iff_surjective aug).2 (augmentationMap_surjective (k := k) (H := H))
  obtain ⟨s, hs⟩ := (inferInstance : CategoryTheory.Projective
    (Rep.of (Representation.trivial k H k))).factors (𝟙 _) aug
  let x : k[H] := s.hom 1
  have hx_aug : aug.hom x = 1 := by
    have hs' := congrArg (fun f => f.hom (1 : k)) hs
    simpa [x, aug] using hs'
  have hinv_x (h : H) : Representation.leftRegular k H h x = x := by
    have hs' := congrArg (fun f => f (1 : k)) (s.hom.2 h)
    simpa [x] using hs'.symm
  have hcoeff (h : H) : x.coeff h = x.coeff 1 := by
    have hc := congrArg (fun y : k[H] => y.coeff h) (hinv_x h)
    simpa [Representation.coeff_ofMulAction] using hc.symm
  have hsum : x.coeff.linearCombination k (fun _ => (1 : k)) = 1 := by
    rw [← augmentationMap_apply (k := k) (H := H) x]
    exact hx_aug
  have hcard : (Nat.card H : k) * x.coeff 1 = 1 := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    simpa [hcoeff, Nat.card_eq_fintype_card]
      using hsum
  have hne : (Nat.card H : k) ≠ 0 := by
    intro hzero
    have : (0 : k) = 1 := by simpa [hzero] using hcard
    exact zero_ne_one this
  exact isUnit_iff_ne_zero.mpr hne

end D5.S3.FiniteGroups.GroupAlgebra.ProjectiveKernelOrder
