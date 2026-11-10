/- GID: D5/S3/FiniteGroups/GroupAlgebra/ProjectiveKernelOrder
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/ProjectiveKernelOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Coinduced, mathlib/module/Mathlib.RepresentationTheory.Rep.Iso, mathlib/module/Mathlib.LinearAlgebra.Dual.Lemmas]
   utility: none
   digest: A finite subgroup acting trivially on a nonzero projective representation has unit cardinal. -/

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Tactic

/-!
Finite subgroup projectivity obstruction for arbitrary fields, groups, and representation
universes.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.GroupAlgebra.ProjectiveKernelOrder

open CategoryTheory
open scoped BigOperators MonoidAlgebra

universe uk uG uV uX uw

private noncomputable def uliftRepresentation {k : Type uk} [Field k] {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module k V] (rho : Representation k G V) :
    Representation k G (ULift.{uw} V) where
  toFun g := (ULift.moduleEquiv.symm.toLinearMap.comp <| (rho g).comp
    ULift.moduleEquiv.toLinearMap)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [LinearMap.comp_apply]

private noncomputable def wideLiftRepresentation
    {k : Type uk} [Field k] {G : Type uG} [Group G]
    {V : Type uX} [AddCommGroup V] [Module k V] (rho : Representation k G V) :
    Representation k G
      (ULift.{max uG (max uk uw)} (ULift.{max uG (max uk uw)} V)) :=
  uliftRepresentation.{uk, uG, max (max uG (max uk uw)) uX, max uG (max uk uw)}
    (uliftRepresentation.{uk, uG, uX, max uG (max uk uw)} rho)

private noncomputable abbrev trivialLift {k : Type uk} [Field k] {H : Type uG} [Group H]
    : Representation k H
      (ULift.{max uG (max uk uw)} (ULift.{max uG (max uk uw)} k)) :=
  wideLiftRepresentation.{uk, uG, uk, uw} (Representation.trivial k H k)

/- The augmentation is the unique intertwiner from the left regular representation to the
   trivial representation.  The coefficient formula below is the arithmetic input used at the
   end of the obstruction. -/
private noncomputable def augmentationMap {k : Type uk} [Field k] {H : Type uG} [Group H] :
    Rep.of (wideLiftRepresentation.{uk, uG, max uk uG, uw}
      (Representation.leftRegular k H)) ⟶
      Rep.of (trivialLift (k := k) (H := H)) := by
  let b := (Representation.leftRegularMapEquiv
    (Representation.trivial k H k)).symm 1
  let down :
      ULift.{max uG (max uk uw)} (ULift.{max uG (max uk uw)} k[H]) ≃ₗ[k] k[H] :=
    ULift.moduleEquiv.trans ULift.moduleEquiv
  exact Rep.ofHom
    { toLinearMap := (ULift.moduleEquiv.symm.trans ULift.moduleEquiv.symm).toLinearMap.comp
        (b.toLinearMap.comp down.toLinearMap)
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro x
        have hb := congrArg (fun f => f x.down.down) (b.isIntertwining' h)
        apply ULift.ext
        apply ULift.ext
        change b ((Representation.leftRegular k H h) x.down.down) =
          (Representation.trivial k H k h) (b x.down.down)
        exact hb }

private theorem augmentationMap_apply {k : Type uk} [Field k] {H : Type uG} [Group H]
    (x : ULift.{max uG (max uk uw)} (ULift.{max uG (max uk uw)} k[H])) :
    (augmentationMap (k := k) (H := H)).hom x =
      ULift.up (ULift.up (x.down.down.coeff.linearCombination k (fun _ => (1 : k)))) := by
  cases x with
  | up x =>
    cases x with
    | up x =>
      induction x using MonoidAlgebra.induction_on with
      | of g => apply ULift.ext; apply ULift.ext; simp [augmentationMap]
      | add x y hx hy =>
          apply ULift.ext
          apply ULift.ext
          change ((augmentationMap (k := k) (H := H)).hom
              (ULift.up (ULift.up (x + y)))).down.down = _
          rw [show ULift.up (ULift.up (x + y)) =
              ULift.up (ULift.up x) + ULift.up (ULift.up y) by rfl]
          rw [map_add, hx, hy]
          simp [Finsupp.linearCombination_apply, Finsupp.sum_add_index']
      | smul r x hx =>
          apply ULift.ext
          apply ULift.ext
          change ((augmentationMap (k := k) (H := H)).hom
              (ULift.up (ULift.up (r • x)))).down.down = _
          rw [show ULift.up (ULift.up (r • x)) =
              r • ULift.up (ULift.up x) by rfl]
          rw [map_smul, hx]
          simp [Finsupp.linearCombination_apply, Finsupp.sum_smul_index']

private theorem augmentationMap_surjective {k : Type uk} [Field k] {H : Type uG} [Group H] :
    Function.Surjective (augmentationMap (k := k) (H := H)).hom := by
  intro r
  refine ⟨ULift.up (ULift.up (MonoidAlgebra.single (1 : H) r.down.down)), ?_⟩
  apply ULift.ext
  apply ULift.ext
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
  letI : Module.Projective k[G] rho.asModule := hproj
  letI : Representation.IsTrivial (rho.comp H.subtype) := htriv
  letI : Fintype H := Fintype.ofFinite H
  let rho' : Representation k G
      (ULift.{max uG (max uk uV)} (ULift.{max uG (max uk uV)} V)) :=
    wideLiftRepresentation.{uk, uG, uV, uV} rho
  have htriv' : Representation.IsTrivial (rho'.comp H.subtype) := by
    constructor
    intro h
    apply LinearMap.ext
    intro x
    apply ULift.ext
    apply ULift.ext
    simpa [rho', wideLiftRepresentation, uliftRepresentation] using
      congrArg (fun z : V =>
          (ULift.up (ULift.up z) :
            ULift.{max uG (max uk uV)} (ULift.{max uG (max uk uV)} V)))
        (Representation.isTrivial_apply (rho.comp H.subtype) h x.down.down)
  letI : Module.Projective k[G]
      (ULift.{max uG (max uk uV)} (ULift.{max uG (max uk uV)} rho.asModule)) := inferInstance
  let liftV : V → rho'.asModule := fun z => ULift.up (ULift.up z)
  have hsource_smul (r : k[G])
      (x : ULift.{max uG (max uk uV)} (ULift.{max uG (max uk uV)} rho.asModule)) :
      (r • x).down.down = r • x.down.down := by
    rfl
  have htarget_single (g : G) (y : rho'.asModule) :
      (MonoidAlgebra.single g (1 : k) • y).down.down =
        rho g y.down.down := by
    have h := Representation.single_smul (ρ := rho') (1 : k) g y
    have h' := congrArg (fun z => z.down.down) h
    have h'' : (MonoidAlgebra.single g (1 : k) • y).down.down =
        (rho' g (rho'.asModuleEquiv y)).down.down := by
      simpa only [one_smul] using h'
    cases y with
    | up y =>
      cases y with
      | up y =>
        simp [rho', wideLiftRepresentation, uliftRepresentation, LinearMap.comp_apply,
          Representation.asModuleEquiv] at h''
        convert h'' using 1 <;> rfl
  let eModule :
      (ULift.{max uG (max uk uV)} (ULift.{max uG (max uk uV)} rho.asModule)) ≃ₗ[k[G]] rho'.asModule :=
    { toFun := fun x =>
      liftV (rho.asModuleEquiv x.down.down)
      invFun := fun y =>
          (ULift.up (ULift.up (rho.asModuleEquiv.symm y.down.down)) :
            ULift.{max uG (max uk uV)} (ULift.{max uG (max uk uV)} rho.asModule))
      left_inv := by
        intro x
        apply ULift.ext
        apply ULift.ext
        change rho.asModuleEquiv.symm (rho.asModuleEquiv x.down.down) = x.down.down
        exact rho.asModuleEquiv.symm_apply_apply x.down.down
      right_inv := by
        intro y
        apply ULift.ext
        apply ULift.ext
        rfl
      map_add' := by
        intro x y
        apply ULift.ext
        apply ULift.ext
        change rho.asModuleEquiv (x.down.down + y.down.down) =
          rho.asModuleEquiv x.down.down + rho.asModuleEquiv y.down.down
        exact rho.asModuleEquiv.map_add x.down.down y.down.down
      map_smul' := by
        intro r x
        induction r using MonoidAlgebra.induction_on with
        | of g =>
            apply ULift.ext
            apply ULift.ext
            let y : rho'.asModule := liftV (rho.asModuleEquiv x.down.down)
            change rho.asModuleEquiv (MonoidAlgebra.single g (1 : k) • x.down.down) =
              (MonoidAlgebra.single g (1 : k) • y).down.down
            rw [Representation.asModuleEquiv_map_smul,
              Representation.asAlgebraHom_single]
            simp only [one_smul]
            exact (htarget_single g y).symm
        | add r s hr hs =>
            let y : rho'.asModule := liftV (rho.asModuleEquiv x.down.down)
            have hr' : rho.asModuleEquiv (r • x.down.down) = (r • y).down.down := by
              have h := congrArg (fun z : rho'.asModule => z.down.down) hr
              change rho.asModuleEquiv (r • x.down.down) = (r • y).down.down at h
              exact h
            have hs' : rho.asModuleEquiv (s • x.down.down) = (s • y).down.down := by
              have h := congrArg (fun z : rho'.asModule => z.down.down) hs
              change rho.asModuleEquiv (s • x.down.down) = (s • y).down.down at h
              exact h
            apply ULift.ext
            apply ULift.ext
            change rho.asModuleEquiv ((r + s) • x.down.down) = ((r + s) • y).down.down
            calc
              rho.asModuleEquiv ((r + s) • x.down.down) =
                  rho.asModuleEquiv (r • x.down.down + s • x.down.down) := by rw [add_smul]
              _ = rho.asModuleEquiv (r • x.down.down) +
                  rho.asModuleEquiv (s • x.down.down) :=
                rho.asModuleEquiv.map_add _ _
              _ = (r • y).down.down + (s • y).down.down := by rw [hr', hs']
              _ = ((r + s) • y).down.down := by
                exact congrArg (fun z : rho'.asModule => z.down.down)
                  (add_smul r s y).symm
        | smul a r hr =>
            let y : rho'.asModule := liftV (rho.asModuleEquiv x.down.down)
            have hr' : rho.asModuleEquiv (r • x.down.down) = (r • y).down.down := by
              have h := congrArg (fun z : rho'.asModule => z.down.down) hr
              change rho.asModuleEquiv (r • x.down.down) = (r • y).down.down at h
              exact h
            apply ULift.ext
            apply ULift.ext
            change rho.asModuleEquiv ((a • r) • x.down.down) = ((a • r) • y).down.down
            calc
              rho.asModuleEquiv ((a • r) • x.down.down) =
                  rho.asModuleEquiv (a • (r • x.down.down)) := by rw [smul_assoc]
              _ = a • rho.asModuleEquiv (r • x.down.down) :=
                rho.asModuleEquiv.map_smul a (r • x.down.down)
              _ = a • (r • y).down.down := by rw [hr']
              _ = ((a • r) • y).down.down := by
                exact congrArg (fun z : rho'.asModule => z.down.down)
                  (smul_assoc a r y).symm }
  letI : Module.Projective k[G] rho'.asModule := Module.Projective.of_equiv' eModule
  let A : Rep.{max uG (max uk uV)} k G := Rep.of rho'
  let E := Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)
  have hmodcat : CategoryTheory.Projective (ModuleCat.of k[G] rho'.asModule) :=
    ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of k[G] rho'.asModule)
  have hinv : CategoryTheory.Projective (E.inverse.obj (E.functor.obj A)) :=
    E.inverse.projective_obj_of_projective hmodcat
  have hA : CategoryTheory.Projective A := by
    exact CategoryTheory.Projective.of_iso (E.unitIso.app A).symm hinv
  let AH := (Rep.resFunctor.{max uG (max uk uV)} H.subtype).obj A
  letI : (Rep.resFunctor.{max uG (max uk uV)} H.subtype).PreservesProjectiveObjects :=
    (Rep.resFunctor.{max uG (max uk uV)} H.subtype).preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (Rep.resCoindAdjunction.{max uk uV, uk, uG, uG} k H.subtype)
  have hAH : CategoryTheory.Projective AH := by
    exact (Rep.resFunctor.{max uG (max uk uV)} H.subtype).projective_obj_of_projective hA
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : V, v₀ ≠ 0 := exists_ne 0
  let v : ULift.{max uG (max uk uV)} (ULift.{max uG (max uk uV)} V) :=
    ULift.up (ULift.up v₀)
  have hv : v ≠ 0 := by
    intro hv
    apply hv₀
    exact ULift.ext_iff.mp (ULift.ext_iff.mp hv)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hv
  let downTriv :
      ULift.{max uG (max uk uV)} (ULift.{max uG (max uk uV)} k) ≃ₗ[k] k :=
    (ULift.moduleEquiv :
      ULift.{max uG (max uk uV), max (max uG (max uk uV)) uk}
          (ULift.{max uG (max uk uV), uk} k) ≃ₗ[k]
        ULift.{max uG (max uk uV), uk} k).trans
      (ULift.moduleEquiv :
        ULift.{max uG (max uk uV), uk} k ≃ₗ[k] k)
  let upTriv : k ≃ₗ[k] ULift.{max uG (max uk uV)} (ULift.{max uG (max uk uV)} k) :=
    (ULift.moduleEquiv :
      ULift.{max uG (max uk uV), uk} k ≃ₗ[k] k).symm.trans
      (ULift.moduleEquiv :
        ULift.{max uG (max uk uV), max (max uG (max uk uV)) uk}
            (ULift.{max uG (max uk uV), uk} k) ≃ₗ[k]
          ULift.{max uG (max uk uV), uk} k).symm
  let i : Rep.of (trivialLift.{uk, uG, uV} (k := k) (H := H)) ⟶ AH :=
    Rep.ofHom
      { toLinearMap := (LinearMap.toSpanSingleton k
          (ULift.{max uG (max uk uV)} (ULift.{max uG (max uk uV)} V)) v).comp
          downTriv.toLinearMap
        isIntertwining' := by
          intro h
          apply LinearMap.ext
          intro r
          simp only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
          have hvh : A.ρ (H.subtype h) v = v := by
            change rho' (H.subtype h) v = v
            exact Representation.isTrivial_apply (rho'.comp H.subtype) h v
          have hvh' : (MonoidHom.comp A.ρ H.subtype) h v = v := hvh
          rw [map_smul, hvh']
          rfl }
  let p : AH ⟶ Rep.of (trivialLift.{uk, uG, uV} (k := k) (H := H)) :=
    Rep.ofHom
      { toLinearMap := upTriv.toLinearMap.comp φ
        isIntertwining' := by
          intro h
          apply LinearMap.ext
          intro x
          simp only [LinearMap.comp_apply]
          change upTriv (φ (A.ρ (H.subtype h) x)) =
            (trivialLift.{uk, uG, uV} h) (upTriv (φ x))
          have hxh : A.ρ (H.subtype h) x = x := by
            change rho' (H.subtype h) x = x
            exact Representation.isTrivial_apply (rho'.comp H.subtype) h x
          rw [hxh]
          rfl }
  have hip : i ≫ p = 𝟙 _ := by
    ext r
    simp [i, p, hφ, upTriv, downTriv]
  letI : CategoryTheory.Projective
      (Rep.of (trivialLift.{uk, uG, uV} (k := k) (H := H))) := by
    refine ⟨fun {E X} f e _ => ?_⟩
    obtain ⟨g, hg⟩ := hAH.factors (p ≫ f) e
    refine ⟨i ≫ g, ?_⟩
    rw [Category.assoc, hg, ← Category.assoc, hip, Category.id_comp]
  let aug : Rep.of (wideLiftRepresentation.{uk, uG, max uk uG, uV}
      (Representation.leftRegular k H)) ⟶
      Rep.of (trivialLift.{uk, uG, uV} (k := k) (H := H)) :=
    augmentationMap.{uk, uG, uV} (k := k) (H := H)
  letI : Epi aug := (Rep.epi_iff_surjective aug).2
    (augmentationMap_surjective.{uk, uG, uV} (k := k) (H := H))
  obtain ⟨s, hs⟩ := (inferInstance : CategoryTheory.Projective
    (Rep.of (trivialLift.{uk, uG, uV} (k := k) (H := H)))).factors (𝟙 _) aug
  let x : ULift.{max uG (max uk uV)} (ULift.{max uG (max uk uV)} k[H]) :=
    s.hom (ULift.up (ULift.up (1 : k)))
  let x₀ : k[H] := x.down.down
  have hx_aug : aug.hom x = 1 := by
    change aug.hom x = ULift.up (ULift.up (1 : k))
    have hs' := congrArg (fun f => f.hom (ULift.up (ULift.up (1 : k)))) hs
    simpa [x] using hs'
  have hinv_x (h : H) :
      (wideLiftRepresentation.{uk, uG, max uk uG, uV}
        (Representation.leftRegular k H)) h x = x := by
    have hs' := congrArg (fun f => f (ULift.up (ULift.up (1 : k)))) (s.hom.2 h)
    have htriv1 :
        (trivialLift.{uk, uG, uV} (k := k) (H := H) h)
            (ULift.up (ULift.up (1 : k))) = ULift.up (ULift.up (1 : k)) := by
      rfl
    simp only [LinearMap.comp_apply] at hs'
    rw [htriv1] at hs'
    simpa [x] using hs'.symm
  have hinv_x₀ (h : H) : Representation.leftRegular k H h x₀ = x₀ := by
    simpa [x, x₀, wideLiftRepresentation, uliftRepresentation] using
      congrArg ULift.down (congrArg ULift.down (hinv_x h))
  have hcoeff (h : H) : x₀.coeff h = x₀.coeff 1 := by
    have hc := congrArg (fun y : k[H] => y.coeff h) (hinv_x₀ h)
    simpa [Representation.coeff_ofMulAction] using hc.symm
  have hsum : x₀.coeff.linearCombination k (fun _ => (1 : k)) = 1 := by
    apply ULift.up_injective
    apply ULift.up_injective
    rw [← augmentationMap_apply.{uk, uG, uV} (k := k) (H := H) x]
    exact hx_aug
  have hcard : (Nat.card H : k) * x₀.coeff 1 = 1 := by
    simpa [Finsupp.linearCombination_apply, Finsupp.sum_fintype, hcoeff,
      Nat.card_eq_fintype_card] using hsum
  have hne : (Nat.card H : k) ≠ 0 := by
    intro hzero
    have hcard0 : (0 : k) * x₀.coeff 1 = 1 := by
      rw [← hzero]
      exact hcard
    have : (0 : k) = 1 := by
      simpa only [zero_mul] using hcard0
    exact zero_ne_one this
  exact isUnit_iff_ne_zero.mpr hne

end D5.S3.FiniteGroups.GroupAlgebra.ProjectiveKernelOrder
