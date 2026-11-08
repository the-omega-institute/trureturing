/- GID: D5/S3/FiniteGroups/FrobeniusInnerActionObstruction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/FrobeniusInnerActionObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Inner implementations on simple finite group-algebra quotients force augmentation. -/

import Mathlib.Algebra.Field.ULift
import D5.S3.FiniteGroups.FrobeniusCharacterDegrees
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-! Inner action rigidity over arbitrary fields, using original-module isotypic support. -/

universe uk un uv

namespace D5.S3.FiniteGroups.FrobeniusInnerActionObstruction

open CategoryTheory
open scoped TensorProduct _root_.MonoidAlgebra
open FrobeniusCharacterDegrees

private theorem ofModule'_action
    {k G M : Type*} [Field k] [Group G] [AddCommGroup M]
    [Module k M] [Module (MonoidAlgebra k G) M]
    [IsScalarTower k (MonoidAlgebra k G) M]
    (r : MonoidAlgebra k G) (x : M) :
    (Representation.ofModule' (k := k) (G := G) M).asAlgebraHom r x = r • x := by
  induction r using MonoidAlgebra.induction_on with
  | of g => simp [Representation.ofModule']
  | add r s hr hs => simp only [map_add, LinearMap.add_apply, add_smul, hr, hs]
  | smul c r hr =>
      rw [map_smul, LinearMap.smul_apply, hr, ← smul_assoc]

/-- An inner implementation in the image algebra of a simple representation descends
to a supported simple submodule after scalar extension, in every characteristic. -/
theorem trivial_of_inner_image
    {k : Type uk} {N : Type un} {V : Type uv} [Field k] [Group N] [Finite N]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k N V)
    (hρ : IsSimpleModule (MonoidAlgebra k N) ρ.asModule)
    (φ : MulAut N) (hφ : ∀ n : N, φ n = n → n = 1)
    (r s : MonoidAlgebra k N)
    (hrs : ρ.asAlgebraHom r * ρ.asAlgebraHom s = 1)
    (hsr : ρ.asAlgebraHom s * ρ.asAlgebraHom r = 1)
    (hint : ∀ n, ρ.asAlgebraHom r * ρ n = ρ (φ n) * ρ.asAlgebraHom r) :
    Representation.IsTrivial ρ := by
  classical
  let E := AlgebraicClosure (ULift.{uv} k)
  letI : Algebra k E := ((algebraMap (ULift.{uv} k) E).comp
    (algebraMap k (ULift.{uv} k))).toAlgebra
  let R := MonoidAlgebra k N
  let B := MonoidAlgebra E N
  let ψ : R →+* B := MonoidAlgebra.mapRingHom N (algebraMap k E)
  let ρE : Representation E N (E ⊗[k] V) := extRep ρ
  let X := E ⊗[k] V
  letI : Module B X := ρE.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower E B X :=
    inferInstanceAs (IsScalarTower E B ρE.asModule)
  letI : Module R X := originalModule ρ
  letI : IsSimpleModule R ρ.asModule := hρ
  letI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial R ρ.asModule
  letI : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  letI : Nontrivial X := Module.nontrivial_of_finrank_pos (R := E) (by
    change 0 < Module.finrank E (E ⊗[k] V)
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos (R := k) (M := V))
  letI : Module.Finite E X := inferInstanceAs (Module.Finite E (E ⊗[k] V))
  letI : Module.Finite B X := Module.Finite.of_restrictScalars_finite E B X
  letI : IsArtinianRing B := IsArtinianRing.of_finite E B
  obtain ⟨Y, hY⟩ := IsAtomic.exists_atom (Submodule B X)
  letI : IsSimpleModule B Y := isSimpleModule_iff_isAtom.mpr hY
  letI : Nontrivial Y := IsSimpleModule.nontrivial B Y
  letI : Module R Y := Module.compHom Y ψ
  have hsupport : supported R B ρ.asModule X ψ := ext_isotypic (E := E) ρ hρ
  have hsupportY := supported_submodule ψ hsupport Y
  change IsSemisimpleModule R Y ∧ IsIsotypicOfType R Y ρ.asModule at hsupportY
  letI : IsSemisimpleModule R Y := hsupportY.1
  obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule R Y
  letI : IsSimpleModule R S := hS
  obtain ⟨e⟩ := hsupportY.2 S
  let j : ρ.asModule →ₗ[R] Y := S.subtype.comp e.symm.toLinearMap
  have hj : Function.Injective j := by
    exact S.subtype_injective.comp e.symm.injective
  have hbase (a : R) :
      ρE.asAlgebraHom (ψ a) = (ρ.asAlgebraHom a).baseChange E := by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp [ha, hb]
    | single g c =>
        change ρE.asAlgebraHom (MonoidAlgebra.mapRingHom N (algebraMap k E)
          (MonoidAlgebra.single g c)) = _
        rw [MonoidAlgebra.mapRingHom_single, Representation.asAlgebraHom_single,
          Representation.asAlgebraHom_single, LinearMap.baseChange_smul]
        apply LinearMap.ext
        intro x
        simp only [LinearMap.smul_apply]
        exact algebraMap_smul E c ((ρ g).baseChange E x)
  have hact (a : R) (x : X) :
      ψ a • x = (ρ.asAlgebraHom a).baseChange E x := by
    exact LinearMap.congr_fun (hbase a) x
  let T : Y →ₗ[E] Y :=
    { toFun := fun x => ⟨ψ r • x.1, Y.smul_mem _ x.2⟩
      map_add' := by intros; apply Subtype.ext; exact smul_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact smul_comm _ _ _ }
  let Tinv : Y →ₗ[E] Y :=
    { toFun := fun x => ⟨ψ s • x.1, Y.smul_mem _ x.2⟩
      map_add' := by intros; apply Subtype.ext; exact smul_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact smul_comm _ _ _ }
  have hleft : Function.LeftInverse Tinv T := by
    intro x
    apply Subtype.ext
    change ψ s • (ψ r • x.1) = x.1
    rw [hact, hact]
    change ((ρ.asAlgebraHom s).baseChange E * (ρ.asAlgebraHom r).baseChange E) x.1 = x.1
    rw [← LinearMap.baseChange_mul, hsr, LinearMap.baseChange_one]
    rfl
  have hright : Function.RightInverse Tinv T := by
    intro x
    apply Subtype.ext
    change ψ r • (ψ s • x.1) = x.1
    rw [hact, hact]
    change ((ρ.asAlgebraHom r).baseChange E * (ρ.asAlgebraHom s).baseChange E) x.1 = x.1
    rw [← LinearMap.baseChange_mul, hrs, LinearMap.baseChange_one]
    rfl
  letI : Module.Finite E Y := Module.Finite.of_injective
    (Y.subtype.restrictScalars E) Y.subtype_injective
  let ρY : Representation E N Y := Representation.ofModule' (k := E) (G := N) Y
  let W : FDRep E N := FDRep.of ρY
  let eY : ρY.asModule ≃ₗ[B] Y :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by
        intro a x
        exact ofModule'_action (M := Y) a x }
  letI : IsSimpleModule B ρY.asModule := IsSimpleModule.congr eY
  letI : Representation.IsIrreducible W.ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρY).mpr inferInstance
  letI : Simple W := FiniteCharacterAlgebra.FDRep.simple_of_isIrreducible W
  have hintertwines (n : N) : T ∘ₗ ρY n = ρY (φ n) ∘ₗ T := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ψ r • ((MonoidAlgebra.of E N n) • x.1) =
      (MonoidAlgebra.of E N (φ n)) • (ψ r • x.1)
    change (ρE.asAlgebraHom (ψ r) * ρE.asAlgebraHom (MonoidAlgebra.of E N n)) x.1 =
      (ρE.asAlgebraHom (MonoidAlgebra.of E N (φ n)) * ρE.asAlgebraHom (ψ r)) x.1
    simp only [Representation.asAlgebraHom_of, hbase]
    change ((ρ.asAlgebraHom r).baseChange E * (ρ n).baseChange E) x.1 =
      ((ρ (φ n)).baseChange E * (ρ.asAlgebraHom r).baseChange E) x.1
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, hint n]
  let eT : Representation.Equiv W.ρ (W.ρ.comp φ.toMonoidHom) :=
    Representation.Equiv.mk (LinearEquiv.ofBijective T ⟨hleft.injective, hright.surjective⟩)
      hintertwines
  letI : Representation.IsTrivial W.ρ :=
    trivial_of_equiv_fixedPointFree_of_isAlgClosed φ hφ W eT
  constructor
  intro n
  ext v
  apply ρ.asModuleEquiv.symm.injective
  apply hj
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul]
  change ψ (MonoidAlgebra.of k N n) • j (ρ.asModuleEquiv.symm v) = _
  have hmap : ψ (MonoidAlgebra.of k N n) = MonoidAlgebra.of E N n := by
    change MonoidAlgebra.mapRingHom N (algebraMap k E)
      (MonoidAlgebra.single n 1) = MonoidAlgebra.single n 1
    rw [MonoidAlgebra.mapRingHom_single]
    rfl
  rw [hmap]
  exact Representation.isTrivial_apply W.ρ n _

/-- The augmentation of the finite group algebra. -/
noncomputable def augmentation (k N : Type*) [Field k] [Group N] :
    MonoidAlgebra k N →ₐ[k] k := MonoidAlgebra.lift k k N 1

/-- Over any field, a fixed-point-free automorphism cannot act inner on a
nonaugmentation finite-dimensional simple quotient of the group algebra. -/
theorem inner_action_obstruction
    {k N A : Type*} [Field k] [Group N] [Finite N]
    [Ring A] [Algebra k A] [IsSimpleRing A] [Module.Finite k A]
    (q : MonoidAlgebra k N →ₐ[k] A) (hq : Function.Surjective q)
    (φ : MulAut N) (hφ : ∀ n : N, φ n = n → n = 1)
    (u : Aˣ)
    (hu : ∀ n, q (MonoidAlgebra.of k N (φ n)) =
      (u : A) * q (MonoidAlgebra.of k N n) * (↑(u⁻¹) : A)) :
    (∀ n, q (MonoidAlgebra.of k N n) = 1) ∧
      q = (Algebra.ofId k A).comp (augmentation k N) ∧ Nonempty (A ≃ₐ[k] k) := by
  classical
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨U, hU⟩ := IsSemisimpleModule.exists_simple_submodule A A
  letI : IsSimpleModule A U := hU
  letI : Nontrivial U := IsSimpleModule.nontrivial A U
  let L : MonoidAlgebra k N →ₐ[k] Module.End k U := (Algebra.lsmul k k U).comp q
  let ρ : Representation k N U := L.toMonoidHom.comp (MonoidAlgebra.of k N)
  have hL : ρ.asAlgebraHom = L := by
    apply MonoidAlgebra.algHom_ext
    · intro n
      simp [ρ, Representation.asAlgebraHom_single]
    · ext
  letI : RingHomSurjective q.toRingHom := ⟨hq⟩
  let f : ρ.asModule →ₛₗ[q.toRingHom] U :=
    { toFun := ρ.asModuleEquiv
      map_add' := ρ.asModuleEquiv.map_add
      map_smul' := by
        intro a x
        rw [Representation.asModuleEquiv_map_smul, hL]
        rfl }
  have hρ : IsSimpleModule (MonoidAlgebra k N) ρ.asModule :=
    (LinearMap.isSimpleModule_iff_of_bijective f ρ.asModuleEquiv.bijective).mpr hU
  obtain ⟨r, hr⟩ := hq (u : A)
  obtain ⟨s, hs⟩ := hq (↑(u⁻¹) : A)
  have hrs : ρ.asAlgebraHom r * ρ.asAlgebraHom s = 1 := by
    rw [hL]
    change (Algebra.lsmul k k U) (q r) * (Algebra.lsmul k k U) (q s) = 1
    rw [← map_mul, hr, hs]
    simp
  have hsr : ρ.asAlgebraHom s * ρ.asAlgebraHom r = 1 := by
    rw [hL]
    change (Algebra.lsmul k k U) (q s) * (Algebra.lsmul k k U) (q r) = 1
    rw [← map_mul, hs, hr]
    simp
  have hint (n : N) : ρ.asAlgebraHom r * ρ n = ρ (φ n) * ρ.asAlgebraHom r := by
    change ρ.asAlgebraHom r * L (MonoidAlgebra.of k N n) =
      L (MonoidAlgebra.of k N (φ n)) * ρ.asAlgebraHom r
    rw [hL]
    change (Algebra.lsmul k k U) (q r) * (Algebra.lsmul k k U) (q _) =
      (Algebra.lsmul k k U) (q _) * (Algebra.lsmul k k U) (q r)
    simp only [hr, hu]
    rw [← map_mul, ← map_mul]
    congr 1
    simp [mul_assoc]
  letI : Representation.IsTrivial ρ := trivial_of_inner_image ρ hρ φ hφ r s hrs hsr hint
  have hqone (n : N) : q (MonoidAlgebra.of k N n) = 1 := by
    apply RingHom.injective (Algebra.lsmul k k U).toRingHom
    rw [map_one]
    change L (MonoidAlgebra.of k N n) = 1
    change ρ n = 1
    exact Representation.isTrivial_def ρ n
  have hfactor : q = (Algebra.ofId k A).comp (augmentation k N) := by
    apply MonoidAlgebra.algHom_ext
    · intro n
      change q (MonoidAlgebra.of k N n) = _
      rw [hqone]
      simp [augmentation]
    · ext
  have hsurj : Function.Surjective (Algebra.ofId k A) := by
    intro a
    obtain ⟨x, hx⟩ := hq a
    exact ⟨augmentation k N x, (AlgHom.congr_fun hfactor x).symm.trans hx⟩
  exact ⟨hqone, hfactor, ⟨(AlgEquiv.ofBijective (Algebra.ofId k A)
    ⟨RingHom.injective (algebraMap k A), hsurj⟩).symm⟩⟩

end D5.S3.FiniteGroups.FrobeniusInnerActionObstruction
