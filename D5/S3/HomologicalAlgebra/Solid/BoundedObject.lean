/- GID: D5/S3/HomologicalAlgebra/Solid/BoundedObject
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/BoundedObject
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.MeasureFactorization

/-!
The actual bounded-integer-sequence condensed abelian group. Its presheaf
consists of integer-measure sections with a single bound on all coordinates.
Sheafification is left exact, so its inclusion in integer measures is a genuine
monomorphism. No derived realization or projective-resolution assumption is used.

New proofs, Apache-2.0. Research construction: Juan Esteban Rodríguez Camargo,
Notes on Solid Geometry, Lemmas 3.3.3--3.3.4, and root's immutable checked
realization response. The retained supplier and official Mathlib attributions
are unchanged.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits Opposite LightProfinite OnePoint MonoidalCategory

namespace LightCondensed.Solid
open IntProof

/-- A coordinate of a genuine measure section, in the locally constant model
of the discrete integers. -/
def integerSectionCoordinate (S : LightProfinite) (j : ℕ) :
    integerMeasures.obj.obj (op S) →ₗ[ℤ] LocallyConstant S ℤ :=
  (((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app
    (ModuleCat.of ℤ ℤ)).hom.app (op S)).hom.comp
      ((Pi.π (fun _ : ℕ => Zdisc) j).hom.app (op S)).hom

theorem integerSectionCoordinate_restrict {S' S : LightProfinite} (f : S' ⟶ S)
    (x : integerMeasures.obj.obj (op S)) (j : ℕ) :
    integerSectionCoordinate S' j (integerMeasures.obj.map f.op x) =
      (integerSectionCoordinate S j x).comap f.hom.hom := by
  exact NatTrans.naturality_apply
    ((Pi.π (fun _ : ℕ => Zdisc) j).hom ≫
      ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app
        (ModuleCat.of ℤ ℤ)).hom) f.op x

/-- Uniform boundedness includes empty and finite tests without any
enumeration of their points. There is still no bound on the number of coordinates. -/
def boundedIntegerSections (S : LightProfinite) :
    Submodule ℤ (integerMeasures.obj.obj (op S)) where
  carrier := {x | ∃ N : ℕ, ∀ j s, |integerSectionCoordinate S j x s| ≤ (N : ℤ)}
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro j s
    simp
  add_mem' := by
    rintro x y ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨N + M, ?_⟩
    intro j s
    simp only [map_add, LocallyConstant.coe_add, Pi.add_apply, Nat.cast_add]
    exact (abs_add_le _ _).trans (add_le_add (hN j s) (hM j s))
  smul_mem' := by
    rintro k x ⟨N, hN⟩
    refine ⟨k.natAbs * N, ?_⟩
    intro j s
    simp only [_root_.map_smul, LocallyConstant.coe_smul, Pi.smul_apply,
      smul_eq_mul, abs_mul, Nat.cast_mul, Int.natCast_natAbs]
    exact mul_le_mul_of_nonneg_left (hN j s) (abs_nonneg k)

theorem boundedIntegerSections_restrict {S' S : LightProfinite} (f : S' ⟶ S)
    {x : integerMeasures.obj.obj (op S)} (hx : x ∈ boundedIntegerSections S) :
    integerMeasures.obj.map f.op x ∈ boundedIntegerSections S' := by
  obtain ⟨N, hN⟩ := hx
  refine ⟨N, ?_⟩
  intro j s
  rw [integerSectionCoordinate_restrict]
  exact hN j (f s)

/-- The concrete module-valued bounded-sequence presheaf. -/
def boundedIntegerPresheaf : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ where
  obj S := ModuleCat.of ℤ (boundedIntegerSections S.unop)
  map f := ModuleCat.ofHom
    ({ toFun x := ⟨integerMeasures.obj.map f x.val,
        boundedIntegerSections_restrict f.unop x.property⟩
       map_zero' := by ext; exact map_zero (integerMeasures.obj.map f).hom
       map_add' x y := by ext; exact map_add (integerMeasures.obj.map f).hom _ _ } :
       boundedIntegerSections _ →+ boundedIntegerSections _).toIntLinearMap
  map_id S := by
    ext x
    exact congrArg Subtype.val (by
      apply Subtype.ext
      exact ConcreteCategory.congr_hom (integerMeasures.obj.map_id S) x.val)
  map_comp f g := by
    ext x
    exact ConcreteCategory.congr_hom (integerMeasures.obj.map_comp f g) x.val

/-- Inclusion before sheafification. -/
def boundedIntegerPresheafInclusion : boundedIntegerPresheaf ⟶ integerMeasures.obj where
  app S := by
    letI : Module ℤ (integerMeasures.obj.obj S) := (integerMeasures.obj.obj S).isModule
    exact ModuleCat.ofHom
      { toFun x := x.val
        map_add' _ _ := rfl
        map_smul' k x := map_intCast_smul
          (boundedIntegerSections S.unop).subtype.toAddMonoidHom ℤ ℤ k x }
  naturality := by intro X Y f; ext x; rfl

instance boundedIntegerPresheafInclusion_mono : Mono boundedIntegerPresheafInclusion := by
  haveI : ∀ S, Mono (boundedIntegerPresheafInclusion.app S) := fun _ =>
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  exact NatTrans.mono_of_mono_app _

/-- B_Z, formed inside light condensed abelian groups by actual sheafification. -/
def boundedIntegerMeasures : LightCondAb :=
  (presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)).obj
    boundedIntegerPresheaf

/-- The genuine inclusion B_Z -> M_Z. -/
def boundedIntegerMeasuresInclusion : boundedIntegerMeasures ⟶ integerMeasures :=
  (presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)).map
      boundedIntegerPresheafInclusion ≫ (sheafificationIso integerMeasures).inv

instance boundedIntegerMeasuresInclusion_mono : Mono boundedIntegerMeasuresInclusion := by
  dsimp only [boundedIntegerMeasuresInclusion]
  infer_instance

/-- The usual free-section equivalence, for the actual protected free functor. -/
def freeSectionEquiv (S : LightProfinite) (A : LightCondAb) :
    (freeOn S ⟶ A) ≃ A.obj.obj (op S) :=
  ((freeForgetAdjunction ℤ).homEquiv S.toCondensed A).trans
    (coherentTopology LightProfinite).yonedaEquiv

theorem freeSectionEquiv_coordinate (S : LightProfinite)
    (f : freeOn S ⟶ integerMeasures) (j : ℕ) :
    integerSectionCoordinate S j (freeSectionEquiv S integerMeasures f) =
      freeHomIntAddEquiv S (f ≫ Pi.π (fun _ : ℕ => Zdisc) j) := by
  dsimp [integerSectionCoordinate, freeSectionEquiv, freeHomIntAddEquiv,
    freeHomDiscreteEquiv]
  rw [Adjunction.homEquiv_naturality_right]
  simp only [Equiv.trans_apply, GrothendieckTopology.yonedaEquiv_comp,
    ← Functor.map_comp]
  rfl

end LightCondensed.Solid
