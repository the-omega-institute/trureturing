/- GID: D5/S3/HomologicalAlgebra/Solid/Supplier/SingularProjective
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/Supplier/SingularProjective
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, reproduced in the native repository LICENSE.
Original source notice referred to src/licenses/LICENSE.LeanCondensed.

Uses the protected challenge definitions and the frozen CWSolid checkpoint.
The singular-chain coproduct argument follows CWSolid.SingularSolid; its inputs
are Mathlib's proved simplicial chain-complex comparison and projectivity API.
-/
import D5.S3.HomologicalAlgebra.Solid.Early
import D5.S3.HomologicalAlgebra.Solid.SingularSolid
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

noncomputable section
open CategoryTheory Limits LightCondensed Opposite
open scoped Simplicial

namespace CWComparison

/-- Evaluation at the one-point test space preserves epimorphisms. A local lift
can be restricted along a constant section of its surjective covering map. -/
instance underlying_preservesEpimorphisms :
    (LightCondensed.underlying (ModuleCat.{0} ℤ)).PreservesEpimorphisms where
  preserves {X Y} f hf := by
    apply (ModuleCat.epi_iff_surjective _).2
    change Function.Surjective (f.hom.app (op (LightProfinite.of PUnit.{1})))
    intro y
    let S : LightProfinite := LightProfinite.of PUnit.{1}
    obtain ⟨T, φ, hφ, x, hx⟩ :=
      (LightCondMod.epi_iff_locallySurjective_on_lightProfinite ℤ f).1 hf S y
    obtain ⟨t, _⟩ := hφ PUnit.unit
    let s : S ⟶ T := ConcreteCategory.ofHom ⟨fun _ => t, continuous_const⟩
    have hs : s ≫ φ = 𝟙 S := by
      ext a
    refine ⟨X.obj.map s.op x, ?_⟩
    change f.hom.app (op S) (X.obj.map s.op x) = y
    rw [LightCondMod.hom_naturality_apply, hx]
    change (Y.obj.map φ.op ≫ Y.obj.map s.op) y = y
    rw [← Functor.map_comp, ← op_comp, hs, op_id, CategoryTheory.Functor.map_id]
    rfl

/-- A projective integral module stays projective as a discrete light condensed group. -/
instance discrete_projective (M : ModuleCat.{0} ℤ) [Projective M] :
    Projective ((LightCondensed.discrete (ModuleCat ℤ)).obj M) :=
  (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).map_projective M inferInstance

end CWComparison

namespace LightCondensed.Solid

/-- Every protected singular chain group is projective in the ambient category,
for arbitrary spaces and with no finite-dimensionality restriction. -/
instance singularChainGroup_projective (X : TopCat) (n : ℕ) :
    Projective ((singularChainsDiscreteFunctor.obj X).X n) := by
  let F := LightCondensed.discrete (ModuleCat ℤ)
  let S := TopCat.toSSet.obj X
  have : F.IsLeftAdjoint := (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).isLeftAdjoint
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let R := ModuleCat.of ℤ ℤ
  change Projective (F.obj ((S.chainComplex R).X n))
  let e : F.obj ((S.chainComplex R).X n) ≅
      ∐ (fun _ : S.obj (.op ⦋n⦌) => F.obj R) :=
    (isColimitCofanMkObjOfIsColimit F (fun _ : S.obj (.op ⦋n⦌) => R)
      (fun x : S.obj (.op ⦋n⦌) => S.ιChainComplex (R := R) x)
      (S.isColimitChainComplexXCofan R n)).coconePointUniqueUpToIso
        (coproductIsCoproduct (fun _ : S.obj (.op ⦋n⦌) => F.obj R))
  have : Projective IntProof.Zdisc := CWComparison.discrete_projective (ModuleCat.of ℤ ℤ)
  apply Projective.of_iso e.symm
  let A : S.obj (.op ⦋n⦌) → LightCondAb := fun _ => IntProof.Zdisc
  change Projective (∐ A)
  refine ⟨fun {E B} f q _ => ?_⟩
  refine ⟨Sigma.desc (fun b => Projective.factorThru (Sigma.ι A b ≫ f) q), ?_⟩
  apply Sigma.hom_ext
  intro b
  simp

/-- Reindexing the protected chains gives a K-projective object of the actual
unbounded cochain-complex category. This is a property of this complex only;
it does not assert existence of K-projective resolutions for all complexes. -/
instance singularChainsComplex_isKProjective (X : TopCat) :
    CochainComplex.IsKProjective (singularChainsLightCondAbComplexFunctor.obj X) :=
  inferInstanceAs (CochainComplex.IsKProjective
    ((singularChainsDiscreteFunctor.obj X).extend ComplexShape.embeddingDownNat))

/-- Projectivity also holds in each cohomological degree, including the zero
terms introduced by the protected extension convention. -/
instance singularChainsComplex_term_projective (X : TopCat) (i : ℤ) :
    Projective ((singularChainsLightCondAbComplexFunctor.obj X).X i) := by
  let K := singularChainsDiscreteFunctor.obj X
  change Projective ((K.extend ComplexShape.embeddingDownNat).X i)
  by_cases hi : ∃ n, ComplexShape.embeddingDownNat.f n = i
  · obtain ⟨n, hn⟩ := hi
    exact Projective.of_iso (K.extendXIso ComplexShape.embeddingDownNat hn).symm
      (singularChainGroup_projective X n)
  · exact (K.isZero_extend_X ComplexShape.embeddingDownNat i
      (fun n hn => hi ⟨n, hn⟩)).projective

/-- Each chain group of the solid lift is projective in the actual solid
category, because the exact fully faithful inclusion preserves epimorphisms. -/
instance singularChainsSolidComplex_term_projective (X : TopCat) (i : ℤ) :
    Projective ((singularChainsSolidComplexFunctor.obj X).X i) :=
  isSolid.ι.projective_of_map_projective (singularChainsComplex_term_projective X i)

instance singularChainsSolidComplex_isStrictlyLE (X : TopCat) :
    (singularChainsSolidComplexFunctor.obj X).IsStrictlyLE 0 := by
  rw [← CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff _ isSolid.ι]
  exact inferInstanceAs
    (CochainComplex.IsStrictlyLE
      ((singularChainsDiscreteFunctor.obj X).extend ComplexShape.embeddingDownNat) 0)

/-- The singular solid lift is K-projective in the full unbounded category. -/
instance singularChainsSolidComplex_isKProjective (X : TopCat) :
    CochainComplex.IsKProjective (singularChainsSolidComplexFunctor.obj X) :=
  CochainComplex.isKProjective_of_projective _ 0

/-- Morphisms from protected singular chains into any derived object represented
in the homotopy category are precisely homotopy classes of chain maps. -/
theorem singularChains_Qh_map_bijective (X : TopCat)
    (K : HomotopyCategory LightCondAb (.up ℤ)) :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient LightCondAb (.up ℤ)).obj
        (singularChainsLightCondAbComplexFunctor.obj X) ⟶ K) → _) :=
  CochainComplex.IsKProjective.Qh_map_bijective _ _

end LightCondensed.Solid
