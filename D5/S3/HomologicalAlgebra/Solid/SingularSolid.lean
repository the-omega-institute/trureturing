/- GID: D5/S3/HomologicalAlgebra/Solid/SingularSolid
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/SingularSolid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.DiscreteInt
import D5.S3.HomologicalAlgebra.Solid.Colimits
import D5.S3.HomologicalAlgebra.Solid.ChainHomology

noncomputable section
open CategoryTheory Limits LightCondensed MonoidalClosed
open scoped Simplicial
namespace LightCondensed.Solid

instance solid_closedIsomorphisms : isSolid.IsClosedUnderIsomorphisms where
  of_iso e h := (isSolid_iff_isLocal _).2
    (solidGeneratingMaps.isLocal.prop_of_iso e ((isSolid_iff_isLocal _).1 h))

/-- The homological singular chains after applying the protected discrete functor. -/
abbrev singularChainsDiscreteFunctor : TopCat ⥤ ChainComplex LightCondAb ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)) ⋙
    (LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (.down ℕ)

/-- Discrete integral singular chain groups are solid in every homological degree,
for every topological space. -/
lemma singularChainGroup_isSolid (X : TopCat) (n : ℕ) :
    isSolid ((singularChainsDiscreteFunctor.obj X).X n) := by
  let F := LightCondensed.discrete (ModuleCat ℤ)
  let S := TopCat.toSSet.obj X
  have : F.IsLeftAdjoint := (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).isLeftAdjoint
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let R := ModuleCat.of ℤ ℤ
  change isSolid (F.obj ((S.chainComplex R).X n))
  let e : F.obj ((S.chainComplex R).X n) ≅
      ∐ (fun _ : S.obj (.op ⦋n⦌) => F.obj R) :=
    (isColimitCofanMkObjOfIsColimit F (fun _ : S.obj (.op ⦋n⦌) => R)
      (fun x : S.obj (.op ⦋n⦌) => S.ιChainComplex (R := R) x)
      (S.isColimitChainComplexXCofan R n)).coconePointUniqueUpToIso
        (coproductIsCoproduct (fun _ : S.obj (.op ⦋n⦌) => F.obj R))
  apply isSolid.prop_of_iso e.symm
  exact isSolid_coproduct (fun _ : S.obj (.op ⦋n⦌) => IntProof.Zdisc) (fun _ => isSolid_int)

/-- Every term of the exact protected reindexed singular-chain complex is solid. -/
lemma singularChainsComplex_isSolid (X : TopCat) (i : ℤ) :
    isSolid ((singularChainsLightCondAbComplexFunctor.obj X).X i) := by
  let K := singularChainsDiscreteFunctor.obj X
  change isSolid ((K.extend ComplexShape.embeddingDownNat).X i)
  by_cases hi : ∃ n, ComplexShape.embeddingDownNat.f n = i
  · obtain ⟨n, hn⟩ := hi
    exact isSolid.prop_of_iso (K.extendXIso ComplexShape.embeddingDownNat hn).symm
      (singularChainGroup_isSolid X n)
  · exact isSolid.prop_of_isZero (K.isZero_extend_X ComplexShape.embeddingDownNat i
      (fun n hn => hi ⟨n, hn⟩))

/-- The protected singular chains lift naturally to complexes in the genuine solid category. -/
def singularChainsSolidComplexFunctor : TopCat ⥤ CochainComplex Solid ℤ :=
  HomologicalComplex.liftFunctorObjectProperty isSolid
    singularChainsLightCondAbComplexFunctor singularChainsComplex_isSolid

/-- Forgetting the solid structure recovers the exact protected singular-chain functor. -/
def singularChainsSolidComplexFactors :
    singularChainsSolidComplexFunctor ⋙ isSolid.ι.mapHomologicalComplex (.up ℤ) ≅
      singularChainsLightCondAbComplexFunctor := Iso.refl _

/-- The integral singular chains viewed in the derived category of solid objects. -/
def singularChainsSolidDerivedFunctor : TopCat ⥤ DSolid :=
  singularChainsSolidComplexFunctor ⋙ DerivedCategory.Q

/-- Singular chains naturally lie in the image of the exact derived inclusion, for all spaces.
This proves a prerequisite of the CW comparison, not that comparison itself. -/
def singularChainsSolidDerivedFactors :
    singularChainsSolidDerivedFunctor ⋙ derivedInclusion ≅
      singularChainsLightCondAbDerivedFunctor :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft singularChainsSolidComplexFunctor isSolid.ι.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight singularChainsSolidComplexFactors DerivedCategory.Q

end LightCondensed.Solid
