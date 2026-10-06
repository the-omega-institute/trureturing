/- GID: D5/S3/HomologicalAlgebra/Solid/Early
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/Early
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import Mathlib
import D5.S3.HomologicalAlgebra.Solid.Definitions
import D5.S3.HomologicalAlgebra.Solid.Reflection
/-!
# Derived solidification of free CW complexes

This challenge is extracted from the LeanCondensed project
<https://github.com/dagurtomas/LeanCondensed>, which develops the theory of light condensed
mathematics of Clausen–Scholze in Lean.  The target statement is the comparison theorem for a CW
complex `X`: the homology of the derived solidification of the free light condensed abelian group
on `X` is integral singular homology.

The non-`sorry` part of this file develops, using only Mathlib, the definition of
*light solid abelian groups*: a light condensed abelian group `A` is solid if the map
`1 - shift` on the free light condensed abelian group `P = ℤ[ℕ∪{∞}]/ℤ[∞]` induces an isomorphism
on internal homs into `A`.  The full subcategory `Solid` of solid objects is closed under limits,
kernels, cokernels and finite products, hence abelian, and the inclusion into light condensed
abelian groups is exact, so it induces a functor on derived categories.

The `sorry`ed declarations (the holes of this multi-hole problem) are:

* `solidification` — the solidification functor `LightCondAb ⥤ Solid`;
* `solidification_additive` — additivity of the solidification functor;
* `solidificationAdjunction` — solidification is left adjoint to the inclusion;
* `derivedSolidification` — the derived solidification functor
  `DerivedCategory LightCondAb ⥤ DerivedCategory Solid`;
* `derivedSolidificationCounit` — the comparison map exhibiting `derivedSolidification` as a
  functor under degreewise solidification;
* `derivedSolidification_isLeftDerivedFunctor` — `derivedSolidification` is the total left
  derived functor of degreewise solidification;
* `derivedSolidificationAdjunction` — derived solidification is left adjoint to the derived
  inclusion;
* `derivedSolidificationFreeCWFunctor` — the functor on CW complexes whose values are the derived
  inclusion of the derived solidification of the free light condensed abelian group;
* `derivedSolidificationFreeCWFunctorSpec` — an isomorphism identifying
  `derivedSolidificationFreeCWFunctor` with the expected composite functor;
* `derivedSolidification_free_CW_derivedNatIso` — naturally in a CW complex `X`, the derived
  inclusion of the derived solidification of `ℤ[X]` is isomorphic in the derived category of light
  condensed abelian groups to the integral singular chain complex of `X`, viewed as a complex of
  discrete light condensed abelian groups with homological degree `n` placed in cohomological
  degree `-n`, this is the main challenge;
* `derivedSolidification_free_CW_homologyIso` — for a CW complex `X`, the homology of the derived
  solidification of `ℤ[X]` is integral singular homology (the derived category is cohomologically
  indexed, so the `n`-th singular homology group appears in degree `-n`);
* `derivedSolidification_free_CW_homology` — the theorem form of the previous isomorphism.

All holes must be filled compatibly: the adjunctions and derived functor property pin down
`solidification` and `derivedSolidification` up to natural isomorphism, so the final derived
comparison theorem and its pointwise homology form have their intended mathematical content.

Note that the LeanCondensed project contains significant progress towards some of the earlier holes
in this challenge.
-/

open CategoryTheory Limits LightProfinite OnePoint LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace LightProfinite



end LightProfinite

namespace LightCondensed



























/-- The class expressing that a light condensed abelian group is solid. -/
abbrev IsSolid (A : LightCondAb) := isSolid.Is A



namespace Solid



































/-- **Hole 1.** The solidification functor, left adjoint to the inclusion of solid objects. -/
def solidification : LightCondAb ⥤ Solid := isSolid.ι.leftAdjoint

/-- **Hole 2.** The solidification functor is additive.  (This follows from the adjunction of the
next hole, but is needed as an instance to state the holes below.) -/
instance solidification_additive : solidification.Additive :=
  (Adjunction.ofIsRightAdjoint isSolid.ι).left_adjoint_additive

/-- **Hole 3.** The solidification adjunction: solidification is left adjoint to the inclusion of
solid objects in light condensed abelian groups. -/
def solidificationAdjunction : solidification ⊣ isSolid.ι := .ofIsRightAdjoint _


end Solid
end LightCondensed
end
