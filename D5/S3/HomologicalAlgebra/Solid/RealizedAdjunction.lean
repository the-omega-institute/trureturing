/- GID: D5/S3/HomologicalAlgebra/Solid/RealizedAdjunction
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/RealizedAdjunction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.DerivedRealization

/-!
Copyright (c) 2026. Released under the Apache 2.0 license.
The genuine unbounded adjunction into the protected D(Solid), obtained
from the proved realization equivalence and the actual local reflector.
The right adjoint is exactly the protected derivedInclusion.
-/

noncomputable section
open CategoryTheory

namespace LightCondensed.Solid

def realizedDerivedSolidification : DLightCondAb ⥤ DSolid :=
  solidDerivedLocalReflection ⋙ derivedSolidLocalEquivalence.inverse

/-- The actual adjunction has no existence, realization or full-faithfulness
premise. Its equivalence is constructed by the unbounded resolution proof. -/
def realizedDerivedSolidificationAdjunction :
    realizedDerivedSolidification ⊣ derivedInclusion :=
  (solidDerivedLocalReflectionAdjunction.comp
    derivedSolidLocalEquivalence.symm.toAdjunction).ofNatIsoRight
      derivedInclusionToLocalCompIso

end LightCondensed.Solid

#print axioms LightCondensed.Solid.realizedDerivedSolidification
#print axioms LightCondensed.Solid.realizedDerivedSolidificationAdjunction
