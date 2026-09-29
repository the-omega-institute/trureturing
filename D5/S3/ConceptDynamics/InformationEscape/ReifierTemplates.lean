/- GID: D5/S3/ConceptDynamics/InformationEscape/ReifierTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/ReifierTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pointwise registration descriptor with sensitivity and variation providers. -/

import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- Utility is none: this registration-template provider has no computational content.
namespace D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates
open D5.S3.ConceptDynamics.InformationEscape PointwiseRegistrationTemplates LeanInformationAudit

/-- Uniform source descriptor. Direct carrier parameters retain the source telescope.
The bridge to the existing pointwise template is a proved equivalence. -/
theorem pointwise {X Y : Type} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (f g : X → Y) :
    LegacyPrimitiveRealization (pointwiseEqArena (Arena.ofFintype X) Y)
      (∀ x : X, f x = g x) (pointwiseEqRealization f g) := pointwiseEqLegacy _ _ _

/-- Evidence provider: nondegeneracy supplies a state, Nontrivial supplies outputs. -/
theorem sensitivity {X Y : Type} [Fintype X] [DecidableEq X] [DecidableEq Y]
    [Nontrivial Y] (h : (Arena.ofFintype X).Nondegenerate) :
    FiniteSlotSensitivity (pointwiseEqArena (Arena.ofFintype X) Y) := by
  obtain ⟨x, _, _⟩ := Arena.exists_ne_of_nondegenerate _ h
  obtain ⟨a, b, hab⟩ := exists_pair_ne Y
  exact pointwiseEq_sensitivity _ x a b hab

/-- Arena-indexed variation, from an inhabited readout slot; no enumeration. -/
theorem variation (A : PrimitiveLawArena) (i : A.signature.Index)
    (h : FiniteSlotSensitivity A) : FiniteLawVariation A := by
  classical
  obtain ⟨r, r', _, _, hr⟩ := h.1 i
  by_cases hp : A.Law r
  · exact ⟨r, r', hp, hr.mp hp⟩
  · have hp' : A.Law r' := Classical.byContradiction (fun hn => hp (hr.mpr hn))
    exact ⟨r', r, hp', hp⟩

#print axioms pointwise
#print axioms sensitivity
#print axioms variation

end D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates
