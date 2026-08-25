/- GID: D5/S3/Estimation/DecisionRisk/LawRepresentationCanonicalQuotient
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/LawRepresentationCanonicalQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A law-determining representation refines the canonical law quotient. -/

import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-25):
   * No D5 theorem combines arbitrary law factorization with both canonical
     equality-kernel quotient clauses.
   * The adjacent experiment-state theorem contains the quotient clauses but
     has unrelated posterior content and no representation premise.
   * Pinned Mathlib's `Setoid.kerLift_injective` and `Quotient.lift_comp_mk`
     are the exact canonical quotient results applied below. This module
     introduces no definition or abbreviation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DecisionRisk.LawRepresentationCanonicalQuotient

/-- If a representation determines the complete experiment law, equality of
representations implies equality of laws. The equality-kernel quotient of that
same law carries an injective lifted law and reconstructs the original law by
composition with its canonical projection. -/
theorem law_determining_representation_refines_canonical_law_quotient
    {State Representation Law : Type*}
    (law : State → Law)
    (representation : State → Representation)
    (decodeLaw : Representation → Law)
    (factors : law = decodeLaw ∘ representation) :
    (∀ x y, representation x = representation y → law x = law y) ∧
      Function.Injective (Setoid.kerLift law) ∧
      law = Setoid.kerLift law ∘
        (Quotient.mk'' : State → Quotient (Setoid.ker law)) := by
  constructor
  · intro x y equalRepresentation
    simpa only [factors, Function.comp_apply] using
      congrArg decodeLaw equalRepresentation
  constructor
  · exact Setoid.kerLift_injective law
  · simpa only [Setoid.kerLift, Quotient.mk''_eq_mk] using
      (Quotient.lift_comp_mk law (fun _ _ equalLaw => equalLaw)).symm

#print axioms law_determining_representation_refines_canonical_law_quotient

end D5.S3.Estimation.DecisionRisk.LawRepresentationCanonicalQuotient
