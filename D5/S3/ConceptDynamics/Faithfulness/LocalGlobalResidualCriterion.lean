/- GID: D5/S3/ConceptDynamics/Faithfulness/LocalGlobalResidualCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Faithfulness/LocalGlobalResidualCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Residual emptiness is equivalent to joint-readout injectivity. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/- Library-search audit trail (2026-08-26):
   * Name and body-shape searches for a dependent family readout found the
     canonical `jointReadout`; it is imported rather than redeclared.
   * Exact repository hit `joint_faithfulness_tfae` identifies joint-readout
     injectivity with point separation and is applied below. Its diagonal-set
     clause does not itself state emptiness of the source's dependent residual.
   * Pinned Mathlib searches found the generic `List.TFAE.out` projection but
     no theorem constructing this distinct-indistinguishable sigma type. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Faithfulness.LocalGlobalResidualCriterion

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/-- The local-global residual is constructed as the dependent type of a pair
of distinct states with equal readings at every coordinate. It is empty
exactly when the canonical joint readout is injective. -/
theorem local_global_residual_empty_iff_joint_injective
    {I X : Type*} {Output : I -> Type*}
    (readout : forall i, X -> Output i) :
    IsEmpty {pair : X × X //
        pair.1 ≠ pair.2 /\ forall i, readout i pair.1 = readout i pair.2} <->
      Function.Injective (jointReadout readout) := by
  have residual_isEmpty_iff_separates :
      IsEmpty {pair : X × X //
          pair.1 ≠ pair.2 /\ forall i, readout i pair.1 = readout i pair.2} <->
        forall x y, (forall i, readout i x = readout i y) -> x = y := by
    constructor
    · intro residualEmpty x y allEqual
      by_contra different
      exact residualEmpty.false ⟨(x, y), different, allEqual⟩
    · intro separates
      exact IsEmpty.mk fun pair :
          {pair : X × X // pair.1 ≠ pair.2 /\
            forall i, readout i pair.1 = readout i pair.2} =>
        pair.property.1
          (separates pair.1.1 pair.1.2 pair.property.2)
  exact residual_isEmpty_iff_separates.trans
    ((joint_faithfulness_tfae readout).out 1 0)

#print axioms local_global_residual_empty_iff_joint_injective

end D5.S3.ConceptDynamics.Faithfulness.LocalGlobalResidualCriterion
