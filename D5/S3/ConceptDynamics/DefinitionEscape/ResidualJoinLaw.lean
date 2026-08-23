/- GID: D5/S3/ConceptDynamics/DefinitionEscape/ResidualJoinLaw
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/ResidualJoinLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joining one definition retains exactly the target residual pairs in its kernel. -/

import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/- Library-search audit trail (2026-08-24):
   * `rg -n "ResidualPair|residual_join|TargetResidual|residual.*join|join.*residual|
     redundant.*definition|DefinitionEscape" D5` found no addressable theorem
     stating the target-residual intersection law.
   * `rg -n "Setoid\\.ker.*conceptJoin|ker \\(conceptJoin|conceptJoin.*Setoid\\.ker|
     ker.*inf" D5` found the accepted joint-kernel conjunct in
     `ConceptKernelOrderDuality.concept_kernel_order_duality`. That conjunct
     requires both coordinate types in one universe, while the statement below
     preserves the source's unrestricted, independently universe-polymorphic
     coordinate types; the complete residual equality is not supplied there.
   * `rg -n -U "defectRelation\\s*\\n?\\s*\\(conceptJoin|defectRelation
     \\(conceptJoin" D5` found consumers of joined defects and the private
     `fullDefect` proof inside `BlindKernelObstruction`, but no public theorem
     with the complete equality below.
   * `rg -n "Setoid\\.ker.*Prod|Setoid\\.ker.*prod|ker_prod|prod.*kernel|
     kernel.*prod" .lake/packages/mathlib/Mathlib --glob '*.lean'` found only
     algebraic, linear, filter, and probability-kernel product results, not an
     equality-kernel law for arbitrary functions. The companion search
     `rg -n "defectRelation.*conceptJoin|conceptJoin.*defectRelation|
     residual.*intersection.*kernel|intersection.*kernel.*residual"
     .lake/packages/mathlib/Mathlib --glob '*.lean'` exited 1 with no hits.
   * Exact atom-id search outside the digestion ledger and source documentation
     missed. The proof reuses the repository's canonical `Concept`,
     `conceptJoin`, `defectRelation`, and `Setoid.ker` declarations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- Joining a definition to the current readout leaves exactly those target
residual pairs on which the new definition still agrees. -/
theorem residual_join_law
    {X C D Target : Type*} (q : Concept X C) (d : Concept X D)
    (target : Concept X Target) :
    defectRelation (conceptJoin q d) target =
      defectRelation q target ∩
        {pair : X × X | Setoid.ker d pair.1 pair.2} := by
  ext pair
  change
    (conceptJoin q d pair.1 = conceptJoin q d pair.2 ∧
        target pair.1 ≠ target pair.2) ↔
      (q pair.1 = q pair.2 ∧ target pair.1 ≠ target pair.2) ∧
        Setoid.ker d pair.1 pair.2
  constructor
  · rintro ⟨sameJoin, differentTarget⟩
    have sameBaseline := congrArg Prod.fst sameJoin
    have sameDefinition := congrArg Prod.snd sameJoin
    exact ⟨⟨sameBaseline, differentTarget⟩, sameDefinition⟩
  · rintro ⟨⟨sameBaseline, differentTarget⟩, sameDefinition⟩
    exact ⟨Prod.ext sameBaseline sameDefinition, differentTarget⟩

/-- Constant baseline and definition readouts leave a nonempty Boolean target
residual, providing an inhabited, nonvacuous instance of the public law. -/
example :
    (defectRelation
        (conceptJoin (fun _ : Bool => ()) (fun _ : Bool => false))
        (id : Concept Bool Bool) =
      defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) ∩
        {pair : Bool × Bool |
          Setoid.ker (fun _ : Bool => false) pair.1 pair.2}) ∧
    (false, true) ∈
      defectRelation
        (conceptJoin (fun _ : Bool => ()) (fun _ : Bool => false))
        (id : Concept Bool Bool) := by
  constructor
  · exact residual_join_law
      (fun _ : Bool => ()) (fun _ : Bool => false) (id : Concept Bool Bool)
  · exact ⟨rfl, Bool.false_ne_true⟩

#print axioms residual_join_law

end D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw
