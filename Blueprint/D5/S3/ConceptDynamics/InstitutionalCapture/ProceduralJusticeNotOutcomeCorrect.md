# Procedural Justice Does Not Guarantee a Correct Outcome

## Abstract

A judgment can use all public facts and rules yet be wrong when their joint readout does not determine truth.

**Lemma 1.1 (A defective public join makes every procedural judgment incorrect).**

$$\forall Case \in Type, Fact \in Type, Rule \in Type, Verdict \in Type, anchor \in Case, facts \in \operatorname{Concept}\left(Case, Fact\right), rules \in \operatorname{Concept}\left(Case, Rule\right), truth \in \operatorname{Concept}\left(Case, Verdict\right),\; \operatorname{Nonempty}\left(\operatorname{defectRelation}\left(\operatorname{conceptJoin}\left(facts, rules\right), truth\right)\right) \Rightarrow \left(\forall judgment \in \operatorname{Concept}\left(Case, Verdict\right),\; \operatorname{ProcedurallyComplete}\left(facts, rules, judgment\right) \Rightarrow \left(\exists case \in Case,\; judgment\left(case\right) \ne truth\left(case\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InstitutionalCapture/ProceduralJusticeNotOutcomeCorrect.every_procedurally_complete_judgment_is_incorrect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On an inhabited case space, a nonempty defect in the joint facts-and-rules readout gives two publicly indistinguishable cases with different truth values.

Every procedurally complete judgment factors through that joint readout, so it cannot distinguish the defective pair. If it agreed with truth on every case, truth would factor through the same readout, contrary to the defect. Thus each such judgment is wrong somewhere.

**Lemma 1.2 (A sufficient public join permits a correct procedural judgment).**

$$\forall Case \in Type, Fact \in Type, Rule \in Type, Verdict \in Type, facts \in \operatorname{Concept}\left(Case, Fact\right), rules \in \operatorname{Concept}\left(Case, Rule\right), truth \in \operatorname{Concept}\left(Case, Verdict\right),\; \operatorname{Refines}\left(truth, \operatorname{conceptJoin}\left(facts, rules\right)\right) \Rightarrow \left(\exists judgment \in \operatorname{Concept}\left(Case, Verdict\right),\; \operatorname{ProcedurallyComplete}\left(facts, rules, judgment\right) \land \operatorname{OutcomeCorrect}\left(truth, judgment\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InstitutionalCapture/ProceduralJusticeNotOutcomeCorrect.sufficient_joint_readout_permits_correct_outcome` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When factual truth factors through the joint facts-and-rules readout, truth itself can serve as the judgment. The factorization makes that judgment procedurally complete, while choosing truth makes it outcome-correct.

**Theorem 1.3 (Procedural completeness can coexist with unavoidable error).**

$$\exists facts \in \operatorname{Concept}\left(Bool, PUnit\right), rules \in \operatorname{Concept}\left(Bool, PUnit\right), truth \in \operatorname{Concept}\left(Bool, Bool\right), judgment \in \operatorname{Concept}\left(Bool, Bool\right),\; \operatorname{Nonempty}\left(\operatorname{defectRelation}\left(\operatorname{conceptJoin}\left(facts, rules\right), truth\right)\right) \land \left(\operatorname{ProcedurallyComplete}\left(facts, rules, judgment\right) \land \left(\left(\exists case \in Bool,\; judgment\left(case\right) \ne truth\left(case\right)\right) \land \left(\forall candidate \in \operatorname{Concept}\left(Bool, Bool\right),\; \operatorname{ProcedurallyComplete}\left(facts, rules, candidate\right) \Rightarrow \left(\exists case \in Bool,\; candidate\left(case\right) \ne truth\left(case\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InstitutionalCapture/ProceduralJusticeNotOutcomeCorrect.procedural_completeness_permits_wrong_outcome` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take Boolean cases, let both public readouts be constant, let truth be the identity, and let the exhibited judgment always return false. The judgment is a function of the public join but disagrees with truth at the true case.

The false and true cases have the same public facts and rules but opposite truth values, so they form a defect of the joint readout. The general obstruction then shows more than one mistaken judgment: every procedurally complete Boolean judgment must fail on some case.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InstitutionalCapture/ProceduralJusticeNotOutcomeCorrect.every_procedurally_complete_judgment_is_incorrect`
- Truth anchor: `D5/S3/ConceptDynamics/InstitutionalCapture/ProceduralJusticeNotOutcomeCorrect.procedural_completeness_permits_wrong_outcome`
- Truth anchor: `D5/S3/ConceptDynamics/InstitutionalCapture/ProceduralJusticeNotOutcomeCorrect.sufficient_joint_readout_permits_correct_outcome`
- Dependency: [D5/S0/Rewriting/Quotients/AnswerabilityCriterion](../../../S0/Rewriting/Quotients/AnswerabilityCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
