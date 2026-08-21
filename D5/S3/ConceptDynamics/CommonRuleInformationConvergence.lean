/- GID: D5/S3/ConceptDynamics/CommonRuleInformationConvergence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/CommonRuleInformationConvergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Correct common facts align a shared rule, while distinct rules can still disagree. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition

/- Library-search audit trail (2026-08-21):
   * Searches of D5 and the active frozen ledger for common-rule convergence,
     shared decisions, and post-disclosure disagreement found no exact theorem.
   * Repository theorem `informed_disclosure_defect` is adjacent: it concerns a
     disclosure collision and recovery of unequal consequences, not distinct
     decision functions applied after one fact value is fully disclosed.
   * Exact pinned-Mathlib hit `congrArg` transports equality of the two correct
     fact values through the shared decision rule and is applied directly.
   * `Function.FactorsThrough` is an adjacent abstraction, but it does not state
     either the common-rule or the distinct-rule conclusion packaged here.
   * The `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CommonRuleInformationConvergence

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- Correct fact values produce the same decision under one deterministic rule.
By contrast, two rules that differ at a fully disclosed target value continue
to produce different decisions at the corresponding source state. -/
theorem common_rule_information_convergence
    {X Z U : Type*} (target : Concept X Z)
    (sharedRule leftRule rightRule : Z -> U) :
    (forall (x : X) (leftFact rightFact : Z),
      leftFact = target x ->
      rightFact = target x ->
      sharedRule leftFact = sharedRule rightFact) ∧
      (forall (x : X) (disclosedFact : Z),
        target x = disclosedFact ->
        leftRule disclosedFact ≠ rightRule disclosedFact ->
        leftRule (target x) ≠ rightRule (target x)) := by
  constructor
  · intro x leftFact rightFact hleft hright
    exact congrArg sharedRule (hleft.trans hright.symm)
  · intro x disclosedFact hdisclosed hdifferent
    simpa only [hdisclosed] using hdifferent

/-- The source, fact, and decision domains can all be inhabited. -/
example : Concept Bool Bool := id

/-- The public conditions are simultaneously realized by Boolean facts: the
shared identity rule agrees on correct facts, while identity and a constant
rule disagree after the fact `true` is disclosed. -/
example :
    let target : Concept Bool Bool := id
    let sharedRule : Bool -> Bool := id
    let leftRule : Bool -> Bool := id
    let rightRule : Bool -> Bool := fun _ => false
    (sharedRule (target true) = sharedRule (target true)) ∧
      leftRule (target true) ≠ rightRule (target true) := by
  decide

/-- Without equal fact values, even a shared rule need not align decisions. -/
example : (id : Bool -> Bool) false ≠ id true := Bool.false_ne_true

#print axioms common_rule_information_convergence

end D5.S3.ConceptDynamics.CommonRuleInformationConvergence
