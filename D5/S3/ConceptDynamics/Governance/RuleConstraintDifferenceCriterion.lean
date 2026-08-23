/- GID: D5/S3/ConceptDynamics/Governance/RuleConstraintDifferenceCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Governance/RuleConstraintDifferenceCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Rule factorization excludes arbitrary differences, with a finite effective converse. -/

import D5.S0.Rewriting.Quotients.AnswerabilityCriterion
import Mathlib.Data.Fintype.Basic

/- Library-search audit trail (2026-08-23):
   * Exact repository hit
     `D5.S0.Rewriting.Quotients.AnswerabilityCriterion.answerability_criterion`
     characterizes factorization by constancy on readout fibers and is applied directly
     in the inhabited branch of the converse.
   * The nearby frozen theorem `MoralLuckDescent.moral_luck_descent_iff` has the same
     structural pattern for control and evaluation, but its global finite hypotheses do
     not preserve the source's unrestricted forward clause.
   * Exact pinned-Mathlib hits `Function.FactorsThrough` and
     `Function.factorsThrough_iff` underlie the imported criterion. Repository and active
     frozen-ledger searches found no existing rule-constraint declaration or atom coverage. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Governance.RuleConstraintDifferenceCriterion

/-- Rule factorization always excludes a pair with equal public attributes and unequal
decisions. Conversely, when all carriers are finite and the public attribute readout is
effective (surjective), absence of such a pair yields a public rule factorization. -/
theorem rule_constraint_difference_criterion
    {X B Y : Type*} (publicReadout : X -> B) (decision : X -> Y) :
    ((exists rule : B -> Y, decision = rule ∘ publicReadout) ->
      Not (exists x y,
        publicReadout x = publicReadout y /\ Ne (decision x) (decision y))) /\
    (forall [Fintype X] [Fintype B] [Fintype Y],
      Function.Surjective publicReadout ->
      Not (exists x y,
        publicReadout x = publicReadout y /\ Ne (decision x) (decision y)) ->
      exists rule : B -> Y, decision = rule ∘ publicReadout) := by
  constructor
  · rintro ⟨rule, factors⟩ ⟨x, y, sameAttribute, differentDecision⟩
    apply differentDecision
    calc
      decision x = rule (publicReadout x) := congrFun factors x
      _ = rule (publicReadout y) := congrArg rule sameAttribute
      _ = decision y := (congrFun factors y).symm
  · intro _finiteX _finiteB _finiteY effective noDifference
    classical
    cases isEmpty_or_nonempty X with
    | inl emptyX =>
        letI : IsEmpty X := emptyX
        refine ⟨fun b => isEmptyElim (Classical.choose (effective b)), ?_⟩
        funext x
        exact isEmptyElim x
    | inr nonemptyX =>
        letI : Nonempty X := nonemptyX
        let anchor : X := Classical.choice nonemptyX
        apply ((D5.S0.Rewriting.Quotients.AnswerabilityCriterion.answerability_criterion
          anchor publicReadout decision).1).mpr
        intro x y sameAttribute
        by_contra differentDecision
        exact noDifference ⟨x, y, sameAttribute, differentDecision⟩

/-- Identity attributes and decisions satisfy the finite effective converse. -/
example : exists rule : Bool -> Bool, id = rule ∘ id := by
  apply (rule_constraint_difference_criterion
    (id : Bool -> Bool) (id : Bool -> Bool)).2 Function.surjective_id
  rintro ⟨x, y, sameAttribute, differentDecision⟩
  exact differentDecision sameAttribute

/-- A constant public attribute and identity decision exhibit the forbidden difference. -/
example :
    exists x y : Bool,
      (fun _ : Bool => ()) x = (fun _ : Bool => ()) y /\ Ne (id x) (id y) := by
  exact ⟨false, true, rfl, Bool.false_ne_true⟩

#print axioms rule_constraint_difference_criterion

end D5.S3.ConceptDynamics.Governance.RuleConstraintDifferenceCriterion
