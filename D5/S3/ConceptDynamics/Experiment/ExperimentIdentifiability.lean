/- GID: D5/S3/ConceptDynamics/Experiment/ExperimentIdentifiability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/ExperimentIdentifiability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Experimental identifiability is target factorization through the joint readout. -/

import D5.S0.Rewriting.Quotients.AnswerabilityCriterion
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'identifiable_tfae' D5 Golden/Frozen/accepted` found no existing
     declaration.
   * Repository searches found `joint_faithfulness_tfae`, whose kernel intersection
     must equal the diagonal, and `target_recovery_criterion`, which treats one
     nondependent readout. Neither states target-relative identifiability for a
     dependent experiment family.
   * Exact pinned-Mathlib hit `Function.factorsThrough_iff` underlies the imported
     `answerability_criterion`; that criterion supplies factorization from fiber
     constancy. The proof below additionally translates the family quantifier into
     membership in the imported `jointKernel`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiment.ExperimentIdentifiability

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w z

/-- The kernel of a target readout, represented as a set of state pairs. -/
def targetKernel {X : Type v} {Y : Type z} (target : X -> Y) : Set (X × X) :=
  {pair | target pair.1 = target pair.2}

/-- On an inhabited state space, a target is identifiable from an experiment family
exactly when it factors through the joint readout, equivalently when the experiments'
joint kernel is contained in the target kernel. This is the target-relative version of
joint faithfulness: choosing the identity target reduces kernel containment to equality
with the diagonal. -/
theorem identifiable_tfae {S : Type u} {X : Type v} {Response : S -> Type w}
    {Y : Type z} [Nonempty X] (experiment : forall u, X -> Response u)
    (target : X -> Y) :
    List.TFAE
      [Exists fun factor : (forall u, Response u) -> Y =>
          target = factor ∘ jointReadout experiment,
        jointKernel experiment ⊆ targetKernel target,
        forall x y, (forall u, experiment u x = experiment u y) -> target x = target y] := by
  let anchor : X := Classical.choice (inferInstance : Nonempty X)
  have criterion :=
    D5.S0.Rewriting.Quotients.AnswerabilityCriterion.answerability_criterion
      anchor (jointReadout experiment) target
  have factorCriterion :
      (Exists fun factor : (forall u, Response u) -> Y =>
          target = factor ∘ jointReadout experiment) ↔
        forall x y,
          (forall u, experiment u x = experiment u y) -> target x = target y := by
    constructor
    · intro factorization x y indistinguishable
      apply criterion.1.mp factorization
      funext u
      exact indistinguishable u
    · intro fiberConstant
      apply criterion.1.mpr
      intro x y sameReadout
      apply fiberConstant x y
      intro u
      exact congrFun sameReadout u
  tfae_have 1 → 3 := factorCriterion.mp
  tfae_have 3 → 1 := factorCriterion.mpr
  tfae_have 2 → 3 := by
    intro kernelContained x y indistinguishable
    change (x, y) ∈ targetKernel target
    apply kernelContained
    apply Set.mem_iInter.2
    intro u
    exact indistinguishable u
  tfae_have 3 → 2 := by
    intro fiberConstant pair hPair
    apply fiberConstant pair.1 pair.2
    intro u
    exact Set.mem_iInter.1 hPair u
  tfae_finish

/-- One identity experiment on `Bool` identifies the identity target. -/
example :
    (Exists fun factor : (forall _ : Unit, Bool) -> Bool =>
      (id : Bool -> Bool) = factor ∘ jointReadout (fun _ : Unit => id)) ∧
    jointKernel (fun _ : Unit => (id : Bool -> Bool)) ⊆
      targetKernel (id : Bool -> Bool) ∧
    (forall x y : Bool, (forall _ : Unit, id x = id y) -> id x = id y) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun responses => responses (), ?_⟩
    rfl
  · intro pair hPair
    change pair.1 = pair.2
    exact Set.mem_iInter.1 hPair ()
  · intro x y indistinguishable
    exact indistinguishable ()

/-- A constant experiment on `Bool` fails all three criteria for the identity target. -/
example :
    (¬Exists fun factor : (forall _ : Unit, Unit) -> Bool =>
      (id : Bool -> Bool) = factor ∘
        jointReadout (fun _ : Unit => fun _ : Bool => ())) ∧
    ¬jointKernel (fun _ : Unit => fun _ : Bool => ()) ⊆
      targetKernel (id : Bool -> Bool) ∧
    ¬(forall x y : Bool,
      (forall _ : Unit, (fun _ : Bool => ()) x = (fun _ : Bool => ()) y) ->
        id x = id y) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨factor, factorization⟩
    apply Bool.false_ne_true
    calc
      false = factor (jointReadout (fun _ : Unit => fun _ : Bool => ()) false) :=
        congrFun factorization false
      _ = factor (jointReadout (fun _ : Unit => fun _ : Bool => ()) true) := by rfl
      _ = true := (congrFun factorization true).symm
  · intro kernelContained
    apply Bool.false_ne_true
    change (false, true) ∈ targetKernel (id : Bool -> Bool)
    apply kernelContained
    apply Set.mem_iInter.2
    intro u
    rfl
  · intro fiberConstant
    exact Bool.false_ne_true (fiberConstant false true (fun _ => rfl))

#print axioms identifiable_tfae

end D5.S3.ConceptDynamics.Experiment.ExperimentIdentifiability
