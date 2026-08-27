/- GID: D5/S3/Observer/ProbabilisticClosure/GraphMechanismLawSeparation
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/GraphMechanismLawSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One graph has distinct mechanisms; opposite graphs share one Bool PMF. -/
/- Library-search audit trail (2026-08-25):
   * The repository's `ObservationInterventionSeparation` supplies the exact two-node
     `CausalDirection`, `DeterministicBoolSCM`, `Obs`, and opposite-direction models used here.
   * FPOD 268.1 was read at commit `84ba75047`. Its `CausallyIndependent` predicate concerns
     crosswise recombination of two mechanism readouts; it states neither graph equality nor
     equality of observational laws, so its conclusions cannot imply either witness below.
   * Pinned Mathlib supplies `PMF.uniformOfFintype` and `PMF.map`. `SimpleGraph` is undirected,
     while `Quiver` supplies arrows but no matching SCM/law theorem; neither is imported.
   * Searches in D5 and pinned Mathlib found no theorem combining both required separations.
     There is no prime parameter, and primality is not used.
-/

import D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
import Mathlib.Probability.Distributions.Uniform

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.GraphMechanismLawSeparation

open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation

/-- The explicit fair exogenous law used by both observational models. -/
def fairNoise : PMF Bool :=
  PMF.uniformOfFintype Bool

/-- The observational law is the pushforward of the fair Boolean noise by `Obs`. -/
def observationalLaw (model : DeterministicBoolSCM) : PMF (Bool × Bool) :=
  fairNoise.map (Obs model)

/-- On the fixed graph `X -> Y`, keep the identity root and flip the child bit. -/
def flippedChildModel : DeterministicBoolSCM where
  direction := .xCausesY
  root := id
  child := fun bit => !bit

/-- The fixed graph `X -> Y` carries two genuinely different child mechanisms.
The distinguishing input is `false`: identity returns `false`, while flipping returns `true`. -/
theorem same_graph_supports_distinct_mechanisms :
    xCausesYModel.direction = flippedChildModel.direction ∧
      xCausesYModel.child ≠ flippedChildModel.child := by
  constructor
  · rfl
  · intro mechanismsEqual
    have false_eq_true : false = true := by
      simpa [xCausesYModel, flippedChildModel] using congrFun mechanismsEqual false
    exact Bool.false_ne_true false_eq_true
#print axioms same_graph_supports_distinct_mechanisms

/-- The two opposite two-node DAGs are distinct, but their identity mechanisms push the same
fair Boolean noise to the same joint observational PMF on `(X, Y)`. -/
theorem opposite_graphs_same_observational_law :
    xCausesYModel.direction ≠ yCausesXModel.direction ∧
      observationalLaw xCausesYModel = observationalLaw yCausesXModel := by
  constructor
  · intro directionsEqual
    exact CausalDirection.noConfusion directionsEqual
  · rfl
#print axioms opposite_graphs_same_observational_law

section DegenerateAudit

-- On an empty node carrier every mechanism-shaped function is equal, so the first contrast dies.
example {O : Type*} (left right : Empty -> O) : left = right := by
  funext input
  exact input.elim

-- A one-node edgeless graph can still carry distinct constant mechanisms with distinct outputs.
example :
    (fun _ : Unit => false) ≠ (fun _ : Unit => true) ∧
      (fun _ : Unit => false) () ≠ (fun _ : Unit => true) () := by
  constructor
  · intro mechanismsEqual
    exact Bool.false_ne_true (congrFun mechanismsEqual ())
  · exact Bool.false_ne_true

-- In contrast, all loopless directed graphs on one node coincide with the empty-edge graph.
example
    (left right : { edge : Unit -> Unit -> Prop // forall v, Not (edge v v) }) :
    left = right := by
  apply Subtype.ext
  funext source target
  cases source
  cases target
  apply propext
  constructor
  · intro edge
    exact (left.property () edge).elim
  · intro edge
    exact (right.property () edge).elim

-- Thus one node retains the same-graph mechanism contrast but not the different-DAG contrast.
-- The no-edge case is already represented by the preceding one-node specialization.
-- Identity mechanisms are used in both same-law models; constant mechanisms are audited above.
-- There is no depth, sample-size, or prime index parameter, so `n = 0` and primality do not apply.

end DegenerateAudit

/-!
Hypothesis audit, declaration by declaration:

* `same_graph_supports_distinct_mechanisms` is closed and has no hypotheses or instance
  parameters. Both direction equality and the separating input are proved in the conclusion.
* `opposite_graphs_same_observational_law` is closed and has no hypotheses or instance
  parameters. The canonical `Fintype Bool` and `Nonempty Bool` instances occur only while defining
  `fairNoise`; they are not theorem assumptions.

There are therefore no necessary theorem hypotheses needing separate named counterexamples.
-/

end D5.S3.Observer.ProbabilisticClosure.GraphMechanismLawSeparation

namespace D5.S3.Observer.ProbabilisticClosure.GraphMechanismLawSeparation

open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation

section DegenerateAuditContinuation

-- Constant mechanisms coincide when their constant outputs coincide; distinct constants, as in
-- the earlier one-node example, remain distinguishable. Thus constancy alone causes no collapse.
example (output : Bool) :
    (fun _ : Unit => output) = (fun _ : Unit => output) := by
  rfl

-- Both identity models send every input to `(u, u)`. Hence their pushforwards agree for every
-- common noise law, not only for the fair law used by `observationalLaw`.
example (noise : PMF Bool) :
    noise.map (Obs xCausesYModel) = noise.map (Obs yCausesXModel) := by
  rfl

-- The point mass at `false` is nonuniform, but the two directions still give the same law.
example :
    (PMF.pure false).map (Obs xCausesYModel) =
        (PMF.pure false).map (Obs yCausesXModel) ∧
      (PMF.pure false : PMF Bool) false ≠ (PMF.pure false : PMF Bool) true := by
  constructor
  · rfl
  · simp [PMF.pure_apply]

-- Unequal observational laws arise here only after changing another input to the pushforward.
-- For example, distinct exogenous laws yield point masses at distinct diagonal observations.
example :
    (PMF.pure false).map (Obs xCausesYModel) ≠
      (PMF.pure true).map (Obs yCausesXModel) := by
  intro lawsEqual
  have supportEqual := congrArg (fun law : PMF (Bool × Bool) => law.support) lawsEqual
  simp [PMF.pure_map, Obs, xCausesYModel, yCausesXModel] at supportEqual

end DegenerateAuditContinuation

end D5.S3.Observer.ProbabilisticClosure.GraphMechanismLawSeparation
