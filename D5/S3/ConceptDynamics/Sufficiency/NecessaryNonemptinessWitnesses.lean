/- GID: D5/S3/ConceptDynamics/Sufficiency/NecessaryNonemptinessWitnesses
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Sufficiency/NecessaryNonemptinessWitnesses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Concrete empty-type witnesses show that target nonemptiness is necessary for fiber-constant factorization and state nonemptiness is necessary for finite-window minimal sufficiency. -/

import D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
import D5.S3.ConceptDynamics.Sufficiency.FiniteWindowMinimalSufficiency

/- Library-search audit trail (2026-08-25):
   * `rg -n -F 'nonempty_value_is_necessary' D5 Golden/Frozen/accepted`
     and the corresponding search for `nonempty_state_is_necessary` returned no hits.
   * The two imported public theorems state the nonempty factorization and finite-window
     results whose hypotheses are tested here; neither contains the concrete empty-type
     counterexample. No relevant private declaration was found.
   * All six existing digests in `ConceptDynamics/Sufficiency` were read; none provides
     either required witness. Pinned Mathlib has no more specific result to reuse, so the
     proofs use only elimination from `Empty`, function application, and subtype projection.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Sufficiency.NecessaryNonemptinessWitnesses

open D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Sufficiency.FiniteWindowMinimalSufficiency
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- Fiber constancy can hold even though no map from the data space factors the target. -/
def FiberConstantButNotFactorizable {Coupling Data Value : Type*}
  (marginals : Coupling -> Data) (Q : Coupling -> Value) : Prop :=
  (forall c c', marginals c = marginals c' -> Q c = Q c') /\
    Not (Exists fun f : Data -> Value => Q = Function.comp f marginals)

/-- The unique observable-data map on an empty coupling space. -/
def emptyMarginals : Empty -> Unit :=
  fun x => nomatch x

/-- The unique empty-valued target on an empty coupling space. -/
def emptyCouplingValue : Empty -> Empty :=
  fun x => nomatch x

/-- With `Coupling = Empty`, `Data = Unit`, and `Value = Empty`, fiber constancy is
vacuous but a factorization would require an impossible function from `Unit` to `Empty`. -/
theorem nonempty_value_is_necessary :
    FiberConstantButNotFactorizable emptyMarginals emptyCouplingValue := by
  constructor
  · intro coupling
    exact Empty.elim coupling
  · rintro ⟨factor, _⟩
    exact Empty.elim (factor ())

/-- The observation from the empty state space into the one-point output space. -/
def emptyObservation : Empty -> Unit :=
  fun x => nomatch x

/-- The unique update of the empty state space. -/
def emptyUpdate : Empty -> Empty :=
  fun x => nomatch x

/-- The full finite-window minimal-sufficiency conclusion for the concrete empty-state model. -/
def EmptyStateFiniteWindowMinimalSufficiency : Prop :=
  (forall i : Fin 1,
    Refines
      (canonicalTargetReadout (orbitTarget emptyObservation emptyUpdate i.1))
      (finiteWindow emptyObservation emptyUpdate 0)) /\
  (forall {C : Type} (p : Concept Empty C),
    (forall i : Fin 1,
      Refines
        (canonicalTargetReadout (orbitTarget emptyObservation emptyUpdate i.1)) p) ->
    Refines (finiteWindow emptyObservation emptyUpdate 0) p)

/-- With `X = Empty` and `O = Unit`, the zero-window carrier is inhabited while the
canonical target image is empty, so the first finite-window sufficiency clause fails. -/
theorem nonempty_state_is_necessary :
    Not EmptyStateFiniteWindowMinimalSufficiency := by
  intro minimalSufficiency
  rcases minimalSufficiency.1 0 with ⟨factor, _⟩
  rcases (factor (fun _ : Fin 1 => ())).property with ⟨state, _⟩
  exact Empty.elim state

example : FiberConstantButNotFactorizable emptyMarginals emptyCouplingValue :=
  nonempty_value_is_necessary

example : Not EmptyStateFiniteWindowMinimalSufficiency :=
  nonempty_state_is_necessary

#print axioms nonempty_value_is_necessary
#print axioms nonempty_state_is_necessary

end D5.S3.ConceptDynamics.Sufficiency.NecessaryNonemptinessWitnesses
