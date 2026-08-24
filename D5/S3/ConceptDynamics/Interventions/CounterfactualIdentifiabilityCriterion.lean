/- GID: D5/S3/ConceptDynamics/Interventions/CounterfactualIdentifiabilityCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interventions/CounterfactualIdentifiabilityCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A counterfactual is determined by all single-world marginals exactly when it is constant on every coupling fiber, while two Boolean SCMs witness nonidentifiability. -/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'counterfactual_identifiable_iff_constant_on_fiber' D5
     Golden/Frozen/accepted` returned no match.
   * Public repository hits `AnswerabilityCriterion.answerability_criterion` and
     `EmpiricalIdentifiability.empirical_identifiability` give adjacent general
     descent criteria, but neither models a joint coupling's intervention-indexed
     marginal projection. No relevant private declaration was found.
   * All eight existing digests in `ConceptDynamics/Interventions` were read.
     `InterventionCounterfactualSeparation` provides the exact public Boolean SCM
     witness reused below; none states the coupling-fiber criterion.
   * Exact pinned-Mathlib hit `Function.factorsThrough_iff` proves the general
     factorization/fiber-constancy equivalence and is applied directly below.
     Its `Nonempty Value` premise supplies the arbitrary value outside the image.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion

open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation

/-- The fiber of all couplings whose observable marginal data equal `data`. -/
def couplingFiber {Coupling Data : Type*} (marginals : Coupling -> Data)
    (data : Data) : Set Coupling :=
  {coupling | marginals coupling = data}

/-- A target factors through its observable data exactly when it is constant on
each fiber. Nonemptiness supplies an arbitrary target value outside the image. -/
theorem counterfactual_identifiable_iff_constant_on_fiber
    {Coupling Data Value : Type*} [Nonempty Value]
    (marginals : Coupling -> Data) (Q : Coupling -> Value) :
    (Exists fun f : Data -> Value => Q = f ∘ marginals) <->
      forall c c', marginals c = marginals c' -> Q c = Q c' := by
  simpa only [Function.FactorsThrough] using
    (Function.factorsThrough_iff (f := marginals) Q).symm

/-- In the finite Boolean model, a coupling is a joint structural causal model. -/
abbrev BooleanCoupling := DeterministicBoolSCM

/-- An intervention marginal counts each Boolean outcome in the two-unit population. -/
abbrev BooleanMarginal := Bool -> Nat

/-- Projection from a joint Boolean SCM to the marginal under one intervention. -/
def booleanMarginal (coupling : BooleanCoupling) (intervention : Bool) :
    BooleanMarginal :=
  Int coupling intervention

/-- The observable data consist of one marginal for every intervention. -/
def allSingleWorldMarginals (coupling : BooleanCoupling) : Bool -> BooleanMarginal :=
  fun intervention => booleanMarginal coupling intervention

/-- For Boolean SCMs, identifiability from all single-world intervention marginals
is equivalent to constancy on every explicitly represented coupling fiber. -/
theorem boolean_counterfactual_identifiable_iff_constant_on_coupling_fibers
    {Value : Type*} [Nonempty Value] (Q : BooleanCoupling -> Value) :
    (Exists fun f : (Bool -> BooleanMarginal) -> Value =>
        Q = f ∘ allSingleWorldMarginals) <->
      forall (mu : Bool -> BooleanMarginal) (M N : BooleanCoupling),
        M ∈ couplingFiber allSingleWorldMarginals mu ->
          N ∈ couplingFiber allSingleWorldMarginals mu -> Q M = Q N := by
  constructor
  · intro factorization mu M N hM hN
    apply
      (counterfactual_identifiable_iff_constant_on_fiber
        allSingleWorldMarginals Q).mp factorization M N
    exact hM.trans hN.symm
  · intro constantOnFibers
    apply
      (counterfactual_identifiable_iff_constant_on_fiber
        allSingleWorldMarginals Q).mpr
    intro M N hsame
    exact constantOnFibers (allSingleWorldMarginals M) M N rfl hsame.symm

/-- Two Boolean joint models occupy one intervention-marginal fiber but have
different complete unit-level counterfactual tables. -/
theorem boolean_counterfactual_varies_on_coupling_fiber :
    Exists fun mu : Bool -> BooleanMarginal =>
      Exists fun M : BooleanCoupling =>
        Exists fun N : BooleanCoupling =>
          M ∈ couplingFiber allSingleWorldMarginals mu /\
            N ∈ couplingFiber allSingleWorldMarginals mu /\ CF M ≠ CF N := by
  rcases intervention_strictly_weaker_than_counterfactual with
    ⟨M, N, hMarginals, hCounterfactual⟩
  refine ⟨allSingleWorldMarginals M, M, N, rfl, ?_, hCounterfactual⟩
  funext intervention
  exact congrFun hMarginals.symm intervention

/-- The complete Boolean unit-level counterfactual table cannot be recovered
from the family of all single-world intervention marginals. -/
theorem boolean_counterfactual_not_identifiable :
    Not (Exists fun f : (Bool -> BooleanMarginal) ->
      (Bool -> Bool -> Bool -> Bool) => CF = f ∘ allSingleWorldMarginals) := by
  intro factorization
  have constantOnFibers :=
    (boolean_counterfactual_identifiable_iff_constant_on_coupling_fibers CF).mp
      factorization
  rcases boolean_counterfactual_varies_on_coupling_fiber with
    ⟨mu, M, N, hM, hN, hDifferent⟩
  exact hDifferent (constantOnFibers mu M N hM hN)

/-- Empty couplings make fiber constancy vacuous, while an inhabited data type cannot
map into an empty value type. Thus the nonempty-value assumption is necessary. -/
theorem nonempty_value_is_necessary :
    let marginals : Empty -> Unit := fun coupling => coupling.elim
    let Q : Empty -> Empty := fun coupling => coupling.elim
    Q.FactorsThrough marginals ∧
      ¬∃ f : Unit -> Empty, Q = f ∘ marginals := by
  dsimp [Function.FactorsThrough]
  constructor
  · intro coupling
    exact coupling.elim
  · rintro ⟨factor, _factors⟩
    exact (factor ()).elim

example :
    noEffectModel ∈ couplingFiber allSingleWorldMarginals
      (allSingleWorldMarginals noEffectModel) :=
  rfl

example :
    Not (Exists fun f : (Bool -> BooleanMarginal) ->
      (Bool -> Bool -> Bool -> Bool) => CF = f ∘ allSingleWorldMarginals) :=
  boolean_counterfactual_not_identifiable

#print axioms counterfactual_identifiable_iff_constant_on_fiber
#print axioms nonempty_value_is_necessary

end D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
