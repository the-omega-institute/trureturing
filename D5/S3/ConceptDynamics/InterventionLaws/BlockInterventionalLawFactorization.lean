/- GID: D5/S3/ConceptDynamics/InterventionLaws/BlockInterventionalLawFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InterventionLaws/BlockInterventionalLawFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Independent block responses yield product intervention laws and edge audits. -/

/- Library-search audit trail (2026-08-25):
   * Six repository searches covered object names, Mathlib names, digests, the
     nearby intervention modules, generalized measure shapes, and causal,
     measure-theoretic, and information-theoretic vocabulary. No existing
     declaration identifies a block intervention law with its product marginals.
   * The exact predecessor `blockInterventionalOutcome` and the accompanying
     response/quotient decomposition are imported instead of reconstructed.
   * Pinned Mathlib exact hit `iIndepFun.map_fun_eq_pi_map` states that the joint
     pushforward of a finite independent family is `Measure.pi` of its marginal
     pushforwards; it is applied directly. `Measure.pi_of_empty` and
     `iIndepFun.of_subsingleton` discharge the empty and one-block audits.
   * `loogle` and `leansearch` executables are absent from PATH. The local
     type-shape search also inspected `iIndepFun_iff_map_fun_eq_pi_map` and
     `iIndepFun.hasLaw_pi`; neither already carries the intervention semantics. -/

import D5.S3.ConceptDynamics.Interventions.BlockCausalQuotientDecomposition
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace D5.S3.ConceptDynamics.InterventionLaws.BlockInterventionalLawFactorization

open D5.S3.ConceptDynamics.Interventions.BlockCausalQuotientDecomposition

/-- The joint post-intervention law is the pushforward of the source law by all
block responses assembled through the existing block outcome map. -/
def blockInterventionalLaw
    {I Omega : Type*} {Action State : I -> Type*}
    [MeasurableSpace Omega] [forall i, MeasurableSpace (State i)]
    (source : Measure Omega) (intervention : forall i, Action i)
    (model : forall i, Action i -> Omega -> State i) : Measure (forall i, State i) :=
  source.map fun omega i => blockInterventionalOutcome intervention model i omega

/-- The local post-intervention law in one block, under the same source law. -/
def localInterventionalLaw
    {I Omega : Type*} {Action State : I -> Type*}
    [MeasurableSpace Omega] [forall i, MeasurableSpace (State i)]
    (source : Measure Omega) (intervention : forall i, Action i)
    (model : forall i, Action i -> Omega -> State i) (i : I) : Measure (State i) :=
  source.map (blockInterventionalOutcome intervention model i)

/-- Probability-level block independence means that every intervened response
is a random variable and the finite family of those responses is independent. -/
def BlockIndependent
    {I Omega : Type*} {Action State : I -> Type*}
    [MeasurableSpace Omega] [forall i, MeasurableSpace (State i)]
    (source : Measure Omega) (intervention : forall i, Action i)
    (model : forall i, Action i -> Omega -> State i) : Prop :=
  (forall i, AEMeasurable (blockInterventionalOutcome intervention model i) source) /\
    iIndepFun (blockInterventionalOutcome intervention model) source

#print axioms blockInterventionalLaw
#print axioms localInterventionalLaw
#print axioms BlockIndependent

/-- Mutually independent block responses make the joint intervention law the
finite product of the local intervention laws. -/
theorem block_interventional_law_factorization
    {I Omega : Type*} {Action State : I -> Type*} [Fintype I]
    [MeasurableSpace Omega] [forall i, MeasurableSpace (State i)]
    (source : Measure Omega) (intervention : forall i, Action i)
    (model : forall i, Action i -> Omega -> State i)
    (independent : BlockIndependent source intervention model) :
    blockInterventionalLaw source intervention model =
      Measure.pi (localInterventionalLaw source intervention model) := by
  exact independent.2.map_fun_eq_pi_map independent.1

#print axioms block_interventional_law_factorization

/-- With one block, independence and the product factorization are automatic
once that block response is a random variable. -/
theorem single_block_factorization_witness
    {Omega Action State : Type*} [MeasurableSpace Omega] [MeasurableSpace State]
    (source : Measure Omega) [IsProbabilityMeasure source]
    (intervention : Unit -> Action) (model : Unit -> Action -> Omega -> State)
    (measurableResponse : AEMeasurable (model () (intervention ())) source) :
    BlockIndependent source intervention model /\
      blockInterventionalLaw source intervention model =
        Measure.pi (localInterventionalLaw source intervention model) := by
  have independent : BlockIndependent source intervention model := by
    constructor
    · intro i
      simpa [blockInterventionalOutcome] using measurableResponse
    · exact iIndepFun.of_subsingleton
  exact ⟨independent,
    block_interventional_law_factorization source intervention model independent⟩

#print axioms single_block_factorization_witness

/-- The empty block family has the unique empty tuple as its law, so its product
decomposition is the Dirac measure at that tuple. -/
theorem empty_block_factorization_witness :
    blockInterventionalLaw (I := Empty) (Action := fun _ => Unit)
        (State := fun _ => Unit) (Measure.dirac ()) isEmptyElim isEmptyElim =
      Measure.dirac isEmptyElim := by
  have independent : BlockIndependent (I := Empty) (Action := fun _ => Unit)
      (State := fun _ => Unit) (Measure.dirac ()) isEmptyElim isEmptyElim := by
    exact ⟨isEmptyElim, iIndepFun.of_subsingleton⟩
  rw [block_interventional_law_factorization _ _ _ independent]
  exact Measure.pi_of_empty _ _

#print axioms empty_block_factorization_witness

/-- A two-block response with the directed edge `false -> true`: the left block
reads the first of two fair exogenous coordinates and the right block copies it. -/
def directedEdgeResponse : Bool -> Unit -> Bool × Bool -> Bool
  | false => fun _ exogenous => exogenous.1
  | true => fun _ exogenous => exogenous.1

/-- Block independence is necessary: the concrete directed-edge model has a
one-half diagonal mass, while the product of its fair marginals has mass one quarter. -/
theorem block_independence_is_necessary :
    let source := (PMF.uniformOfFintype (Bool × Bool)).toMeasure
    let intervention := fun _ : Bool => ()
    Not (BlockIndependent source intervention directedEdgeResponse) /\
      Not (blockInterventionalLaw source intervention directedEdgeResponse =
        Measure.pi (localInterventionalLaw source intervention directedEdgeResponse)) := by
  dsimp only
  have measurableEdge (i : Bool) : Measurable (directedEdgeResponse i ()) := by
    cases i <;> exact measurable_fst
  have jointPreimage :
      (fun exogenous i => directedEdgeResponse i () exogenous) ⁻¹'
          ({fun _ => true} : Set (Bool -> Bool)) =
        {exogenous : Bool × Bool | exogenous.1 = true} := by
    ext exogenous
    rcases exogenous with ⟨first, second⟩
    cases first <;> cases second <;> simp [directedEdgeResponse, funext_iff]
  have localPreimage (i : Bool) :
      directedEdgeResponse i () ⁻¹' ({true} : Set Bool) =
        {exogenous : Bool × Bool | exogenous.1 = true} := by
    ext exogenous
    rcases exogenous with ⟨first, second⟩
    cases i <;> cases first <;> cases second <;> simp [directedEdgeResponse]
  letI (i : Bool) : IsProbabilityMeasure
      (localInterventionalLaw (PMF.uniformOfFintype (Bool × Bool)).toMeasure
        (fun _ : Bool => ()) directedEdgeResponse i) :=
    Measure.isProbabilityMeasure_map (measurableEdge i).aemeasurable
  have lawMismatch :
      Not (blockInterventionalLaw (PMF.uniformOfFintype (Bool × Bool)).toMeasure
        (fun _ : Bool => ()) directedEdgeResponse =
          Measure.pi (localInterventionalLaw (PMF.uniformOfFintype (Bool × Bool)).toMeasure
            (fun _ : Bool => ()) directedEdgeResponse)) := by
    intro lawsEqual
    have atAllTrue := congrArg
      (fun law : Measure (Bool -> Bool) => law {fun _ => true}) lawsEqual
    rw [blockInterventionalLaw, Measure.map_apply (by fun_prop)
      (measurableSet_singleton _)] at atAllTrue
    simp only [blockInterventionalOutcome] at atAllTrue
    rw [jointPreimage] at atAllTrue
    rw [Measure.pi_singleton] at atAllTrue
    simp only [localInterventionalLaw, blockInterventionalOutcome] at atAllTrue
    simp_rw [Measure.map_apply (measurableEdge _) (measurableSet_singleton true)] at atAllTrue
    simp_rw [localPreimage] at atAllTrue
    norm_num [directedEdgeResponse, PMF.toMeasure_apply_fintype,
      PMF.uniformOfFintype_apply, Fintype.card_prod, Fintype.card_bool,
      Fintype.sum_prod_type, Fintype.sum_bool, Set.indicator] at atAllTrue
    have realEquality := congrArg ENNReal.toReal atAllTrue
    norm_num [ENNReal.toReal_add] at realEquality
  constructor
  · intro independent
    exact lawMismatch
      (block_interventional_law_factorization _ _ _ independent)
  · exact lawMismatch

#print axioms directedEdgeResponse
#print axioms block_independence_is_necessary

section DegenerateAudit

-- A constant zero response on the one-block index gives the trivial product law.
example :
    blockInterventionalLaw (I := Unit) (Action := fun _ => Unit)
        (State := fun _ => Nat) (Measure.dirac ()) (fun _ => ())
          (fun _ _ _ => 0) =
      Measure.pi (localInterventionalLaw (I := Unit) (Action := fun _ => Unit)
        (State := fun _ => Nat) (Measure.dirac ()) (fun _ => ())
          (fun _ _ _ => 0)) := by
  exact (single_block_factorization_witness (Measure.dirac ())
    (fun _ => ()) (fun _ _ _ => 0) (by fun_prop)).2

-- The identity response is likewise the one-coordinate product of its own law.
example :
    blockInterventionalLaw (I := Unit) (Action := fun _ => Unit)
        (State := fun _ => Bool) (PMF.uniformOfFintype Bool).toMeasure
          (fun _ => ()) (fun _ _ source => source) =
      Measure.pi (localInterventionalLaw (I := Unit) (Action := fun _ => Unit)
        (State := fun _ => Bool) (PMF.uniformOfFintype Bool).toMeasure
          (fun _ => ()) (fun _ _ source => source)) := by
  exact (single_block_factorization_witness (PMF.uniformOfFintype Bool).toMeasure
    (fun _ => ()) (fun _ _ source => source) (by fun_prop)).2

-- There is no repetition count or depth parameter, so an `n = 0` case is inapplicable.

end DegenerateAudit

/-!
Hypothesis audit:

* `block_interventional_law_factorization` uses both fields of `BlockIndependent`:
  measurability supplies `map_fun_eq_pi_map`'s first argument, and mutual independence supplies
  the theorem receiver. `Fintype` and the measurable-space instances are definitionally required
  by the finite product and pushforward APIs. No nonempty action, explicit probability, algebraic,
  decidable-equality, or positivity hypothesis is present.
* `single_block_factorization_witness` uses its probability instance in
  `iIndepFun.of_subsingleton` and its measurability hypothesis for the only response.
* `empty_block_factorization_witness` and `block_independence_is_necessary` have no hypotheses.
  The latter is the named concrete counterexample showing the sole substantive premise cannot be
  removed: its responses are measurable, but the cross-block directed edge destroys independence
  and the product-law equality.
-/

end D5.S3.ConceptDynamics.InterventionLaws.BlockInterventionalLawFactorization
