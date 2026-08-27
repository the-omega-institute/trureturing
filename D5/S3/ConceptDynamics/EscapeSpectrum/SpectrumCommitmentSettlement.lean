/- GID: D5/S3/ConceptDynamics/EscapeSpectrum/SpectrumCommitmentSettlement
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/EscapeSpectrum/SpectrumCommitmentSettlement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A five-atom spectrum commitment settles by its fixed decisive-vote threshold. -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/- Library-search audit trail (2026-08-27):
   * Exact D5 searches for `SpectrumCommitment`,
     `spectrum_commitment_local_settlement`, `decisiveCount`, and a fixed
     cutoff verdict found no existing declaration. The nearby adjudication
     modules model versioned lookup and regrading, not this five-atom local
     count-and-threshold settlement.
   * Pinned Mathlib provides `Finset.filter`, `Finset.card`, the `Fin 5`
     fintype, and standard `if` simplification. `card_filter_le` is the
     closest named counting lemma, but the exact threshold equivalences here
     reduce directly from the fixed prediction function. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentSettlement

/-- Research states available before the fixed evidence cutoff. -/
inductive ResearchState
  | open
  | proved
  | refuted
  | statementRevised
  | invalid
  deriving DecidableEq

/-- The total prediction verdict emitted at the fixed cutoff. -/
inductive CommitmentVerdict
  | success
  | failure
  deriving DecidableEq

/-- The local seven-field commitment record. Its comparator and prediction
fields are executable because they determine the fixed-cutoff settlement. -/
structure SpectrumCommitment
    (AtomFamily Scope Baseline WeightSpec TestPlan : Type*) where
  atomFamily : AtomFamily
  scope : Scope
  baseline : Baseline
  weightSpec : WeightSpec
  comparator : ResearchState -> Bool
  testPlan : TestPlan
  falsifiablePrediction : Nat -> CommitmentVerdict

/-- Missing evidence is terminally invalid at the cutoff; no open state
survives terminalization. -/
def ResearchState.terminalize : ResearchState -> ResearchState
  | .open => .invalid
  | state => state

/-- Only proof and refutation states contribute decisive votes. -/
def ResearchState.isDecisive : ResearchState -> Bool
  | .proved | .refuted => true
  | .open | .statementRevised | .invalid => false

/-- Number of decisive terminal states among the five frozen parent atoms. -/
def decisiveCount
    (comparator : ResearchState -> Bool)
    (states : Fin 5 -> ResearchState) : Nat :=
  (Finset.univ.filter fun atom =>
    comparator (ResearchState.terminalize (states atom))).card

/-- The preregistered prediction succeeds exactly at three decisive votes. -/
def fixedCutoffPrediction (count : Nat) : CommitmentVerdict :=
  if 3 <= count then .success else .failure

/-- The DESC-local instance keeps the five-atom family and the descriptive
fields supplied by the caller, while freezing its comparator and prediction. -/
def localSpectrumCommitment
    {AtomFamily Scope Baseline WeightSpec TestPlan : Type*}
    (atomFamily : AtomFamily) (scope : Scope) (baseline : Baseline)
    (weightSpec : WeightSpec) (testPlan : TestPlan) :
    SpectrumCommitment AtomFamily Scope Baseline WeightSpec TestPlan where
  atomFamily := atomFamily
  scope := scope
  baseline := baseline
  weightSpec := weightSpec
  comparator := ResearchState.isDecisive
  testPlan := testPlan
  falsifiablePrediction := fixedCutoffPrediction

/-- Settle a commitment from the terminalized states of its five parent atoms. -/
def localSettlement
    {AtomFamily Scope Baseline WeightSpec TestPlan : Type*}
    (commitment :
      SpectrumCommitment AtomFamily Scope Baseline WeightSpec TestPlan)
    (states : Fin 5 -> ResearchState) : CommitmentVerdict :=
  commitment.falsifiablePrediction
    (decisiveCount commitment.comparator states)

/-- At the fixed cutoff, open states become invalid, proved and refuted states
are the only decisive votes, and the five-atom commitment has exactly the two
preregistered verdict branches: success at three or more votes and failure
below three. -/
theorem spectrum_commitment_local_settlement
    {AtomFamily Scope Baseline WeightSpec TestPlan : Type*}
    (atomFamily : AtomFamily) (scope : Scope) (baseline : Baseline)
    (weightSpec : WeightSpec) (testPlan : TestPlan)
    (states : Fin 5 -> ResearchState) :
    let commitment := localSpectrumCommitment
      atomFamily scope baseline weightSpec testPlan
    (forall atom, ResearchState.terminalize (states atom) != .open) /\
      (localSettlement commitment states = .success <->
        3 <= decisiveCount commitment.comparator states) /\
      (localSettlement commitment states = .failure <->
        decisiveCount commitment.comparator states < 3) := by
  dsimp only
  constructor
  case left =>
    intro atom
    cases states atom <;> simp [ResearchState.terminalize]
  case right =>
    constructor <;> simp [localSettlement, localSpectrumCommitment,
      fixedCutoffPrediction]

/- Three proved parent atoms meet the fixed success threshold. -/
example :
    let commitment := localSpectrumCommitment (fun atom : Fin 5 => atom)
      () () () ()
    localSettlement commitment
        (fun atom => if atom.val < 3 then .proved else .invalid) =
      .success := by
  decide

/- Two decisive parent atoms remain below the fixed success threshold. -/
example :
    let commitment := localSpectrumCommitment (fun atom : Fin 5 => atom)
      () () () ()
    localSettlement commitment
        (fun atom => if atom.val < 2 then .refuted else .statementRevised) =
      .failure := by
  decide

#print axioms spectrum_commitment_local_settlement

end D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentSettlement
