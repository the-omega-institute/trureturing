/- GID: D5/S3/ConceptDynamics/Coding/AdaptiveResidueIdentification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/AdaptiveResidueIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A four-state modular model has adaptive depth two and static depth three. -/

import D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Batteries.Data.BitVec.Lemmas
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/- Library-search audit trail (2026-08-24):
   * Exact current-tree hit `FiberBinaryIdentification.BinaryProtocol` supplies
     the canonical finite binary protocol and is imported rather than redeclared.
     Its arbitrary-question existence theorem does not restrict questions to a
     supplied observation family and therefore does not prove this example.
   * Exact current-tree hit `JointFaithfulnessLeibnizCriterion.jointReadout`
     supplies the dependent fixed-suite readout used by the static cost test.
   * Repository searches for adaptive identification, decision-tree costs, fixed
     sensor-suite costs, and the explicit four-state modular model found no exact
     theorem or sibling cost primitive.
   * Exact pinned-Mathlib hits `Nat.find_eq_iff` and `BitVec.getLsb_ofFnLE`
     support minima over the source tests and the explicit transcript. No packaged
     adaptive-identification result was found. `loogle` and `leansearch` are absent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification

open D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/-- The source's exact four-state carrier. -/
abbrev ResidueState :=
  {value : Nat // value ∈ ({0, 10, 15, 21} : Finset Nat)}

-- Lean 4.33's stricter type check breaks mathlib's `Fintype` deriving handler.
section
set_option backward.isDefEq.respectTransparency.types false

/-- The three available modular sensors. -/
inductive ResidueSensor
  | two
  | three
  | five
  deriving DecidableEq, Fintype

end

/-- The modulus represented by a sensor. -/
def sensorModulus : ResidueSensor -> Nat
  | .two => 2
  | .three => 3
  | .five => 5

/-- On the source carrier, each selected modular observation has value zero or one. -/
def residueReadout (sensor : ResidueSensor) (state : ResidueState) : Bool :=
  decide (state.1 % sensorModulus sensor = 1)

def zeroState : ResidueState := ⟨0, by decide⟩
def tenState : ResidueState := ⟨10, by decide⟩
def fifteenState : ResidueState := ⟨15, by decide⟩
def twentyOneState : ResidueState := ⟨21, by decide⟩

/-- Every question at every history is one of the supplied readouts. -/
def UsesReadoutFamily {Sensor State : Type*} {depth : Nat}
    (readout : Sensor -> State -> Bool) (protocol : BinaryProtocol State depth) : Prop :=
  forall round history, exists sensor,
    protocol.question round history = readout sensor

/-- The source test for exact adaptive identification at a given depth. -/
def ExactAtDepth {Sensor State : Type*} (readout : Sensor -> State -> Bool)
    (depth : Nat) : Prop :=
  exists protocol : BinaryProtocol State depth,
    UsesReadoutFamily readout protocol ∧ Function.Injective protocol.transcript

/-- The source test for an injective fixed suite of a given cardinality. -/
def StaticExactAtCardinality {Sensor State : Type*}
    (readout : Sensor -> State -> Bool) (cardinality : Nat) : Prop :=
  exists suite : Finset Sensor, suite.card = cardinality ∧
    Function.Injective (jointReadout (fun sensor : suite => readout sensor.1))

/-- The transcript of the explicit adaptive protocol: first sensor two, followed
by sensor three on the zero branch and sensor five on the one branch. -/
def adaptiveTranscript (state : ResidueState) : BitVec 2 :=
  BitVec.ofFnLE fun round =>
    if round.1 = 0 then residueReadout .two state
    else if residueReadout .two state then residueReadout .five state
    else residueReadout .three state

/-- The history-indexed question selector for the explicit protocol. -/
def adaptiveQuestion (round : Fin 2) (history : Fin round.1 -> Bool) :
    ResidueState -> Bool :=
  if hzero : round.1 = 0 then residueReadout .two
  else if history ⟨0, Nat.pos_of_ne_zero hzero⟩ then residueReadout .five
  else residueReadout .three

/-- The source-constructed two-round adaptive protocol. -/
def adaptiveProtocol : BinaryProtocol ResidueState 2 where
  transcript := adaptiveTranscript
  question := adaptiveQuestion
  transcript_consistent := by
    intro state round
    by_cases hzero : round.1 = 0
    · simp [adaptiveTranscript, adaptiveQuestion, hzero]
    · have hone : round.1 = 1 := by omega
      by_cases hreadout : residueReadout .two state = true
      · simp [adaptiveTranscript, adaptiveQuestion, hone, hreadout]
      · simp [adaptiveTranscript, adaptiveQuestion, hone, hreadout]

private theorem adaptive_protocol_uses_readouts :
    UsesReadoutFamily residueReadout adaptiveProtocol := by
  intro round history
  by_cases hzero : round.1 = 0
  · exact ⟨.two, by simp [adaptiveProtocol, adaptiveQuestion, hzero] <;> rfl⟩
  · by_cases hone : history ⟨0, Nat.pos_of_ne_zero hzero⟩
    · exact ⟨.five, by simp [adaptiveProtocol, adaptiveQuestion, hzero, hone] <;> rfl⟩
    · exact ⟨.three, by simp [adaptiveProtocol, adaptiveQuestion, hzero, hone] <;> rfl⟩

private theorem adaptive_protocol_exact :
    Function.Injective adaptiveProtocol.transcript := by
  rintro ⟨left, hleft⟩ ⟨right, hright⟩ hequal
  have hzero := congrArg
    (fun bits : BitVec 2 => bits.getLsb ⟨0, by decide⟩) hequal
  have hone := congrArg
    (fun bits : BitVec 2 => bits.getLsb ⟨1, by decide⟩) hequal
  simp only [Finset.mem_insert, Finset.mem_singleton] at hleft hright
  rcases hleft with rfl | rfl | rfl | rfl <;>
    rcases hright with rfl | rfl | rfl | rfl <;>
    simp [adaptiveProtocol, adaptiveTranscript, residueReadout, sensorModulus]
      at hzero hone ⊢

private theorem residue_adaptive_exists :
    exists depth, ExactAtDepth residueReadout depth :=
  ⟨2, adaptiveProtocol, adaptive_protocol_uses_readouts, adaptive_protocol_exact⟩

/-- Minimum exact adaptive depth, using exactness and allowed-readout selection as
the minimization test. -/
noncomputable def residueAdaptiveDepth : Nat :=
  by
    classical
    exact Nat.find residue_adaptive_exists

private theorem no_exact_protocol_below_two :
    forall depth, depth < 2 -> ¬ExactAtDepth residueReadout depth := by
  intro depth hdepth
  interval_cases depth
  all_goals
    rintro ⟨protocol, _usesReadouts, injective⟩
    have hcard := Fintype.card_le_of_injective
      (BitVec.equivFin ∘ protocol.transcript)
      (BitVec.equivFin.injective.comp injective)
    have hstateCard : Fintype.card ResidueState = 4 := by decide
    have hcard' := hcard
    simp only [hstateCard, Fintype.card_fin] at hcard'
    norm_num at hcard'

private theorem residue_adaptive_depth_eq_two : residueAdaptiveDepth = 2 := by
  classical
  exact (Nat.find_eq_iff residue_adaptive_exists).2
    ⟨⟨adaptiveProtocol, adaptive_protocol_uses_readouts, adaptive_protocol_exact⟩,
      no_exact_protocol_below_two⟩

private theorem residue_static_exists :
    exists cardinality, StaticExactAtCardinality residueReadout cardinality := by
  refine ⟨3, Finset.univ, by decide, ?_⟩
  decide

/-- Minimum cardinality of an injective fixed suite, using the source's static
joint-readout test. -/
noncomputable def residueStaticDepth : Nat :=
  by
    classical
    exact Nat.find residue_static_exists

private theorem static_suite_not_injective_of_card_lt
    (suite : Finset ResidueSensor) (hcard : suite.card < 3) :
    ¬Function.Injective
      (jointReadout (fun sensor : suite => residueReadout sensor.1)) := by
  intro injective
  by_cases htwo : ResidueSensor.two ∈ suite
  · by_cases hthree : ResidueSensor.three ∈ suite
    · by_cases hfive : ResidueSensor.five ∈ suite
      · have huniv : suite = Finset.univ := by
          ext sensor
          fin_cases sensor <;> simp_all
        have hsuiteCard : suite.card = 3 := by rw [huniv]; decide
        omega
      · apply (show fifteenState ≠ twentyOneState by decide)
        apply injective
        funext sensor
        rcases sensor with ⟨sensor, hsensor⟩
        fin_cases sensor <;>
          simp_all [jointReadout, residueReadout, sensorModulus,
            fifteenState, twentyOneState]
    · apply (show zeroState ≠ tenState by decide)
      apply injective
      funext sensor
      rcases sensor with ⟨sensor, hsensor⟩
      fin_cases sensor <;>
        simp_all [jointReadout, residueReadout, sensorModulus, zeroState, tenState]
  · apply (show zeroState ≠ fifteenState by decide)
    apply injective
    funext sensor
    rcases sensor with ⟨sensor, hsensor⟩
    fin_cases sensor <;>
      simp_all [jointReadout, residueReadout, sensorModulus, zeroState, fifteenState]

private theorem no_static_suite_below_three :
    forall cardinality, cardinality < 3 ->
      ¬StaticExactAtCardinality residueReadout cardinality := by
  rintro cardinality hcardinality ⟨suite, hsuiteCard, injective⟩
  apply static_suite_not_injective_of_card_lt suite
  · omega
  · exact injective

private theorem residue_static_depth_eq_three : residueStaticDepth = 3 := by
  classical
  apply (Nat.find_eq_iff residue_static_exists).2
  constructor
  · refine ⟨Finset.univ, by decide, ?_⟩
    decide
  · exact no_static_suite_below_three

/-- The explicit modular decision tree identifies all four states in two rounds,
while every one-round allowed protocol fails and every static exact suite uses all
three sensors. -/
theorem two_step_adaptive_residue_identification :
    (forall state, residueReadout .two state = false <->
      state = zeroState ∨ state = tenState) ∧
    (forall state, residueReadout .two state = true <->
      state = fifteenState ∨ state = twentyOneState) ∧
    (exists protocol : BinaryProtocol ResidueState 2,
      (forall history : Fin 0 -> Bool,
        protocol.question ⟨0, by decide⟩ history = residueReadout .two) ∧
      (forall history : Fin 1 -> Bool,
        protocol.question ⟨1, by decide⟩ history =
          if history 0 then residueReadout .five else residueReadout .three) ∧
      UsesReadoutFamily residueReadout protocol ∧
      Function.Injective protocol.transcript) ∧
    (forall sensor, ¬Function.Injective (residueReadout sensor)) ∧
    (forall depth, depth < 2 -> ¬ExactAtDepth residueReadout depth) ∧
    residueAdaptiveDepth = 2 ∧
    residueStaticDepth = 3 ∧
    residueAdaptiveDepth < residueStaticDepth := by
  refine ⟨by decide, by decide, ?_, by decide,
    no_exact_protocol_below_two, residue_adaptive_depth_eq_two,
    residue_static_depth_eq_three, ?_⟩
  · refine ⟨adaptiveProtocol, ?_, ?_, adaptive_protocol_uses_readouts,
      adaptive_protocol_exact⟩
    · intro history
      simp [adaptiveProtocol, adaptiveQuestion] <;> rfl
    · intro history
      funext state
      by_cases hbit : history 0 = true <;>
        simp [adaptiveProtocol, adaptiveQuestion, hbit]
  · rw [residue_adaptive_depth_eq_two, residue_static_depth_eq_three]
    omega

#print axioms two_step_adaptive_residue_identification

end D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
