/- GID: D5/S3/ConceptDynamics/OperationalTuition/PreregisteredArtifactAcceptance
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/OperationalTuition/PreregisteredArtifactAcceptance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Preregistered artifact verification survives a missing envelope and seat death. -/

import D5.S3.ConceptDynamics.OperationalTuition.ArtifactSufficiencyAndKillLoss

/- Library-search audit trail (2026-08-31):
   * Exact repository searches for missing-envelope acceptance, preregistered
     criteria, and inheritable delivery witnesses found no covering declaration.
   * Shape searches found preregistration vocabulary in transport certificates
     and spectrum settlement, but no finite artifact-delivery characterization.
   * The frozen OTT artifact carrier supplies `ToyTrajectory`, `finalState`, and
     independently checkable persistent-artifact states; these are imported
     rather than replaced by a second artifact model.

   Clause echo:
   * Definition 5.1's product is `artifactRun : ToyTrajectory Byte`; its final
     state is independently available to the fixed Boolean verifier.  The
     envelope is a separate optional routing report and never supplies evidence.
   * Criterion precedence is literal list position: `beforeArtifact` is placed
     before the unique `artifactCheckpoint artifactRun` in `deliveryEvents`.
   * T-E's forward direction extracts a finite `PreregisteredAcceptanceWitness`;
     the reverse direction runs the registered verifier without an envelope.
   * `inheritAfterSeatDeath` deletes the envelope and marks the seat dead while
     preserving the finite trace, artifact, and acceptance witness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.OperationalTuition.PreregisteredArtifactAcceptance

open D5.S3.ConceptDynamics.OperationalTuition.ArtifactSufficiencyAndKillLoss

/-- Finite delivery events on either side of the distinguished artifact event. -/
inductive DeliveryEvent (Criterion Byte : Type*) where
  | preregister (criterion : Criterion)
  | artifactCheckpoint (run : ToyTrajectory Byte)
  | auditReadout
deriving DecidableEq

/-- A finite delivery separates the routing envelope from the independently
checkable artifact and records which events precede artifact production. -/
structure DeliveryRecord (Criterion Byte : Type*) where
  beforeArtifact : List (DeliveryEvent Criterion Byte)
  artifactRun : ToyTrajectory Byte
  afterArtifact : List (DeliveryEvent Criterion Byte)
  envelope : Option Bool
  seatAlive : Bool

/-- The complete finite delivery trace, with artifact production at its recorded
boundary. -/
def deliveryEvents {Criterion Byte : Type*}
    (delivery : DeliveryRecord Criterion Byte) : List (DeliveryEvent Criterion Byte) :=
  delivery.beforeArtifact ++
    DeliveryEvent.artifactCheckpoint delivery.artifactRun :: delivery.afterArtifact

/-- The envelope channel supplied no routing report. -/
def EnvelopeMissing {Criterion Byte : Type*}
    (delivery : DeliveryRecord Criterion Byte) : Prop :=
  delivery.envelope = none

/-- An event qualifies an artifact exactly when it is a preregistered criterion
whose fixed verifier accepts the independently computed final artifact state. -/
def qualifyingEvent {Criterion Byte : Type*} [DecidableEq Byte]
    (verify : Criterion -> ToyState Byte -> Bool)
    (artifactRun : ToyTrajectory Byte) : DeliveryEvent Criterion Byte -> Bool
  | .preregister criterion => verify criterion (finalState artifactRun)
  | .artifactCheckpoint _ => false
  | .auditReadout => false

/-- Executable artifact-only judgment over the finite prefix preceding
production. -/
def independentlyAcceptable {Criterion Byte : Type*} [DecidableEq Byte]
    (verify : Criterion -> ToyState Byte -> Bool)
    (delivery : DeliveryRecord Criterion Byte) : Bool :=
  delivery.beforeArtifact.any (qualifyingEvent verify delivery.artifactRun)

/-- The requested finite witness: a concrete criterion was recorded in the
pre-artifact prefix and its fixed verifier accepts the produced artifact. -/
structure PreregisteredAcceptanceWitness {Criterion Byte : Type*}
    [DecidableEq Criterion] [DecidableEq Byte]
    (verify : Criterion -> ToyState Byte -> Bool)
    (delivery : DeliveryRecord Criterion Byte) where
  criterion : Criterion
  registeredBefore :
    DeliveryEvent.preregister criterion ∈ delivery.beforeArtifact
  verifierAccepts : verify criterion (finalState delivery.artifactRun) = true

/-- Missing-envelope judgment: the envelope must actually be absent and the
artifact-only verifier must accept. -/
def missingEnvelopeAcceptance {Criterion Byte : Type*} [DecidableEq Byte]
    (verify : Criterion -> ToyState Byte -> Bool)
    (delivery : DeliveryRecord Criterion Byte) : Bool :=
  match delivery.envelope with
  | none => independentlyAcceptable verify delivery
  | some _ => false

/-- Seat death changes only liveness and routing-envelope state. -/
def inheritAfterSeatDeath {Criterion Byte : Type*}
    (delivery : DeliveryRecord Criterion Byte) : DeliveryRecord Criterion Byte :=
  { delivery with envelope := none, seatAlive := false }

private theorem qualifying_events_iff_exists_preregistered
    {Criterion Byte : Type*} [DecidableEq Byte]
    (verify : Criterion -> ToyState Byte -> Bool)
    (artifactRun : ToyTrajectory Byte)
    (events : List (DeliveryEvent Criterion Byte)) :
    events.any (qualifyingEvent verify artifactRun) = true <->
      exists criterion,
        DeliveryEvent.preregister criterion ∈ events /\
          verify criterion (finalState artifactRun) = true := by
  induction events with
  | nil => simp
  | cons event events inductionHypothesis =>
      cases event with
      | preregister criterion =>
          simp [qualifyingEvent, inductionHypothesis]
      | artifactCheckpoint run =>
          simp [qualifyingEvent, inductionHypothesis]
      | auditReadout =>
          simp [qualifyingEvent, inductionHypothesis]

private theorem independently_acceptable_iff_witness
    {Criterion Byte : Type*} [DecidableEq Criterion] [DecidableEq Byte]
    (verify : Criterion -> ToyState Byte -> Bool)
    (delivery : DeliveryRecord Criterion Byte) :
    independentlyAcceptable verify delivery = true <->
      Nonempty (PreregisteredAcceptanceWitness verify delivery) := by
  rw [independentlyAcceptable,
    qualifying_events_iff_exists_preregistered verify delivery.artifactRun
      delivery.beforeArtifact]
  constructor
  · rintro ⟨criterion, registeredBefore, verifierAccepts⟩
    exact ⟨⟨criterion, registeredBefore, verifierAccepts⟩⟩
  · rintro ⟨witness⟩
    exact ⟨witness.criterion, witness.registeredBefore, witness.verifierAccepts⟩

private def inheritWitness
    {Criterion Byte : Type*} [DecidableEq Criterion] [DecidableEq Byte]
    {verify : Criterion -> ToyState Byte -> Bool}
    {delivery : DeliveryRecord Criterion Byte}
    (witness : PreregisteredAcceptanceWitness verify delivery) :
    PreregisteredAcceptanceWitness verify (inheritAfterSeatDeath delivery) :=
  { criterion := witness.criterion
    registeredBefore := witness.registeredBefore
    verifierAccepts := witness.verifierAccepts }

private theorem missing_envelope_acceptance_iff_witness
    {Criterion Byte : Type*} [DecidableEq Criterion] [DecidableEq Byte]
    (verify : Criterion -> ToyState Byte -> Bool)
    (delivery : DeliveryRecord Criterion Byte) :
    missingEnvelopeAcceptance verify delivery = true <->
      EnvelopeMissing delivery /\
        Nonempty (PreregisteredAcceptanceWitness verify delivery) := by
  cases envelopeValue : delivery.envelope with
  | none =>
      simp only [missingEnvelopeAcceptance, envelopeValue]
      rw [independently_acceptable_iff_witness]
      simp [EnvelopeMissing, envelopeValue]
  | some report =>
      simp [missingEnvelopeAcceptance, EnvelopeMissing, envelopeValue]

/-- T-E: with no envelope, independent acceptance is equivalent to a finite
pre-artifact criterion witness.  Either direction yields the other, and the same
witness still accepts after the producing seat dies and its envelope disappears. -/
theorem missing_envelope_acceptance_iff_preregistered_and_inheritable
    {Criterion Byte : Type*} [DecidableEq Criterion] [DecidableEq Byte]
    (verify : Criterion -> ToyState Byte -> Bool)
    (delivery : DeliveryRecord Criterion Byte) :
    (missingEnvelopeAcceptance verify delivery = true <->
      EnvelopeMissing delivery /\
        Nonempty (PreregisteredAcceptanceWitness verify delivery)) /\
      (Nonempty (PreregisteredAcceptanceWitness verify delivery) ->
        missingEnvelopeAcceptance verify (inheritAfterSeatDeath delivery) = true) := by
  constructor
  · exact missing_envelope_acceptance_iff_witness verify delivery
  · intro witness
    apply (missing_envelope_acceptance_iff_witness verify
      (inheritAfterSeatDeath delivery)).2
    exact ⟨rfl, witness.map inheritWitness⟩

#print axioms missing_envelope_acceptance_iff_preregistered_and_inheritable

private inductive SampleCriterion where
  | artifactSufficient
  | detectsUnpersistedLoss
deriving DecidableEq

private def sampleVerifier : SampleCriterion -> ToyState Nat -> Bool
  | .artifactSufficient, state => decide (state.required \ state.artifact = ∅)
  | .detectsUnpersistedLoss, state =>
      decide (byteLoss state KillAction.sessionInterrupt).Nonempty

private def sampleDelivery : DeliveryRecord SampleCriterion Nat where
  beforeArtifact := [DeliveryEvent.preregister .detectsUnpersistedLoss]
  artifactRun := unpersistedByteTrajectory
  afterArtifact := [DeliveryEvent.auditReadout]
  envelope := none
  seatAlive := true

-- Domain inhabitance uses the frozen finite artifact trajectory.
example : DeliveryRecord SampleCriterion Nat := sampleDelivery

-- The preregistration side has a checked finite witness, not a prose assertion.
example : Nonempty (PreregisteredAcceptanceWitness sampleVerifier sampleDelivery) := by
  refine ⟨⟨SampleCriterion.detectsUnpersistedLoss, ?_, ?_⟩⟩
  · simp [sampleDelivery]
  · decide

-- The missing-envelope side is independently executable on the same witness.
example : missingEnvelopeAcceptance sampleVerifier sampleDelivery = true := by
  decide

-- The inherited record is dead and still independently acceptable.
example :
    (inheritAfterSeatDeath sampleDelivery).seatAlive = false /\
      missingEnvelopeAcceptance sampleVerifier
        (inheritAfterSeatDeath sampleDelivery) = true := by
  decide

end D5.S3.ConceptDynamics.OperationalTuition.PreregisteredArtifactAcceptance
