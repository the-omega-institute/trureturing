/- GID: D5/S3/ConceptDynamics/OperationalTuition/ArtifactSufficiencyAndKillLoss
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/OperationalTuition/ArtifactSufficiencyAndKillLoss
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Persistent artifact sufficiency exactly characterizes zero-byte loss under every kill. -/

import Mathlib.Data.Finset.SDiff
import Mathlib.Tactic.DeriveFintype

/- Library-search audit trail (2026-08-31):
   * Exact repository and pinned-Mathlib searches for artifact sufficiency,
     byte loss, kill actions, and the stated iff found no covering declaration.
   * Pinned Mathlib supplies `Finset.sdiff_eq_empty_iff_subset` and
     `Finset.sdiff_nonempty`; these bridge independently defined persistence and
     post-kill loss rather than making the two sides identical by definition.
   * Repository transition searches found only domain-specific word and graph
     runners.  The Part IV toy system is therefore transcribed directly with a
     finite `List` event trace and `List.foldl` execution.

   Clause echo:
   * Definition 4.1 is `ArtifactSufficient state`: every required byte belongs
     to the persistent artifact, independently of volatile session memory.
   * The toy trajectory is `ToyTrajectory.events : List (ToyEvent Byte)` and its
     final state is computed by `List.foldl toyStep`.
   * Process-group clearing and session interruption are the two constructors of
     finite `KillAction`; both clear volatile bytes and preserve artifacts.
   * T-D's forward and reverse directions are the first iff conjunct.  The
     second conjunct explicitly constructs an unrecoverable kill from
     insufficiency, and the third identifies the clock-loss bound with time
     since the last checkpoint. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.OperationalTuition.ArtifactSufficiencyAndKillLoss

/-- A toy operational state separates required information, persistent artifact
bytes, volatile session bytes, and time since the last artifact checkpoint. -/
structure ToyState (Byte : Type*) where
  required : Finset Byte
  artifact : Finset Byte
  session : Finset Byte
  checkpointAge : Nat
deriving DecidableEq

/-- Finite pre-kill events: produce required session bytes, checkpoint all
session bytes into the artifact, or merely advance wall-clock time. -/
inductive ToyEvent (Byte : Type*) where
  | work (newBytes : Finset Byte) (elapsed : Nat)
  | checkpoint
  | wait (elapsed : Nat)
deriving DecidableEq

/-- One transition of the toy operational system. -/
def toyStep {Byte : Type*} [DecidableEq Byte]
    (state : ToyState Byte) : ToyEvent Byte -> ToyState Byte
  | .work newBytes elapsed =>
      { required := state.required ∪ newBytes
        artifact := state.artifact
        session := state.session ∪ newBytes
        checkpointAge := state.checkpointAge + elapsed }
  | .checkpoint =>
      { required := state.required
        artifact := state.artifact ∪ state.session
        session := ∅
        checkpointAge := 0 }
  | .wait elapsed =>
      { state with checkpointAge := state.checkpointAge + elapsed }

/-- A finite toy trajectory, represented exactly by a starting state and a list
of operational events. -/
structure ToyTrajectory (Byte : Type*) where
  initial : ToyState Byte
  events : List (ToyEvent Byte)
deriving DecidableEq

/-- Execute a finite toy trajectory. -/
def finalState {Byte : Type*} [DecidableEq Byte]
    (trajectory : ToyTrajectory Byte) : ToyState Byte :=
  trajectory.events.foldl toyStep trajectory.initial

-- Lean 4.33's stricter type check breaks mathlib's `Fintype` deriving handler.
set_option backward.isDefEq.respectTransparency.types false in
/-- The two external kills named in Part IV. -/
inductive KillAction where
  | processGroupClear
  | sessionInterrupt
deriving DecidableEq, Fintype, Repr

/-- A kill preserves persistent artifacts and clears volatile session memory. -/
def applyKill {Byte : Type*} (state : ToyState Byte) : KillAction -> ToyState Byte
  | .processGroupClear => { state with session := ∅ }
  | .sessionInterrupt => { state with session := ∅ }

/-- Bytes from which operation can be reconstructed after a state transition. -/
def recoverableBytes {Byte : Type*} [DecidableEq Byte]
    (state : ToyState Byte) : Finset Byte :=
  state.artifact ∪ state.session

/-- Definition 4.1: every required byte is already in the persistent artifact. -/
def ArtifactSufficient {Byte : Type*} (state : ToyState Byte) : Prop :=
  state.required ⊆ state.artifact

/-- Required bytes unavailable after the selected kill. -/
def byteLoss {Byte : Type*} [DecidableEq Byte]
    (state : ToyState Byte) (kill : KillAction) : Finset Byte :=
  state.required \ recoverableBytes (applyKill state kill)

/-- The toy clock loss is bounded by work time since the last checkpoint. -/
def clockLoss {Byte : Type*} (state : ToyState Byte) (_kill : KillAction) : Nat :=
  state.checkpointAge

private theorem artifact_sufficient_iff_all_kills_zero
    {Byte : Type*} [DecidableEq Byte] (state : ToyState Byte) :
    ArtifactSufficient state <->
      forall kill : KillAction, byteLoss state kill = ∅ := by
  constructor
  · intro sufficient kill
    cases kill <;>
      simpa [ArtifactSufficient, byteLoss, recoverableBytes, applyKill] using sufficient
  · intro zeroLoss
    have processClear := zeroLoss KillAction.processGroupClear
    simpa [ArtifactSufficient, byteLoss, recoverableBytes, applyKill] using processClear

private theorem insufficient_has_unrecoverable_kill
    {Byte : Type*} [DecidableEq Byte] (state : ToyState Byte)
    (insufficient : Not (ArtifactSufficient state)) :
    exists kill : KillAction, (byteLoss state kill).Nonempty := by
  refine ⟨KillAction.sessionInterrupt, ?_⟩
  simpa [ArtifactSufficient, byteLoss, recoverableBytes, applyKill] using
    (Finset.sdiff_nonempty.mpr insufficient)

private theorem every_kill_clock_loss_eq_checkpoint_age
    {Byte : Type*} (state : ToyState Byte) :
    forall kill : KillAction, clockLoss state kill = state.checkpointAge := by
  intro kill
  cases kill <;> rfl

/-- T-D: on every finite toy trajectory, artifact sufficiency is equivalent to
zero required-byte loss for every external kill.  Insufficiency supplies an
explicit unrecoverable kill, while clock loss is exactly checkpoint age. -/
theorem artifact_sufficient_iff_every_kill_zero_byte_loss
    {Byte : Type*} [DecidableEq Byte] (trajectory : ToyTrajectory Byte) :
    (ArtifactSufficient (finalState trajectory) <->
      forall kill : KillAction, byteLoss (finalState trajectory) kill = ∅) /\
    (Not (ArtifactSufficient (finalState trajectory)) ->
      exists kill : KillAction, (byteLoss (finalState trajectory) kill).Nonempty) /\
    (forall kill : KillAction,
      clockLoss (finalState trajectory) kill =
        (finalState trajectory).checkpointAge) := by
  exact ⟨artifact_sufficient_iff_all_kills_zero (finalState trajectory),
    insufficient_has_unrecoverable_kill (finalState trajectory),
    every_kill_clock_loss_eq_checkpoint_age (finalState trajectory)⟩

#print axioms artifact_sufficient_iff_every_kill_zero_byte_loss

/-- A finite run with one checkpoint followed by one unpersisted required byte. -/
def unpersistedByteTrajectory : ToyTrajectory Nat where
  initial :=
    { required := ∅
      artifact := ∅
      session := ∅
      checkpointAge := 0 }
  events := [ToyEvent.work {0, 1} 3, ToyEvent.checkpoint, ToyEvent.work {2} 2]

-- Domain inhabitance and a nonzero reverse-direction witness are kernel checked.
example : ToyTrajectory Nat := unpersistedByteTrajectory

example :
    byteLoss (finalState unpersistedByteTrajectory) KillAction.sessionInterrupt = {2} := by
  decide

example :
    exists kill : KillAction,
      (byteLoss (finalState unpersistedByteTrajectory) kill).Nonempty := by
  refine ⟨KillAction.sessionInterrupt, ?_⟩
  have loss :
      byteLoss (finalState unpersistedByteTrajectory) KillAction.sessionInterrupt = {2} := by
    decide
  rw [loss]
  simp

end D5.S3.ConceptDynamics.OperationalTuition.ArtifactSufficiencyAndKillLoss
