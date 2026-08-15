/- GID: D5/S3/ObserverMemory/FiniteForgettingCertificate
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FiniteForgettingCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certify finite forgetting and recall dynamics over six named cognitive states. -/

/- Library-search audit trail (2026-08-10):
   * Local mathlib search found `Relation.ReflTransGen`, reused below for finite histories.
   * Local searches found no existing theorem packaging these cognitive transitions or their
     ledger invariants; the domain-specific one-step preservation proof is therefore local. -/

import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation
import Mathlib.Tactic

namespace D5.S3.ObserverMemory.FiniteForgettingCertificate

set_option backward.isDefEq.respectTransparency false in
/-- The six cognitive states, named by their epistemic meanings rather than coordinates. -/
inductive CognitiveState where
  | remember
  | neverKnown
  | forgotten
  | misremember
  | recall
  | accessRevoked
  deriving DecidableEq, Fintype

/--
The append-only observer ledger. `Reason` is deliberately left to the application: a revocation
must carry a reason, but this certificate does not invent a closed reason vocabulary.
-/
structure Ledger (Reason : Type*) where
  forgottenLogged : Bool := false
  revocationReason : Option Reason := none
  misrememberOpen : Bool := false
  recallOpen : Bool := false

/-- A cognitive state together with the audit marks that must survive later state changes. -/
structure CertificateState (Reason : Type*) where
  cognition : CognitiveState
  ledger : Ledger Reason

/-- The genuine state-changing actions admitted by the finite certificate. -/
inductive Action (Reason : Type*) where
  | learn
  | forget
  | recall
  | misremember
  | retractError
  | revoke (reason : Reason)

variable {Reason : Type*}

/-- Clear mutually exclusive current claims without erasing historical audit marks. -/
def closeClaims (ledger : Ledger Reason) : Ledger Reason :=
  { ledger with misrememberOpen := false, recallOpen := false }

/--
The partial dynamics. Forgetting and recall are different arcs; recall keeps the forgotten audit
mark, error retraction returns to Forgotten before any later accurate recall, and revocation is
terminal while retaining a typed reason.
-/
def applyAction (action : Action Reason) (source : CertificateState Reason) :
    Option (CertificateState Reason) :=
  match action, source.cognition with
  | .learn, .neverKnown =>
      some { cognition := .remember, ledger := closeClaims source.ledger }
  | .forget, .remember =>
      some {
        cognition := .forgotten
        ledger := { closeClaims source.ledger with forgottenLogged := true }
      }
  | .forget, .recall =>
      some {
        cognition := .forgotten
        ledger := { closeClaims source.ledger with forgottenLogged := true }
      }
  | .recall, .forgotten =>
      some {
        cognition := .recall
        ledger := {
          source.ledger with misrememberOpen := false, recallOpen := true
        }
      }
  | .misremember, .forgotten =>
      some {
        cognition := .misremember
        ledger := {
          source.ledger with misrememberOpen := true, recallOpen := false
        }
      }
  | .retractError, .misremember =>
      some {
        cognition := .forgotten
        ledger := { closeClaims source.ledger with forgottenLogged := true }
      }
  | .revoke _, .accessRevoked => none
  | .revoke reason, _ =>
      some {
        cognition := .accessRevoked
        ledger := {
          closeClaims source.ledger with revocationReason := some reason
        }
      }
  | _, _ => none

/-- A transition exists when one admitted action executes to the target state. -/
def Transition (source target : CertificateState Reason) : Prop :=
  ∃ action, applyAction action source = some target

/-- A finite history is the reflexive-transitive closure of the one-step dynamics. -/
abbrev FiniteHistory (source target : CertificateState Reason) : Prop :=
  Relation.ReflTransGen (Transition (Reason := Reason)) source target

/--
Coherence connects current cognition to its required reason and active-claim fields. Historical
forgetting is only forced in the Forgotten state because Recall must retain it by transition law.
-/
def Coherent (state : CertificateState Reason) : Prop :=
  (state.cognition = .forgotten -> state.ledger.forgottenLogged = true) ∧
  (state.ledger.revocationReason.isSome = true ↔ state.cognition = .accessRevoked) ∧
  (state.ledger.misrememberOpen = true ↔ state.cognition = .misremember) ∧
  (state.ledger.recallOpen = true ↔ state.cognition = .recall)

/-- The event has been entered in the forgetting ledger. -/
def ForgottenLogged (state : CertificateState Reason) : Prop :=
  state.ledger.forgottenLogged = true

/-- Access revocation, unlike epistemic forgetting, is identified by a reason-bearing entry. -/
def RevokedLogged (state : CertificateState Reason) : Prop :=
  state.ledger.revocationReason.isSome = true

/-- A ledger cannot carry simultaneous active false-memory and accurate-recall claims. -/
def ClaimsCompatible (state : CertificateState Reason) : Prop :=
  ¬(state.ledger.misrememberOpen = true ∧ state.ledger.recallOpen = true)

/-- A canonical coherent Remember certificate with no earlier audit events. -/
def initialRemember : CertificateState Reason :=
  { cognition := .remember, ledger := {} }

/-- The intermediate certificate after genuinely forgetting the canonical Remember state. -/
def forgottenAfterRemember : CertificateState Reason :=
  {
    cognition := .forgotten
    ledger := { forgottenLogged := true }
  }

/-- The final certificate after accurately recalling the previously forgotten event. -/
def recalledAfterForgetting : CertificateState Reason :=
  {
    cognition := .recall
    ledger := { forgottenLogged := true, recallOpen := true }
  }

/-- The named cognitive alphabet has six states. This is support, not the main certificate. -/
theorem cognitive_state_card : Fintype.card CognitiveState = 6 := by
  decide

/-- A coherent entry cannot activate both Misremember and Recall claims. -/
theorem claims_compatible_of_coherent {state : CertificateState Reason}
    (hstate : Coherent state) : ClaimsCompatible state := by
  rcases hstate with ⟨_, _, hmisremember, hrecall⟩
  rintro ⟨hmisrememberOpen, hrecallOpen⟩
  have hm := hmisremember.mp hmisrememberOpen
  have hr := hrecall.mp hrecallOpen
  simp [hm] at hr

/-- Concrete positive witness: Remember can genuinely transition to Forgotten. -/
theorem remember_forgets (ledger : Ledger Reason) :
    Transition
      { cognition := .remember, ledger := ledger }
      {
        cognition := .forgotten
        ledger := { closeClaims ledger with forgottenLogged := true }
      } := by
  exact ⟨.forget, rfl⟩

/-- Concrete positive witness: Forgotten can genuinely transition to Recall. -/
theorem forgotten_recalls (ledger : Ledger Reason) :
    Transition
      { cognition := .forgotten, ledger := ledger }
      {
        cognition := .recall
        ledger := { ledger with misrememberOpen := false, recallOpen := true }
      } := by
  exact ⟨.recall, rfl⟩

/--
Nonempty witness for the dynamics: a coherent Remember certificate follows two distinct admitted
arcs through Forgotten to Recall, while the final certificate retains the forgetting audit mark
and satisfies the incompatible-claim invariant.
-/
theorem remember_forget_recall_certificate :
    Coherent (initialRemember (Reason := Reason)) ∧
      FiniteHistory (initialRemember (Reason := Reason))
        (recalledAfterForgetting (Reason := Reason)) ∧
      ForgottenLogged (recalledAfterForgetting (Reason := Reason)) ∧
      ClaimsCompatible (recalledAfterForgetting (Reason := Reason)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Coherent, initialRemember]
  · apply Relation.ReflTransGen.tail
    · exact Relation.ReflTransGen.single ⟨.forget, rfl⟩
    · exact ⟨.recall, rfl⟩
  · rfl
  · simp [ClaimsCompatible, recalledAfterForgetting]

/-- AccessRevoked is irreversible: no admitted action has it as a source. -/
theorem access_revoked_terminal {source target : CertificateState Reason}
    (hsource : source.cognition = .accessRevoked) : ¬Transition source target := by
  rintro ⟨action, haction⟩
  rcases source with ⟨cognition, ledger⟩
  change cognition = .accessRevoked at hsource
  subst cognition
  cases action <;> simp [applyAction] at haction

/-- An open Misremember claim cannot jump directly to the incompatible Recall class. -/
theorem misremember_cannot_recall_directly {source target : CertificateState Reason}
    (hsource : source.cognition = .misremember)
    (htarget : target.cognition = .recall) : ¬Transition source target := by
  rintro ⟨action, haction⟩
  rcases source with ⟨sourceCognition, sourceLedger⟩
  rcases target with ⟨targetCognition, targetLedger⟩
  change sourceCognition = .misremember at hsource
  change targetCognition = .recall at htarget
  subst sourceCognition
  subst targetCognition
  cases action <;> simp [applyAction] at haction

/--
One admitted transition is closed on coherent certificates, cannot erase a prior Forgotten or
reason-bearing AccessRevoked entry, and preserves Misremember/Recall incompatibility.
-/
theorem transition_certificate {source target : CertificateState Reason}
    (hsource : Coherent source) (hstep : Transition source target) :
    Coherent target ∧
      (ForgottenLogged source -> ForgottenLogged target) ∧
      (RevokedLogged source ->
        target.ledger.revocationReason = source.ledger.revocationReason) ∧
      ClaimsCompatible target := by
  rcases source with ⟨sourceCognition, sourceLedger⟩
  rcases target with ⟨targetCognition, targetLedger⟩
  rcases hstep with ⟨action, haction⟩
  cases action <;> cases sourceCognition <;>
    simp only [applyAction, Option.some.injEq, CertificateState.mk.injEq] at haction
  all_goals rcases haction with ⟨rfl, rfl⟩
  all_goals simp_all [closeClaims, Coherent, ForgottenLogged, RevokedLogged,
    ClaimsCompatible]

/--
Main finite certificate: every finite transition history stays coherent; once forgetting or
revocation is entered it cannot be erased; and Misremember never coexists with Recall.
-/
theorem finite_history_certificate {source target : CertificateState Reason}
    (hsource : Coherent source) (history : FiniteHistory source target) :
    Coherent target ∧
      (ForgottenLogged source -> ForgottenLogged target) ∧
      (RevokedLogged source ->
        target.ledger.revocationReason = source.ledger.revocationReason) ∧
      ClaimsCompatible target := by
  induction history with
  | refl =>
      exact ⟨hsource, id, fun _ => rfl, claims_compatible_of_coherent hsource⟩
  | @tail middle final history hstep ih =>
      have hone := transition_certificate ih.1 hstep
      refine ⟨hone.1, ?_, ?_, hone.2.2.2⟩
      · exact fun hforgotten => hone.2.1 (ih.2.1 hforgotten)
      · intro hrevoked
        have hmiddleReason := ih.2.2.1 hrevoked
        have hmiddleRevoked : RevokedLogged middle := by
          unfold RevokedLogged at hrevoked ⊢
          rw [hmiddleReason]
          exact hrevoked
        exact (hone.2.2.1 hmiddleRevoked).trans hmiddleReason

end D5.S3.ObserverMemory.FiniteForgettingCertificate
