import D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound
import Reg.Support.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound

open _root_.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound
open _root_.D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

universe u v

def signature : Signature where
  Params := Σ Q : Type u, Σ F : Type v, Σ _ : F → Q → Q, Q → F → ℕ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List p.2.1 → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p initial ↦ Comm p.2.2.1 p.2.2.2 initial)
    (fun e ↦ nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ ↦ 1) (fun e ↦ nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {Q F : Type*} [Fintype Q] [Nonempty Q] [Fintype F] [Nonempty F]
    (I : Set Q) (T : F → Q → Q) (w : Q → F → ℕ)
    (_hReach : ∀ state : Q, ∃ initial ∈ I, ∃ path : List F,
      runWord T path initial = state),
    let finiteInfinite := ∀ initial ∈ I, ∀ word : ℕ → F,
      InfiniteComm T w initial word ≠ ⊤
    let uniformlyBounded := ∃ bound : ℕ, ∀ initial ∈ I, ∀ word : List F,
      Comm T w initial word ≤ bound
    let zeroCycles := ∀ state : Q, ∀ cycle : List F, cycle ≠ [] →
      runWord T cycle state = state → Comm T w state cycle = 0
    List.TFAE [finiteInfinite, uniformlyBounded, zeroCycles] ∧
      (zeroCycles → ∀ initial ∈ I, ∀ word : List F,
        R.readout () ⟨Q, F, T, w⟩ initial word ≤
          (Fintype.card Q - 1) * maxEdgeCost w)

def registration : Registration arena (arena.Law actual) := by
  have rejectedNotLaw : ¬ arena.Law rejected := by
    intro law
    have specialized := law (Q := ULift.{u} Unit) (F := ULift.{v} Unit)
      Set.univ (fun _ state ↦ state) (fun _ _ ↦ 0)
      (fun state ↦ ⟨state, Set.mem_univ state, [], rfl⟩)
    have zeroCycles :
        ∀ state : ULift.{u} Unit, ∀ cycle : List (ULift.{v} Unit), cycle ≠ [] →
          runWord (fun _ state ↦ state) cycle state = state →
            Comm (fun _ state ↦ state) (fun _ _ ↦ 0) state cycle = 0 := by
      intro state cycle hNonempty hClosed
      clear hNonempty hClosed
      induction cycle generalizing state with
      | nil => rfl
      | cons action cycle ih =>
          simp only [Comm, zero_add]
          exact ih state
    have impossible := specialized.2 zeroCycles ⟨()⟩ (Set.mem_univ _) [⟨()⟩]
    norm_num [rejected, realize, signature, maxEdgeCost] at impossible
  exact
    { actual := actual
      bridge := Iff.rfl
      variation := ⟨by
        intro Q F _ _ _ _ I T w hReach
        exact cumulative_communication_criterion I T w hReach
      , rejected, rejectedNotLaw⟩
      sensitivity := by
        constructor
        · intro i
          refine ⟨rejected, ?_, rfl, rejectedNotLaw⟩
          intro j h
          exact (h (@Subsingleton.elim Unit _ j i)).elim
        · intro i
          exact nomatch i
      dependence := by
        intro i
        cases i
        let p : signature.Params := ⟨ULift.{u} Bool, ULift.{v} Unit,
          (fun _ state ↦ state), (fun state _ ↦ if state.down then 1 else 0)⟩
        refine ⟨p, ⟨false⟩, ⟨true⟩, ?_⟩
        intro readingsEqual
        have atOne := congrFun readingsEqual [⟨()⟩]
        norm_num [actual, realize, signature, p, Comm] at atOne }

register_information_theorem cumulative_communication_criterion in arena
  readout via (realize signature
    (fun _ p initial ↦ Comm p.2.2.1 p.2.2.2 initial)
    (fun e ↦ nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound
    coordinates := #[0, 1, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg",
        "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 14 }] })
  escape continues (open)

#print axioms registration

end

end Reg.D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound
