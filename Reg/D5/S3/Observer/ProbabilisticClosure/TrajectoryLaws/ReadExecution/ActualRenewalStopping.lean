import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalStopping
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalStopping
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalStopping
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart
universe u v

abbrev bitSignature : Signature where
  Params := ℕ × (ℕ → ℕ)
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def bitActual : Realization bitSignature :=
  realize bitSignature (fun _ p t => sourceBit p.1 p.2 t) (fun e => nomatch e)

def bitRejected : Realization bitSignature :=
  realize bitSignature (fun _ _ _ => false) (fun e => nomatch e)

def bitArena : Arena where
  signature := bitSignature
  Law F := ∀ (wait : ℕ) (gaps : ℕ → ℕ),
    (∀ t < wait, F.readout () (wait, gaps) t = false) ∧
    F.readout () (wait, gaps) wait = true ∧
    (∀ n k, k ≤ gaps n → F.readout () (wait, gaps) (clock wait gaps n + k) =
      decide (k = gaps n)) ∧
    (∀ n, F.readout () (wait, gaps) (clock wait gaps n - 1) = true)

private theorem bit_rejected : ¬ bitArena.Law bitRejected := by
  intro h
  have hf := (h 0 (fun _ => 0)).2.1
  cases hf

def bitRecord : Registration bitArena (type_of% source_words) where
  actual := bitActual
  bridge := Iff.rfl
  variation := ⟨source_words, bitRejected, bit_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bitRejected, ?_, rfl, bit_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(1, fun _ => 0), 0, 1, ?_⟩
    have h := source_words 1 (fun _ => 0)
    change sourceBit 1 (fun _ => 0) 0 ≠ sourceBit 1 (fun _ => 0) 1
    rw [h.1 0 (by omega), h.2.1]
    decide

def bitRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    source_words (type_of% (realize bitSignature
      (fun _ p t => sourceBit p.1 p.2 t) (fun e => nomatch e))) Unit Unit := {
  unitName := `ActualRenewalStopping.source_words.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalStopping.bitRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨bitArena⟩, objectArena := .source ⟨bitArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source bitArena ⟨bitRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize bitSignature
    (fun _ p t => sourceBit p.1 p.2 t) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalStopping,
    definition := none, coordinates := #[0,1],
    readouts := #[{
      path := #["body","body","arg","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

def stoppingArena : Arena where
  signature := hitSignature.{u}
  Law F := ∀ {S : Type u} {R : Type v} (labels : Set S)
      (update : S → Bool → R → S) (initial : S) (coins : ℕ → R)
      (wait : ℕ) (gaps : ℕ → ℕ),
    (∀ T, firstHit labels (run labels update initial coins wait gaps) = some T →
      ∃ N, F.readout () ⟨S, labels⟩ (epoch labels update initial coins wait gaps) = some N ∧
        epoch labels update initial coins wait gaps N =
          run labels update initial coins wait gaps T ∧
        T ≤ clock wait gaps N ∧
        (∀ n < N, clock wait gaps n < T) ∧
        N ≤ paidTicks wait gaps T ∧ paidTicks wait gaps T ≤ T ∧
        (N = 0 ↔ T ≤ wait + 1)) ∧
    (firstHit labels (run labels update initial coins wait gaps) = none ↔
      firstHit labels (epoch labels update initial coins wait gaps) = none)

private theorem stopping_rejected : ¬ stoppingArena.{u,v}.Law hitRejected := by
  intro h
  let a : ULift.{u} Bool := ⟨false⟩
  let update : ULift.{u} Bool → Bool → ULift.{v} Unit → ULift.{u} Bool := fun s _ _ => s
  let coins : ℕ → ULift.{v} Unit := fun _ => ⟨()⟩
  have hzero : firstHit Set.univ (run Set.univ update a coins 0 (fun _ => 0)) = some 0 :=
    (first_hit_some _ _ 0).mpr ⟨Set.mem_univ _, fun i hi => by omega⟩
  obtain ⟨N, hN, _⟩ := (h Set.univ update a coins 0 (fun _ => 0)).1 0 hzero
  cases hN

def stoppingRecord : Registration stoppingArena.{u,v}
    (type_of% (@stopping_correspondence.{u,v})) where
  actual := hitActual
  bridge := Iff.rfl
  variation := ⟨stopping_correspondence, hitRejected, stopping_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨hitRejected, ?_, rfl, stopping_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := hitRecord.dependence

def stoppingRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stopping_correspondence.{u,v}) (type_of% (realize hitSignature.{u}
      (fun _ C ω => firstHit C.accept ω) (fun e => nomatch e))) Unit Unit := {
  unitName := `ActualRenewalStopping.stopping_correspondence.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalStopping.stoppingRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨stoppingArena⟩, objectArena := .source ⟨stoppingArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source stoppingArena ⟨stoppingRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize hitSignature.{u}
    (fun _ C ω => firstHit C.accept ω) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalStopping,
    definition := none, coordinates := #[0,2],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "fn","arg","body","body","arg","body","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalStopping
