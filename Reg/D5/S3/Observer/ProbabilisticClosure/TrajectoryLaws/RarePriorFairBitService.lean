import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFairBitService
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFairBitService
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFairBitService
open FourthSegmentStoppedLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory Set
open scoped ENNReal

abbrev singletonSignature : Signature where
  Params := Unit
  State _ := Set Packet
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def singletonActual : Realization singletonSignature :=
  realize singletonSignature (fun _ _ s => packetLaw s) (fun e => nomatch e)
def singletonRejected : Realization singletonSignature :=
  realize singletonSignature (fun _ _ _ => 0) (fun e => nomatch e)
def singletonArena : Arena where
  signature := singletonSignature
  Law R := ∀ p : Packet,  R.readout () () {p} = (1/128 : ℝ≥0∞)

private theorem singleton_rejected : ¬ singletonArena.Law singletonRejected := by
  intro h
  have he := h (0, 0, 0, 0, 0, 0, 0)
  simp only [singletonRejected, realize, one_div] at he
  have hf := ENNReal.inv_eq_zero.mp he.symm
  norm_num at hf

def singletonRecord : Registration singletonArena (type_of% (@packet_law_singleton)) where
  actual := singletonActual
  bridge := Iff.rfl
  variation := ⟨packet_law_singleton, singletonRejected, singleton_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨singletonRejected, ?_, rfl, singleton_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), (∅ : Set Packet), (univ : Set Packet), ?_⟩
    change packetLaw (∅ : Set Packet) ≠ packetLaw univ
    simp only [measure_empty, measure_univ]
    exact zero_ne_one

def singletonRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@packet_law_singleton) (type_of% (realize singletonSignature
      (fun _ _ s => packetLaw s) (fun e => nomatch e))) (Type) Unit := {
  unitName := `RarePriorFairBitService.packet_law_singleton.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFairBitService.singletonRecord,
  realizationSource := none,  generated := false,
  arena := .source ⟨singletonArena⟩,  objectArena := .source ⟨singletonArena⟩,
  catalog := Lean.Name.anonymous,  localNames := false,
  realization := .source singletonArena ⟨singletonRecord⟩,
  correspondence := { stage := .evidence,  objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize singletonSignature
    (fun _ _ s => packetLaw s) (fun e => nomatch e)),
  variation := .absent,  sensitivity := .absent,  partialSensitivity := none,
  escapeFrom := some Packet,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFairBitService,
    definition := none,  coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,  familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit,  value := .bool false }] }

abbrev resetSignature : Signature where
  Params := Threshold × ℕ
  State _ := ℕ → Packet
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Service
  Anchor := Empty
  finiteAnchor := inferInstance

def resetActual : Realization resetSignature :=
  realize resetSignature (fun _ C ω => trialRun (entry C.1) ω C.2) (fun e => nomatch e)
def resetRejected : Realization resetSignature :=
  realize resetSignature (fun _ C _ => bitEntry C.1) (fun e => nomatch e)
def resetArena : Arena where
  signature := resetSignature
  Law R := ∀ (t : Threshold) (ω : ℕ → Packet) (m : ℕ),
    (∀ j < m,  100 ≤ (packetEquiv (ω j)).val) → R.readout () (t, m) ω = entry t

private theorem reset_rejected : ¬ resetArena.Law resetRejected := by
  intro h
  have he := h .ordinary (fun _ => (0, 0, 0, 0, 0, 0, 0)) 0 (by omega)
  have hp := congrArg Service.pc he
  cases hp

def resetRecord : Registration resetArena (type_of% (@prefix_reset)) where
  actual := resetActual
  bridge := Iff.rfl
  variation := ⟨prefix_reset, resetRejected, reset_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨resetRejected, ?_, rfl, reset_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(.ordinary, 1), (fun _ => (0, 0, 0, 0, 0, 0, 0)),
      (fun _ => (1, 1, 1, 1, 1, 1, 1)), ?_⟩
    intro he
    have hp := congrArg Service.pc he
    norm_num [resetActual, realize, trialRun, finishTrial, entry, packet_transaction,
      packetEquiv, finProdFinEquiv, threshold] at hp
    cases hp

def resetRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prefix_reset) (type_of% (realize resetSignature
      (fun _ C ω => trialRun (entry C.1) ω C.2) (fun e => nomatch e))) (Type) Unit := {
  unitName := `RarePriorFairBitService.prefix_reset.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFairBitService.resetRecord,
  realizationSource := none,  generated := false,
  arena := .source ⟨resetArena⟩,  objectArena := .source ⟨resetArena⟩,
  catalog := Lean.Name.anonymous,  localNames := false,
  realization := .source resetArena ⟨resetRecord⟩,
  correspondence := { stage := .evidence,  objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize resetSignature
    (fun _ C ω => trialRun (entry C.1) ω C.2) (fun e => nomatch e)),
  variation := .absent,  sensitivity := .absent,  partialSensitivity := none,
  escapeFrom := some Packet,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFairBitService,
    definition := none,  coordinates := #[0, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 1, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,  familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit,  value := .bool false }] }

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFairBitService
