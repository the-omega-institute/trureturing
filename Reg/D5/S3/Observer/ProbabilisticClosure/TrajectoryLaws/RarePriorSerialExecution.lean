import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorSerialExecution
import Reg.Support.DependentFamily
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFairBitService

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorSerialExecution.RepeatedService
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open RarePriorSerialExecution RarePriorFairBitService FourthSegmentStoppedLaw FreshServiceRestart
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory ProbabilityTheory Set

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ → Letter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (ℕ → Packet) × (Threshold → ℕ → Option Service)
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ ω => (acceptedStream ω,fun t k => executedReadyService t ω k))
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ ω => (acceptedStream ω,fun _ _ => none)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R :=
    freshBitLaw.map (fun ω => (R.readout () () ω).1) =
      Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond packetLaw acceptedPackets) ∧
    (∀ᵐ ω ∂freshBitLaw, ∀ k : ℕ, ∀ t : Threshold,
      (R.readout () () ω).2 t k =
        some ⟨t,.returned,6,packetEquiv ((R.readout () () ω).1 k),
          if (packetEquiv ((R.readout () () ω).1 k)).val < (threshold t).val then 0 else 1⟩)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : ∀ᵐ ω ∂freshBitLaw, False := by
    filter_upwards [h.2] with ω hω
    have hn := hω 0 .ordinary
    cases hn
  obtain ⟨ω,hfalse⟩ := he.exists
  exact hfalse

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  let a : ℕ → Letter := fun _ => 0
  let b : ℕ → Letter := fun n => if n%7 = 0 then 1 else 0
  have ha : firstHit acceptedPackets (packetize a) = some 0 :=
    (first_hit_some _ _ 0).mpr ⟨by
      norm_num [a,acceptedPackets,packetize,RarePriorSerialExecution.vectorPacket,
        packetEquiv,finProdFinEquiv],fun i hi => by omega⟩
  have hb : firstHit acceptedPackets (packetize b) = some 0 :=
    (first_hit_some _ _ 0).mpr ⟨by
      norm_num [b,acceptedPackets,packetize,RarePriorSerialExecution.vectorPacket,
        packetEquiv,finProdFinEquiv],fun i hi => by omega⟩
  refine ⟨(),a,b,?_⟩
  intro he
  have hp := congrArg (fun p => packetEquiv (p.1 0)) he
  simp only [actual,realize,acceptedStream,draws,unused,restart,ha,hb] at hp
  norm_num [a,b,packetize,RarePriorSerialExecution.vectorPacket,packetEquiv,finProdFinEquiv] at hp

def record : Registration arena (type_of% (@repeated_fresh_bit_service)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨repeated_fresh_bit_service,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@repeated_fresh_bit_service) (type_of% (realize signature
      (fun _ _ ω => (acceptedStream ω,fun t k => executedReadyService t ω k))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `RarePriorSerialExecution.repeated_fresh_bit_service.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorSerialExecution.RepeatedService.record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ _ ω => (acceptedStream ω,fun t k => executedReadyService t ω k)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorSerialExecution,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["fn","arg","fn","arg","fn","arg"],stateBinder := 0,functionOperand := true,
      stateOperand := none,booleanPredicate := false },
      { path := #["arg","body","body","body","fn","arg"],stateBinder := 0,
        functionOperand := true,stateOperand := none,booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

abbrev positiveSignature : Signature where
  Params := Unit
  State _ := Packet
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def positiveActual : Realization positiveSignature :=
  realize positiveSignature (fun _ _ p => decide ((packetEquiv p).val < 100)) (fun e => nomatch e)
def positiveRejected : Realization positiveSignature :=
  realize positiveSignature (fun _ _ _ => false) (fun e => nomatch e)
def positiveArena : Arena where
  signature := positiveSignature
  Law R := packetLaw {p | R.readout () () p = true} ≠ 0

private theorem positive_rejected : ¬ positiveArena.Law positiveRejected := by
  simp [positiveArena,positiveRejected,realize]

private theorem positive_dependence : ObservationalDependence positiveSignature positiveActual := by
  intro i
  cases i
  refine ⟨(),(0,0,0,0,0,0,0),(1,1,1,1,1,1,1),?_⟩
  norm_num [positiveActual,realize,packetEquiv,finProdFinEquiv]
  decide

def positiveRecord : Registration positiveArena (type_of% (@acceptance_positive)) where
  actual := positiveActual
  bridge := by simp [positiveArena,positiveActual,realize,acceptedPackets]
  variation := ⟨by simpa [positiveArena,positiveActual,realize,acceptedPackets]
    using acceptance_positive,positiveRejected,positive_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨positiveRejected,?_,rfl,positive_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := positive_dependence

def positiveRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@acceptance_positive) (type_of% (realize positiveSignature
      (fun _ _ p => decide ((packetEquiv p).val < 100)) (fun e => nomatch e))) Unit Unit := {
  unitName := `RarePriorSerialExecution.acceptance_positive.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorSerialExecution.RepeatedService.positiveRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨positiveArena⟩, objectArena := .source ⟨positiveArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source positiveArena ⟨positiveRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize positiveSignature
    (fun _ _ p => decide ((packetEquiv p).val < 100)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none, continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorSerialExecution.RepeatedService


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorSerialExecution
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeAcquiredPrefixState FourthSegmentStoppedLaw RarePriorFiniteMonitor RarePriorFairBitService RarePriorResidentCode
open RarePriorSerialExecution
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory ProbabilityTheory Set

structure ExecutionReadout where
  flight : (k n : ℕ) → (Fin k → Fin n) → Flight k n → ℕ → Flight k n
  step : ServiceMachine → Letter → ServiceMachine
  ticks : ServiceMachine → ℕ → ServiceMachine
  code : ServiceMachine → List Bool
  trial : Service → Packet → Option Service
  states : Runtime → ℕ → Option Runtime
  operation : Runtime → ℕ → Option (Operation × Runtime)
  source : ℕ → Letter

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ → Letter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ExecutionReadout
  Anchor := Empty
  finiteAnchor := inferInstance

def observed (ω : ℕ → Letter) : ExecutionReadout :=
  ⟨fun _ _ => flightRun,machineStep,machineRun,machineCode,serialTrial,
    fun z => serialStates z ω,fun z => serialOperation z ω,ω⟩

def actual : Realization signature := realize signature (fun _ _ => observed) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ ω => { observed ω with states := fun _ _ => none }) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    let v := R.readout () () (fun _ => 0)
    (∀ (k n : ℕ) (table : Fin k → Fin n) (s : Flight k n) (m : ℕ),
      m ≤ s.remaining.val →
      (v.flight k n table s m).scanner = (installedGraphStep table)^[m] s.scanner ∧
      (v.flight k n table s m).remaining.val = s.remaining.val-m) ∧
    (∀ (z : Runtime) (s : Service) (b : Letter),
      let x : Letter := if s.pc = .bit then b else 0
      let f : Flight 43008 21504 := flightEntry (bitKeyCodec (s,x))
      v.ticks (v.step (.ready z s) b) (f.remaining.val+1) = .ready z (microStep s b)) ∧
    (∀ (q : ServiceMachine) (a b : Letter), bitRequest q = false → v.step q a = v.step q b) ∧
    (∀ (base : MicroSnapshot) (q : ServiceMachine), (v.code q).length = machineSize ∧
      residentCode.length+(snapshotCode base).length+(v.code q).length < localBound) ∧
    Function.Injective v.code ∧
    (∀ (s : Service) (p : Packet), v.trial s p = some (finishTrial s p)) ∧
    (∀ z : Runtime, freshBitLaw.map (fun ω => (R.readout () () ω).states z) = packetRuntimeLaw z) ∧
    (∀ᵐ ω ∂freshBitLaw, ∀ z : Runtime,
      (∀ n, (R.readout () () ω).states z n =
        some (packetStates z (acceptedStream (R.readout () () ω).source) n)) ∧
      ∀ k, (R.readout () () ω).operation
          (packetStates z (acceptedStream (R.readout () () ω).source) k) k =
        packetOperation (packetStates z (acceptedStream (R.readout () () ω).source) k)
          (acceptedStream (R.readout () () ω).source k))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : ∀ᵐ ω ∂freshBitLaw, False := by
    filter_upwards [h.2.2.2.2.2.2.2] with ω hω
    have hn := (hω runtimeInitial).1 0
    cases hn
  obtain ⟨ω,hfalse⟩ := he.exists
  exact hfalse

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(),(fun _ => 0),(fun _ => 1),?_⟩
  intro h
  have he := congrArg (fun v : ExecutionReadout => v.source 0) h
  norm_num [actual,realize,observed] at he

def record : Registration arena (type_of% (@serial_adaptive_execution)) where
  actual := actual
  bridge := by
    simp only [arena,actual,realize,observed]
  variation := ⟨by simpa only [arena,actual,realize,observed]
    using serial_adaptive_execution,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@serial_adaptive_execution) (type_of% (realize signature
      (fun _ _ => observed) (fun e => nomatch e))) Unit Unit := {
  unitName := `RarePriorSerialExecution.serial_adaptive_execution.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorSerialExecution.record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ => observed) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none, continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorSerialExecution
