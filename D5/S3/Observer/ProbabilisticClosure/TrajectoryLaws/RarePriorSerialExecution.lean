/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite scanner flights execute adaptive services and original updates. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFairBitService
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.ProductMeasure
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFullFields

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorSerialExecution
open FourthSegmentStoppedLaw RarePriorFiniteMonitor RarePriorFairBitService
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology
open Filter

def vectorPacket (v : Fin 7 → Letter) : Packet :=
  (v 0,v 1,v 2,v 3,v 4,v 5,v 6)

private def packetVector (p : Packet) : Fin 7 → Letter := fun i =>
  ![p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2.1,p.2.2.2.2.2.2] i

/-! Grouping consecutive external bits is an analysis coordinate; the service
    reads them individually through its existing bit instruction. -/
def packetize (ω : ℕ → Letter) (n : ℕ) : Packet :=
  vectorPacket (fun i => ω (n*7+i.val))

noncomputable def freshBitLaw : Measure (ℕ → Letter) :=
  Measure.infinitePi (fun _ => bernoulliMeasure (0 : Letter) 1 fairParameter)

instance : IsProbabilityMeasure freshBitLaw := by unfold freshBitLaw; infer_instance

private theorem vector_packet_law :
    (Measure.infinitePi (fun _ : Fin 7 =>
      bernoulliMeasure (0 : Letter) 1 fairParameter)).map vectorPacket = packetLaw := by
  apply Measure.ext_of_singleton
  intro p
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  have he : vectorPacket ⁻¹' {p} =
      Set.pi (Finset.univ : Finset (Fin 7)) (fun i => {packetVector p i}) := by
    ext v
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_pi,Finset.mem_coe,
      Finset.mem_univ,true_implies]
    constructor
    · intro hv
      rw [← hv]
      intro i
      fin_cases i <;> rfl
    · intro hv
      rcases p with ⟨a,b,c,d,e,f,g⟩
      have h0 := hv 0; have h1 := hv 1; have h2 := hv 2
      have h3 := hv 3; have h4 := hv 4; have h5 := hv 5; have h6 := hv 6
      simp only [packetVector,Matrix.cons_val_zero,Matrix.cons_val_succ,
        Set.mem_singleton_iff] at h0 h1 h2 h3 h4 h5 h6
      simp [vectorPacket,h0,h1,h2,h3,h4,h5,h6]
  rw [he,Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  rw [RarePriorFairBitService.packet_law_singleton,← fair_packet_mass p]
  rcases p with ⟨a,b,c,d,e,f,g⟩
  simp [Fin.prod_univ_succ,packetVector,wordMass,packetBits,mul_assoc]

private theorem packetize_law : freshBitLaw.map packetize = packetStreamLaw := by
  let f := bernoulliMeasure (0 : Letter) 1 fairParameter
  let reindex : (ℕ → Letter) → (ℕ × Fin 7 → Letter) :=
    fun ω i => ω ((Nat.divModEquiv 7).symm i)
  have hr : freshBitLaw.map reindex = Measure.infinitePi (fun _ : ℕ × Fin 7 => f) :=
    Measure.map_infinitePi_infinitePi_of_inj (Nat.divModEquiv 7).symm.injective
  have hc : freshBitLaw.map (fun (ω : ℕ → Letter) (n : ℕ) (i : Fin 7) => ω (n*7+i.val)) =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : Fin 7 => f)) := by
    change freshBitLaw.map ((MeasurableEquiv.curry ℕ (Fin 7) Letter) ∘ reindex) = _
    rw [← Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop),hr]
    exact Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Fin 7) => f)
  change freshBitLaw.map ((fun v n => vectorPacket (v n)) ∘
    (fun (ω : ℕ → Letter) (n : ℕ) (i : Fin 7) => ω (n*7+i.val))) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop),hc,
    Measure.infinitePi_map_pi (fun _ : ℕ => Measure.infinitePi (fun _ : Fin 7 => f))
      (fun _ => measurable_of_finite _)]
  simp only [f,vector_packet_law,packetStreamLaw]

def acceptedPackets : Set Packet := {p | (packetEquiv p).val < 100}

private def fallbackPacket : Packet := (0,0,0,0,0,0,0)

theorem acceptance_positive : packetLaw acceptedPackets ≠ 0 := by
  have hs : ({fallbackPacket} : Set Packet) ⊆ acceptedPackets := by
    intro p hp
    have he : p = fallbackPacket := hp
    subst p
    norm_num [fallbackPacket,acceptedPackets,packetEquiv,finProdFinEquiv]
  have hle := measure_mono (μ := packetLaw) hs
  rw [RarePriorFairBitService.packet_law_singleton] at hle
  exact ne_of_gt (lt_of_lt_of_le (by norm_num) hle)

/-! These suffixes and indices belong only to analysis, not to Service. -/
noncomputable def acceptedStream (ω : ℕ → Letter) : ℕ → Packet :=
  FreshServiceRestart.draws acceptedPackets fallbackPacket (packetize ω)

/-! This is the existing service graph executed until its first accepting
    packet. The null nonreturn branch is retained as none. -/
noncomputable def executedReadyService (t : Threshold) (ω : ℕ → Letter) (k : ℕ) : Option Service :=
  let suffix := FreshServiceRestart.unused acceptedPackets fallbackPacket k (packetize ω)
  match FreshServiceRestart.firstHit acceptedPackets suffix with
  | none => none
  | some n => some (trialRun (entry t) suffix (n+1))

/-! A single one-bit stream supplies all trials and all repeated services.
    The whole accepted-packet law is a product law, and each service's actual
    graph returns the candidate's threshold result from its prescribed entry. -/
theorem repeated_fresh_bit_service :
    freshBitLaw.map acceptedStream =
      Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond packetLaw acceptedPackets) ∧
    (∀ᵐ ω ∂freshBitLaw, ∀ k : ℕ, ∀ t : Threshold,
      executedReadyService t ω k =
        some ⟨t,.returned,6,packetEquiv (acceptedStream ω k),
          if (packetEquiv (acceptedStream ω k)).val < (threshold t).val then 0 else 1⟩) := by
  have h := FreshServiceRestart.repeated_acceptance_law packetLaw acceptedPackets
    fallbackPacket (Set.toFinite _).measurableSet acceptance_positive
  have hp : Measurable packetize := by unfold packetize vectorPacket; fun_prop
  constructor
  · change freshBitLaw.map
      ((FreshServiceRestart.draws acceptedPackets fallbackPacket) ∘ packetize) = _
    rw [← Measure.map_map h.1 hp,packetize_law]
    exact h.2.1
  · have ha : ∀ᵐ ω ∂freshBitLaw, ∀ k : ℕ,
        FreshServiceRestart.firstHit acceptedPackets
          (FreshServiceRestart.unused acceptedPackets fallbackPacket k (packetize ω)) ≠ none :=
      ae_of_ae_map hp.aemeasurable (by
        rw [packetize_law]
        exact h.2.2)
    filter_upwards [ha] with ω hω
    intro k t
    let suffix := FreshServiceRestart.unused acceptedPackets fallbackPacket k (packetize ω)
    cases hh : FreshServiceRestart.firstHit acceptedPackets suffix with
    | none => exact (hω k hh).elim
    | some n =>
      obtain ⟨hn,hprev⟩ := (FreshServiceRestart.first_hit_some acceptedPackets suffix n).mp hh
      have hs : ∀ i < n, 100 ≤ (packetEquiv (suffix i)).val := by
        intro i hi
        have := hprev i hi
        change ¬(packetEquiv (suffix i)).val < 100 at this
        omega
      have he : acceptedStream ω k = suffix n := by
        change (FreshServiceRestart.restart acceptedPackets fallbackPacket suffix).1 = _
        rw [FreshServiceRestart.restart,hh]
      change (match FreshServiceRestart.firstHit acceptedPackets suffix with
        | none => none
        | some j => some (trialRun (entry t) suffix (j+1))) = _
      rw [hh]
      change some (trialRun (entry t) suffix (n+1)) = _
      rw [trialRun,RarePriorFairBitService.prefix_reset t suffix n hs]
      simp only [finishTrial,entry]
      change (packetEquiv (suffix n)).val < 100 at hn
      rw [packet_transaction,if_pos hn,he]

#print axioms repeated_fresh_bit_service


end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorSerialExecution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorSerialExecution
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeFullResidual
open RarePriorFiniteMonitor RarePriorFairBitService RarePriorResidentCode
open RarePriorFullFields
open MeasureTheory ProbabilityTheory

instance : MeasurableSpace (Option Runtime) := ⊤
instance : MeasurableSingletonClass (Option Runtime) := ⟨fun _ => trivial⟩

/-- The countdown is bounded by the table dimensions, not by elapsed sampling time. -/
def flightCeiling (k n : ℕ) : ℕ := k*(k+1)+n+1

@[ext] structure Flight (k n : ℕ) where
  scanner : Scanner k n
  remaining : Fin (flightCeiling k n+1)
  deriving DecidableEq, Fintype

def flightEntry {k n : ℕ} (a : Fin k) : Flight k n :=
  ⟨scannerEntry a,⟨a.val*(k+1)+k+1+n+1,by
    have ha := a.isLt
    unfold flightCeiling
    nlinarith⟩⟩

/-- A single deterministic instruction advances the installed graph and its finite countdown. -/
def flightStep {k n : ℕ} (table : Fin k → Fin n) (s : Flight k n) : Flight k n :=
  if h : s.remaining.val = 0 then s else
    ⟨installedGraphStep table s.scanner,⟨s.remaining.val-1,by
      have := s.remaining.isLt
      omega⟩⟩

def flightRun {k n : ℕ} (table : Fin k → Fin n) (s : Flight k n) (m : ℕ) : Flight k n :=
  (flightStep table)^[m] s

def flightResult {k n : ℕ} (s : Flight k n) : Option (Fin n) :=
  if s.remaining.val = 0 then scannerResult s.scanner else none

private theorem flight_invariant {k n : ℕ} (table : Fin k → Fin n)
    (s : Flight k n) (m : ℕ) (hm : m ≤ s.remaining.val) :
    (flightRun table s m).scanner = (installedGraphStep table)^[m] s.scanner ∧
    (flightRun table s m).remaining.val = s.remaining.val-m := by
  induction m with
  | zero => exact ⟨rfl,by simp [flightRun]⟩
  | succ m ih =>
    obtain ⟨hs,hr⟩ := ih (by omega)
    have hpos : (flightRun table s m).remaining.val ≠ 0 := by omega
    rw [flightRun,Function.iterate_succ_apply']
    change (flightStep table (flightRun table s m)).scanner = _ ∧
      (flightStep table (flightRun table s m)).remaining.val = _
    simp only [flightStep,hpos,↓reduceDIte]
    constructor
    · rw [hs,Function.iterate_succ_apply']
    · simp only [hr]; omega

private theorem flight_result {k n : ℕ} (table : Fin k → Fin n) (a : Fin k) :
    flightResult (flightRun table (flightEntry a) (flightEntry (n := n) a).remaining.val) =
      tableProgram table a := by
  obtain ⟨hs,hr⟩ := flight_invariant table (flightEntry a) _ le_rfl
  rw [flightResult,hr,Nat.sub_self,if_pos rfl,hs]
  unfold tableProgram
  rfl

/-- This evaluator runs a finite countdown; the countdown is present at every internal cut. -/
def scanTable {k n : ℕ} (table : Fin k → Fin n) (a : Fin k) : Option (Fin n) :=
  flightResult (flightRun table (flightEntry a) (flightEntry (n := n) a).remaining.val)

def scanService (s : Service) (b : Letter) : Option Service :=
  (scanTable serviceTable (bitKeyCodec (s,b))).map serviceCodec.symm

def scanInitialization (z : Runtime) : Option Service :=
  (scanTable initializationTable (runtimeCodec z)).map serviceCodec.symm

def scanNative (z : Runtime) (op : Operation) : Option Runtime :=
  (scanTable nativeTable (nativeKeyCodec (z,op))).bind optionalRuntimeCodec.symm

private def baseSnapshot (z : Runtime) (s : Service) (op : Operation) : MicroSnapshot :=
  ⟨z,z,s,op,fun _ => 0,0,0,0,0,0,0,false,false⟩

private theorem scanned_programs (z : Runtime) (op : Operation) (s : Service) (b : Letter) :
    scanNative z op = runtimeStep z op ∧ scanService s b = some (microStep s b) ∧
    scanInitialization z = some (entry (selectedThreshold z)) := by
  have h := installed_bounded_program z op s b (baseSnapshot z s op)
  have hn := h.1
  have hs := h.2.1
  have hi := h.2.2.1
  simp only [nativeProgram] at hn
  simp only [serviceProgram] at hs
  simp only [initializationProgram] at hi
  simpa only [scanNative,scanService,scanInitialization,scanTable,flight_result]
    using And.intro hn (And.intro hs hi)

/-- A retained service context and a finite scanner flight are the complete local machine state. -/
inductive ServiceMachine where
  | ready (context : Runtime) (service : Service)
  | scanning (context : Runtime) (service : Service) (flight : Flight 43008 21504)
  | fault (context : Runtime) (service : Service)
  deriving DecidableEq, Fintype

def bitRequest : ServiceMachine → Bool
  | .ready _ s => decide (s.pc = .bit)
  | _ => false

/-- The port supplies one bit only at bitRequest. Reset, comparison and all scanner
    instructions receive no source data, and returned/fault states are absorbing. -/
def machineStep (q : ServiceMachine) (port : Letter) : ServiceMachine :=
  match q with
  | .ready z s => if s.pc = .returned then q else
      .scanning z s (flightEntry (bitKeyCodec (s,if s.pc = .bit then port else 0)))
  | .scanning z s f => if f.remaining.val = 0 then
      match flightResult f with
      | none => .fault z s
      | some v => .ready z (serviceCodec.symm v)
    else .scanning z s (flightStep serviceTable f)
  | .fault _ _ => q

def machineRun (q : ServiceMachine) (m : ℕ) : ServiceMachine := (fun q => machineStep q 0)^[m] q

private theorem machine_flight (z : Runtime) (s : Service) (f : Flight 43008 21504)
    (m : ℕ) (hm : m ≤ f.remaining.val) :
    machineRun (.scanning z s f) m = .scanning z s (flightRun serviceTable f m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [machineRun,Function.iterate_succ_apply']
    change machineStep (machineRun (.scanning z s f) m) 0 = _
    rw [ih (by omega)]
    have hr := (flight_invariant serviceTable f m (by omega)).2
    have hpos : (flightRun serviceTable f m).remaining.val ≠ 0 := by omega
    simp only [machineStep,hpos,↓reduceIte]
    exact congrArg (ServiceMachine.scanning z s)
      (Function.iterate_succ_apply' (flightStep serviceTable) m f).symm

private theorem machine_instruction (z : Runtime) (s : Service) (b : Letter) :
    let x : Letter := if s.pc = .bit then b else 0
    let f : Flight 43008 21504 := flightEntry (bitKeyCodec (s,x))
    machineRun (machineStep (.ready z s) b) (f.remaining.val+1) = .ready z (microStep s b) := by
  dsimp only
  by_cases hs : s.pc = .returned
  · have hm : microStep s b = s := by simp [microStep,hs]
    have hfix : ∀ m, machineRun (.ready z s) m = .ready z s := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [machineRun,Function.iterate_succ_apply']
        change machineStep (machineRun (.ready z s) m) 0 = _
        rw [ih]
        simp [machineStep,hs]
    simp only [machineStep,hs,↓reduceIte]
    rw [hfix,hm]
  · let x : Letter := if s.pc = .bit then b else 0
    let f : Flight 43008 21504 := flightEntry (bitKeyCodec (s,x))
    have hr := (flight_invariant serviceTable f f.remaining.val le_rfl).2
    have hzero : (flightRun serviceTable f f.remaining.val).remaining.val = 0 := by
      rw [hr,Nat.sub_self]
    have he : (flightResult (flightRun serviceTable f f.remaining.val)).map serviceCodec.symm =
        some (microStep s x) := by
      exact (scanned_programs z (.read x) s x).2.1
    have hv : flightResult (flightRun serviceTable f f.remaining.val) =
        some (serviceCodec (microStep s x)) := by
      obtain ⟨v,hv,hsv⟩ := Option.map_eq_some_iff.mp he
      rw [hv]
      exact congrArg some ((serviceCodec.apply_symm_apply v).symm.trans (congrArg serviceCodec hsv))
    have hb : microStep s x = microStep s b := by
      cases hp : s.pc <;> simp [x,microStep,hp]
    rw [machineStep,if_neg hs]
    change machineRun (.scanning z s f) (f.remaining.val+1) = _
    rw [machineRun,Function.iterate_succ_apply']
    change machineStep (machineRun (.scanning z s f) f.remaining.val) 0 = _
    rw [machine_flight z s f _ le_rfl]
    simp only [machineStep,hzero,↓reduceIte,hv,serviceCodec.symm_apply_apply,hb]

private theorem machine_port (q : ServiceMachine) (a b : Letter) (h : bitRequest q = false) :
    machineStep q a = machineStep q b := by
  cases q with
  | ready z s =>
    have hs : s.pc ≠ .bit := by simpa [bitRequest] using h
    simp [machineStep,hs]
  | scanning z s f => rfl
  | fault z s => rfl

private def boolCodec : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun n := n = 1
  left_inv b := by cases b <;> rfl
  right_inv n := by fin_cases n <;> rfl

def scannerCodec (k n : ℕ) : Scanner k n ≃
    Fin (k*((k+1)*((k+n+1)*((n+1)*(4*2))))) :=
  ({ toFun := fun s => (s.query,s.row,s.cursor,s.accumulator,s.pc,s.equalFlag)
     invFun := fun s => ⟨s.1,s.2.1,s.2.2.1,s.2.2.2.1,s.2.2.2.2.1,s.2.2.2.2.2⟩
     left_inv := by intro s; rfl
     right_inv := by intro s; rfl } :
      Scanner k n ≃ (Fin k × Fin (k+1) × Fin (k+n+1) × Fin (n+1) × Fin 4 × Bool)).trans
    (pairFin (Equiv.refl _) (pairFin (Equiv.refl _) (pairFin (Equiv.refl _)
      (pairFin (Equiv.refl _) (pairFin (Equiv.refl _) boolCodec)))))

def flightSize (k n : ℕ) : ℕ :=
  (k*((k+1)*((k+n+1)*((n+1)*(4*2)))))*(flightCeiling k n+1)

def flightCodec (k n : ℕ) : Flight k n ≃ Fin (flightSize k n) :=
  ({ toFun := fun f => (f.scanner,f.remaining)
     invFun := fun f => ⟨f.1,f.2⟩
     left_inv := by intro f; rfl
     right_inv := by intro f; rfl } :
      Flight k n ≃ (Scanner k n × Fin (flightCeiling k n+1))).trans
    (pairFin (scannerCodec k n) (Equiv.refl _))

def machineSize : ℕ :=
  runtimeSize*21504 + (runtimeSize*(21504*flightSize 43008 21504) + runtimeSize*21504)

def machineCodec : ServiceMachine ≃ Fin machineSize :=
  ({ toFun := fun q => match q with
      | .ready z s => .inl (z,s)
      | .scanning z s f => .inr (.inl (z,s,f))
      | .fault z s => .inr (.inr (z,s))
     invFun := fun q => match q with
      | .inl (z,s) => .ready z s
      | .inr (.inl (z,s,f)) => .scanning z s f
      | .inr (.inr (z,s)) => .fault z s
     left_inv := by intro q; cases q <;> rfl
     right_inv := by intro q; rcases q with ⟨z,s⟩ | ⟨z,s,f⟩ | ⟨z,s⟩ <;> rfl } :
      ServiceMachine ≃ ((Runtime × Service) ⊕ (Runtime × Service × Flight 43008 21504) ⊕
        (Runtime × Service))).trans
    (sumFin (pairFin runtimeCodec serviceCodec)
      (sumFin (pairFin runtimeCodec (pairFin serviceCodec (flightCodec 43008 21504)))
        (pairFin runtimeCodec serviceCodec)))

/-- The local controller encoding includes every possible paused/fault state and its countdown. -/
def machineCode (q : ServiceMachine) : List Bool := bitCode (machineCodec q)

/-- This is the old resident data plus local state bound; whole-renderer/interpreter code is separate. -/
def localBound : ℕ := B0 + machineSize + 1

private theorem machine_charge (base : MicroSnapshot) (q : ServiceMachine) :
    (machineCode q).length = machineSize ∧
    residentCode.length+(snapshotCode base).length+(machineCode q).length < localBound := by
  have hlen (p : ServiceMachine) : (machineCode p).length = machineSize := by
    exact bit_code_length (machineCodec p)
  have hres := (charged_snapshot_bound base).2.1
  refine ⟨hlen q,?_⟩
  rw [hlen,localBound]
  omega

private theorem machine_encoding : Function.Injective machineCode := by
  intro q r h
  exact machineCodec.injective (bit_code_injective h)

/-- Only this instruction receives a source bit; all its scanner microsteps are deterministic. -/
def serialBits : Service → List Letter → Option Service
  | s,[] => some s
  | s,b::bs => (scanService s b).bind fun q => serialBits q bs

private theorem serial_bits (s : Service) (bs : List Letter) :
    serialBits s bs = some (bs.foldl microStep s) := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    rw [serialBits,(scanned_programs runtimeInitial (.read b) s b).2.1]
    simpa using ih (microStep s b)

/-- Paused service states use precisely the remaining bits, never a new ready-entry law. -/
def serialTrial (s : Service) (p : Packet) : Option Service :=
  match s.pc with
  | .reset => (scanService s 0).bind fun q =>
      (serialBits q (packetBits p)).bind fun r => scanService r 0
  | .bit => (serialBits s ((packetBits p).take (7-s.bitPosition.val))).bind fun q =>
      scanService q 0
  | .compare => scanService s 0
  | .returned => some s

private theorem serial_trial (s : Service) (p : Packet) :
    serialTrial s p = some (finishTrial s p) := by
  have hstep (q : Service) (b : Letter) :=
    (scanned_programs runtimeInitial (.read b) q b).2.1
  cases hp : s.pc <;> simp only [serialTrial,hp,serial_bits,hstep,Option.bind_some,finishTrial]
  · have he : microStep s 0 = bitEntry s.thresholdTag := by
      simp [microStep,hp,bitEntry,entry]
    rw [he]
    rfl

/-- The loop retains only the finite service; the trial number is an external execution index. -/
def serialTrials (s : Service) (ω : ℕ → Packet) : ℕ → Option Service
  | 0 => some s
  | n+1 => (serialTrials s ω n).bind fun q => serialTrial q (ω n)

private theorem serial_trials (s : Service) (ω : ℕ → Packet) (n : ℕ) :
    serialTrials s ω n = some (trialRun s ω n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [serialTrials,ih,Option.bind_some,serial_trial]; rfl

/-- The first-hit search is a semantic evaluation of the serial loop, never an instruction. -/
noncomputable def serialReady (z : Runtime) (ω : ℕ → Letter) (k : ℕ) : Option Service :=
  (scanInitialization z).bind fun s =>
    let packets := packetize ω
    let suffix := FreshServiceRestart.unused acceptedPackets (0,0,0,0,0,0,0) k packets
    match FreshServiceRestart.firstHit acceptedPackets suffix with
    | none => none
    | some n => serialTrials s suffix (n+1)

private theorem serial_ready (z : Runtime) (ω : ℕ → Letter) (k : ℕ) :
    serialReady z ω k = executedReadyService (selectedThreshold z) ω k := by
  rw [serialReady,(scanned_programs z (.read 0) (entry .ordinary) 0).2.2,Option.bind_some]
  unfold executedReadyService
  dsimp only
  let suffix := FreshServiceRestart.unused acceptedPackets (0,0,0,0,0,0,0) k (packetize ω)
  change (match FreshServiceRestart.firstHit acceptedPackets suffix with
    | none => none | some n => serialTrials (entry (selectedThreshold z)) suffix (n+1)) =
    (match FreshServiceRestart.firstHit acceptedPackets suffix with
    | none => none | some n => some (trialRun (entry (selectedThreshold z)) suffix (n+1)))
  cases FreshServiceRestart.firstHit acceptedPackets suffix <;> simp only [serial_trials]

def packetColor (z : Runtime) (p : Packet) : Letter :=
  if (packetEquiv p).val < (threshold (selectedThreshold z)).val then 0 else 1

/-- Both pending and delivered use the original menu, without invoking the bit source. -/
noncomputable def serialOperation (z : Runtime) (ω : ℕ → Letter) (k : ℕ) :
    Option (Operation × Runtime) :=
  match z.fields.control with
  | .fourth (.pending b) => (scanNative z (.stop b)).map fun d => (.stop b,d)
  | .fourth .delivered => none
  | _ => (serialReady z ω k).bind fun s =>
      (scanNative z (.read s.output)).map fun d => (.read s.output,d)

def packetOperation (z : Runtime) (p : Packet) : Option (Operation × Runtime) :=
  (finiteOperation z.fields (packetColor z p)).bind fun op =>
    (runtimeStep z op).map fun d => (op,d)

/-- Infinite semantic coordinates are external; this recurrence stores only the current Runtime. -/
def packetStates (z : Runtime) (p : ℕ → Packet) : ℕ → Runtime
  | 0 => z
  | n+1 => ((packetOperation (packetStates z p n) (p n)).map Prod.snd).getD (packetStates z p n)

noncomputable def serialStates (z : Runtime) (ω : ℕ → Letter) : ℕ → Option Runtime
  | 0 => some z
  | n+1 => (serialStates z ω n).bind fun q =>
      match serialOperation q ω n with
      | none => if q.fields.control = .fourth .delivered then some q else none
      | some (_,d) => some d

private theorem read_permitted (z : Runtime)
    (hp : ∀ b, z.fields.control ≠ .fourth (.pending b))
    (hd : z.fields.control ≠ .fourth .delivered) (x : Letter) :
    ∃ d, runtimeStep z (.read x) = some d := by
  cases hc : z.fields.control with
  | seed a => cases a <;> simp [runtimeStep,finiteStep,finiteRead,hc]
  | early t s => simp [runtimeStep,finiteStep,finiteRead,hc]
  | fourth c => cases c with
    | active s => simp [runtimeStep,finiteStep,finiteRead,hc]
    | pending b => exact (hp b hc).elim
    | delivered => exact (hd hc).elim

private theorem operation_of_return (z : Runtime) (ω : ℕ → Letter) (k : ℕ)
    (h : ∀ t : Threshold, executedReadyService t ω k =
      some ⟨t,.returned,6,packetEquiv (acceptedStream ω k),
        if (packetEquiv (acceptedStream ω k)).val < (threshold t).val then 0 else 1⟩) :
    serialOperation z ω k = packetOperation z (acceptedStream ω k) := by
  have hnative (op : Operation) := (scanned_programs z op (entry .ordinary) 0).1
  have hs := (serial_ready z ω k).trans (h (selectedThreshold z))
  cases hc : z.fields.control with
  | seed a => simp [serialOperation,packetOperation,finiteOperation,hc,hs,hnative,packetColor]
  | early t s => simp [serialOperation,packetOperation,finiteOperation,hc,hs,hnative,packetColor]
  | fourth c => cases c <;>
      simp [serialOperation,packetOperation,finiteOperation,hc,hs,hnative,packetColor]

private theorem serial_states (z : Runtime) (ω : ℕ → Letter)
    (h : ∀ k : ℕ, ∀ t : Threshold, executedReadyService t ω k =
      some ⟨t,.returned,6,packetEquiv (acceptedStream ω k),
        if (packetEquiv (acceptedStream ω k)).val < (threshold t).val then 0 else 1⟩) :
    ∀ n, serialStates z ω n = some (packetStates z (acceptedStream ω) n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [serialStates,ih,Option.bind_some,operation_of_return _ _ _ (h n)]
    generalize hq : packetStates z (acceptedStream ω) n = q
    cases hc : q.fields.control with
    | seed a =>
      obtain ⟨d,hd⟩ := read_permitted q (by intro b hb; rw [hc] at hb; cases hb)
        (by rw [hc]; intro he; cases he) (packetColor q (acceptedStream ω n))
      simp [packetOperation,finiteOperation,hc,hd,packetStates,hq]
    | early t s =>
      obtain ⟨d,hd⟩ := read_permitted q (by intro b hb; rw [hc] at hb; cases hb)
        (by rw [hc]; intro he; cases he) (packetColor q (acceptedStream ω n))
      simp [packetOperation,finiteOperation,hc,hd,packetStates,hq]
    | fourth c => cases c with
      | active s =>
        obtain ⟨d,hd⟩ := read_permitted q (by intro b hb; rw [hc] at hb; cases hb)
          (by rw [hc]; intro he; cases he) (packetColor q (acceptedStream ω n))
        simp [packetOperation,finiteOperation,hc,hd,packetStates,hq]
      | pending b => simp [packetOperation,finiteOperation,runtimeStep,finiteStep,finiteStop,
          hc,packetStates,hq]
      | delivered => simp [packetOperation,finiteOperation,hc,packetStates,hq]

private theorem packet_states_measurable (z : Runtime) : Measurable (packetStates z) := by
  apply measurable_pi_lambda
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun p =>
      ((packetOperation (packetStates z p n) (p n)).map Prod.snd).getD (packetStates z p n))
    exact (measurable_of_finite (fun v : Runtime × Packet =>
      ((packetOperation v.1 v.2).map Prod.snd).getD v.1)).comp
        (ih.prodMk (measurable_pi_apply n))

private theorem accepted_measurable : Measurable acceptedStream := by
  have h := FreshServiceRestart.repeated_acceptance_law packetLaw acceptedPackets
    (0,0,0,0,0,0,0) (Set.toFinite _).measurableSet acceptance_positive
  change Measurable ((FreshServiceRestart.draws acceptedPackets (0,0,0,0,0,0,0)) ∘ packetize)
  exact h.1.comp (by unfold packetize vectorPacket; fun_prop)

/-- This is an adaptive whole-runtime law; it includes the original pending and delivered menus. -/
noncomputable def packetRuntimeLaw (z : Runtime) : Measure (ℕ → Option Runtime) :=
  (Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond packetLaw acceptedPackets)).map
    (fun p n => some (packetStates z p n))

private theorem serial_state_law (z : Runtime) :
    freshBitLaw.map (serialStates z) = packetRuntimeLaw z := by
  have hm : Measurable (fun p n => some (packetStates z p n)) :=
    (by fun_prop : Measurable (fun q : ℕ → Runtime => fun n => some (q n))).comp
      (packet_states_measurable z)
  have hs : serialStates z =ᵐ[freshBitLaw] (fun ω n => some (packetStates z (acceptedStream ω) n)) := by
    filter_upwards [repeated_fresh_bit_service.2] with ω hω
    exact funext (serial_states z ω hω)
  rw [Measure.map_congr hs]
  change freshBitLaw.map ((fun p n => some (packetStates z p n)) ∘ acceptedStream) = _
  rw [← Measure.map_map hm accepted_measurable,repeated_fresh_bit_service.1]
  rfl

/-- A common full-measure source event supports every adaptive return and native update,
    including prelude, partial original transactions, pending Stop and delivered cuts. -/
theorem serial_adaptive_execution :
    (∀ (k n : ℕ) (table : Fin k → Fin n) (s : Flight k n) (m : ℕ),
      m ≤ s.remaining.val →
      (flightRun table s m).scanner = (installedGraphStep table)^[m] s.scanner ∧
      (flightRun table s m).remaining.val = s.remaining.val-m) ∧
    (∀ (z : Runtime) (s : Service) (b : Letter),
      let x : Letter := if s.pc = .bit then b else 0
      let f : Flight 43008 21504 := flightEntry (bitKeyCodec (s,x))
      machineRun (machineStep (.ready z s) b) (f.remaining.val+1) = .ready z (microStep s b)) ∧
    (∀ (q : ServiceMachine) (a b : Letter), bitRequest q = false → machineStep q a = machineStep q b) ∧
    (∀ (base : MicroSnapshot) (q : ServiceMachine), (machineCode q).length = machineSize ∧
      residentCode.length+(snapshotCode base).length+(machineCode q).length < localBound) ∧
    Function.Injective machineCode ∧
    (∀ (s : Service) (p : Packet), serialTrial s p = some (finishTrial s p)) ∧
    (∀ z : Runtime, freshBitLaw.map (serialStates z) = packetRuntimeLaw z) ∧
    (∀ᵐ ω ∂freshBitLaw, ∀ z : Runtime,
      (∀ n, serialStates z ω n = some (packetStates z (acceptedStream ω) n)) ∧
      ∀ k, serialOperation (packetStates z (acceptedStream ω) k) ω k =
        packetOperation (packetStates z (acceptedStream ω) k) (acceptedStream ω k)) := by
  refine ⟨fun _ _ table s m hm => flight_invariant table s m hm,machine_instruction,
    machine_port,machine_charge,machine_encoding,serial_trial,serial_state_law,?_⟩
  filter_upwards [repeated_fresh_bit_service.2] with ω hω
  intro z
  exact ⟨serial_states z ω hω,fun k => operation_of_return _ _ _ (hω k)⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorSerialExecution
