/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Charged sequential primitives consume fair bits only at requests and have exact trajectory cylinders. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixState
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Set Finset Preorder
open scoped ENNReal NNReal BigOperators
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn

/-- Alternatives of one decoded instruction, not an arbitrary stochastic row. -/
inductive Instruction (S : Type) where
  | deterministic (next : S)
  | fair (zero one : S)

/-- External coordinates never belong to a machine snapshot. -/
def tail (ω : ℕ → Bool) : ℕ → Bool := fun n => ω (n+1)

def successor {S : Type} (i : Instruction S) (ω : ℕ → Bool) : S × (ℕ → Bool) :=
  match i with
  | .deterministic s => (s,ω)
  | .fair s t => (if ω 0 then t else s,tail ω)

/-- Deterministic instructions leave the entire unused suffix alone. -/
def run {S : Type} (decode : S → Instruction S) (s : S) (ω : ℕ → Bool) : ℕ → S
  | 0 => s
  | n+1 => let p := successor (decode s) ω; run decode p.1 p.2 n

def requests {S : Type} (decode : S → Instruction S) (s : S) (ω : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n+1 =>
    match decode s with
    | .deterministic t => requests decode t ω n
    | .fair t u => 1 + requests decode (if ω 0 then u else t) (tail ω) n

/-- Unused suffix is an external coordinate, never a retained random tape. -/
def unused {S : Type} (decode : S → Instruction S) (s : S) (ω : ℕ → Bool) :
    ℕ → (ℕ → Bool)
  | 0 => ω
  | n+1 => let p := successor (decode s) ω; unused decode p.1 p.2 n

theorem unused_suffix {S : Type} (decode : S → Instruction S)
    (s : S) (ω : ℕ → Bool) (n k : ℕ) :
    unused decode s ω n k = ω (k + requests decode s ω n) := by
  induction n generalizing s ω with
  | zero => simp [unused,requests]
  | succ n ih =>
    cases h : decode s with
    | deterministic t => simpa [unused,successor,requests,h] using ih t ω
    | fair t u =>
      simp only [unused,successor,requests,h]
      rw [ih]
      unfold tail
      congr 1
      omega

def fairBit : PMF Bool := PMF.bernoulli (1/2) (by norm_num)

theorem fair_bit_mass (b : Bool) : fairBit b = (1/2 : ℝ≥0∞) := by
  cases b <;> norm_num [fairBit,PMF.bernoulli_apply]

def tapeLaw : Measure (ℕ → Bool) := Measure.infinitePi (fun _ => fairBit.toMeasure)
instance : IsProbabilityMeasure tapeLaw := by unfold tapeLaw; infer_instance

theorem split_tape :
    tapeLaw.map (fun ω => (ω 0,tail ω)) = fairBit.toMeasure.prod tapeLaw := by
  have h := FreshServiceRestart.first_acceptance_restart fairBit.toMeasure univ false
    MeasurableSet.univ (by rw [measure_univ]; exact one_ne_zero)
  have he : FreshServiceRestart.restart univ false = fun ω : ℕ → Bool => (ω 0,tail ω) := by
    funext ω
    have hh : FreshServiceRestart.firstHit univ ω = some 0 :=
      (FreshServiceRestart.first_hit_some univ ω 0).mpr ⟨mem_univ _,by simp⟩
    simp only [FreshServiceRestart.restart,hh,FreshServiceRestart.shift,tail]
    rfl
  rw [he,ProbabilityTheory.cond_univ] at h
  exact h

def row {S : Type} (decode : S → Instruction S) (s : S) : PMF S :=
  match decode s with
  | .deterministic t => PMF.pure t
  | .fair t u => fairBit.map (fun b => if b then u else t)

theorem row_fair {S : Type} (t u v : S) :
    (fairBit.map (fun b => if b then u else t)) v =
      (if v=t then (1/2 : ℝ≥0∞) else 0) + (if v=u then (1/2 : ℝ≥0∞) else 0) := by
  rw [PMF.map_apply,tsum_fintype]
  simp [Fintype.sum_bool,fair_bit_mass,add_comm]

def instructionKernel {S : Type} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (decode : S → Instruction S) : Kernel S S :=
  Kernel.ofFunOfCountable (fun s => (row decode s).toMeasure)
instance {S : Type} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] (decode : S → Instruction S) :
    IsMarkovKernel (instructionKernel decode) :=
  ⟨fun s => by
    change IsProbabilityMeasure (row decode s).toMeasure
    infer_instance⟩

def instructionLaw {S : Type} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (decode : S → Instruction S) (s : S) : Measure (ℕ → S) :=
  Kernel.trajMeasure (X := fun _ => S) (Measure.dirac s)
    (fun n => (instructionKernel decode).comap
      (fun x : Finset.Iic n → S => x ⟨n,Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _))

theorem measurable_run {S : Type} [MeasurableSpace S]
    (decode : S → Instruction S) (s : S) (n : ℕ) :
    Measurable (fun ω => run decode s ω n) := by
  induction n generalizing s with
  | zero => exact measurable_const
  | succ n ih =>
    cases h : decode s with
    | deterministic t => simpa [run,successor,h] using ih t
    | fair t u =>
      have ht : Measurable tail := by unfold tail; fun_prop
      have he : MeasurableSet {ω : ℕ → Bool | ω 0 = true} := by measurability
      have hh : (fun ω => run decode s ω (n+1)) =
          fun ω => if ω 0 then run decode u (tail ω) n else run decode t (tail ω) n := by
        funext ω
        simp only [run,successor,h]
        split <;> rfl
      rw [hh]
      exact Measurable.ite he ((ih u).comp ht) ((ih t).comp ht)

private def cylinder {S : Type} (decode : S → Instruction S) (s : S)
    (n : ℕ) (w : Fin (n+1) → S) : Set (ℕ → Bool) :=
  {ω | ∀ i : Fin (n+1), run decode s ω i.val = w i}

private theorem cylinder_measurable {S : Type} [MeasurableSpace S]
    [MeasurableSingletonClass S] (decode : S → Instruction S) (s : S)
    (n : ℕ) (w : Fin (n+1) → S) : MeasurableSet (cylinder decode s n w) := by
  have he : cylinder decode s n w = ⋂ i : Fin (n+1),
      (fun ω => run decode s ω i.val) ⁻¹' {w i} := by
    ext ω
    simp [cylinder]
  rw [he]
  exact MeasurableSet.iInter (fun i =>
    (measurableSet_singleton (w i)).preimage (measurable_run decode s i.val))

private theorem cylinder_succ {S : Type} (decode : S → Instruction S) (s : S)
    (n : ℕ) (w : Fin (n+2) → S) (ω : ℕ → Bool) :
    ω ∈ cylinder decode s (n+1) w ↔
      s = w 0 ∧ (successor (decode s) ω).2 ∈
        cylinder decode (successor (decode s) ω).1 n (Fin.tail w) := by
  simp only [cylinder,mem_setOf_eq]
  constructor
  · intro h
    exact ⟨h 0,fun i => h i.succ⟩
  · rintro ⟨h0,hs⟩ i
    exact Fin.cases h0 (fun j => hs j) i

private theorem fair_cylinder {S : Type} [MeasurableSpace S] [MeasurableSingletonClass S]
    (decode : S → Instruction S) (t u : S) (n : ℕ) (w : Fin (n+1) → S) :
    tapeLaw {ω | tail ω ∈ cylinder decode (if ω 0 then u else t) n w} =
      (1/2 : ℝ≥0∞) * tapeLaw (cylinder decode t n w) +
      (1/2 : ℝ≥0∞) * tapeLaw (cylinder decode u n w) := by
  let E := ({false} ×ˢ cylinder decode t n w) ∪ ({true} ×ˢ cylinder decode u n w)
  have he : {ω : ℕ → Bool | tail ω ∈ cylinder decode (if ω 0 then u else t) n w} =
      (fun ω => (ω 0,tail ω)) ⁻¹' E := by
    ext ω
    cases h : ω 0 <;> simp [E,h]
  have hE : MeasurableSet E := ((measurableSet_singleton _).prod
    (cylinder_measurable decode t n w)).union ((measurableSet_singleton _).prod
    (cylinder_measurable decode u n w))
  rw [he,← Measure.map_apply (by unfold tail; fun_prop) hE,split_tape]
  have hd : Disjoint ({false} ×ˢ cylinder decode t n w) ({true} ×ˢ cylinder decode u n w) := by
    rw [Set.disjoint_left]
    rintro ⟨b,ω⟩ ⟨hb,_⟩ ⟨hb',_⟩
    simp only [mem_singleton_iff] at hb hb'
    exact Bool.false_ne_true (hb.symm.trans hb')
  rw [show E = _ from rfl,measure_union hd
      ((measurableSet_singleton _).prod (cylinder_measurable decode u n w)),
    Measure.prod_prod,Measure.prod_prod]
  simp [PMF.toMeasure_apply_singleton,fair_bit_mass]

/-- The operational induction is proved before the Markov identification. -/
private theorem operational_cylinder {S : Type} [MeasurableSpace S]
    [MeasurableSingletonClass S] (decode : S → Instruction S) (s : S)
    (n : ℕ) (w : Fin (n+1) → S) :
    tapeLaw (cylinder decode s n w) =
      (if w 0 = s then 1 else 0) * ∏ i : Fin n, row decode (w i.castSucc) (w i.succ) := by
  induction n generalizing s with
  | zero =>
    have he : cylinder decode s 0 w = if w 0 = s then univ else ∅ := by
      ext ω
      simp [cylinder,run,Subsingleton.elim (0 : Fin 1),eq_comm]
    rw [he]
    split <;> simp
  | succ n ih =>
    by_cases h0 : w 0 = s
    · subst s
      cases hi : decode (w 0) with
      | deterministic t =>
        have he : cylinder decode (w 0) (n+1) w = cylinder decode t n (Fin.tail w) := by
          ext ω
          simp [cylinder_succ,hi,successor]
        rw [he,ih,Fin.prod_univ_succ]
        simp only [Fin.castSucc_zero,Fin.tail,Fin.succ_castSucc,
          row,hi,PMF.pure_apply,ite_true,one_mul]
        rfl
      | fair t u =>
        have he : cylinder decode (w 0) (n+1) w =
            {ω | tail ω ∈ cylinder decode (if ω 0 then u else t) n (Fin.tail w)} := by
          ext ω
          simp [cylinder_succ,hi,successor]
        rw [he,fair_cylinder,ih,ih,Fin.prod_univ_succ]
        simp only [Fin.castSucc_zero,Fin.tail,Fin.succ_castSucc,
          row,hi,ite_true,one_mul,row_fair]
        simp only [show Fin.succ (0 : Fin (n+1)) = (1 : Fin (n+2)) from rfl]
        split_ifs <;> simp_all [mul_add,add_mul,mul_assoc]
    · have he : cylinder decode s (n+1) w = ∅ := by
        ext ω
        simp only [Set.mem_empty_iff_false,iff_false]
        intro hh
        exact h0 ((cylinder_succ decode s n w ω).mp hh).1.symm
      rw [he,measure_empty,if_neg h0,zero_mul]

/-- Actual variable-request fair execution has the instruction-kernel prefix law. -/
theorem execution_prefix_law {S : Type} [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (decode : S → Instruction S) (s : S)
    (n : ℕ) (w : Fin (n+1) → S) :
    (tapeLaw.map (fun ω i => run decode s ω (i : Fin (n+1)))) {w} =
      ((instructionLaw decode s).map (fun x i => x (i : Fin (n+1)))) {w} := by
  rw [Measure.map_apply (by
    exact Measurable.of_eval (fun i => measurable_run decode s i.val))
    (measurableSet_singleton _)]
  have he : (fun ω i => run decode s ω (i : Fin (n+1))) ⁻¹' {w} =
      cylinder decode s n w := by
    ext ω
    simp only [Set.mem_preimage,Set.mem_singleton_iff,cylinder,Set.mem_setOf_eq,funext_iff]
  rw [he]
  rw [operational_cylinder, instructionLaw,
    MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton]
  simp [instructionKernel,Kernel.ofFunOfCountable,
    PMF.toMeasure_apply_singleton,Measure.dirac_apply',Pi.single_apply,eq_comm]

/-- Only decoded sequential primitives, rather than state transition tables. -/
inductive Command (p a : ℕ) where
  | read (zero one : Fin p)
  | write (b : Bool) (next : Fin p)
  | move (right : Bool) (next : Fin p)
  | fair (zero one : Fin p)
  | fairStore (next : Fin p)
  | buffer (symbol : Fin a) (next : Fin p)
  | send (next : Fin p)
  | letter (next : Fin p)
  | finish

inductive ServiceMode where
  | initialize | alpha | beta | nextLetter | stop
  deriving DecidableEq

instance : Fintype ServiceMode := ⟨{.initialize,.alpha,.beta,.nextLetter,.stop},by
  intro x; cases x <;> simp⟩

/-- Decoded primitive address view. Paid instruction fetching is a separate refinement. -/
structure Program (p a : ℕ) where
  code : Fin p → Command p a
  entry : ServiceMode → Option (Fin p)

structure Snapshot (p m a : ℕ) where
  tape : Fin (m+1) → Bool
  head : Fin (m+1)
  pc : Fin p
  mode : ServiceMode
  input : Option FourthSegmentStoppedLaw.Letter
  buffer : Option (Fin a)
  deriving DecidableEq

instance {p m a : ℕ} : Fintype (Snapshot p m a) :=
  Fintype.ofEquiv
    ((Fin (m+1) → Bool) × Fin (m+1) × Fin p × ServiceMode ×
      Option FourthSegmentStoppedLaw.Letter × Option (Fin a))
    { toFun := fun x => ⟨x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2.1,x.2.2.2.2.2⟩
      invFun := fun s => (s.tape,s.head,s.pc,s.mode,s.input,s.buffer)
      left_inv := by intro x; rfl
      right_inv := by intro s; rfl }

/-- Renderer characters and semantic selected letters are distinct events. -/
structure Event (a : ℕ) where
  rendered : Option (Fin a) := none
  selected : Option FourthSegmentStoppedLaw.Letter := none
  returned : Bool := false

structure Action (p m a : ℕ) where
  snapshot : Snapshot p m a
  event : Event a

def bitLetter (b : Bool) : FourthSegmentStoppedLaw.Letter := if b then 1 else 0

/-- Local actions. Multi-bit computation and provider state use the charged tape.
    Head movement is totalized at the ends; a source refinement must establish
    its own valid movement boundary before applying this interpretation. -/
def act {p m a : ℕ} (P : Program p a) (s : Snapshot p m a) (b : Bool) : Action p m a :=
  match P.code s.pc with
  | .read z o => ⟨{s with pc := if s.tape s.head then o else z},{}⟩
  | .write v n => ⟨{s with tape := Function.update s.tape s.head v, pc := n},{}⟩
  | .move r n =>
    ⟨{s with head := ⟨if r then min m (s.head.val+1) else s.head.val-1,by
        split <;> have := s.head.isLt <;> omega⟩,pc := n},{}⟩
  | .fair z o => ⟨{s with pc := if b then o else z},{}⟩
  | .fairStore n => ⟨{s with tape := Function.update s.tape s.head b,pc := n},{}⟩
  | .buffer v n => ⟨{s with buffer := some v,pc := n},{}⟩
  | .send n => ⟨{s with pc := n},⟨s.buffer,none,false⟩⟩
  | .letter n => ⟨{s with pc := n},⟨none,some (bitLetter (s.tape s.head)),false⟩⟩
  | .finish => ⟨s,⟨none,none,true⟩⟩

def asks {p a : ℕ} : Command p a → Bool
  | .fair _ _ | .fairStore _ => true
  | _ => false

def decoded {p m a : ℕ} (P : Program p a) (s : Snapshot p m a) :
    Instruction (Snapshot p m a) :=
  if asks (P.code s.pc) then .fair (act P s false).snapshot (act P s true).snapshot
  else .deterministic (act P s false).snapshot

private theorem deterministic_action {p m a : ℕ} (P : Program p a) (s : Snapshot p m a)
    (h : asks (P.code s.pc) = false) (b : Bool) : act P s b = act P s false := by
  cases hc : P.code s.pc <;> simp_all [asks,act]

/-- Completion belongs to this launch; old work fields need not be reset. -/
def launch {p m a : ℕ} (P : Program p a) (s : Snapshot p m a)
    (mode : ServiceMode) (input : Option FourthSegmentStoppedLaw.Letter) : Action p m a :=
  match P.entry mode with
  | none => ⟨{s with mode := mode,input := input},⟨none,none,true⟩⟩
  | some pc => ⟨{s with mode := mode,input := input,pc := pc},{}⟩

/-- The initial action is the real launch event. Later coordinates are
    primitive actions on the same physical snapshot; no runtime event log is added. -/
def trace {p m a : ℕ} (P : Program p a) (start : Action p m a)
    (ω : ℕ → Bool) : ℕ → Action p m a × (ℕ → Bool)
  | 0 => (start,ω)
  | n+1 =>
    let z := if asks (P.code start.snapshot.pc)
      then (act P start.snapshot (ω 0),tail ω) else (act P start.snapshot false,ω)
    trace P z.1 z.2 n

/-- Bounded actual execution stops at this invocation's first return event. -/
def executeUntil {p m a : ℕ} (P : Program p a) (start : Action p m a)
    (ω : ℕ → Bool) : ℕ → Option (Snapshot p m a)
  | 0 => if start.event.returned then some start.snapshot else none
  | n+1 =>
    if start.event.returned then some start.snapshot
    else
      let z := if asks (P.code start.snapshot.pc)
        then (act P start.snapshot (ω 0),tail ω) else (act P start.snapshot false,ω)
      executeUntil P z.1 z.2 n

def firstReturnAt {p m a : ℕ} (P : Program p a) (start : Action p m a)
    (ω : ℕ → Bool) (k : ℕ) : Prop :=
  (trace P start ω k).1.event.returned = true ∧
    ∀ j < k, (trace P start ω j).1.event.returned = false

/-- The analytical event cut equals bounded execution of the original return
    protocol and retains the entire returned snapshot. It includes k = 0. -/
private theorem bounded_return_iff {p m a : ℕ} (P : Program p a) (start : Action p m a)
    (ω : ℕ → Bool) (n : ℕ) (t : Snapshot p m a) :
    executeUntil P start ω n = some t ↔
      ∃ k ≤ n, firstReturnAt P start ω k ∧ (trace P start ω k).1.snapshot = t := by
  induction n generalizing start ω with
  | zero =>
    cases h : start.event.returned <;> simp [executeUntil,firstReturnAt,trace,h]
  | succ n ih =>
    let z := if asks (P.code start.snapshot.pc)
      then (act P start.snapshot (ω 0),tail ω) else (act P start.snapshot false,ω)
    have hs (j : ℕ) : trace P start ω (j+1) = trace P z.1 z.2 j := rfl
    cases h : start.event.returned with
    | true =>
      simp only [executeUntil,h,ite_true,Option.some.injEq]
      constructor
      · intro ht
        exact ⟨0,Nat.zero_le _,⟨h,by simp⟩,ht⟩
      · rintro ⟨k,hkn,⟨hk,hp⟩,ht⟩
        cases k with
        | zero => exact ht
        | succ k =>
          have hh := hp 0 (by omega)
          simp [trace,h] at hh
    | false =>
      simp only [executeUntil,h,Bool.false_eq_true,ite_false]
      change executeUntil P z.1 z.2 n = some t ↔ _
      rw [ih]
      constructor
      · rintro ⟨k,hkn,⟨hk,hp⟩,ht⟩
        refine ⟨k+1,by omega,⟨by rw [hs]; exact hk,?_⟩,by rw [hs]; exact ht⟩
        intro j hj
        cases j with
        | zero => exact h
        | succ j => rw [hs]; exact hp j (by omega)
      · rintro ⟨k,hkn,⟨hk,hp⟩,ht⟩
        cases k with
        | zero => simp [trace,h] at hk
        | succ k =>
          refine ⟨k,by omega,⟨by rw [← hs]; exact hk,?_⟩,by rw [← hs]; exact ht⟩
          intro j hj
          rw [← hs]
          exact hp (j+1) (by omega)

/-- Every genuine launch, including immediate completion, uses the first
    return of this invocation and retains all persistent returned fields. -/
theorem invocation_return_iff {p m a : ℕ} (P : Program p a) (s : Snapshot p m a)
    (mode : ServiceMode) (input : Option FourthSegmentStoppedLaw.Letter)
    (ω : ℕ → Bool) (n : ℕ) (t : Snapshot p m a) :
    executeUntil P (launch P s mode input) ω n = some t ↔
      ∃ k ≤ n, firstReturnAt P (launch P s mode input) ω k ∧
        (trace P (launch P s mode input) ω k).1.snapshot = t := by
  exact bounded_return_iff P (launch P s mode input) ω n t

/-- Original membership supplies a representation of this installation's
    admitted complete snapshots. The decoded resident code is recovered with
    the runtime fields; other installations need not fit the same B. -/
structure CompleteCodec {p m a : ℕ} (P : Program p a)
    (micro : Set (Snapshot p m a)) (B : ℕ) where
  encode : micro → (Fin B → Bool)
  decode : (Fin B → Bool) → Option (Program p a × Snapshot p m a)
  roundtrip : ∀ s, decode (encode s) = some (P,s.val)

private theorem codec_injective {p m a B : ℕ} {P : Program p a}
    {micro : Set (Snapshot p m a)} (c : CompleteCodec P micro B) :
    Function.Injective c.encode := by
  intro x y h
  have hd := congrArg c.decode h
  rw [c.roundtrip,c.roundtrip] at hd
  exact Subtype.ext (congrArg Prod.snd (Option.some.inj hd))

theorem charged_cardinality {p m a B : ℕ} {P : Program p a}
    {micro : Set (Snapshot p m a)} (c : CompleteCodec P micro B) (ready : Set micro) :
    Nat.card micro ≤ 2^B ∧ Nat.card ready ≤ 2^B := by
  letI : Finite micro := Finite.of_injective _ (codec_injective c)
  have hle := Nat.card_le_card_of_injective _ (codec_injective c)
  have he : Nat.card (Fin B → Bool) = 2^B := by
    rw [Nat.card_eq_fintype_card]
    simp
  rw [he] at hle
  exact ⟨hle,(Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans hle⟩

/-- A bit is consulted only in the fair branch of the physical step. -/
def physicalStep {p m a : ℕ} (P : Program p a) (s : Snapshot p m a)
    (ω : ℕ → Bool) : Action p m a × (ℕ → Bool) :=
  if asks (P.code s.pc) then (act P s (ω 0),tail ω) else (act P s false,ω)

/-- This is an external trace, not a machine output-history register. The
    invocation stops at the first returned event; the trace totalizes it. -/
def physicalRun {p m a : ℕ} (P : Program p a) (s : Snapshot p m a)
    (ω : ℕ → Bool) : ℕ → Snapshot p m a
  | 0 => s
  | n+1 => let z := physicalStep P s ω; physicalRun P z.1.snapshot z.2 n

/-- One common primitive graph for all supplied entrances. Both fair branches
    belong to it; deterministic branches coincide. It is an analysis predicate. -/
inductive Reachable {p m a : ℕ} (P : Program p a)
    (entrances : Set (Snapshot p m a)) : Snapshot p m a → Prop where
  | entrance {s} : s ∈ entrances → Reachable P entrances s
  | step {s} : Reachable P entrances s → (b : Bool) →
      Reachable P entrances (act P s b).snapshot

private theorem physical_run_reachable {p m a : ℕ} (P : Program p a)
    (entrances : Set (Snapshot p m a)) (s : Snapshot p m a)
    (hs : Reachable P entrances s) (ω : ℕ → Bool) (n : ℕ) :
    Reachable P entrances (physicalRun P s ω n) := by
  induction n generalizing s ω with
  | zero => exact hs
  | succ n ih =>
    simp only [physicalRun]
    apply ih
    unfold physicalStep
    split
    · exact Reachable.step hs (ω 0)
    · exact Reachable.step hs false

private theorem physical_step_identification {p m a : ℕ} (P : Program p a)
    (s : Snapshot p m a) (ω : ℕ → Bool) :
    ((physicalStep P s ω).1.snapshot,(physicalStep P s ω).2) =
      successor (decoded P s) ω := by
  unfold physicalStep decoded
  split
  · simp only [successor,Prod.fst,Prod.snd]
    cases h : ω 0 <;> rfl
  · rfl

private theorem physical_run_identification {p m a : ℕ} (P : Program p a)
    (s : Snapshot p m a) (ω : ℕ → Bool) (n : ℕ) :
    physicalRun P s ω n = run (decoded P) s ω n := by
  induction n generalizing s ω with
  | zero => rfl
  | succ n ih =>
    simp only [physicalRun,run]
    rw [← physical_step_identification]
    exact ih _ _

/-- Local deterministic primitives are independent of an unused hypothetical
    bit, and the concrete physical execution has the charged kernel cylinders. -/
theorem charged_execution_prefix {p m a B : ℕ} (P : Program p a)
    (entrances : Set (Snapshot p m a))
    (c : CompleteCodec P {t | Reachable P entrances t} B)
    (ready : Set {t | Reachable P entrances t})
    [MeasurableSpace (Snapshot p m a)]
    [MeasurableSingletonClass (Snapshot p m a)] (s : Snapshot p m a)
    (hs : Reachable P entrances s)
    (n : ℕ) (w : Fin (n+1) → Snapshot p m a) :
    Nat.card {t | Reachable P entrances t} ≤ 2^B ∧ Nat.card ready ≤ 2^B ∧
    (∀ ω : ℕ → Bool, Reachable P entrances (physicalRun P s ω n)) ∧
    (∀ (z : Snapshot p m a) (b : Bool), asks (P.code z.pc) = false →
      act P z b = act P z false) ∧
    (∀ (ω : ℕ → Bool) (k : ℕ), unused (decoded P) s ω n k =
      ω (k + requests (decoded P) s ω n)) ∧
    (tapeLaw.map (fun ω i => physicalRun P s ω (i : Fin (n+1)))) {w} =
      ((instructionLaw (decoded P) s).map (fun x i => x (i : Fin (n+1)))) {w} := by
  obtain ⟨hm,hr⟩ := charged_cardinality c ready
  refine ⟨hm,hr,fun ω => physical_run_reachable P entrances s hs ω n,
    fun z b h => deterministic_action P z h b,
    fun ω k => unused_suffix (decoded P) s ω n k,?_⟩
  simp only [physical_run_identification]
  exact execution_prefix_law (decoded P) s n w

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn
