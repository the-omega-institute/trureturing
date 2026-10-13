/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/PaidTraceResidual
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/PaidTraceResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual paid receipts and almost-sure completed correctness derive Read residual simulation. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitReturnRestart

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory Set
open scoped ENNReal BigOperators
local instance {O : Type} : MeasurableSpace (Option O) := ⊤
local instance {O : Type} : MeasurableSingletonClass (Option O) := ⟨fun _ => trivial⟩
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.PaidTraceResidual
open OriginalNativeServiceBridge OriginalNativeServiceBridge.Initialization
open NativeAcquiredPrefixState NativeFullResidual FourthSegmentStoppedLaw
open FiniteFairBitFirstReturn FiniteFairBitExitLaws

variable {S Head Symbol : Type} [DecidableEq Head] [DecidableEq Symbol] {B : ℕ}

/-- Current-call return is an observation of the paid prestate and actual receipt.
    This interface does not prescribe a stack or saved-frame implementation. -/
structure ReturnCut (A : Architecture S Head Symbol B) where
  observe : S → (S × PrimitiveReceipt Symbol) → Option (Ready A)
  state : ∀ s r y, observe s r = some y → y.val = r.1

instance (A : Architecture S Head Symbol B) :
    CoeFun (ReturnCut A) (fun _ => S → (S × PrimitiveReceipt Symbol) → Option (Ready A)) :=
  ⟨ReturnCut.observe⟩

/-- The existing frame detector returns the actual complete successor snapshot. -/
def savedCut (A : Architecture S Head Symbol B) : ReturnCut A where
  observe := currentReturn A
  state := by
    intro s r y h
    unfold currentReturn at h
    split at h
    · exact congrArg Subtype.val (Option.some.inj h).symm
    · cases h

/-- A receipt includes its actual sending prestate. No endpoint decoder is used. -/
abbrev Receipt (S Symbol : Type) := S × (S × PrimitiveReceipt Symbol)

def target (A : Architecture S Head Symbol B) (C : ReturnCut A)
    (s : S) (r : S × PrimitiveReceipt Symbol) : S ⊕ Ready A :=
  match C s r with | none => .inl r.1 | some y => .inr y

def tickTarget (A : Architecture S Head Symbol B) (C : ReturnCut A)
    (s : S) (r : S × Option (PrimitiveReceipt Symbol)) : S ⊕ Ready A :=
  match r.2 with | none => .inl r.1 | some e => target A C s (r.1,e)

/-- Independent source execution: permitted local actions, physical sends, and
    the supplied actual current cut. Returned copies are proof coordinates. -/
def sourceTrace (A : Architecture S Head Symbol B) (C : ReturnCut A)
    (a : S ⊕ Ready A) (ω : ℕ → Bool) : ℕ → (S ⊕ Ready A) × List (Receipt S Symbol)
  | 0 => (a,[])
  | n+1 => match a with
    | .inr y => (.inr y,[])
    | .inl s =>
      let r := nativeTick A s ω
      let v := sourceTrace A C (tickTarget A C s r.1) r.2 n
      (v.1,(match r.1.2 with | none => [] | some e => [(s,(r.1.1,e))]) ++ v.2)

/-- The graph is derived from the local source, on exactly S. Receipts and proof
    words do not enlarge its internal carrier. -/
def instruction (A : Architecture S Head Symbol B) (C : ReturnCut A) (s : S) :
    Instruction (S ⊕ Ready A) :=
  mapInstruction (tickTarget A C s) (primitiveInstruction A s)

/-- One actual enabled source edge; both fair receipts remain available even
    when their complete successor states coincide. -/
def Edge (A : Architecture S Head Symbol B) (C : ReturnCut A)
    (s : S) (r : S × PrimitiveReceipt Symbol) (a : S ⊕ Ready A) : Prop :=
  (∃ b, A.nativeEdge s b r) ∧ a = target A C s r

inductive Prefix (A : Architecture S Head Symbol B) (C : ReturnCut A) (a : S) :
    List (Receipt S Symbol) → S → Prop
  | nil : Prefix A C a [] a
  | step {p s r t} : Prefix A C a p s → Edge A C s r (.inl t) →
      Prefix A C a (p ++ [(s,r)]) t

inductive Complete (A : Architecture S Head Symbol B) (C : ReturnCut A) :
    S → List (Receipt S Symbol) → Ready A → Prop
  | exit {s r y} : Edge A C s r (.inr y) → Complete A C s [(s,r)] y
  | step {s r t p y} : Edge A C s r (.inl t) → Complete A C t p y →
      Complete A C s ([(s,r)] ++ p) y

/-- This is a proof readout of actually sent symbols at their paid prestates.
    Correct interpretation as the original event alphabet is a separate premise. -/
def events (decode : S → Symbol → Option OriginalEvent)
    (rs : List (Receipt S Symbol)) : List OriginalEvent :=
  rs.filterMap fun e => e.2.2.sent.bind (decode e.1)

private theorem events_append (decode : S → Symbol → Option OriginalEvent)
    (p v : List (Receipt S Symbol)) : events decode (p ++ v) = events decode p ++ events decode v :=
  List.filterMap_append

theorem prepend (A : Architecture S Head Symbol B) (C : ReturnCut A)
    {a p s v y} (hp : Prefix A C a p s) (hv : Complete A C s v y) :
    Complete A C a (p ++ v) y := by
  induction hp generalizing v with
  | nil => simpa using hv
  | step hp he ih => simpa [List.append_assoc] using ih (Complete.step he hv)

variable [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

private theorem trace_return (A : Architecture S Head Symbol B) (C : ReturnCut A)
    (y : Ready A) (ω : ℕ → Bool) (n : ℕ) : sourceTrace A C (.inr y) ω n = (.inr y,[]) := by
  cases n <;> rfl

private theorem trace_state (A : Architecture S Head Symbol B) (C : ReturnCut A)
    (a : S ⊕ Ready A) (ω : ℕ → Bool) (n : ℕ) :
    (sourceTrace A C a ω n).1 = path (instruction A C) a ω n := by
  induction n generalizing a ω with
  | zero => rfl
  | succ n ih =>
    cases a with
    | inr y => simpa [sourceTrace] using (path_exit (instruction A C) y ω (n+1)).symm
    | inl s =>
      have hm : successor (instruction A C s) ω =
          (tickTarget A C s (nativeTick A s ω).1,(nativeTick A s ω).2) := by
        rw [tick_refinement]
        unfold instruction
        cases h : primitiveInstruction A s with
        | deterministic r => rfl
        | fair r t => cases hb : ω 0 <;> simp [mapInstruction,successor,hb]
      change (sourceTrace A C (.inl s) ω (n+1)).1 =
        run (stopped (instruction A C)) (successor (instruction A C s) ω).1
          (successor (instruction A C s) ω).2 n
      rw [hm]
      exact ih _ _

private theorem trace_stable (A : Architecture S Head Symbol B) (C : ReturnCut A)
    (a : S ⊕ Ready A) (ω σ : ℕ → Bool) (n : ℕ)
    (h : ∀ i < n, ω i = σ i) : sourceTrace A C a ω n = sourceTrace A C a σ n := by
  induction n generalizing a ω σ with
  | zero => rfl
  | succ n ih =>
    cases a with
    | inr y => rfl
    | inl s =>
      by_cases he : A.enabled s
      · by_cases hf : A.action s = .freshBit
        · have h0 := h 0 (Nat.zero_lt_succ n)
          have ht : ∀ i < n, tail ω i = tail σ i :=
            fun i hi => h (i+1) (Nat.succ_lt_succ hi)
          simp only [sourceTrace,nativeTick,he,if_pos,hf,← h0]
          rw [ih _ (tail ω) (tail σ) ht]
        · simp only [sourceTrace,nativeTick,he,if_pos,hf,if_neg,↓reduceIte]
          rw [ih _ ω σ (fun i hi => h i (Nat.lt_succ_of_lt hi))]
      · simp only [sourceTrace,nativeTick,he,if_neg,↓reduceIte]
        rw [ih _ ω σ (fun i hi => h i (Nat.lt_succ_of_lt hi))]

private theorem fair_prefix_mass (n : ℕ) (ω : ℕ → Bool) :
    tapeLaw {σ | ∀ i ∈ Finset.range n, σ i = ω i} = (1/2 : ℝ≥0∞)^n := by
  change Measure.infinitePi (fun _ : ℕ => fairBit.toMeasure)
    (Set.pi (↑(Finset.range n)) (fun i => {ω i})) = _
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  have hb (i : ℕ) : fairBit.toMeasure {ω i} = (1/2 : ℝ≥0∞) := by
    rw [PMF.toMeasure_apply_singleton fairBit (ω i) (measurableSet_singleton _)]
    exact fair_bit_mass (ω i)
  simp_rw [hb]
  simp

theorem finite_good (A : Architecture S Head Symbol B) (C : ReturnCut A)
    (a : S ⊕ Ready A) (n : ℕ)
    (Good : (S ⊕ Ready A) × List (Receipt S Symbol) → Prop)
    (hgood : ∀ᵐ σ ∂tapeLaw, Good (sourceTrace A C a σ n)) :
    ∀ ω, Good (sourceTrace A C a ω n) := by
  intro ω
  by_contra hbad
  let D : Set (ℕ → Bool) := {σ | ∀ i ∈ Finset.range n, σ i = ω i}
  have hp : 0 < tapeLaw D := by
    rw [show tapeLaw D = (1/2 : ℝ≥0∞)^n from fair_prefix_mass n ω]
    exact pos_iff_ne_zero.mpr (pow_ne_zero n (by norm_num))
  have hsub : D ⊆ {σ | ¬ Good (sourceTrace A C a σ n)} := by
    intro σ hσ
    change ¬ Good (sourceTrace A C a σ n)
    rw [trace_stable A C a σ ω n (fun i hi => hσ i (Finset.mem_range.mpr hi))]
    exact hbad
  exact (ne_of_gt hp) (measure_mono_null hsub (ae_iff.mp hgood))

private def consBit (b : Bool) (ω : ℕ → Bool) : ℕ → Bool
  | 0 => b
  | n+1 => ω n

private theorem edge_tick (A : Architecture S Head Symbol B)
    (s : S) (b : Bool) (r : S × PrimitiveReceipt Symbol)
    (he : A.nativeEdge s b r) (ω : ℕ → Bool) :
    nativeTick A s (if A.action s = .freshBit then consBit b ω else ω) =
      ((r.1,some r.2),ω) := by
  obtain ⟨hen,hr⟩ := (A.result_iff s b r).mp he
  subst r
  by_cases hf : A.action s = .freshBit
  · have ht : tail (consBit b ω) = ω := by funext n; rfl
    simp [nativeTick,hen,hf,consBit,ht]
  · have hd : A.result s false = A.result s b := by
      cases b
      · rfl
      · exact (A.deterministic s hf).symm
    simp [nativeTick,hen,hf,hd]

private theorem complete_realized (A : Architecture S Head Symbol B) (C : ReturnCut A)
    {s p y} (hp : Complete A C s p y) :
    ∃ ω n, sourceTrace A C (.inl s) ω n = (.inr y,p) := by
  induction hp with
  | @exit s r y he =>
    obtain ⟨⟨b,hb⟩,hc⟩ := he
    let ω : ℕ → Bool := fun _ => false
    refine ⟨(if A.action s = .freshBit then consBit b ω else ω),1,?_⟩
    rw [sourceTrace,edge_tick A _ b _ hb ω]
    simp only [tickTarget,← hc,trace_return,List.append_nil,Prod.fst,Prod.snd]
  | @step s r t p y he hp ih =>
    obtain ⟨⟨b,hb⟩,hc⟩ := he
    obtain ⟨ω,n,hn⟩ := ih
    refine ⟨(if A.action s = .freshBit then consBit b ω else ω),n+1,?_⟩
    rw [sourceTrace,edge_tick A _ b _ hb ω]
    simp only [tickTarget,← hc,hn]

private theorem trace_complete (A : Architecture S Head Symbol B) (C : ReturnCut A)
    (s : S) (ω : ℕ → Bool) (n : ℕ) (y : Ready A)
    (hy : (sourceTrace A C (.inl s) ω n).1 = .inr y) :
    Complete A C s (sourceTrace A C (.inl s) ω n).2 y := by
  induction n generalizing s ω with
  | zero => cases hy
  | succ n ih =>
    by_cases he : A.enabled s
    · let b := if A.action s = .freshBit then ω 0 else false
      let σ := if A.action s = .freshBit then tail ω else ω
      let r := A.result s b
      have ht : nativeTick A s ω = ((r.1,some r.2),σ) := by
        by_cases hf : A.action s = .freshBit <;> simp [nativeTick,he,hf,b,σ,r]
      have hb := (A.result_iff s b r).mpr ⟨he,rfl⟩
      cases hc : C s r with
      | none =>
        have hh : (sourceTrace A C (.inl r.1) σ n).1 = .inr y := by
          simpa [sourceTrace,ht,tickTarget,target,hc] using hy
        simpa [sourceTrace,ht,tickTarget,target,hc] using
          Complete.step ⟨⟨b,hb⟩,by simp [target,hc]⟩ (ih _ _ hh)
      | some z =>
        have hz : z = y := by simpa [sourceTrace,ht,tickTarget,target,hc,trace_return]
          using hy
        subst z
        simpa [sourceTrace,ht,tickTarget,target,hc,trace_return] using
          (Complete.exit (A := A) (C := C) (s := s) (r := r) (y := y) ⟨⟨b,hb⟩,by simp [target,hc]⟩)
    · have hh : (sourceTrace A C (.inl s) ω n).1 = .inr y := by
        simpa [sourceTrace,nativeTick,he,tickTarget] using hy
      simpa [sourceTrace,nativeTick,he,tickTarget] using ih s ω hh

private theorem edge_positive (A : Architecture S Head Symbol B) (C : ReturnCut A)
    {s r t} (he : Edge A C s r (.inl t)) : 0 < T (instruction A C) s t := by
  obtain ⟨⟨b,hb⟩,hc⟩ := he
  obtain ⟨hen,hr⟩ := (A.result_iff s b r).mp hb
  subst r
  by_cases hf : A.action s = .freshBit
  · have ht : tickTarget A C s ((A.result s b).1,some (A.result s b).2) = .inl t := hc.symm
    cases b <;> simp [T,row,stopped,instruction,primitiveInstruction,hen,hf,
      mapInstruction,row_fair,tickTarget,ht,PMF.map_apply,tsum_fintype,
      fairBit,PMF.bernoulli_apply,Fintype.sum_bool] <;> split_ifs <;> norm_num
  · have hd : A.result s false = A.result s b := by
      cases b
      · rfl
      · exact (A.deterministic s hf).symm
    simp [T,row,stopped,instruction,primitiveInstruction,hen,hf,mapInstruction,
      tickTarget,hd,← hc]

private theorem prefix_reachable (A : Architecture S Head Symbol B) (C : ReturnCut A)
    (E : Set (S ⊕ Ready A)) {a p s} (ha : Sum.inl a ∈ E)
    (hp : Prefix A C a p s) : Reachable (instruction A C) E s := by
  induction hp with
  | nil => exact Reachable.entrance a ha
  | step hp he ih => exact Reachable.step _ _ ih (edge_positive A C he)

theorem prefix_completable (A : Architecture S Head Symbol B) (C : ReturnCut A)
    (E : Set (S ⊕ Ready A)) (hE : ∀ a ∈ E, tapeLaw (never (instruction A C) a) = 0)
    {a p s} (ha : Sum.inl a ∈ E) (hp : Prefix A C a p s) :
    ∃ v y, Complete A C s v y := by
  have hn := (normalized_reachable_exits (instruction A C) E hE).2 s
    (prefix_reachable A C E ha hp)
  obtain ⟨ω,n,y,hy⟩ : ∃ ω n y, ω ∈ hit (instruction A C) (.inl s) n y := by
    by_contra h
    have hz (y : Ready A) : Z (instruction A C) s y = 0 := by
      have he : exits (instruction A C) (.inl s) y = ∅ := by
        ext ω
        simp only [exits,mem_iUnion,mem_empty_iff_false,iff_false]
        rintro ⟨n,hh⟩
        exact h ⟨ω,n,y,hh⟩
      simp [Z,he]
    simp_rw [hz] at hn
    simp at hn
  exact ⟨_,y,trace_complete A C s ω n y (by rw [trace_state]; exact hy.1)⟩

private theorem saved_instruction (A : Architecture S Head Symbol B) :
    instruction A (savedCut A) = initInstruction A := by
  funext s
  unfold instruction initInstruction
  congr 1
  funext r
  rcases r with ⟨t,e⟩
  cases e <;> rfl

/-- Enabled receipt paths and finite tape executions correspond in both
    directions, and every realized finite trace has positive mass. The general
    current cut uses the same carrier; the saved-frame detector is a special case.
    The genuine return's unused suffix stays fresh by the existing supplier. -/
theorem paid_receipt_execution (A : Architecture S Head Symbol B) (C : ReturnCut A) :
    (∀ s p y, Complete A C s p y ↔
      ∃ ω n, sourceTrace A C (.inl s) ω n = (.inr y,p)) ∧
    (∀ a ω n, (sourceTrace A C a ω n).1 = path (instruction A C) a ω n) ∧
    (∀ a ω n, 0 < tapeLaw {σ | sourceTrace A C a σ n = sourceTrace A C a ω n}) ∧
    (∀ a ω n, (sourceTrace A (savedCut A) a ω n).1 = nativeUntil A a ω n) ∧
    (∀ a, tapeLaw (never (instruction A C) a) = 0 →
      Measurable (FiniteFairBitReturnRestart.restart (instruction A C) a) ∧
      tapeLaw.map (FiniteFairBitReturnRestart.restart (instruction A C) a) =
        (tapeLaw.map (fun ω => (FiniteFairBitReturnRestart.restart (instruction A C) a ω).1)).prod tapeLaw) := by
  refine ⟨?_,trace_state A C,?_,?_,?_⟩
  · intro s p y
    constructor
    · exact complete_realized A C
    · rintro ⟨ω,n,hn⟩
      have hh := trace_complete A C s ω n y (by rw [hn])
      simpa only [hn] using hh
  · intro a ω n
    have hm := measure_mono (μ := tapeLaw) (show {σ | ∀ i ∈ Finset.range n, σ i = ω i} ⊆
        {σ | sourceTrace A C a σ n = sourceTrace A C a ω n} from
      fun σ hσ => trace_stable A C a σ ω n
        (fun i hi => hσ i (Finset.mem_range.mpr hi)))
    rw [fair_prefix_mass] at hm
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (pow_ne_zero n (by norm_num))) hm
  · intro a ω n
    rw [trace_state,saved_instruction]
    exact (native_until_refinement A a ω n).symm
  · intro a ha
    have hh := FiniteFairBitReturnRestart.actual_return_restart (instruction A C) a ha
    exact ⟨hh.1,hh.2.1⟩

#print axioms paid_receipt_execution

/-- Completed correctness is the original finite T0 operation specification,
    independent of a probability row, rationality, normalization, or Tracks. -/
def Correct (A : Architecture S Head Symbol B) (fields : S → FiniteFields)
    (decode : S → Symbol → Option OriginalEvent) (f : FiniteFields) (x : Letter)
    (v : (S ⊕ Ready A) × List (Receipt S Symbol)) : Prop :=
  ∀ y, v.1 = .inr y → finiteRead f x = some (fields y.val) ∧
    events decode v.2 = ReadUpdate.body f x

/-- Historic fields and x are proof indices. The existential witness is an actual
    delivered entrance and a nonreturning sequence of enabled physical receipts. -/
def Tracks (A : Architecture S Head Symbol B) (C : ReturnCut A)
    (fields : S → FiniteFields) (decode : S → Symbol → Option OriginalEvent)
    (arrival : Ready A → Letter → Option (S ⊕ Ready A))
    (f : FiniteFields) (x : Letter) (todo : List OriginalEvent) (s : S) : Prop :=
  ∃ z a p, fields z.val = f ∧ arrival z x = some (.inl a) ∧
    Prefix A C a p s ∧ ReadUpdate.body f x = events decode p ++ todo

/-- Original a.s. finite-return correctness becomes correctness of every finite
    physical return, then yields residual start and each enabled step. Only ONE
    possible finite completion per reachable prefix is used; exceptional infinite
    executions are not removed. The source interpretation premises remain explicit. -/
theorem paid_read_residual (A : Architecture S Head Symbol B) (C : ReturnCut A)
    (fields : S → FiniteFields) (decode : S → Symbol → Option OriginalEvent)
    (arrival : Ready A → Letter → Option (S ⊕ Ready A))
    (hReturn : ∀ z x a, arrival z x = some a → tapeLaw (never (instruction A C) a) = 0)
    (hCorrect : ∀ z x a, arrival z x = some a →
      ∀ᵐ ω ∂tapeLaw, ∀ n, Correct A fields decode (fields z.val) x (sourceTrace A C a ω n)) :
    (∀ z x a, arrival z x = some a → ∀ ω n,
      Correct A fields decode (fields z.val) x (sourceTrace A C a ω n)) ∧
    (∀ z x a, arrival z x = some a → match a with
      | .inl s => Tracks A C fields decode arrival (fields z.val) x (ReadUpdate.body (fields z.val) x) s
      | .inr y => finiteRead (fields z.val) x = some (fields y.val) ∧ ReadUpdate.body (fields z.val) x = []) ∧
    (∀ f x todo s b, Tracks A C fields decode arrival f x todo s → A.enabled s →
      match C s (A.result s b) with
      | some y => finiteRead f x = some (fields y.val) ∧
          todo = ReadUpdate.committed decode s (A.result s b)
      | none => ∃ rest, todo = ReadUpdate.committed decode s (A.result s b) ++ rest ∧
          Tracks A C fields decode arrival f x rest (A.result s b).1) := by
  have hall : ∀ z x a, arrival z x = some a → ∀ ω n,
      Correct A fields decode (fields z.val) x (sourceTrace A C a ω n) := by
    intro z x a ha ω n
    exact finite_good A C a n _ ((hCorrect z x a ha).mono (fun σ hs => hs n)) ω
  have hc : ∀ z x a p y, arrival z x = some (.inl a) → Complete A C a p y →
      finiteRead (fields z.val) x = some (fields y.val) ∧
      events decode p = ReadUpdate.body (fields z.val) x := by
    intro z x a p y ha hp
    obtain ⟨ω,n,hn⟩ := complete_realized A C hp
    have hh := hall z x (.inl a) ha ω n
    rw [hn] at hh
    exact hh y rfl
  refine ⟨hall,?_,?_⟩
  · intro z x a ha
    cases a with
    | inl s => exact ⟨z,s,[],rfl,ha,Prefix.nil,by simp [events]⟩
    | inr y =>
      have hh := hall z x (.inr y) ha (fun _ => false) 0 y rfl
      exact ⟨hh.1,by simpa [events,sourceTrace] using hh.2.symm⟩
  · intro f x todo s b ht he
    obtain ⟨z,a,p,hf,ha,hp,hw⟩ := ht
    subst f
    have hb := (A.result_iff s b _).mpr ⟨he,rfl⟩
    cases hr : C s (A.result s b) with
    | some y =>
      have hret : Complete A C s [(s,A.result s b)] y :=
        Complete.exit ⟨⟨b,hb⟩,by simp [target,hr]⟩
      have hh := hc z x a _ y ha (prepend A C hp hret)
      have hevent : events decode [(s,A.result s b)] = ReadUpdate.committed decode s (A.result s b) := rfl
      refine ⟨hh.1,List.append_cancel_left (as := events decode p) ?_⟩
      rw [← hw,← hevent,← events_append]
      exact hh.2.symm
    | none =>
      have hstep : Edge A C s (A.result s b) (.inl (A.result s b).1) :=
        ⟨⟨b,hb⟩,by simp [target,hr]⟩
      have hpt := Prefix.step hp hstep
      let E : Set (S ⊕ Ready A) := {v | ∃ z, arrival z x = some v}
      have hE : ∀ v ∈ E, tapeLaw (never (instruction A C) v) = 0 := by
        rintro v ⟨w,hw⟩
        exact hReturn w x v hw
      obtain ⟨v,y,hv⟩ := prefix_completable A C E hE ⟨z,ha⟩ hpt
      have hh := hc z x a _ y ha (prepend A C hpt hv)
      have hword : todo = ReadUpdate.committed decode s (A.result s b) ++ events decode v := by
        apply List.append_cancel_left (as := events decode p)
        rw [← hw]
        have hevent : events decode [(s,A.result s b)] = ReadUpdate.committed decode s (A.result s b) := rfl
        simpa only [events_append,List.append_assoc,hevent] using hh.2.symm
      refine ⟨events decode v,hword,z,a,p ++ [(s,A.result s b)],rfl,ha,hpt,?_⟩
      exact hh.2.symm.trans (events_append decode _ _)

#print axioms paid_read_residual
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.PaidTraceResidual
