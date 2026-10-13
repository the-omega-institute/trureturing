/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalNativeServiceBridge
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalNativeServiceBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original receipts persist, and paid local initialization refines complete first-return laws. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitDenominator

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge

open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeFullResidual

/-- This is a proof readout of original events, not a retained parser or letter bank. -/
def acquiredEvent : OriginalEvent → Option Letter
  | .acquired x => some x
  | _ => none

def acquiredLetters (events : List OriginalEvent) : List Letter :=
  events.filterMap acquiredEvent

private theorem completion_no_acquisition (f : FiniteFields) (t : ℕ) (b : Letter) :
    acquiredLetters (completionEvents f t b) = [] := by
  simp only [acquiredLetters, completionEvents, List.filterMap_append]
  split_ifs <;> rfl

private theorem payload_no_acquisition (f : FiniteFields) (t : ℕ)
    (s : ActivePhase) (x : Letter) :
    acquiredLetters (payloadEvents f t s x) = [] := by
  cases s <;> simp only [payloadEvents] <;> split_ifs
  all_goals first | exact completion_no_acquisition _ _ _ |
    simp [acquiredLetters, acquiredEvent]

private theorem block_acquisition (f : FiniteFields) (op : Operation) :
    acquiredLetters (eventBlock f op) = readLetters [op] := by
  cases op with
  | stop b => rfl
  | read x =>
    simp only [eventBlock, acquiredLetters, List.filterMap_cons, acquiredEvent,
      readLetters]
    congr 1
    cases f.control with
    | seed first =>
      cases first
      · rfl
      · dsimp only
        split_ifs <;> rfl
    | early t s => exact payload_no_acquisition f t.val s x
    | fourth c =>
      cases c with
      | active s => exact payload_no_acquisition f 3 s x
      | pending b => rfl
      | delivered => rfl

private theorem prefix_acquisition (c d : AcquiredNativeState) (ops : List Operation)
    (h : execute c ops = some d) :
    acquiredLetters (eventBlocks c.source.finiteFields ops).flatten = readLetters ops := by
  induction ops generalizing c with
  | nil => rfl
  | cons op ops ih =>
    obtain ⟨e, he, hd⟩ := Option.bind_eq_some_iff.mp h
    have hf : finiteStep c.source.finiteFields op = some e.source.finiteFields := by
      rw [← finite_projection_commutes, he]
      rfl
    simp only [eventBlocks, hf, List.flatten_cons, acquiredLetters,
      List.filterMap_append]
    change acquiredLetters (eventBlock c.source.finiteFields op) ++
      acquiredLetters (eventBlocks e.source.finiteFields ops).flatten = _
    rw [block_acquisition, ih e hd]
    cases op <;> rfl

private theorem prefix_blocks_append (c d : AcquiredNativeState) (p v : List Operation)
    (h : execute c p = some d) :
    eventBlocks c.source.finiteFields (p ++ v) =
      eventBlocks c.source.finiteFields p ++ eventBlocks d.source.finiteFields v := by
  induction p generalizing c with
  | nil =>
    have hc : c = d := Option.some.inj h
    subst d
    rfl
  | cons op p ih =>
    obtain ⟨e, he, hd⟩ := Option.bind_eq_some_iff.mp h
    have hf : finiteStep c.source.finiteFields op = some e.source.finiteFields := by
      rw [← finite_projection_commutes, he]
      rfl
    simpa only [List.cons_append, eventBlocks, hf, List.cons_append] using
      congrArg (List.cons (eventBlock c.source.finiteFields op)) (ih e hd)

/-- Later original operations cannot erase an acquired receipt. All rejected seeds,
    payload loops, completion writes, latches, held records and Stop remain in the
    same original blocks. The assertion is about native transactions, not about
    an unproved physical bit/symbol serialization. -/
theorem lawful_receipt_extension (c d e : AcquiredNativeState) (p v : List Operation)
    (hp : execute c p = some d) (hv : execute d v = some e) :
    eventBlocks c.source.finiteFields (p ++ v) =
      eventBlocks c.source.finiteFields p ++ eventBlocks d.source.finiteFields v ∧
    acquiredLetters (eventBlocks c.source.finiteFields (p ++ v)).flatten =
      readLetters p ++ readLetters v := by
  have ha := prefix_blocks_append c d p v hp
  refine ⟨ha, ?_⟩
  rw [ha, List.flatten_append]
  simp only [acquiredLetters, List.filterMap_append]
  exact congrArg₂ List.append (prefix_acquisition c d p hp) (prefix_acquisition d e v hv)

#print axioms lawful_receipt_extension


/-! The architecture below is the supplied local semantics of one fixed installed
    sequential bit architecture. It is not a compiler or an instruction-set
    encoding. Every projection is of the current paid snapshot. -/
namespace Initialization
open Classical MeasureTheory Set
open scoped ENNReal
open FiniteFairBitFirstReturn FiniteFairBitExitLaws FiniteFairBitDenominator

/-- The physical inventory counts literal resident storage, the union of live
    runtime regions, and the total installation peak. Shared regions are counted
    once and temporaries that never coexist are not added together. Computing
    providers belong here; the source and passive receiver have separate accounts. -/
structure PaidImage (S : Type) (B : ℕ) where
  resident : List Bool
  residentSite : Fin resident.length ↪ Fin B
  complete : S ↪ (Fin B → Bool)
  resident_exact : ∀ s i, complete s (residentSite i) = resident.get i
  runtimePeak : ℕ
  installationTotalPeak : ℕ
  online_bound : resident.length + runtimePeak ≤ B
  installation_bound : installationTotalPeak ≤ B

/-- These are the source's local actions, not wide arithmetic, table lookup,
    fetch/decode, seek, copy, clear or frame-preparation macro instructions. -/
inductive LocalAction (Head Symbol : Type) where
  | readCurrent (h : Head)
  | writeCurrent (h : Head) (b : Bool)
  | moveOne (h : Head) (right : Bool)
  | booleanBranch
  | freshBit
  | writeBuffer (x : Symbol)
  | sendBuffer
  deriving DecidableEq

structure PrimitiveReceipt (Symbol : Type) where
  readBit : Option Bool
  consumed : Option Bool
  sent : Option Symbol
  deriving DecidableEq

/-- A proof view of an existing paid invocation frame. Depth and saved return
    address are not new runtime fields or remembered entrance parameters. -/
structure InitFrame where
  depth : ℕ
  returnAddress : ℕ
  deriving DecidableEq

/-- The real local transition relation is independent of graph instructions.
    The result certificate selects actual deterministic/fair outcomes when enabled.
    Disabled words receive proof-only stutters; in particular a last-cell move
    cannot be enabled and satisfy local_effect. -/
structure Architecture (S Head Symbol : Type) [DecidableEq Head] [DecidableEq Symbol]
    (B : ℕ) where
  headFinite : Fintype Head
  symbolFinite : Fintype Symbol
  paid : PaidImage S B
  memoryCell : Fin B → Prop
  head : S → Head → Fin B
  head_owned : ∀ s h, memoryCell (head s h)
  buffer : S → Option Symbol
  pc : S → ℕ
  branchBit : S → Fin B
  branchZero : S → ℕ
  branchOne : S → ℕ
  randomCell : S → Option (Fin B)
  readLatch : S → Fin B
  initFrame : S → Option InitFrame
  ready : S → Prop
  action : S → LocalAction Head Symbol
  enabled : S → Prop
  nativeEdge : S → Bool → S × PrimitiveReceipt Symbol → Prop
  result : S → Bool → S × PrimitiveReceipt Symbol
  result_iff : ∀ s b r, nativeEdge s b r ↔ enabled s ∧ r = result s b
  deterministic : ∀ s, action s ≠ .freshBit → result s true = result s false
  local_effect : ∀ s b, enabled s → let r := result s b
    r.2.consumed = (if action s = .freshBit then some b else none) ∧
    (match action s with
    | .readCurrent h => r.2.readBit = some (paid.complete s (head s h)) ∧
        paid.complete r.1 (readLatch s) = paid.complete s (head s h)
    | .writeCurrent h v => paid.complete r.1 (head s h) = v ∧
        ∀ i, memoryCell i → i ≠ head s h → paid.complete r.1 i = paid.complete s i
    | .moveOne h right =>
        (if right then (head s h).val + 1 = (head r.1 h).val
         else (head r.1 h).val + 1 = (head s h).val) ∧
        ∀ i, memoryCell i → paid.complete r.1 i = paid.complete s i
    | .booleanBranch => pc r.1 =
        (if paid.complete s (branchBit s) then branchOne s else branchZero s) ∧
        ∀ i, memoryCell i → paid.complete r.1 i = paid.complete s i
    | .freshBit => (∀ i, randomCell s = some i → paid.complete r.1 i = b) ∧
        ∀ i, memoryCell i → randomCell s ≠ some i →
          paid.complete r.1 i = paid.complete s i
    | .writeBuffer x => buffer r.1 = some x
    | .sendBuffer => r.2.sent = buffer s ∧ (buffer s).isSome) ∧
    (action s ≠ .sendBuffer → r.2.sent = none)

variable {S Head Symbol : Type} [DecidableEq Head] [DecidableEq Symbol] {B : ℕ}

abbrev Ready (A : Architecture S Head Symbol B) := {s : S // A.ready s}

/-- Only a transition out of the current outer initialization frame, to its
    saved caller PC and a complete ready state, closes this invocation. -/
def currentReturn (A : Architecture S Head Symbol B) (s : S)
    (r : S × PrimitiveReceipt Symbol) : Option (Ready A) :=
  if h : (∃ f, A.initFrame s = some f ∧ f.depth = 0 ∧
      A.initFrame r.1 = none ∧ A.pc r.1 = f.returnAddress) ∧ A.ready r.1
  then some ⟨r.1, h.2⟩ else none

/-- The bit coordinate is external. A deterministic primitive does not advance
    it, even when its result happens to agree with a fair successor. -/
def nativeTick (A : Architecture S Head Symbol B) (s : S) (ω : ℕ → Bool) :
    (S × Option (PrimitiveReceipt Symbol)) × (ℕ → Bool) :=
  if A.enabled s then
    if A.action s = .freshBit then
      (((A.result s (ω 0)).1, some (A.result s (ω 0)).2), tail ω)
    else (((A.result s false).1, some (A.result s false).2), ω)
  else ((s, none), ω)

def primitiveInstruction (A : Architecture S Head Symbol B) (s : S) :
    Instruction (S × Option (PrimitiveReceipt Symbol)) :=
  if A.enabled s then
    if A.action s = .freshBit then
      .fair ((A.result s false).1, some (A.result s false).2)
        ((A.result s true).1, some (A.result s true).2)
    else .deterministic ((A.result s false).1, some (A.result s false).2)
  else .deterministic (s, none)

/-- Native prefixes are legal local edges with their distinct branch receipts.
    No graph function occurs in this relation. -/
inductive NativePrefix (A : Architecture S Head Symbol B) :
    S → (ℕ → Bool) → ℕ → List (S × PrimitiveReceipt Symbol) → (ℕ → Bool) → Prop
  | nil (s ω) : NativePrefix A s ω 0 [] ω
  | blocked (s ω n) (h : ¬ A.enabled s) : NativePrefix A s ω (n+1) [] ω
  | deterministic (s ω n rs σ) (r : S × PrimitiveReceipt Symbol)
      (h : A.action s ≠ .freshBit) (edge : A.nativeEdge s false r)
      (rest : NativePrefix A r.1 ω n rs σ) :
      NativePrefix A s ω (n+1) (r :: rs) σ
  | fair (s ω n rs σ) (r : S × PrimitiveReceipt Symbol)
      (h : A.action s = .freshBit) (edge : A.nativeEdge s (ω 0) r)
      (rest : NativePrefix A r.1 (tail ω) n rs σ) :
      NativePrefix A s ω (n+1) (r :: rs) σ

structure PrefixValue (S Symbol : Type) where
  statesAndReceipts : List (S × PrimitiveReceipt Symbol)
  unused : ℕ → Bool
  requests : ℕ

/-- Actual primitive execution; it uses the native supplier, not Instruction. -/
def nativePrefix (A : Architecture S Head Symbol B) (s : S) (ω : ℕ → Bool) :
    ℕ → PrefixValue S Symbol
  | 0 => ⟨[], ω, 0⟩
  | n+1 =>
    let r := nativeTick A s ω
    match r.1.2 with
    | none => ⟨[], ω, 0⟩
    | some receipt =>
      let p := nativePrefix A r.1.1 r.2 n
      ⟨(r.1.1, receipt) :: p.statesAndReceipts, p.unused,
        (if receipt.consumed.isSome then 1 else 0) + p.requests⟩

/-- Disabled graph stutters have no physical receipt and are omitted from the
    primitive prefix. They neither move a head nor request a random bit. -/
def graphPrefix (A : Architecture S Head Symbol B) (s : S) (ω : ℕ → Bool) :
    ℕ → PrefixValue S Symbol
  | 0 => ⟨[], ω, 0⟩
  | n+1 =>
    let r := successor (primitiveInstruction A s) ω
    match r.1.2 with
    | none => ⟨[], ω, 0⟩
    | some receipt =>
      let p := graphPrefix A r.1.1 r.2 n
      ⟨(r.1.1, receipt) :: p.statesAndReceipts, p.unused,
        (if A.action s = .freshBit then 1 else 0) + p.requests⟩

theorem tick_refinement (A : Architecture S Head Symbol B)
    (s : S) (ω : ℕ → Bool) :
    nativeTick A s ω = successor (primitiveInstruction A s) ω := by
  by_cases he : A.enabled s
  · by_cases h : A.action s = .freshBit
    · cases hb : ω 0 <;> simp [nativeTick, primitiveInstruction, successor, he, h, hb]
    · simp [nativeTick, primitiveInstruction, successor, he, h]
  · simp [nativeTick, primitiveInstruction, successor, he]

end Initialization
open Initialization
open FiniteFairBitFirstReturn FiniteFairBitExitLaws FiniteFairBitDenominator
open Classical MeasureTheory Set
open scoped ENNReal
variable {S Head Symbol : Type} [DecidableEq Head] [DecidableEq Symbol] {B : ℕ}

/-- Complete snapshots, actual zero/one request counts, unused coordinates and
    outcome receipts agree. Nonblocked prefix entries are enabled native edges;
    a disabled word has no edge and contributes an empty physical prefix. -/
theorem original_primitive_prefix_refinement (A : Architecture S Head Symbol B)
    (s : S) (ω : ℕ → Bool) (n : ℕ) :
    nativePrefix A s ω n = graphPrefix A s ω n ∧
    NativePrefix A s ω n (nativePrefix A s ω n).statesAndReceipts
      (nativePrefix A s ω n).unused := by
  induction n generalizing s ω with
  | zero => exact ⟨rfl, NativePrefix.nil s ω⟩
  | succ n ih =>
    by_cases he : A.enabled s
    · by_cases h : A.action s = .freshBit
      · have hc := (A.local_effect s (ω 0) he).1
        simp only [h, if_pos] at hc
        have hi := ih (A.result s (ω 0)).1 (tail ω)
        constructor
        · rw [nativePrefix, graphPrefix, ← tick_refinement]
          simp only [nativeTick, he, if_pos, h, hc, Option.isSome_some]
          rw [hi.1]
        · simpa only [nativePrefix, nativeTick, he, if_pos, h] using
            NativePrefix.fair s ω n _ _ (A.result s (ω 0)) h
              ((A.result_iff s (ω 0) _).mpr ⟨he, rfl⟩) hi.2
      · have hc := (A.local_effect s false he).1
        simp only [h, if_neg, ↓reduceIte] at hc
        have hi := ih (A.result s false).1 ω
        constructor
        · rw [nativePrefix, graphPrefix, ← tick_refinement]
          simp [nativeTick, he, h, hc, hi.1]
        · simpa [nativePrefix, nativeTick, he, h] using
            NativePrefix.deterministic s ω n _ _ (A.result s false) h
              ((A.result_iff s false _).mpr ⟨he, rfl⟩) hi.2
    · constructor
      · simp [nativePrefix, graphPrefix, nativeTick, primitiveInstruction, successor, he]
      · simpa [nativePrefix, nativeTick, he] using NativePrefix.blocked s ω n he

namespace Initialization
/-- This readout uses an actual receipt; proof-only disabled stutters cannot
    manufacture a return. -/
def tickReturn (A : Architecture S Head Symbol B) (s : S)
    (r : S × Option (PrimitiveReceipt Symbol)) : Option (Ready A) :=
  r.2.bind fun receipt => currentReturn A s (r.1, receipt)

/-- A lawful immediate return is a separate actual interface case. Otherwise
    setup, frame construction and initialization remain native paid execution. -/
structure InitProtocol (A : Architecture S Head Symbol B) where
  entrances : Set (S ⊕ Ready A)
  running_frame : ∀ s, Sum.inl s ∈ entrances → ∃ f, A.initFrame s = some f ∧ f.depth = 0
  immediate_frame : ∀ x, Sum.inr x ∈ entrances → A.initFrame x.val = none
  actualFields : S → FiniteFields
  immediate_initial : ∀ x, Sum.inr x ∈ entrances → actualFields x.val = initial.source.finiteFields
  outer_initial : ∀ s b x, A.enabled s → currentReturn A s (A.result s b) = some x →
    actualFields x.val = initial.source.finiteFields

/-- Native current-invocation execution, stopped only by the actual convention.
    Absorbing copies after return are proof coordinates, not physical actions. -/
def nativeUntil (A : Architecture S Head Symbol B) (a : S ⊕ Ready A)
    (ω : ℕ → Bool) : ℕ → S ⊕ Ready A
  | 0 => a
  | n+1 => match a with
    | .inr x => .inr x
    | .inl s =>
      let r := nativeTick A s ω
      match tickReturn A s r.1 with
      | some x => .inr x
      | none => nativeUntil A (.inl r.1.1) r.2 n

def initInstruction (A : Architecture S Head Symbol B) (s : S) :
    Instruction (S ⊕ Ready A) :=
  mapInstruction (fun r => match tickReturn A s r with
    | none => Sum.inl r.1 | some x => Sum.inr x) (primitiveInstruction A s)

variable [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem native_until_refinement (A : Architecture S Head Symbol B)
    (a : S ⊕ Ready A) (ω : ℕ → Bool) (n : ℕ) :
    nativeUntil A a ω n = path (initInstruction A) a ω n := by
  induction n generalizing a ω with
  | zero => rfl
  | succ n ih =>
    cases a with
    | inr x => simpa [nativeUntil] using (path_exit (initInstruction A) x ω (n+1)).symm
    | inl s =>
      have hp := (original_primitive_prefix_refinement A s ω 1).1
      have ht : nativeTick A s ω = successor (primitiveInstruction A s) ω := by
        by_cases he : A.enabled s
        · obtain ⟨r, hr⟩ : ∃ r, (nativeTick A s ω).1.2 = some r := by
            by_cases h : A.action s = .freshBit <;> simp [nativeTick, he, h]
          obtain ⟨t, ht⟩ : ∃ t, (successor (primitiveInstruction A s) ω).1.2 = some t := by
            by_cases h : A.action s = .freshBit
            · cases hb : ω 0 <;> simp [primitiveInstruction, successor, he, h, hb]
            · simp [primitiveInstruction, successor, he, h]
          have hl := congrArg PrefixValue.statesAndReceipts hp
          have hu := congrArg (fun p : PrefixValue S Symbol => p.unused) hp
          simp only [nativePrefix, graphPrefix, hr, ht] at hl hu
          have hpairs := (List.cons.inj hl).1
          apply Prod.ext
          · apply Prod.ext
            · exact (Prod.mk.inj hpairs).1
            · rw [hr, ht]
              exact congrArg some (Prod.mk.inj hpairs).2
          · exact hu
        · simp [nativeTick, primitiveInstruction, successor, he]
      have hm : successor (initInstruction A s) ω =
          ((match tickReturn A s (nativeTick A s ω).1 with
            | none => Sum.inl (nativeTick A s ω).1.1
            | some x => Sum.inr x), (nativeTick A s ω).2) := by
        rw [ht]
        unfold initInstruction
        cases h : primitiveInstruction A s with
        | deterministic r => rfl
        | fair r t => cases hb : ω 0 <;> simp [mapInstruction, successor, hb]
      change nativeUntil A (.inl s) ω (n+1) =
        run (stopped (initInstruction A)) (successor (initInstruction A s) ω).1
          (successor (initInstruction A s) ω).2 n
      rw [hm]
      simp only [nativeUntil]
      cases h : tickReturn A s (nativeTick A s ω).1 with
      | none => exact ih _ _
      | some x => exact (path_exit (initInstruction A) x _ n).symm

def nativeFirstReturn (A : Architecture S Head Symbol B) (a : S ⊕ Ready A)
    (n : ℕ) (x : Ready A) : Set (ℕ → Bool) :=
  {ω | nativeUntil A a ω n = .inr x ∧
    ∀ k < n, ∃ s, nativeUntil A a ω k = .inl s}

def nativeExits (A : Architecture S Head Symbol B) (a : S ⊕ Ready A)
    (x : Ready A) : Set (ℕ → Bool) := ⋃ n, nativeFirstReturn A a n x

def nativeNever (A : Architecture S Head Symbol B) (a : S ⊕ Ready A) :
    Set (ℕ → Bool) := {ω | ∀ n, ∃ s, nativeUntil A a ω n = .inl s}

def eta (A : Architecture S Head Symbol B) (a : S ⊕ Ready A) (x : Ready A) : ℝ≥0∞ :=
  tapeLaw (nativeExits A a x)

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
private theorem returned_initial (A : Architecture S Head Symbol B) (P : InitProtocol A)
    (s : S) (ω : ℕ → Bool) (n : ℕ) (x : Ready A)
    (hx : nativeUntil A (.inl s) ω n = .inr x) :
    P.actualFields x.val = initial.source.finiteFields := by
  induction n generalizing s ω with
  | zero => cases hx
  | succ n ih =>
    cases h : tickReturn A s (nativeTick A s ω).1 with
    | some y =>
      have hy : y = x := Sum.inr.inj (show (Sum.inr y : S ⊕ Ready A) = Sum.inr x from
        by simpa [nativeUntil, h] using hx)
      subst y
      by_cases he : A.enabled s
      · by_cases hb : A.action s = .freshBit
        · exact P.outer_initial s (ω 0) x he
            (by simpa [tickReturn, nativeTick, he, hb] using h)
        · exact P.outer_initial s false x he
            (by simpa [tickReturn, nativeTick, he, hb] using h)
      · simp [tickReturn, nativeTick, he] at h
    | none => exact ih _ _ (by simpa [nativeUntil, h] using hx)

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
private theorem initial_projection (A : Architecture S Head Symbol B) (P : InitProtocol A)
    (a : S ⊕ Ready A) (ha : a ∈ P.entrances) (ω : ℕ → Bool)
    (n : ℕ) (x : Ready A) (hx : ω ∈ nativeFirstReturn A a n x) :
    P.actualFields x.val = initial.source.finiteFields := by
  cases a with
  | inl s => exact returned_initial A P s ω n x hx.1
  | inr y =>
    cases n with
    | zero =>
      have hy : y = x := Sum.inr.inj hx.1
      subst y
      exact P.immediate_initial x ha
    | succ n =>
      obtain ⟨s, hs⟩ := hx.2 0 (Nat.zero_lt_succ n)
      cases hs

end Initialization
open Initialization FiniteFairBitFirstReturn FiniteFairBitExitLaws FiniteFairBitDenominator
open Classical MeasureTheory Set
open scoped ENNReal BigOperators

variable {S Head Symbol : Type} [DecidableEq Head] [DecidableEq Symbol] {B : ℕ}
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Actual initialization first-return events, native nonreturn and all complete
    output rows have one positive bounded certificate. The source premise is
    almost-sure native return, not graph transience or a prescribed eta. -/
theorem original_initialization_exit_certificate (A : Architecture S Head Symbol B)
    (P : InitProtocol A)
    (hReturn : ∀ a ∈ P.entrances, tapeLaw (nativeNever A a) = 0) :
    (∀ a n x, nativeFirstReturn A a n x = hit (initInstruction A) a n x) ∧
    (∀ a x, nativeExits A a x = exits (initInstruction A) a x) ∧
    (∀ a, nativeNever A a = never (initInstruction A) a) ∧
    (∀ a ∈ P.entrances, ∀ ω n x, ω ∈ nativeFirstReturn A a n x →
      P.actualFields x.val = initial.source.finiteFields) ∧
    ∃ d : ℕ, 0 < d ∧ d ≤ 4 ^ (2 ^ B) ∧
      (∀ a ∈ P.entrances, ∀ x, Clears d (eta A a x).toReal) ∧
      (∀ a ∈ P.entrances, ∑ x, eta A a x = 1) := by
  have hf (a n x) : nativeFirstReturn A a n x = hit (initInstruction A) a n x := by
    ext ω
    simp only [nativeFirstReturn, hit, Set.mem_ofPred_eq, live, native_until_refinement]
  have he (a x) : nativeExits A a x = exits (initInstruction A) a x := by
    simp only [nativeExits, exits, hf]
  have hn (a) : nativeNever A a = never (initInstruction A) a := by
    ext ω
    simp only [nativeNever, never, Set.mem_ofPred_eq, Set.mem_iInter, live,
      native_until_refinement]
  have hE : ∀ a ∈ P.entrances, tapeLaw (never (initInstruction A) a) = 0 := by
    intro a ha
    rw [← hn]
    exact hReturn a ha
  have hd := actual_exit_denominator (initInstruction A) P.entrances hE
  have hc : Fintype.card S ≤ 2 ^ B := by
    simpa using Fintype.card_le_of_injective A.paid.complete A.paid.complete.injective
  have hu : Fintype.card (U (initInstruction A) P.entrances) ≤ Fintype.card S :=
    Fintype.card_subtype_le _
  refine ⟨hf, he, hn, ?_, denominator (initInstruction A) P.entrances,
    hd.1, hd.2.1.trans (Nat.pow_le_pow_right (by decide) (hu.trans hc)), ?_, ?_⟩
  · intro a ha ω n x hx
    exact initial_projection A P a ha ω n x hx
  · intro a ha x
    simpa only [eta, he] using hd.2.2.2.1 a ha x
  · intro a ha
    simpa only [eta, he] using hd.2.2.2.2 a ha

#print axioms original_primitive_prefix_refinement
#print axioms original_initialization_exit_certificate


/-! Actual paid Read uses the same complete carrier and local execution as
    initialization. The old finite fields and received letter below index a
    simulation proof; neither is an argument to the executing transition. -/
namespace ReadUpdate

/-- Original events after the paid source receipt. The receipt itself is the
    acquired event at the interface, not a synthesized observer letter. -/
def body (f : FiniteFields) (x : Letter) : List OriginalEvent :=
  (eventBlock f (.read x)).tail

/-- An original event is a semantic readout of an actually sent symbol and the
    current paid serialization cursor. Unsigned primitive steps emit no event.
    The decoder is the supplied original finite rendering convention. -/
def committed (decode : S → Symbol → Option OriginalEvent) (s : S)
    (r : S × PrimitiveReceipt Symbol) : List OriginalEvent :=
  (r.2.sent.bind (decode s)).toList

/-- Supplied local Read interface of the installed architecture. Arrival is only
    the original provider's delivery into its existing input port. All observer
    setup, copying, latching, seeking and frame work is subsequent nativeTick
    execution. The input projection is of S, not a new letter latch. Tracks is
    a proof relation; its indices and residual list are never runtime inputs.

    The local obligation checks each enabled native edge, its emitted original
    events and its finite-field effect at a genuine current outer return. It
    assumes no exit probability, normalized row, rationality or graph property. -/
structure Protocol (A : Architecture S Head Symbol B) where
  fields : S → FiniteFields
  inputSite : Fin B → Prop
  offered : S → Option Letter
  arrival : Ready A → Letter → Option (S ⊕ Ready A)
  menu : ∀ z x, (arrival z x).isSome ↔ (finiteRead (fields z.val) x).isSome
  boundary : ∀ z x a, arrival z x = some a →
    let s := a.elim id Subtype.val
    offered s = some x ∧ fields s = fields z.val ∧
    A.initFrame s = none ∧
    (∀ i, ¬ inputSite i → A.paid.complete s i = A.paid.complete z.val i)
  decodeSymbol : S → Symbol → Option OriginalEvent
  Tracks : FiniteFields → Letter → List OriginalEvent → S → Prop
  start : ∀ z x a, arrival z x = some a → match a with
    | .inl s => Tracks (fields z.val) x (body (fields z.val) x) s
    | .inr y => finiteRead (fields z.val) x = some (fields y.val) ∧
        body (fields z.val) x = []
  step : ∀ f x todo s b, Tracks f x todo s → A.enabled s →
    match currentReturn A s (A.result s b) with
    | some y => finiteRead f x = some (fields y.val) ∧
        todo = committed decodeSymbol s (A.result s b)
    | none => ∃ rest, todo = committed decodeSymbol s (A.result s b) ++ rest ∧
        Tracks f x rest (A.result s b).1

/-- Original semantic events actually committed by the stopped native execution.
    This is an external proof readout, not a retained event archive. -/
def nativeEvents (A : Architecture S Head Symbol B) (P : Protocol A)
    (a : S ⊕ Ready A) (ω : ℕ → Bool) : ℕ → List OriginalEvent
  | 0 => []
  | n+1 => match a with
    | .inr _ => []
    | .inl s =>
      let r := nativeTick A s ω
      (match r.1.2 with | none => [] | some e => committed P.decodeSymbol s (r.1.1,e)) ++
        (match tickReturn A s r.1 with
        | some _ => []
        | none => nativeEvents A P (.inl r.1.1) r.2 n)

/-- All ready rows for this letter use one graph. Illegal terminal Read is absent
    from this set; the original pending/delivered conventions are not calls. -/
def entrances (A : Architecture S Head Symbol B) (P : Protocol A) (x : Letter) :
    Set (S ⊕ Ready A) := {a | ∃ z, P.arrival z x = some a}

/-- Eliminate the actual native computation. None denotes an illegal Read, not
    a subprobability row or an assumed normalized service. -/
def actual (A : Architecture S Head Symbol B) (P : Protocol A)
    (x : Letter) (z : Ready A) : Option (Ready A → ℝ≥0∞) :=
  (P.arrival z x).map (eta A)

/-- PH37.1's proof-only identity completion at rows with no Read permission.
    This definition neither invokes a source nor opens a terminal menu. -/
def row (A : Architecture S Head Symbol B) (P : Protocol A)
    (x : Letter) (z y : Ready A) : ℝ≥0∞ :=
  match actual A P x z with
  | some p => p y
  | none => if y = z then 1 else 0

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
private theorem progress (A : Architecture S Head Symbol B) (P : Protocol A)
    (f : FiniteFields) (x : Letter) (todo : List OriginalEvent)
    (s : S) (ht : P.Tracks f x todo s) (ω : ℕ → Bool) (n : ℕ) (y : Ready A)
    (hy : nativeUntil A (.inl s) ω n = .inr y) :
    finiteRead f x = some (P.fields y.val) ∧
      nativeEvents A P (.inl s) ω n = todo := by
  induction n generalizing s todo ω with
  | zero => cases hy
  | succ n ih =>
    by_cases he : A.enabled s
    · let b := if A.action s = .freshBit then ω 0 else false
      let σ := if A.action s = .freshBit then tail ω else ω
      have htick : nativeTick A s ω =
          (((A.result s b).1, some (A.result s b).2), σ) := by
        by_cases hb : A.action s = .freshBit <;> simp [nativeTick,he,hb,b,σ]
      have hl := P.step f x todo s b ht he
      cases hr : currentReturn A s (A.result s b) with
      | some z =>
        rw [hr] at hl
        have hz : z = y := Sum.inr.inj (show (Sum.inr z : S ⊕ Ready A) = Sum.inr y from by
          simpa [nativeUntil,htick,tickReturn,hr] using hy)
        subst z
        exact ⟨hl.1, by simpa [nativeEvents,htick,tickReturn,hr] using hl.2.symm⟩
      | none =>
        rw [hr] at hl
        obtain ⟨rest,hevents,hrest⟩ := hl
        have hh := ih rest (A.result s b).1 hrest σ
          (by simpa [nativeUntil,htick,tickReturn,hr] using hy)
        exact ⟨hh.1, by simpa [nativeEvents,htick,tickReturn,hr,hh.2] using hevents.symm⟩
    · have hh := ih todo s ht ω (by simpa [nativeUntil,nativeTick,he,tickReturn] using hy)
      exact ⟨hh.1,by simpa [nativeEvents,nativeTick,he,tickReturn] using hh.2⟩

end ReadUpdate

/-- Both original paid letter updates retain the complete ready output, the
    exact receipt/event block and finite update. Their actual current-return
    events are graph events, and every lawful full row has a positive common
    bounded denominator. Only original terminal rows are identity-completed.

    Protocol.step is an installed-interface simulation obligation, not an
    assertion that an arbitrary guessed architecture implements the source. -/
theorem original_read_update_rows (A : Architecture S Head Symbol B)
    (P : ReadUpdate.Protocol A)
    (hReturn : ∀ x a, a ∈ ReadUpdate.entrances A P x →
      tapeLaw (nativeNever A a) = 0) :
    (∀ a n y, nativeFirstReturn A a n y = hit (initInstruction A) a n y) ∧
    (∀ a y, nativeExits A a y = exits (initInstruction A) a y) ∧
    (∀ a, nativeNever A a = never (initInstruction A) a) ∧
    (∀ x z a, P.arrival z x = some a → ∀ ω n y,
      ω ∈ nativeFirstReturn A a n y →
      finiteRead (P.fields z.val) x = some (P.fields y.val) ∧
      OriginalEvent.acquired x :: ReadUpdate.nativeEvents A P a ω n =
        eventBlock (P.fields z.val) (.read x)) ∧
    (∀ x z a, P.arrival z x = some a → ∀ y,
      finiteRead (P.fields z.val) x ≠ some (P.fields y.val) → eta A a y = 0) ∧
    (∀ x, ∃ d : ℕ, 0 < d ∧ d ≤ 4 ^ (2 ^ B) ∧
      (∀ z y, Clears d (ReadUpdate.row A P x z y).toReal) ∧
      (∀ z, ∑ y, ReadUpdate.row A P x z y = 1)) ∧
    (∀ x z, (ReadUpdate.actual A P x z).isSome ↔
      (finiteRead (P.fields z.val) x).isSome) ∧
    (∀ x z, finiteRead (P.fields z.val) x = none →
      P.arrival z x = none ∧ ReadUpdate.actual A P x z = none ∧
      ∀ y, ReadUpdate.row A P x z y = if y = z then 1 else 0) := by
  have hf (a n y) : nativeFirstReturn A a n y = hit (initInstruction A) a n y := by
    ext ω
    simp only [nativeFirstReturn,hit,Set.mem_ofPred_eq,live,native_until_refinement]
  have he (a y) : nativeExits A a y = exits (initInstruction A) a y := by
    simp only [nativeExits,exits,hf]
  have hn (a) : nativeNever A a = never (initInstruction A) a := by
    ext ω
    simp only [nativeNever,never,Set.mem_ofPred_eq,Set.mem_iInter,live,native_until_refinement]
  have hp : ∀ x z a, P.arrival z x = some a → ∀ ω n y,
      ω ∈ nativeFirstReturn A a n y →
      finiteRead (P.fields z.val) x = some (P.fields y.val) ∧
      OriginalEvent.acquired x :: ReadUpdate.nativeEvents A P a ω n =
        eventBlock (P.fields z.val) (.read x) := by
    intro x z a ha ω n y hy
    have hs := P.start z x a ha
    have hb : OriginalEvent.acquired x :: ReadUpdate.body (P.fields z.val) x =
        eventBlock (P.fields z.val) (.read x) := rfl
    cases a with
    | inl s =>
      have hp := ReadUpdate.progress A P _ x _ s hs ω n y hy.1
      exact ⟨hp.1,by rw [hp.2]; exact hb⟩
    | inr v =>
      cases n with
      | zero =>
        have hv : v = y := Sum.inr.inj hy.1
        subst v
        exact ⟨hs.1,by simpa [ReadUpdate.nativeEvents,hs.2] using hb⟩
      | succ n =>
        obtain ⟨s,hh⟩ := hy.2 0 (Nat.zero_lt_succ n)
        cases hh
  refine ⟨hf,he,hn,hp,?_,?_,?_,?_⟩
  · intro x z a ha y hy
    have hz : nativeExits A a y = ∅ := by
      ext ω
      simp only [nativeExits,Set.mem_iUnion,Set.mem_empty_iff_false,iff_false]
      rintro ⟨n,hn⟩
      exact hy (hp x z a ha ω n y hn).1
    simp [eta,hz]
  · intro x
    have hE : ∀ a ∈ ReadUpdate.entrances A P x,
        tapeLaw (never (initInstruction A) a) = 0 := by
      intro a ha
      rw [← hn]
      exact hReturn x a ha
    obtain ⟨hd,hbound,_,hclear,hnorm⟩ :=
      actual_exit_denominator (initInstruction A) (ReadUpdate.entrances A P x) hE
    have hc : Fintype.card S ≤ 2 ^ B := by
      simpa using Fintype.card_le_of_injective A.paid.complete A.paid.complete.injective
    have hu : Fintype.card (U (initInstruction A) (ReadUpdate.entrances A P x)) ≤
        Fintype.card S := Fintype.card_subtype_le _
    refine ⟨denominator (initInstruction A) (ReadUpdate.entrances A P x),hd,
      hbound.trans (Nat.pow_le_pow_right (by decide) (hu.trans hc)),?_,?_⟩
    · intro z y
      cases ha : P.arrival z x with
      | none =>
        simp only [ReadUpdate.row,ReadUpdate.actual,ha,Option.map_none]
        split_ifs
        · exact ⟨denominator (initInstruction A) (ReadUpdate.entrances A P x), by simp⟩
        · exact ⟨0, by simp⟩
      | some a =>
        simpa only [ReadUpdate.row,ReadUpdate.actual,ha,Option.map_some,eta,he] using
          hclear a ⟨z,ha⟩ y
    · intro z
      cases ha : P.arrival z x with
      | none => simp [ReadUpdate.row,ReadUpdate.actual,ha]
      | some a =>
        simpa only [ReadUpdate.row,ReadUpdate.actual,ha,Option.map_some,eta,he] using
          hnorm a ⟨z,ha⟩
  · intro x z
    simpa [ReadUpdate.actual] using P.menu z x
  · intro x z hz
    have hm := P.menu z x
    rw [hz] at hm
    have ha : P.arrival z x = none := by
      cases h : P.arrival z x with
      | none => rfl
      | some a => simp [h] at hm
    exact ⟨ha,by simp [ReadUpdate.actual,ha],by intros; simp [ReadUpdate.row,ReadUpdate.actual,ha]⟩

#print axioms original_read_update_rows

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge
