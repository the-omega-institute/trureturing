/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixState
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Paid native seed and payload prefixes reconstruct the original written state. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
import Mathlib.Data.Fintype.Option

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixState

open FourthSegmentStoppedLaw (Letter ActivePhase FourthControl loopWord pWord)

instance : Fintype ActivePhase := ⟨{.p, .beta}, by intro x; cases x <;> simp⟩
instance : Fintype FourthControl :=
  Fintype.ofEquiv (ActivePhase ⊕ Letter ⊕ Unit)
    { toFun := fun x => match x with
        | .inl s => .active s
        | .inr (.inl b) => .pending b
        | .inr (.inr _) => .delivered
      invFun := fun c => match c with
        | .active s => .inl s
        | .pending b => .inr (.inl b)
        | .delivered => .inr (.inr ())
      left_inv := by
        intro x
        rcases x with s | b | u
        · rfl
        · rfl
        · cases u; rfl
      right_inv := by intro c; cases c <;> rfl }


inductive NativeControl where
  | seed (first : Option Letter)
  | early (t : Fin 3) (phase : ActivePhase)
  | fourth (c : FourthControl)
  deriving DecidableEq, Fintype

inductive QOne where
  | empty | a | ac | d | ad | da
  deriving DecidableEq

instance : Fintype QOne := ⟨{.empty, .a, .ac, .d, .ad, .da}, by intro x; cases x <;> simp⟩

inductive QTwo where
  | empty | b | c | bc | cb
  deriving DecidableEq

instance : Fintype QTwo := ⟨{.empty, .b, .c, .bc, .cb}, by intro x; cases x <;> simp⟩

/-- The selected snapshot has fixed ell=2 and completed count 3. -/
structure ThirdSnapshot where
  seed : Letter
  weight : Fin 5
  syndrome : Letter
  deriving DecidableEq, Fintype

/-- Only actually written finite registers; no retry or marker archive. -/
structure Registers where
  seed : Option Letter
  weight : Fin 5
  syndrome : Option Letter
  qone : QOne
  qtwo : QTwo
  z : Letter
  snapshot : Option ThirdSnapshot
  deriving DecidableEq

instance : Fintype Registers :=
  Fintype.ofEquiv
    (Option Letter × Fin 5 × Option Letter × QOne × QTwo × Letter × Option ThirdSnapshot)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1,
        x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2⟩
      invFun := fun r => ⟨r.seed, r.weight, r.syndrome, r.qone, r.qtwo, r.z, r.snapshot⟩
      left_inv := by intro x; rfl
      right_inv := by intro r; rfl }

structure FiniteFields where
  control : NativeControl
  registers : Registers
  deriving DecidableEq, Fintype

structure NativeSourceState where
  finiteFields : FiniteFields
  payloadReturns : ℕ
  deriving DecidableEq

structure Counts where
  alpha : ℕ
  beta : ℕ
  deriving DecidableEq

/-- A concrete from-zero acquired-letter extension, with no selected-count bank. -/
structure AcquiredNativeState where
  source : NativeSourceState
  counts : Counts
  deriving DecidableEq

inductive Operation where
  | read (x : Letter)
  | stop (b : Letter)
  deriving DecidableEq, Fintype

def emptyRegisters : Registers := ⟨none, 0, none, .empty, .empty, 0, none⟩
def initial : AcquiredNativeState := ⟨⟨⟨.seed none, emptyRegisters⟩, 0⟩, ⟨0, 0⟩⟩

def acquiredRegisters (rho : Letter) : Registers :=
  { emptyRegisters with seed := some rho, syndrome := some (1 + rho) }

def payloadControl (t : ℕ) (s : ActivePhase) : NativeControl :=
  if h : t < 3 then .early ⟨t, h⟩ s else .fourth (.active s)

def completedCount : NativeControl → ℕ
  | .seed _ => 0
  | .early t _ => t.val
  | .fourth (.active _) => 3
  | .fourth (.pending _) => 4
  | .fourth .delivered => 4

/-- Old t and weight route original ordinal writes. Unmatched ordinals hold. -/
def writeRecords (r : Registers) (t : ℕ) (e : Letter) : QOne × QTwo :=
  if t < 3 then
    if e = 0 then
      if t - r.weight.val = 0 then
        ((match r.qone with | .empty => .a | .d => .da | q => q), r.qtwo)
      else if t - r.weight.val = 1 then
        ((match r.qone with | .a => .ac | q => q),
         (match r.qtwo with | .empty => .c | .b => .bc | q => q))
      else (r.qone, r.qtwo)
    else if r.weight.val = 0 then
      (r.qone, (match r.qtwo with | .empty => .b | .c => .cb | q => q))
    else if r.weight.val = 1 then
      ((match r.qone with | .empty => .d | .a => .ad | q => q), r.qtwo)
    else (r.qone, r.qtwo)
  else (r.qone, r.qtwo)

/-- Marker arithmetic and record writes precede the third-completion latch. -/
def writeMarker (r : Registers) (t : ℕ) (e : Letter) : Registers :=
  let weight := r.weight + (⟨e.val, by omega⟩ : Fin 5)
  let syndrome := r.syndrome.getD 0 + (if t % 2 = 0 then 1 else r.seed.getD 0) * e
  let q := writeRecords r t e
  { r with
    weight := weight
    syndrome := some syndrome
    qone := q.1
    qtwo := q.2
    z := if t = 0 then e else r.z
    snapshot := if t = 2 then some (ThirdSnapshot.mk (r.seed.getD 0) weight syndrome)
      else r.snapshot }

def completionControl (t : ℕ) (e : Letter) : NativeControl :=
  if t < 3 then payloadControl (t + 1) .p else .fourth (.pending e)

def payloadRead (f : FiniteFields) (t : ℕ) (s : ActivePhase) (x : Letter) : FiniteFields :=
  match s with
  | .p => if x = 0 then ⟨completionControl t 0, writeMarker f.registers t 0⟩
      else { f with control := payloadControl t .beta }
  | .beta => if x = 0 then { f with control := payloadControl t .p }
      else ⟨completionControl t 1, writeMarker f.registers t 1⟩

/-- Literal partial macro Read transaction. Its sole raw input is the next Letter. -/
def finiteRead (f : FiniteFields) (x : Letter) : Option FiniteFields :=
  match f.control with
  | .seed none => some { f with control := .seed (some x) }
  | .seed (some y) => some (if x = y then { f with control := .seed none }
      else ⟨payloadControl 0 .p, { f.registers with
        seed := some y
        weight := 0
        syndrome := some (1 + y) }⟩)
  | .early t s => some (payloadRead f t.val s x)
  | .fourth (.active s) => some (payloadRead f 3 s x)
  | .fourth (.pending _) | .fourth .delivered => none

def finiteStop (f : FiniteFields) (b : Letter) : Option FiniteFields :=
  match f.control with
  | .fourth (.pending a) => if b = a then some { f with control := .fourth .delivered } else none
  | _ => none

def isReturn (c : NativeControl) (x : Letter) : Bool :=
  match c with
  | .early _ .beta | .fourth (.active .beta) => x == 0
  | _ => false

def countRead (c : Counts) (x : Letter) : Counts :=
  if x = 0 then ⟨c.alpha + 1, c.beta⟩ else ⟨c.alpha, c.beta + 1⟩

def nativeRead (c : AcquiredNativeState) (x : Letter) : Option AcquiredNativeState :=
  (finiteRead c.source.finiteFields x).map fun f =>
    ⟨⟨f, c.source.payloadReturns + if isReturn c.source.finiteFields.control x then 1 else 0⟩,
      countRead c.counts x⟩

def nativeStop (c : AcquiredNativeState) (b : Letter) : Option AcquiredNativeState :=
  (finiteStop c.source.finiteFields b).map fun f =>
    ⟨⟨f, c.source.payloadReturns⟩, c.counts⟩

def nativeStep (c : AcquiredNativeState) : Operation → Option AcquiredNativeState
  | .read x => nativeRead c x
  | .stop b => nativeStop c b

def finiteStep (c : FiniteFields) : Operation → Option FiniteFields
  | .read x => finiteRead c x
  | .stop b => finiteStop c b

/-- Folding the actual partial transactions defines execution independently of forms. -/
def execute (c : AcquiredNativeState) : List Operation → Option AcquiredNativeState
  | [] => some c
  | op :: ops => (nativeStep c op).bind (fun d => execute d ops)

def run (ops : List Operation) : Option AcquiredNativeState := execute initial ops
def Legal (ops : List Operation) : Prop := ∃ c, run ops = some c

/-- Independent concatenation grammar: arbitrary returns before each completion,
    or an active cut with optional pending beta; exactly four slots are available. -/
inductive PayloadForm : ℕ → Letter → Type where
  | active {n : ℕ} {last : Letter} (j : ℕ) (phase : ActivePhase) : PayloadForm (n + 1) last
  | segment {n : ℕ} {last : Letter} (j : ℕ) (bit : Letter)
      (tail : PayloadForm n bit) : PayloadForm (n + 1) last
  | pending {last : Letter} : PayloadForm 0 last
  | delivered {last : Letter} : PayloadForm 0 last
  deriving DecidableEq

inductive SeedTail where
  | ready
  | first (x : Letter)
  | acquired (rho : Letter) (payload : PayloadForm 4 0)
  deriving DecidableEq

/-- Rejected pairs in their actual order are proof witnesses, never runtime fields. -/
structure PrefixForm where
  retries : List Letter
  tail : SeedTail
  deriving DecidableEq

def reads (w : List Letter) : List Operation := w.map Operation.read


/-- Payload control at a given native cut, with the original registers and numeric banks. -/
def atPhase (t : ℕ) (r : Registers) (s : ℕ) (c : Counts) (phase : ActivePhase) :
    AcquiredNativeState := ⟨⟨⟨payloadControl t phase, r⟩, s⟩, c⟩

private theorem execute_loop_head (t : ℕ) (ht : t ≤ 3) (r : Registers)
    (s : ℕ) (c : Counts) (ops : List Operation) :
    execute (atPhase t r s c .p) (.read 1 :: .read 0 :: ops) =
      execute (atPhase t r (s + 1) ⟨c.alpha + 1, c.beta + 1⟩ .p) ops := by
  interval_cases t <;>
    simp [atPhase, execute, nativeStep, nativeRead, finiteRead, payloadRead,
      payloadControl, isReturn, countRead]

/-- Arbitrarily many actual returns preserve the finite fields and increase all live banks.
    The suffix is executed from the resulting native state, including at the fourth segment. -/
theorem execute_payload_loops (t : ℕ) (ht : t ≤ 3) (r : Registers)
    (s : ℕ) (c : Counts) (j : ℕ) (ops : List Operation) :
    execute (atPhase t r s c .p) (reads (loopWord j) ++ ops) =
      execute (atPhase t r (s + j) ⟨c.alpha + j, c.beta + j⟩ .p) ops := by
  induction j generalizing s c with
  | zero => simp [loopWord, reads]
  | succ j ih =>
      have he := execute_loop_head t ht r s c (reads (loopWord j) ++ ops)
      have hi := ih (s + 1) ⟨c.alpha + 1, c.beta + 1⟩
      simpa [loopWord, List.replicate_succ, reads, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using he.trans hi

def phaseWord : ActivePhase → List Letter
  | .p => []
  | .beta => [1]

def renderPayload {n : ℕ} {last : Letter} : PayloadForm n last → List Operation
  | .active j s => reads (loopWord j ++ phaseWord s)
  | .segment j b rest => reads (pWord j b) ++ renderPayload rest
  | .pending => []
  | .delivered => [.stop last]

def retryWord (u : List Letter) : List Letter := (u.map (fun x => [x, x])).flatten

def seedWord (rho : Letter) : List Letter := if rho = 0 then [0, 1] else [1, 0]

def render (nf : PrefixForm) : List Operation :=
  reads (retryWord nf.retries) ++ match nf.tail with
    | .ready => []
    | .first x => [.read x]
    | .acquired rho p => reads (seedWord rho) ++ renderPayload p

def retryCounts (u : List Letter) : Counts := ⟨2 * u.count 0, 2 * u.count 1⟩

/-- Reconstruction uses marker transactions and explicit numeric formulas, not Read execution. -/
def reconstructPayload {n : ℕ} {last : Letter} (t : ℕ) (r : Registers)
    (s : ℕ) (c : Counts) : PayloadForm n last → AcquiredNativeState
  | .active j phase => ⟨⟨⟨payloadControl t phase, r⟩, s + j⟩,
      ⟨c.alpha + j, c.beta + j + match phase with | .p => 0 | .beta => 1⟩⟩
  | .segment j b rest => reconstructPayload (t + 1) (writeMarker r t b) (s + j)
      ⟨c.alpha + j + (1 - b.val), c.beta + j + 2 * b.val⟩ rest
  | .pending => ⟨⟨⟨.fourth (.pending last), r⟩, s⟩, c⟩
  | .delivered => ⟨⟨⟨.fourth .delivered, r⟩, s⟩, c⟩

def reconstruct (nf : PrefixForm) : AcquiredNativeState :=
  let c := retryCounts nf.retries
  match nf.tail with
  | .ready => ⟨⟨⟨.seed none, emptyRegisters⟩, 0⟩, c⟩
  | .first x => ⟨⟨⟨.seed (some x), emptyRegisters⟩, 0⟩, countRead c x⟩
  | .acquired rho p => reconstructPayload 0 (acquiredRegisters rho) 0
      ⟨c.alpha + 1, c.beta + 1⟩ p

def completedBits {n : ℕ} {last : Letter} : PayloadForm n last → List Letter
  | .active _ _ => []
  | .segment _ b rest => b :: completedBits rest
  | .pending | .delivered => []

def returns {n : ℕ} {last : Letter} : PayloadForm n last → ℕ
  | .active j _ => j
  | .segment j _ rest => j + returns rest
  | .pending | .delivered => 0

def pendingExponent {n : ℕ} {last : Letter} : PayloadForm n last → ℕ
  | .active _ .p => 0
  | .active _ .beta => 1
  | .segment _ _ rest => pendingExponent rest
  | .pending | .delivered => 0

def foldMarkers (t : ℕ) (r : Registers) : List Letter → Registers
  | [] => r
  | b :: bs => foldMarkers (t + 1) (writeMarker r t b) bs

def markerRegisters (rho : Letter) (bs : List Letter) : Registers :=
  foldMarkers 0 (acquiredRegisters rho) bs

def markerWeight (bs : List Letter) : ℕ := (bs.map Fin.val).sum

def markerSyndrome (rho : Letter) (bs : List Letter) : Letter :=
  1 + rho + (bs.zipIdx.map (fun be => (if be.2 % 2 = 0 then 1 else rho) * be.1)).sum

/-- The exact finite writers, including the post-write bare latch and subsequent hold. -/
def WrittenFields (rho : Letter) (bs : List Letter) (r : Registers) : Prop :=
  r.seed = some rho ∧ r.weight.val = markerWeight bs ∧
  r.syndrome = some (markerSyndrome rho bs) ∧ r.z = bs.headD 0 ∧
  r.qone = (markerRegisters rho (bs.take 3)).qone ∧
  r.qtwo = (markerRegisters rho (bs.take 3)).qtwo ∧
  r.snapshot = if bs.length < 3 then none else
    some ⟨rho, ⟨markerWeight (bs.take 3) % 5, Nat.mod_lt _ (by decide)⟩,
      markerSyndrome rho (bs.take 3)⟩

/-- Readout of written fields, not a retained completed-marker word. -/
def recoverFromRegisters (t : ℕ) (r : Registers) : List Letter :=
  match min t 3 with
  | 0 => []
  | 1 => [r.z]
  | 2 => if r.weight = 0 then [0, 0]
      else if r.weight = 2 then [1, 1] else [r.z, 1 - r.z]
  | _ => match r.qone, r.qtwo with
      | .ac, .c => [0, 0, 0]
      | .ac, .cb => [0, 0, 1]
      | .ac, .bc => if r.z = 0 then [0, 1, 0] else [1, 0, 0]
      | .ad, .b => if r.z = 0 then [0, 1, 1] else [1, 0, 1]
      | .da, .b => [1, 1, 0]
      | .d, .b => [1, 1, 1]
      | _, _ => []

def recoverMarkers (f : FiniteFields) : List Letter :=
  recoverFromRegisters (completedCount f.control) f.registers

/-- The finite projection preserves both permissions and actual successors. -/
theorem finite_projection_commutes (c : AcquiredNativeState) (op : Operation) :
    (nativeStep c op).map (fun d => d.source.finiteFields) =
      finiteStep c.source.finiteFields op := by
  cases op <;>
    simp [nativeStep, nativeRead, nativeStop, finiteStep, Option.map_map, Function.comp_def]

private theorem fold_markers_live (t : ℕ) (r : Registers) (rho sigma : Letter)
    (hseed : r.seed = some rho) (hsyn : r.syndrome = some sigma) (bs : List Letter) :
    (foldMarkers t r bs).seed = some rho ∧
    (foldMarkers t r bs).weight.val = (r.weight.val + markerWeight bs) % 5 ∧
    (foldMarkers t r bs).syndrome = some
      (sigma + ((bs.zipIdx t).map
        (fun be => (if be.2 % 2 = 0 then 1 else rho) * be.1)).sum) := by
  induction bs generalizing t r sigma with
  | nil => simp [foldMarkers, markerWeight, hseed, hsyn, Nat.mod_eq_of_lt r.weight.isLt]
  | cons b bs ih =>
    let next := writeMarker r t b
    have hnseed : next.seed = some rho := hseed
    have hnsyn : next.syndrome = some (sigma + (if t % 2 = 0 then 1 else rho) * b) := by
      simp [next, writeMarker, hseed, hsyn]
    obtain ⟨h1, h2, h3⟩ := ih (t + 1) next _ hnseed hnsyn
    refine ⟨h1, ?_, ?_⟩
    · simpa only [foldMarkers, next, writeMarker, Fin.val_add, markerWeight,
        List.map_cons, List.sum_cons, Nat.mod_add_mod, Nat.add_assoc] using h2
    · simpa [foldMarkers, List.zipIdx_cons, List.map_cons, List.sum_cons,
        add_assoc] using h3

private theorem fold_markers_hold (t : ℕ) (ht : 3 ≤ t) (r : Registers) (bs : List Letter) :
    (foldMarkers t r bs).qone = r.qone ∧
    (foldMarkers t r bs).qtwo = r.qtwo ∧
    (foldMarkers t r bs).z = r.z ∧
    (foldMarkers t r bs).snapshot = r.snapshot := by
  induction bs generalizing t r with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons b bs ih =>
    have h0 : t ≠ 0 := by omega
    have h2 : t ≠ 2 := by omega
    have hlt : ¬ t < 3 := by omega
    simpa [foldMarkers, writeMarker, writeRecords, h0, h2, hlt]
      using ih (t + 1) (by omega) (writeMarker r t b)

/-- Unrestricted writer fields; live weight wraps while the first-three records hold. -/
def FoldWrittenFields (rho : Letter) (bs : List Letter) (r : Registers) : Prop :=
  r.seed = some rho ∧ r.weight.val = markerWeight bs % 5 ∧
  r.syndrome = some (markerSyndrome rho bs) ∧ r.z = bs.headD 0 ∧
  r.qone = (markerRegisters rho (bs.take 3)).qone ∧
  r.qtwo = (markerRegisters rho (bs.take 3)).qtwo ∧
  r.snapshot = if bs.length < 3 then none else
    some ⟨rho, ⟨markerWeight (bs.take 3) % 5, Nat.mod_lt _ (by decide)⟩,
      markerSyndrome rho (bs.take 3)⟩

/-- The total writer recovers the same selected prefix after arbitrarily many markers. -/
theorem marker_fields_recover (rho : Letter) (bs : List Letter) :
    recoverMarkers ⟨if bs.length < 4 then payloadControl bs.length .p
      else .fourth (.pending (bs.getLastD 0)), markerRegisters rho bs⟩ = bs.take 3 := by
  rcases bs with _ | ⟨a, bs⟩
  · rfl
  rcases bs with _ | ⟨b, bs⟩
  · fin_cases a <;> simp [recoverMarkers, recoverFromRegisters, completedCount,
      payloadControl, markerRegisters, foldMarkers, acquiredRegisters, emptyRegisters,
      writeMarker, writeRecords]
  rcases bs with _ | ⟨c, bs⟩
  · fin_cases a <;> fin_cases b <;> simp [recoverMarkers, recoverFromRegisters,
      completedCount, payloadControl, markerRegisters, foldMarkers, acquiredRegisters,
      emptyRegisters, writeMarker, writeRecords]
  have hq := fold_markers_hold 3 (by omega)
    (markerRegisters rho [a, b, c]) bs
  have hf : markerRegisters rho (a :: b :: c :: bs) =
      foldMarkers 3 (markerRegisters rho [a, b, c]) bs := rfl
  have hc : min (completedCount
      (if (a :: b :: c :: bs).length < 4 then payloadControl (a :: b :: c :: bs).length .p
        else .fourth (.pending ((a :: b :: c :: bs).getLastD 0)))) 3 = 3 := by
    split
    · rename_i hlt
      have hlen : (a :: b :: c :: bs).length = 3 := by
        simp only [List.length_cons] at hlt ⊢
        omega
      simp [hlen, payloadControl, completedCount]
    · rfl
  unfold recoverMarkers recoverFromRegisters
  rw [hc, hf, hq.1, hq.2.1, hq.2.2.1]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [markerRegisters, foldMarkers, acquiredRegisters, emptyRegisters,
      writeMarker, writeRecords]

/-- Exact live arithmetic and held records for every word of the total marker writer. -/
theorem marker_fields_exact (rho : Letter) (bs : List Letter) :
    FoldWrittenFields rho bs (markerRegisters rho bs) := by
  obtain ⟨hs, hw, hy⟩ := fold_markers_live 0 (acquiredRegisters rho) rho (1 + rho)
    rfl rfl bs
  change (markerRegisters rho bs).seed = some rho at hs
  have hw' : (markerRegisters rho bs).weight.val = markerWeight bs % 5 := by
    simpa [markerRegisters, acquiredRegisters, emptyRegisters] using hw
  have hy' : (markerRegisters rho bs).syndrome = some (markerSyndrome rho bs) := by
    simpa [markerRegisters, markerSyndrome] using hy
  refine ⟨hs, hw', hy', ?_⟩
  rcases bs with _ | ⟨a, bs⟩
  · simp [markerRegisters, foldMarkers, acquiredRegisters, emptyRegisters]
  rcases bs with _ | ⟨b, bs⟩
  · simp [markerRegisters, foldMarkers, acquiredRegisters, emptyRegisters,
      writeMarker, writeRecords]
  rcases bs with _ | ⟨c, bs⟩
  · simp [markerRegisters, foldMarkers, acquiredRegisters, emptyRegisters,
      writeMarker, writeRecords]
  have hq := fold_markers_hold 3 (by omega)
    (markerRegisters rho [a, b, c]) bs
  have hf : markerRegisters rho (a :: b :: c :: bs) =
      foldMarkers 3 (markerRegisters rho [a, b, c]) bs := rfl
  rw [hf]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hq.2.2.1]
    simp [markerRegisters, foldMarkers, acquiredRegisters, emptyRegisters, writeMarker]
  · simpa using hq.1
  · simpa using hq.2.1
  · rw [hq.2.2.2]
    have hlast : (markerRegisters rho [a, b, c]).snapshot =
        some ⟨rho, (markerRegisters rho [a, b, c]).weight,
          markerSyndrome rho [a, b, c]⟩ := by
      simp [markerRegisters, foldMarkers, acquiredRegisters, emptyRegisters,
        writeMarker, markerSyndrome, List.zipIdx_cons, add_assoc]
    have hval := (fold_markers_live 0 (acquiredRegisters rho) rho (1 + rho)
      rfl rfl [a, b, c]).2.1
    have heq : (markerRegisters rho [a, b, c]).weight =
        (⟨markerWeight [a, b, c] % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) := by
      apply Fin.ext
      simpa [markerRegisters, acquiredRegisters, emptyRegisters] using hval
    have hlen : ¬ (a :: b :: c :: bs).length < 3 := by
      simp only [List.length_cons]
      omega
    simp only [hlen, if_false, List.take_succ_cons, List.take_zero]
    rw [hlast, heq]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixState
