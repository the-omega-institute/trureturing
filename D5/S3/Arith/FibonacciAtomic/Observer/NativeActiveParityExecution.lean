/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeActiveParityExecution
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeActiveParityExecution
   mirror-E: none(waiver:unbounded-symbolic-execution)
   anchors: []
   utility: none
   digest: Full expanded active parity execution on independently labelled original source cones. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativePollingAlignment
import D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
import D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open ActualCutPartitionRecovery (LiteralRow rowAt evaluateRow)
open DelayedOriginalReadout (rightClock rights right_clock_iterate right_clock_readout)
open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution

/-- An original full skeleton with exactly h independently indexed leaves.
The locations are immutable literal addresses, not runtime registers. -/
structure Chart (h : Nat) where
  row : LiteralRow
  address : Fin h → Address
  located : ∀ i, rowAt (address i) row = some (.of (.inr i.val))
  size : row.length = h

/-- Index every leaf of a public full ordered skeleton, retaining its shape. -/
def numbered : Source → Nat → LiteralRow
  | .of _, offset => .of (.inr offset)
  | .mul l r, offset => .mul (numbered l offset) (numbered r (offset + l.length))

/-- The immutable address of an indexed original leaf. -/
def locator : (S : Source) → Fin S.length → Address
  | .of _, _ => []
  | .mul l r, i => if hi : i.val < l.length then
      false :: locator l ⟨i.val, hi⟩
    else true :: locator r ⟨i.val - l.length, by
      have bound := i.isLt
      change i.val < l.length + r.length at bound
      omega⟩

private theorem numbered_location (S : Source) (offset : Nat) (i : Fin S.length) :
    rowAt (locator S i) (numbered S offset) = some (.of (.inr (offset + i.val))) := by
  induction S generalizing offset with
  | of b =>
      have zero : i.val = 0 := by
        have bound := i.isLt
        change i.val < 1 at bound
        omega
      simp [locator, numbered, rowAt, zero]
  | mul l r ihl ihr =>
      by_cases hi : i.val < l.length
      · simpa [locator, numbered, hi, rowAt] using ihl offset ⟨i.val, hi⟩
      · have small : i.val - l.length < r.length := by
          have bound := i.isLt
          change i.val < l.length + r.length at bound
          omega
        have index : offset + l.length + (i.val - l.length) = offset + i.val := by omega
        simpa [locator, numbered, hi, rowAt, index] using
          ihr (offset + l.length) ⟨i.val - l.length, small⟩

/-- Every public full skeleton supplies its own complete original source chart. -/
def chartOf (S : Source) : Chart S.length where
  row := numbered S 0
  address := locator S
  located := by intro i; simpa using numbered_location S 0 i
  size := by
    have size (S : Source) (offset : Nat) : (numbered S offset).length = S.length := by
      induction S generalizing offset with
      | of b => rfl
      | mul l r ihl ihr =>
          change (numbered l offset).length +
            (numbered r (offset + l.length)).length = _
          rw [ihl, ihr]
          rfl
    exact size S 0

/-- Numerical original labels: false is alpha and true is beta. -/
def bit (b : Bool) : Nat := if b then 1 else 0

def atom (n : Nat) : Source := substitution^[n] (.of true)

/-- Extend the original label vector only to interpret the finite row. -/
def labels {h : Nat} (x : Fin h → Bool) (i : Nat) : Bool :=
  if hi : i < h then x ⟨i, hi⟩ else false

def source {h : Nat} (C : Chart h) (x : Fin h → Bool) : Source :=
  evaluateRow (fun i => atom (bit (labels x i))) C.row

/-- The only observation field is obtained from this actual original source. -/
def observations {h : Nat} (C : Chart h) (t : Nat) (x : Fin h → Bool) :
    Nat → Address → Reply :=
  NativePollingAlignment.observations (substitution^[t] (source C x))

/-- This decoder is used only after actual polling alignment. -/
def chi : Reply → Bool
  | .absent | .beta => true
  | .alpha | .branch => false

/-- The three nonzero phase words 01, 11, 10, in that order. -/
inductive Phase where
  | first | second | route
  deriving DecidableEq

/-- Symbolic coordinates of all Q, B, C and V rows of the expanded table.
Their binary realization is a separate mathematical obligation. -/
inductive Control (h : Nat) where
  | q : Fin (h + 1) → Bool → Control h
  | b : Fin h → Bool → Bool → Control h
  | c : Fin h → Bool → Control h
  | v : Bool → Phase → Control h
  deriving DecidableEq

def start (h : Nat) : Control h := .q ⟨0, by omega⟩ false

def endpoint (h : Nat) (a : Bool) : Control h := .q ⟨h, by omega⟩ a

/-- Halt payloads are fixed by the complete control row. -/
def output {h : Nat} : Control h → Option Bool
  | .q i a => if i.val = h then some a else none
  | _ => none

def next {h : Nat} (i : Fin h) (b : Bool) : Control h :=
  .q ⟨i.val + 1, by omega⟩ b

def dispatch {h : Nat} (i : Fin h) (a : Bool) (o : Reply) : Control h :=
  if i.val = 0 then
    match o with
    | .absent => .v a .first
    | .branch => .q ⟨0, by omega⟩ a
    | .alpha | .beta => .b i a (xor a (chi o))
  else .b i a (xor a (chi o))

/-- Every listed raw response has a row, including the unsupported pilot hold.
The two genuine updates and the paid return Read are distinct instructions. -/
def program {h : Nat} (C : Chart h) (K : Nat) :
    Control h → Instruction (Control h) Address Reply
  | .q i a => if hi : i.val < h then
      .read (C.address ⟨i.val, hi⟩ ++ rights K) (dispatch ⟨i.val, hi⟩ a)
    else .halt
  | .b i a b => .read [] (fun _ => if a = b then .c i b else .b i b b)
  | .c i b => .read [] (fun _ => next i b)
  | .v a .first => .update (.v a .second)
  | .v a .second => .update (.v a .route)
  | .v a .route => .read [] (fun _ => .q ⟨0, by omega⟩ a)

/-- XOR of the first n original labels; n is proof data, not runtime storage. -/
def parity (x : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => xor (parity x n) (x n)

theorem cone_read {h : Nat} (C : Chart h) (x : Fin h → Bool)
    (t j : Nat) (i : Fin h) (p : Address) :
    observations C t x j (C.address i ++ p) =
      readout p (atom (t + j + bit (x i))) := by
  have location := NativeCutFibers.rowAt_evaluate C.row
    (fun n => atom (bit (labels x n))) (C.address i) _ (C.located i)
  have original : subtree (C.address i) (source C x) = some (atom (bit (x i))) := by
    simpa [source, evaluateRow, labels, i.isLt] using location
  have current := NativeDepthPatterns.original_present_transport (t + j)
    (C.address i) (source C x) _ original
  have append := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (C.address i) p (substitution^[t + j] (source C x))
  rw [current] at append
  have iter : substitution^[j] (substitution^[t] (source C x)) =
      substitution^[t + j] (source C x) := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  change readout (C.address i ++ p)
    (substitution^[j] (substitution^[t] (source C x))) = _
  rw [iter, append]
  change readout p (substitution^[t + j] (substitution^[bit (x i)] (.of true))) = _
  rw [← Function.iterate_add_apply]
  rfl

private theorem window_decode (K n : Nat) (window : n + 1 ≥ 2 * K ∧ n ≤ 2 * K + 2) :
    chi (readout (rights K) (atom n)) = decide (n % 2 = 1) := by
  have clock : rightClock (atom n) = n := by
    simpa [atom, rightClock] using right_clock_iterate n (.of true)
  have replies := right_clock_readout K (atom n)
  rw [clock] at replies
  rcases replies with ⟨ha, hb, hc, hd⟩
  by_cases a : n < 2 * K
  · rw [ha.mpr a, chi]
    have odd : n % 2 = 1 := by omega
    simp [odd]
  · by_cases b : n = 2 * K
    · rw [hb.mpr b, chi]; subst n; simp
    · by_cases c : n = 2 * K + 1
      · rw [hc.mpr c, chi]; subst n; simp
      · rw [hd.mpr (by omega), chi]
        have even : n % 2 = 0 := by omega
        simp [even]

private theorem route {h : Nat} (C : Chart h) (K : Nat)
    (obs : Nat → Address → Reply) (i : Fin h) (a b : Bool)
    (j J : Nat) (z : Control h)
    (tail : Run (program C K) obs (next i b) j z J) :
    Run (program C K) obs (.b i a b) j z J := by
  by_cases eq : a = b
  · apply Run.read (p := []) (k := fun _ => if a = b then .c i b else .b i b b) rfl
    simp only [if_pos eq]
    exact Run.read (p := []) (k := fun _ => next i b) rfl tail
  · apply Run.read (p := []) (k := fun _ => if a = b then .c i b else .b i b b) rfl
    simp only [if_neg eq]
    apply Run.read (p := []) (k := fun _ => if b = b then .c i b else .b i b b) rfl
    simp only
    exact Run.read (p := []) (k := fun _ => next i b) rfl tail

/-- Splice into the already proved pilot path; no retry descent is reproved. -/
private def pilotImage {h : Nat} (positive : 0 < h) (a : Bool) :
    NativePollingAlignment.Control → Control h
  | .poll => .q ⟨0, by omega⟩ a
  | .firstUpdate => .v a .first
  | .secondUpdate => .v a .second
  | .route => .v a .route
  | .done e => .b ⟨0, positive⟩ a (xor a e)

private theorem pilot_continue {h : Nat} (C : Chart h) (K : Nat) (positive : 0 < h)
    (obs : Nat → Address → Reply) (pilotObs : Nat → Address → Reply)
    (same : ∀ j p, obs j (C.address ⟨0, positive⟩ ++ p) = pilotObs j p)
    (a : Bool) (q q' : NativePollingAlignment.Control) (j J L : Nat)
    (path : Run (NativePollingAlignment.program K) pilotObs q j q' J)
    (z : Control h)
    (tail : Run (program C K) obs (pilotImage positive a q') J z L) :
    Run (program C K) obs (pilotImage positive a q) j z L := by
  induction path with
  | refl => exact tail
  | @read q p k j qlast J hop suffix ih =>
    cases q with
    | poll =>
      simp only [NativePollingAlignment.program, Instruction.read.injEq] at hop
      rcases hop with ⟨rfl, rfl⟩
      apply Run.read (p := C.address ⟨0, positive⟩ ++ rights K)
        (k := dispatch ⟨0, positive⟩ a) (by simp [program, pilotImage, positive])
      rw [same]
      cases response : pilotObs j (rights K) <;>
        simpa [pilotImage, NativePollingAlignment.dispatch, dispatch, chi, response] using (ih tail)
    | route =>
      simp only [NativePollingAlignment.program, Instruction.read.injEq] at hop
      rcases hop with ⟨rfl, rfl⟩
      exact Run.read (p := []) (k := fun _ => .q ⟨0, by omega⟩ a) rfl (ih tail)
    | firstUpdate => simp [NativePollingAlignment.program] at hop
    | secondUpdate => simp [NativePollingAlignment.program] at hop
    | done e => simp [NativePollingAlignment.program] at hop
  | @update q qnext j qlast J hop suffix ih =>
    cases q with
    | firstUpdate =>
      simp only [NativePollingAlignment.program, Instruction.update.injEq] at hop
      subst qnext
      exact Run.update rfl (ih tail)
    | secondUpdate =>
      simp only [NativePollingAlignment.program, Instruction.update.injEq] at hop
      subst qnext
      exact Run.update rfl (ih tail)
    | poll => simp [NativePollingAlignment.program] at hop
    | route => simp [NativePollingAlignment.program] at hop
    | done e => simp [NativePollingAlignment.program] at hop

private theorem stages {h : Nat} (C : Chart h) (K : Nat)
    (obs : Nat → Address → Reply) (j : Nat) (bits : Nat → Bool)
    (decoded : ∀ i : Fin h, chi (obs j (C.address i ++ rights K)) = bits i.val) :
    ∀ (n i : Nat) (total : i + n = h) (_pos : 0 < i),
      Run (program C K) obs (.q ⟨i, by omega⟩ (parity bits i)) j
        (endpoint h (parity bits h)) j := by
  intro n
  induction n with
  | zero =>
      intro i total pos
      have eq : i = h := by omega
      subst i
      exact .refl _ _
  | succ n ih =>
    intro i total pos
    have small : i < h := by omega
    let idx : Fin h := ⟨i, small⟩
    have suffix := ih (i + 1) (by omega) (by omega)
    have bitlaw : xor (parity bits i) (chi (obs j (C.address idx ++ rights K))) =
        parity bits (i + 1) := by rw [decoded]; rfl
    have routed := route C K obs idx (parity bits i)
      (xor (parity bits i) (chi (obs j (C.address idx ++ rights K)))) j j
      (endpoint h (parity bits h)) (by simpa [next, bitlaw] using suffix)
    apply Run.read (p := C.address idx ++ rights K) (k := dispatch idx (parity bits i))
      (by simp [program, small, idx])
    simpa [dispatch, idx, Nat.ne_of_gt pos] using routed

theorem shifted_parity (x : Nat → Bool) (b : Bool) (n : Nat) :
    parity (fun i => xor b (x i)) n =
      xor (decide (n % 2 = 1) && b) (parity x n) := by
  induction n with
  | zero => simp [parity]
  | succ n ih =>
    rw [parity, ih, parity]
    have rem := Nat.mod_lt n (by decide : 0 < 2)
    rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with even | odd
    · have nextOdd : (n + 1) % 2 = 1 := by omega
      simp only [even, nextOdd, decide_true, Bool.true_and]
      cases b <;> cases parity x n <;> cases x n <;> rfl
    · have nextEven : (n + 1) % 2 = 0 := by omega
      simp only [odd, nextEven, decide_true, Bool.true_and]
      cases b <;> cases parity x n <;> cases x n <;> rfl

/-- The complete expanded table reaches exactly the original parity halt and the
pilot's real update epoch, in the admissible source regimes. -/
private theorem charted_execution {h : Nat} (C : Chart h) (positive : 0 < h)
    (x : Fin h → Bool) (t K : Nat) (bound : t ≤ 2 * K)
    (admissible : h % 2 = 0 ∨ t = 0) (b : Bool) (N : Nat) :
    Run (program C K) (observations C t x) (start h) 0 (endpoint h b) N ↔
      b = parity (labels x) h ∧ N = 2 * (K - (t + bit (x ⟨0, positive⟩)) / 2) := by
  let first : Fin h := ⟨0, positive⟩
  let n := t + bit (x first)
  let J := 2 * (K - n / 2)
  let shift := decide (t % 2 = 1)
  let bits := fun i => xor shift (labels x i)
  have labelBound : bit (x first) ≤ 1 := by cases x first <;> simp [bit]
  have promise : n ≤ 2 * K + 1 := by dsimp [n]; omega
  have pilotClock : rightClock (atom n) = n := by
    simpa [atom, rightClock] using right_clock_iterate n (.of true)
  have pilot := (NativePollingAlignment.native_polling_alignment K (atom n)
    (by omega) (decide (n % 2 = 1)) J).mpr (by simp [pilotClock, J])
  have quotient := Nat.mod_add_div n 2
  have remainder := Nat.mod_lt n (by decide : 0 < 2)
  have qbound : n / 2 ≤ K := by omega
  have aligned : n + J = 2 * K + n % 2 := by dsimp [J]; omega
  have decoded : ∀ i : Fin h,
      chi (observations C t x J (C.address i ++ rights K)) = bits i.val := by
    intro i
    rw [cone_read]
    have bi : bit (x i) ≤ 1 := by cases x i <;> simp [bit]
    have window : t + J + bit (x i) + 1 ≥ 2 * K ∧ t + J + bit (x i) ≤ 2 * K + 2 := by
      dsimp [n] at aligned; omega
    rw [window_decode K _ window]
    dsimp [bits, shift, labels]
    simp only [i.isLt, ↓reduceIte]
    rcases (show t % 2 = 0 ∨ t % 2 = 1 by omega) with even | odd
    · cases xi : x i <;> simp [bit, even] <;> dsimp [J] <;> omega
    · cases xi : x i <;> simp [bit, odd] <;> dsimp [J] <;> omega
  have firstbit : decide (n % 2 = 1) = bits 0 := by
    have actual := decoded first
    have reply : observations C t x J (C.address first ++ rights K) =
        readout (rights K) (atom (n + J)) := by
      simpa [n, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        cone_read C x t J first (rights K)
    rw [reply, window_decode K (n + J) (by omega)] at actual
    have sameMod : (n + J) % 2 = n % 2 := by dsimp [J]; omega
    simpa [first, sameMod] using actual
  have terminal : parity bits h = parity (labels x) h := by
    rw [shifted_parity]
    rcases admissible with even | rfl
    · simp [even]
    · simp [shift]
  have suffix : Run (program C K) (observations C t x)
      (.b first false (xor false (decide (n % 2 = 1)))) J
      (endpoint h (parity (labels x) h)) J := by
    apply route
    have rest := stages C K (observations C t x) J bits decoded
      (h - 1) 1 (by omega) (by omega)
    simpa [next, first, parity, firstbit, terminal] using rest
  have same : ∀ j p, observations C t x j (C.address first ++ p) =
      NativePollingAlignment.observations (atom n) j p := by
    intro j p
    rw [cone_read]
    change readout p (substitution^[t + j + bit (x first)] (.of true)) =
      readout p (substitution^[j] (substitution^[n] (.of true)))
    rw [← Function.iterate_add_apply]
    congr 2
    dsimp [n]
    omega
  have run : Run (program C K) (observations C t x) (start h) 0
      (endpoint h (parity (labels x) h)) J :=
    pilot_continue C K positive _ _ same false .poll _ 0 J J pilot _ suffix
  have halt (a : Bool) : program C K (endpoint h a) = .halt := by simp [program, endpoint]
  constructor
  · intro path
    obtain ⟨eq, epoch⟩ := run_halt_unique path run (halt b) (halt _)
    exact ⟨(Control.q.inj eq).2, epoch⟩
  · rintro ⟨rfl, rfl⟩
    exact run

/-- On every full original skeleton and all its independent labels, the expanded
active table has exactly the original parity halt and the real pilot epoch. -/
theorem native_active_parity_execution (S : Source) (x : Fin S.length → Bool)
    (t K : Nat) (bound : t ≤ 2 * K) (admissible : S.length % 2 = 0 ∨ t = 0)
    (b : Bool) (N : Nat) :
    Run (program (chartOf S) K) (observations (chartOf S) t x)
      (start S.length) 0 (endpoint S.length b) N ↔
      b = parity (labels x) S.length ∧
        N = 2 * (K - (t + bit (x ⟨0, S.length_pos⟩)) / 2) ∧
        output (endpoint S.length b) = some (parity (labels x) S.length) := by
  have exactRun := charted_execution (chartOf S) S.length_pos x t K bound admissible b N
  constructor
  · intro path
    obtain ⟨bitEq, epochEq⟩ := exactRun.mp path
    exact ⟨bitEq, epochEq, by simp [output, endpoint, bitEq]⟩
  · rintro ⟨bitEq, epochEq, _⟩
    exact exactRun.mpr ⟨bitEq, epochEq⟩

#print axioms native_active_parity_execution

end D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution
