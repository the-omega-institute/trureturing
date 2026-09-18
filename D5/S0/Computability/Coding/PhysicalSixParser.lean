/- GID: D5/S0/Computability/Coding/PhysicalSixParser
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/PhysicalSixParser
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Size]
   utility: none
   digest: A physical eighteen-bit-tape parser with retained little-endian buffers and counted width. -/

import Mathlib.Data.Nat.Size
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
The program has eighteen independent Boolean tapes. A transition performs exactly one read,
write, or unit move; only a read can select between successors. The source companion never
moves. Input length, decoded parameters, coordinates and run histories occur only in specifications.
The return frame supplies input capacity, not arithmetic workspace or a complete executor.
-/

namespace D5.S0.Computability.Coding.PhysicalSixParser

/-- Nine pairs of physical bit tapes; `false` selects occupancy (raw data in pair zero). -/
abbrev Track := Fin 9 × Bool

/-- The six parameter pairs, in their wire order. -/
def parameterPair (i : Fin 6) : Fin 9 := ⟨i.val + 1, by omega⟩

/-- A finite return address for the shared tally routine. -/
inductive Continuation where
  | header (field : Fin 6)
  | payload (field : Fin 6)
  | finish
  deriving DecidableEq, Fintype

/-- All substates are finite. Stage numbers select literal rows of `program`. -/
inductive Control where
  | init (pair : Fin 9)
  | start
  | header (field : Fin 6) (stage : Fin 5)
  | payload (field : Fin 6) (stage : Fin 7)
  | consume (next : Continuation)
  | count (next : Continuation) (stage : Fin 19)
  | sourceRewind (stage : Fin 7)
  | pad (field : Fin 6) (stage : Fin 16)
  | halt
  | sink
  deriving DecidableEq, Fintype

/-- A single charged elementary instruction, or the halted control. -/
inductive Instruction where
  | read (tape : Track) (onFalse onTrue : Control)
  | write (tape : Track) (value : Bool) (next : Control)
  | move (tape : Track) (right : Bool) (next : Control)
  | halt
  deriving DecidableEq

/-- Finite return-address decoding, with no stack or runtime natural number. -/
def resume : Continuation → Control
  | .header i => .header i 0
  | .payload i => .payload i 0
  | .finish => .sourceRewind 0

/-- The fixed, literal transition table. Pair actions occupy separate rows. -/
def program : Control → Instruction
  | .init p => .write (p, true) true
      (if h : p.val < 8 then .init ⟨p.val + 1, by omega⟩ else .start)
  | .start => .move (0, false) true (.header 0 0)
  | .header i k => match k.val with
    | 0 => .read (0, false) (.consume (.payload i)) (.header i 1)
    | 1 => .move (parameterPair i, false) true (.header i 2)
    | 2 => .move (parameterPair i, true) true (.header i 3)
    | 3 => .write (parameterPair i, false) true (.header i 4)
    | _ => .write (parameterPair i, true) false (.consume (.header i))
  | .payload i k => match k.val with
    | 0 => .read (parameterPair i, false) (.payload i 1) (.payload i 2)
    | 1 => .read (parameterPair i, true) .sink
        (if h : i.val < 5 then .header ⟨i.val + 1, by omega⟩ 0
          else .count .finish 0)
    | 2 => .read (0, false) (.payload i 3) (.payload i 4)
    | 3 => .write (parameterPair i, true) false (.payload i 5)
    | 4 => .write (parameterPair i, true) true (.payload i 5)
    | 5 => .move (parameterPair i, false) false (.payload i 6)
    | _ => .move (parameterPair i, true) false (.consume (.payload i))
  | .consume c => .move (0, false) true (.count c 0)
  | .count c k => match k.val with
    | 0 => .move (7, false) true (.count c 1)
    | 1 => .move (7, true) true (.count c 2)
    | 2 => .write (7, false) true (.count c 3)
    | 3 => .write (7, true) true (.count c 4)
    | 4 => .move (8, false) true (.count c 5)
    | 5 => .move (8, true) true (.count c 6)
    | 6 => .read (8, false) (.count c 7) (.count c 8)
    | 7 => .write (8, false) true (.count c 9)
    | 8 => .read (8, true) (.count c 9) (.count c 10)
    | 9 => .write (8, true) true (.count c 13)
    | 10 => .write (8, true) false (.count c 11)
    | 11 => .move (8, false) true (.count c 12)
    | 12 => .move (8, true) true (.count c 6)
    | 13 => .read (8, false) (.count c 14) (.count c 15)
    | 14 => .read (8, true) .sink (resume c)
    | 15 => .move (8, false) false (.count c 16)
    | 16 => .move (8, true) false (.count c 13)
    | _ => .read (0, true) .sink .sink
  | .sourceRewind k => match k.val with
    | 0 => .read (7, false) (.sourceRewind 1) (.sourceRewind 2)
    | 1 => .read (7, true) .sink (.pad 0 0)
    | 2 => .read (7, true) .sink (.sourceRewind 3)
    | 3 => .move (0, false) false (.sourceRewind 4)
    | 4 => .move (7, false) false (.sourceRewind 5)
    | 5 => .move (7, true) false (.sourceRewind 0)
    | _ => .read (0, true) .sink .sink
  | .pad i k => match k.val with
    | 0 => .move (7, false) true (.pad i 1)
    | 1 => .move (7, true) true (.pad i 2)
    | 2 => .move (parameterPair i, false) true (.pad i 3)
    | 3 => .move (parameterPair i, true) true (.pad i 4)
    | 4 => .read (7, false) (.pad i 9) (.pad i 5)
    | 5 => .read (7, true) .sink (.pad i 6)
    | 6 => .read (parameterPair i, false) (.pad i 7) (.pad i 0)
    | 7 => .write (parameterPair i, false) true (.pad i 8)
    | 8 => .write (parameterPair i, true) false (.pad i 0)
    | 9 => .move (7, false) false (.pad i 10)
    | 10 => .move (7, true) false (.pad i 11)
    | 11 => .move (parameterPair i, false) false (.pad i 12)
    | 12 => .move (parameterPair i, true) false (.pad i 13)
    | 13 => .read (7, false) (.pad i 14) (.pad i 9)
    | 14 => .read (7, true) .sink
        (if h : i.val < 5 then .pad ⟨i.val + 1, by omega⟩ 0 else .halt)
    | _ => .read (0, true) .sink .sink
  | .halt => .halt
  | .sink => .read (0, true) .sink .sink

/-- Physical memory and signed head coordinates. Neither is available to finite control. -/
structure Configuration where
  control : Control
  head : Track → ℤ
  cell : Track → ℤ → Bool

/-- One physical action. A halted configuration remains halted for mathematical iteration. -/
def step (c : Configuration) : Configuration :=
  match program c.control with
  | .read t f g => { c with control := if c.cell t (c.head t) then g else f }
  | .write t b k => { c with
      control := k
      cell := Function.update c.cell t (Function.update (c.cell t) (c.head t) b) }
  | .move t d k => { c with
      control := k
      head := Function.update c.head t (c.head t + (if d then 1 else -1)) }
  | .halt => c

/-- Iteration of actual elementary actions; its index is also the charged time. -/
def run (c : Configuration) (n : ℕ) : Configuration := step^[n] c

/-- A finite word beginning immediately to the right of the origin; no end marker. -/
def rawCell (w : List Bool) (z : ℤ) : Bool :=
  if 0 < z then w[z.toNat - 1]?.getD false else false

/-- A two-track word with the distinct home marker, occupied digits and blank suffix. -/
def wordCell (w : List Bool) (value : Bool) (z : ℤ) : Bool :=
  if z = 0 then value
  else if 0 < z then
    if value then w[z.toNat - 1]?.getD false else decide (z.toNat ≤ w.length)
  else false

/-- The source supplies only its raw bits. All eighteen heads and all work start blank at zero. -/
def initial (q : List Bool) : Configuration where
  control := .init 0
  head := fun _ => 0
  cell := fun t => if t = (0, false) then rawCell q else fun _ => false

/-- The positive-integer wire code uses most-significant-bit-first payloads. -/
def code (n : ℕ) : List Bool := List.replicate n.bits.length true ++ false :: n.bits.reverse

/-- Six fields in fixed order; this is a specification, not a runtime decoder. -/
def source (v : Fin 6 → ℕ) : List Bool := (List.ofFn fun i => code (v i)).flatten

/-- Exact returned memory, including all blank cells outside the counted regions. -/
def returned (v : Fin 6 → ℕ) : Configuration where
  control := .halt
  head := fun _ => 0
  cell := fun (p, b) =>
    if h0 : p = 0 then if b then fun z => decide (z = 0) else rawCell (source v)
    else if h7 : p = 7 then wordCell (List.replicate ((source v).length + 1) true) b
    else if h8 : p = 8 then wordCell ((source v).length + 1).bits b
    else wordCell
      ((v ⟨p.val - 1, by have h := p.isLt; simp only [Fin.ext_iff] at h0 h7 h8; omega⟩).bits ++
        List.replicate ((source v).length + 1 - (v ⟨p.val - 1, by have h := p.isLt; simp only [Fin.ext_iff] at h0 h7 h8; omega⟩).bits.length) false) b

/-- Initial cells count even when their input bit is zero. Origins on all tapes count. -/
def initialVisited (s : ℕ) (t : Track) : Finset ℤ :=
  if t = (0, false) then (Finset.range (s + 1)).image Int.ofNat else {0}

/-- Persistent visited history is proof data. No instruction can read it. -/
def visited (q : List Bool) (t : Track) : ℕ → Finset ℤ
  | 0 => initialVisited q.length t
  | n + 1 => insert ((run (initial q) (n + 1)).head t) (visited q t n)

/-- Signed unary addresses: sign, magnitude many ones, and a terminating zero. -/
def headDescription (z : ℤ) : List Bool := decide (z < 0) :: List.replicate z.natAbs true ++ [false]

/-- A fixed-width one-hot description of finite control. -/
noncomputable def controlDescription (c : Control) : List Bool :=
  List.ofFn fun i : Fin (Fintype.card Control) => decide ((Fintype.equivFin Control).symm i = c)

/-- Fixed-width one-hot tape selectors. -/
def trackDescription (t : Track) : List Bool :=
  List.ofFn fun i : Fin 18 => decide (i.val = 2 * t.1.val + t.2.toNat)

/-- Fixed-width instruction rows: opcode, tape, bit/direction and two successor slots. -/
noncomputable def instructionDescription : Instruction → List Bool
  | .read t f g => [false, false] ++ trackDescription t ++ [false] ++
      controlDescription f ++ controlDescription g
  | .write t b k => [false, true] ++ trackDescription t ++ [b] ++
      controlDescription k ++ controlDescription k
  | .move t b k => [true, false] ++ trackDescription t ++ [b] ++
      controlDescription k ++ controlDescription k
  | .halt => [true, true] ++ List.replicate 18 false ++ [false] ++
      controlDescription .halt ++ controlDescription .halt

/-- The entire finite table, in the fixed control enumeration. -/
noncomputable def programDescription : List Bool :=
  (List.ofFn fun i : Fin (Fintype.card Control) =>
    instructionDescription (program ((Fintype.equivFin Control).symm i))).flatten

/-- All tape bits ever supplied or visited, every framed head, current control and fixed table. -/
noncomputable def charge (q : List Bool) (n : ℕ) : ℕ :=
  programDescription.length + (controlDescription (run (initial q) n).control).length +
    ∑ t : Track, ((visited q t n).card + (headDescription (run (initial q) n |>.head t)).length)

/-- The complete operational target; no correctness premise is included in this specification. -/
def Contract : Prop :=
  ∃ C_T C_S : ℕ, 0 < C_T ∧ 0 < C_S ∧
    ∀ P A R B E C : ℕ,
      0 < P → 0 < A → 0 < R → 0 < B → 0 < E → 0 < C →
      2 * P < A → 2 * R < B →
      let v : Fin 6 → ℕ := ![P, A, R, B, E, C]
      let q := source v
      ∃ T : ℕ, run (initial q) T = returned v ∧
        T ≤ C_T * (q.length + 1) ^ 2 ∧
        (∀ n ≤ T, charge q n ≤ C_S * (q.length + 1)) ∧
        (∀ n ≤ T, ∀ t, 0 ≤ (run (initial q) n).head t ∧
          (run (initial q) n).head t ≤ (q.length : ℤ) + 3) ∧
        (∀ i, v i < 2 ^ (q.length + 1))

/-- Ghost placement of the three moving heads, leaving all fifteen other heads literal. -/
def rewindHeads (h : Track → ℤ) (r o v : ℤ) : Track → ℤ :=
  fun t => if t = (0, false) then r else if t = (7, false) then o
    else if t = (7, true) then v else h t

/-- A prefix of the coupled rewind preserves every cell and has at most one-cell skew. -/
def RewindFrame (m : Track → ℤ → Bool) (h : Track → ℤ) (B : ℕ)
    (c : Configuration) : Prop :=
  ∃ r o v : ℤ, 0 ≤ r ∧ r ≤ o ∧ o ≤ v ∧ v ≤ r + 1 ∧ v ≤ B ∧
    c.head = rewindHeads h r o v ∧ c.cell = m

/-- The paid coupled rewind terminates without inspecting the parked source companion.
Its frame covers all intermediate reads and each of the three separate left moves. -/
theorem coupled_source_rewind (m : Track → ℤ → Bool) (h : Track → ℤ) (W B k : ℕ)
    (hhome : m (7, false) 0 = false ∧ m (7, true) 0 = true)
    (hmarks : ∀ j : ℕ, 0 < j → j ≤ W →
      m (7, false) j = true ∧ m (7, true) j = true)
    (hk : k ≤ W) (hB : k ≤ B) :
    run ⟨.sourceRewind 0, rewindHeads h k k k, m⟩ (5 * k + 2) =
        ⟨.pad 0 0, rewindHeads h 0 0 0, m⟩ ∧
      ∀ n ≤ 5 * k + 2,
        RewindFrame m h B (run ⟨.sourceRewind 0, rewindHeads h k k k, m⟩ n) := by
  have configExt {a b : Configuration} (hc : a.control=b.control)
      (hh : a.head=b.head) (hm : a.cell=b.cell) : a=b := by
    cases a
    cases b
    cases hc
    cases hh
    cases hm
    rfl
  let cfg (c : Control) (r o v : ℤ) : Configuration := ⟨c, rewindHeads h r o v, m⟩
  have home : run (cfg (.sourceRewind 0) 0 0 0) 2 = cfg (.pad 0 0) 0 0 0 := by
    simp [run, Function.iterate_succ_apply, cfg, step, program, rewindHeads, hhome.1, hhome.2]
  have cycle (j : ℕ) (hj : j + 1 ≤ W) :
      run (cfg (.sourceRewind 0) (j + 1) (j + 1) (j + 1)) 5 =
        cfg (.sourceRewind 0) j j j := by
    obtain ⟨ho, hv⟩ := hmarks (j + 1) (by omega) hj
    simp only [Nat.cast_add, Nat.cast_one] at ho hv
    simp only [run, show 5 = 1 + 1 + 1 + 1 + 1 from rfl,
      Function.iterate_succ_apply, Function.iterate_zero_apply]
    apply configExt <;>
      simp [cfg, step, program, rewindHeads, ho, hv, Function.update_apply]
    funext t
    simp only [Function.update_apply, rewindHeads]
    split_ifs <;> simp_all
  have small (j : ℕ) (hj : j + 1 ≤ W) (hb : j + 1 ≤ B) :
      ∀ n ≤ 5, RewindFrame m h B
        (run (cfg (.sourceRewind 0) (j + 1) (j + 1) (j + 1)) n) := by
    obtain ⟨ho, hv⟩ := hmarks (j + 1) (by omega) hj
    simp only [Nat.cast_add, Nat.cast_one] at ho hv
    intro n hn
    interval_cases n
    · refine ⟨j+1, j+1, j+1, by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩ <;>
        simp [run, Function.iterate_succ_apply, cfg, step, program, ho, hv,
          rewindHeads, Function.update_apply]
      all_goals
        funext t
        simp only [Function.update_apply, rewindHeads]
        split_ifs <;> simp_all
    · refine ⟨j+1, j+1, j+1, by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩ <;>
        simp [run, Function.iterate_succ_apply, cfg, step, program, ho, hv,
          rewindHeads, Function.update_apply]
      all_goals
        funext t
        simp only [Function.update_apply, rewindHeads]
        split_ifs <;> simp_all
    · refine ⟨j+1, j+1, j+1, by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩ <;>
        simp [run, Function.iterate_succ_apply, cfg, step, program, ho, hv,
          rewindHeads, Function.update_apply]
      all_goals
        funext t
        simp only [Function.update_apply, rewindHeads]
        split_ifs <;> simp_all
    · refine ⟨j, j+1, j+1, by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩ <;>
        simp [run, Function.iterate_succ_apply, cfg, step, program, ho, hv,
          rewindHeads, Function.update_apply]
      all_goals
        funext t
        simp only [Function.update_apply, rewindHeads]
        split_ifs <;> simp_all
    · refine ⟨j, j, j+1, by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩ <;>
        simp [run, Function.iterate_succ_apply, cfg, step, program, ho, hv,
          rewindHeads, Function.update_apply]
      all_goals
        funext t
        simp only [Function.update_apply, rewindHeads]
        split_ifs <;> simp_all
    · refine ⟨j, j, j, by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩ <;>
        simp [run, Function.iterate_succ_apply, cfg, step, program, ho, hv,
          rewindHeads, Function.update_apply]
      all_goals
        funext t
        simp only [Function.update_apply, rewindHeads]
        split_ifs <;> simp_all
  induction k with
  | zero =>
    constructor
    · exact home
    · intro n hn
      interval_cases n <;>
        refine ⟨0, 0, 0, by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩ <;>
        simp [run, Function.iterate_succ_apply, step, program, rewindHeads,
          hhome.1, hhome.2]
  | succ j ih =>
    obtain ⟨endRun, prefixes⟩ := ih (by omega) (by omega)
    have hc := cycle j hk
    constructor
    · have ht : 5 * (j + 1) + 2 = (5 * j + 2) + 5 := by omega
      rw [ht]
      change run (run (cfg (.sourceRewind 0) (j + 1) (j + 1) (j + 1)) 5)
        (5 * j + 2) = _
      rw [hc]
      exact endRun
    · intro n hn
      by_cases hn5 : n ≤ 5
      · exact small j hk hB n hn5
      · have heq : n = (n - 5) + 5 := by omega
        rw [heq]
        change RewindFrame m h B
          (run (run (cfg (.sourceRewind 0) (j + 1) (j + 1) (j + 1)) 5) (n - 5))
        rw [hc]
        exact prefixes (n - 5) (by omega)

end D5.S0.Computability.Coding.PhysicalSixParser
