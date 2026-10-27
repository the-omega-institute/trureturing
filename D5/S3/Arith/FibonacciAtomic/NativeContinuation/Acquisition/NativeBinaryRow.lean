/- GID: D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow
   mirror-E: none(waiver:unbounded-symbolic-execution)
   anchors: []
   utility: none
   digest: A finite binary program computes an original restricted suffix row. -/


import D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeSuffixAcquisition
import D5.S0.Computability.BinaryMachine.StackWords
import D5.S0.Computability.BinaryMachine.StackCompile
import D5.S0.Computability.PhysicalDivider.WordArithmetic
import Mathlib.Data.List.Sublists

/-! Two simultaneous carry scans implement the original five-mode backward row.
The five input permission bits precede interleaved little-endian child counts.
Three final columns drain both carries, including on empty and zero inputs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false


namespace D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow

open LiteralWindowEnd (Window first last)
open NativeSuffixAcquisition (Row entry advance modes)
open Complexity StackProgram StackWords
open Lax51Proofs.RamToTM (bitsValue fixedBits)

abbrev Column := Bool × Bool
abbrev Carry := Fin 5 × Fin 5

def serialize (xs : List Column) : List Bool := xs.flatMap (fun p => [p.1, p.2])

def parse : List Bool → List Column
  | x :: y :: bs => (x, y) :: parse bs
  | _ => []

def value (xs : List Column) : Row := (bitsValue (xs.map Prod.fst), bitsValue (xs.map Prod.snd))

def decode (bs : List Bool) : Row := value (parse bs)

def input (a : Finset Window) (xs : List Column) : List Bool :=
  modes.map (fun b => decide (b ∈ a)) ++ serialize xs

theorem serialize_length (xs : List Column) : (serialize xs).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons p xs ih => simp only [serialize, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at *; omega

theorem parse_serialize (xs : List Column) : parse (serialize xs) = xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih => simpa [serialize, parse] using congrArg (List.cons p) ih

private theorem bit_bound (a : Finset Window) (p : Column) (s : Bool) :
    entry (advance a (p.1.toNat, p.2.toNat)) s ≤ 5 := by
  have hterm (b : Window) : entry (p.1.toNat, p.2.toNat) (first b) ≤ 1 := by
    cases h : first b <;> simp [entry] <;> exact Bool.toNat_le _
  have hsum : (∑ b ∈ a, if ¬ (s = true ∧ last b = true) then
      entry (p.1.toNat, p.2.toNat) (first b) else 0) ≤ a.card := by
    calc
      _ ≤ ∑ _b ∈ a, 1 := Finset.sum_le_sum (fun b _ => by split <;> simp_all [hterm])
      _ = a.card := by simp
  have hcard : a.card ≤ 5 := by
    have := Finset.card_le_card (Finset.subset_univ a)
    have hu : (Finset.univ : Finset Window).card = 5 := by decide
    omega
  cases s <;> exact hsum.trans hcard

private def digit (a : Finset Window) (p : Column) (c : Fin 5) (s : Bool) : ℕ :=
  entry (advance a (p.1.toNat, p.2.toNat)) s + c.val

private def half (c : Fin 5) : Fin 5 := ⟨c.val / 2, by have := c.isLt; omega⟩

def round (a : Finset Window) (c : Carry) (p : Column) : Column × Carry :=
  ((Nat.bodd (digit a p c.1 false), Nat.bodd (digit a p c.2 true)),
   (⟨digit a p c.1 false / 2, by
      have := bit_bound a p false; have := c.1.isLt; simp only [digit]; omega⟩,
    ⟨digit a p c.2 true / 2, by
      have := bit_bound a p true; have := c.2.isLt; simp only [digit]; omega⟩))

def drain : ℕ → Carry → List Column
  | 0, _ => []
  | n + 1, c => (Nat.bodd c.1.val, Nat.bodd c.2.val) :: drain n (half c.1, half c.2)

def columns (a : Finset Window) : Carry → List Column → List Column
  | c, [] => drain 3 c
  | c, p :: xs => let q := round a c p; q.1 :: columns a q.2 xs

private theorem drain_bits (n : ℕ) (c : Carry) :
    (drain n c).map Prod.fst = fixedBits n c.1.val ∧
    (drain n c).map Prod.snd = fixedBits n c.2.val := by
  induction n generalizing c with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      obtain ⟨h0, h1⟩ := ih (half c.1, half c.2)
      constructor
      · simpa only [drain, List.map_cons, fixedBits, List.cons.injEq, true_and, half, Nat.div2_val] using h0
      · simpa only [drain, List.map_cons, fixedBits, List.cons.injEq, true_and, half, Nat.div2_val] using h1

theorem columns_length (a : Finset Window) (c : Carry) (xs : List Column) :
    (columns a c xs).length = xs.length + 3 := by
  induction xs generalizing c with
  | nil => rfl
  | cons p xs ih => simpa [columns] using congrArg Nat.succ (ih (round a c p).2)

private theorem advance_split (a : Finset Window) (r d : Row) (s : Bool) :
    entry (advance a (r.1 + 2 * d.1, r.2 + 2 * d.2)) s =
      entry (advance a r) s + 2 * entry (advance a d) s := by
  cases s <;> simp only [advance, entry, Bool.false_eq_true, false_and,
    not_false_eq_true, Bool.true_eq, true_and, ↓reduceIte]
  all_goals
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    cases h : first b <;> simp only [h, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
    all_goals split_ifs <;> omega

private theorem value_cons (p : Column) (xs : List Column) :
    value (p :: xs) =
      (p.1.toNat + 2 * (value xs).1, p.2.toNat + 2 * (value xs).2) := by
  simp [value, bitsValue, Nat.bit_val, Nat.add_comm]

private theorem columns_value (a : Finset Window) (c : Carry) (xs : List Column) :
    value (columns a c xs) =
      ((advance a (value xs)).1 + c.1.val, (advance a (value xs)).2 + c.2.val) := by
  induction xs generalizing c with
  | nil =>
      obtain ⟨h0, h1⟩ := drain_bits 3 c
      have hc0 : c.1.val < 8 := by have := c.1.isLt; omega
      have hc1 : c.2.val < 8 := by have := c.2.isLt; omega
      simp only [columns, value, h0, h1, Lax51Proofs.RamToTM.bitsValue_fixedBits]
      simp [Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1, advance, entry, bitsValue]
  | cons p xs ih =>
      have h0 := advance_split a (p.1.toNat, p.2.toNat) (value xs) false
      have h1 := advance_split a (p.1.toNat, p.2.toNat) (value xs) true
      have hd0 := Nat.bit_bodd_div2 (digit a p c.1 false)
      have hd1 := Nat.bit_bodd_div2 (digit a p c.2 true)
      rw [columns, value_cons, ih, value_cons]
      apply Prod.ext
      all_goals
        simp only [round, digit, entry, Nat.bit_val, Nat.div2_val,
          Bool.false_eq_true, Bool.true_eq, ↓reduceIte] at *
        omega

/-- Each label contains only a permission mask, two carries below five, and finitely many bits. -/
inductive Control where
  | load (n : Fin 6) (a : Finset Window)
  | scan (a : Finset Window) (c : Carry)
  | second (a : Finset Window) (c : Carry) (x : Bool)
  | put0 (a : Finset Window) (c : Carry) (p : Column)
  | put1 (a : Finset Window) (c : Carry) (p : Column)
  | flush0 (n : Fin 4) (c : Carry)
  | flush1 (n : Fin 4) (c : Carry)
  | fail
  deriving DecidableEq

def scanProgram : Program 1 Control where
  start := .load 0 ∅
  code q := match q with
    | .load n a => if h : n.val < 5 then
        .pop 0 .fail (.load ⟨n.val + 1, by omega⟩ a)
          (.load ⟨n.val + 1, by omega⟩ (insert (modes[n.val]'(by simp [modes]; omega)) a))
      else .goto (.scan a (0, 0))
    | .scan a c => .pop 0 (.flush0 3 c) (.second a c false) (.second a c true)
    | .second a c x => .pop 0 .fail (.put0 a c (x, false)) (.put0 a c (x, true))
    | .put0 a c p => .push 1 (round a c p).1.1 (.put1 a c p)
    | .put1 a c p => .push 1 (round a c p).1.2 (.scan a (round a c p).2)
    | .flush0 n c => if h : n.val = 0 then .halt true
      else .push 1 (Nat.bodd c.1.val) (.flush1 n c)
    | .flush1 n c => .push 1 (Nat.bodd c.2.val)
        (.flush0 ⟨n.val - 1, by have := n.isLt; omega⟩ (half c.1, half c.2))
    | .fail => .halt false

/-- The final physical reversal restores the interleaved little-endian output. -/
def program := seq scanProgram (transfer (k := 1) 1 0)

private def masks : List (Finset Window) := modes.sublists.map List.toFinset

private theorem mem_masks (a : Finset Window) : a ∈ masks := by
  have h : (modes.filter (fun b => decide (b ∈ a))).toFinset = a := by
    ext b
    cases b <;> simp [modes]
  apply List.mem_map.mpr
  exact ⟨_, List.mem_sublists.mpr List.filter_sublist, h⟩

private def carries : List Carry := (List.finRange 5).flatMap fun a =>
  (List.finRange 5).map fun b => (a, b)

private theorem mem_carries (c : Carry) : c ∈ carries := by
  obtain ⟨a, b⟩ := c
  simp [carries]

private def pairs : List Column := [(false, false), (false, true), (true, false), (true, true)]

private theorem mem_pairs (p : Column) : p ∈ pairs := by
  obtain ⟨x, y⟩ := p
  cases x <;> cases y <;> simp [pairs]

@[irreducible] private def labels : List Control :=
  ((List.finRange 6).flatMap fun n => masks.map (Control.load n)) ++
  (masks.flatMap fun a => carries.map (Control.scan a)) ++
  (masks.flatMap fun a => carries.flatMap fun c => [Control.second a c false, .second a c true]) ++
  (masks.flatMap fun a => carries.flatMap fun c => pairs.map (Control.put0 a c)) ++
  (masks.flatMap fun a => carries.flatMap fun c => pairs.map (Control.put1 a c)) ++
  ((List.finRange 4).flatMap fun n => carries.map (Control.flush0 n)) ++
  ((List.finRange 4).flatMap fun n => carries.map (Control.flush1 n)) ++ [.fail]

private theorem mem_labels (q : Control) : q ∈ labels := by
  cases q with
  | load n a => simp [labels, mem_masks]
  | scan a c => simp [labels, mem_masks, mem_carries]
  | second a c x => cases x <;> simp [labels, mem_masks, mem_carries]
  | put0 a c p => simp [labels, mem_masks, mem_carries, mem_pairs]
  | put1 a c p => simp [labels, mem_masks, mem_carries, mem_pairs]
  | flush0 n c => simp [labels, mem_carries]
  | flush1 n c => simp [labels, mem_carries]
  | fail => simp [labels]

/-- A computable finite instruction table, with one harmless padding label. -/
def controlEncoding : Encoding Control where
  states := labels.length
  encode q := ⟨labels.idxOf q, by
    exact Nat.lt_succ_of_le (List.idxOf_le_length (l := labels) (a := q))⟩
  decode q := (labels[q.val]?).getD .fail
  decode_encode q := by
    have h : q ∈ labels := mem_labels q
    simp only [List.getElem?_idxOf h, Option.getD_some]

def encoding := Encoding.sum controlEncoding (Encoding.fin 3)

def stackMachine : StackMachine.Machine := StackProgram.compile program encoding

def binaryMachine : Complexity.Machine := StackCompile.compile stackMachine

def registers (src dst : List Bool) : StackMachine.Registers 1 :=
  fun j => if j = 0 then src else dst

private theorem set0 (src dst bs : List Bool) :
    StackMachine.set (registers src dst) 0 bs = registers bs dst := by
  funext j; fin_cases j <;> simp [StackMachine.set, registers]

private theorem set1 (src dst bs : List Bool) :
    StackMachine.set (registers src dst) 1 bs = registers src bs := by
  funext j; fin_cases j <;> simp [StackMachine.set, registers]

private theorem exec_drain (n : ℕ) (hn : n < 4) (c : Carry) (acc : List Bool) :
    Exec scanProgram (.flush0 ⟨n, hn⟩ c) (registers [] acc) (2 * n + 1)
      (true, registers [] ((serialize (drain n c)).reverse ++ acc)) := by
  induction n generalizing c acc with
  | zero => exact .halt rfl
  | succ n ih =>
      have h := ih (by omega) (half c.1, half c.2)
        (Nat.bodd c.2.val :: Nat.bodd c.1.val :: acc)
      have hh := Exec.next (p := scanProgram)
        (q := .flush0 ⟨n + 1, hn⟩ c)
        (q' := .flush1 ⟨n + 1, hn⟩ c)
        (r := registers [] acc) (r' := registers [] (Nat.bodd c.1.val :: acc))
        (by simp [StackProgram.step, scanProgram, set1, registers])
        (Exec.next (by simp [StackProgram.step, scanProgram, set1, registers]) h)
      convert hh using 1 <;>
        simp [drain, serialize, List.reverse_append, List.append_assoc] <;> omega

private theorem exec_scan (a : Finset Window) (c : Carry) (xs : List Column)
    (acc : List Bool) :
    Exec scanProgram (.scan a c) (registers (serialize xs) acc) (4 * xs.length + 8)
      (true, registers [] ((serialize (columns a c xs)).reverse ++ acc)) := by
  induction xs generalizing c acc with
  | nil =>
      exact .next (by simp [StackProgram.step, scanProgram, serialize, registers, set0,
        StackMachine.branch]) (exec_drain 3 (by decide) c acc)
  | cons p xs ih =>
      have h := ih (round a c p).2 ((round a c p).1.2 :: (round a c p).1.1 :: acc)
      have hs0 : StackProgram.step scanProgram (.scan a c)
          (registers (serialize (p :: xs)) acc) =
          .inr (.second a c p.1, registers (p.2 :: serialize xs) acc) := by
        rcases p with ⟨x, y⟩
        cases x <;> simp [StackProgram.step, scanProgram, serialize, registers,
          StackMachine.branch, set0]
      have hs1 : StackProgram.step scanProgram (.second a c p.1)
          (registers (p.2 :: serialize xs) acc) =
          .inr (.put0 a c p, registers (serialize xs) acc) := by
        cases p with
        | mk x y => cases y <;> simp [StackProgram.step, scanProgram, registers,
            StackMachine.branch, set0]
      have hh := Exec.next hs0 (Exec.next hs1
        (Exec.next (q' := .put1 a c p)
          (r' := registers (serialize xs) ((round a c p).1.1 :: acc))
          (by simp [StackProgram.step, scanProgram, set1, registers])
          (Exec.next (by simp [StackProgram.step, scanProgram, set1, registers]) h)))
      convert hh using 1 <;>
        simp [columns, serialize, List.reverse_append, List.append_assoc] <;> omega

def insertBit (a : Finset Window) (b : Window) (v : Bool) : Finset Window :=
  if v then insert b a else a

private theorem mem_insertBit (a : Finset Window) (b w : Window) (v : Bool) :
    w ∈ insertBit a b v ↔ (w = b ∧ v = true) ∨ w ∈ a := by
  cases v <;> simp [insertBit]

private theorem exec_load_next (n : ℕ) (hn : n < 5) (a : Finset Window)
    (v : Bool) (src acc : List Bool) (t : ℕ) (out : Bool × StackMachine.Registers 1)
    (h : Exec scanProgram
      (.load ⟨n + 1, by omega⟩ (insertBit a (modes[n]'(by simp [modes]; omega)) v))
      (registers src acc) t out) :
    Exec scanProgram (.load ⟨n, by omega⟩ a) (registers (v :: src) acc) (t + 1) out := by
  apply Exec.next (rest := h)
  cases v <;> simp [StackProgram.step, scanProgram, hn, insertBit,
    registers, StackMachine.branch, set0]

private theorem exec_input (a : Finset Window) (xs : List Column) :
    Exec scanProgram scanProgram.start (registers (input a xs) []) (4 * xs.length + 14)
      (true, registers [] (serialize (columns a (0, 0) xs)).reverse) := by
  let a1 := insertBit ∅ Window.zero (decide (Window.zero ∈ a))
  let a2 := insertBit a1 Window.low (decide (Window.low ∈ a))
  let a3 := insertBit a2 Window.middle (decide (Window.middle ∈ a))
  let a4 := insertBit a3 Window.high (decide (Window.high ∈ a))
  let a5 := insertBit a4 Window.ends (decide (Window.ends ∈ a))
  have ha : a5 = a := by
    ext b
    cases b <;> simp [a5, a4, a3, a2, a1, mem_insertBit]
  have hs := exec_scan a (0, 0) xs []
  have h5 : Exec scanProgram (.load 5 a5) (registers (serialize xs) [])
      (4 * xs.length + 9)
      (true, registers [] (serialize (columns a (0, 0) xs)).reverse) := by
    rw [ha]
    exact .next rfl (by simpa using hs)
  have h4 := exec_load_next 4 (by decide) a4 (decide (Window.ends ∈ a)) _ _ _ _ h5
  have h3 := exec_load_next 3 (by decide) a3 (decide (Window.high ∈ a)) _ _ _ _ h4
  have h2 := exec_load_next 2 (by decide) a2 (decide (Window.middle ∈ a)) _ _ _ _ h3
  have h1 := exec_load_next 1 (by decide) a1 (decide (Window.low ∈ a)) _ _ _ _ h2
  have h0 := exec_load_next 0 (by decide) ∅ (decide (Window.zero ∈ a)) _ _ _ _ h1
  convert h0 using 1 <;> simp [input, modes, scanProgram] <;> omega

theorem exec_program (a : Finset Window) (xs : List Column) :
    Exec program program.start (registers (input a xs) []) (8 * xs.length + 28)
      (true, registers (serialize (columns a (0, 0) xs)) []) := by
  let ys := serialize (columns a (0, 0) xs)
  have ht := exec_transfer (k := 1) 1 0 (by decide) (registers [] ys.reverse)
  have ht' : Exec (transfer (k := 1) 1 0) 0 (registers [] ys.reverse)
      (4 * (xs.length + 3) + 2) (true, registers ys []) := by
    simpa [registers, set1, set0, ys, serialize_length, columns_length, ← Nat.mul_assoc] using ht
  have h := exec_seq scanProgram (transfer (k := 1) 1 0) (exec_input a xs) ht'
  convert h using 1 <;> first | rfl | omega

/-- The same fixed binary program reads an original permission mask and a child row,
produces both exact guarded row sums, and pays for input initialization and physical output. -/
theorem native_binary_row (a : Finset Window) (xs : List Column) :
    (input a xs).length = 5 + 2 * xs.length ∧
    (serialize (columns a (0, 0) xs)).length = 2 * (xs.length + 3) ∧
    decode (serialize (columns a (0, 0) xs)) = advance a (value xs) ∧
    ∃ time tape, time ≤ 16384 * (xs.length + 1) ^ 2 ∧
      Complexity.runInput binaryMachine time (input a xs) = some (true, tape) ∧
      tape.output = serialize (columns a (0, 0) xs) := by
  have he := StackProgram.compile_exec encoding (exec_program a xs)
  have hr : StackMachine.runInput stackMachine (8 * xs.length + 28) (input a xs) =
      some (true, registers (serialize (columns a (0, 0) xs)) []) := by
    have hi : StackMachine.initial stackMachine (input a xs) =
        ⟨encoding.encode program.start, registers (input a xs) []⟩ := rfl
    change StackMachine.run stackMachine _ (StackMachine.initial stackMachine _) = _
    rw [hi]
    exact he
  obtain ⟨time, tape, ht, hrun, hout⟩ := StackCompile.simulate stackMachine
    (8 * xs.length + 28) (input a xs) _ hr
  have hlen : (input a xs).length = 5 + 2 * xs.length := by
    simp only [input, List.length_append, List.length_map, modes, List.length_cons,
      List.length_nil, serialize_length] <;> omega
  refine ⟨hlen, by rw [serialize_length, columns_length], ?_, time, tape, ?_, hrun, hout⟩
  · simp only [decode, parse_serialize, columns_value]
    simp
  · apply ht.trans
    rw [hlen]
    simp only [StackCompile.budget, StackInit.initBudget, StackSimulation.instructionBudget,
      stackMachine, StackProgram.compile]
    nlinarith

end D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow
