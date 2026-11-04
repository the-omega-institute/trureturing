/- GID: D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable
   mirror-E: none(waiver:unbounded-symbolic-execution)
   anchors: []
   utility: none
   digest: A fixed binary program initializes and retains every original suffix count. -/

import D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow
import D5.S0.Computability.BinaryMachine.StackFrame
import D5.S0.Computability.BinaryMachine.StackControl

/-! Physical backward-table construction using the original native row subroutine. -/

set_option maxRecDepth 10000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryTable

open LiteralWindowEnd (Window)
open NativeSuffixAcquisition (modes counts table entry completions)
open NativeBinaryRow (Column serialize columns value)
open Complexity StackProgram StackWords
open StackMachine (Registers set branch)

/-- The actual five membership bits, including separately counted equal-successor modes. -/
def mask (a : Finset Window) : List Bool := modes.map (fun b => decide (b ∈ a))

def terminalColumns (B : Finset Bool) : List Column :=
  [(decide (false ∈ B), decide (true ∈ B))]

def row (B : Finset Bool) : List (Finset Window) → List Column
  | [] => terminalColumns B
  | a :: as => columns a (0, 0) (row B as)

def rows (B : Finset Bool) : List (Finset Window) → List (List Column)
  | [] => [row B []]
  | a :: as => row B (a :: as) :: rows B as

/-- A row header is false; each following high-to-low data bit has a true marker. -/
def pack (bs : List Bool) : List Bool := false :: bs.reverse.flatMap (fun b => [true, b])

def records (B : Finset Bool) (as : List (Finset Window)) : List Bool :=
  (rows B as).flatMap (fun xs => pack (serialize xs))

/-- Two terminal bits followed by the explicit permission masks in backward processing order. -/
def input (B : Finset Bool) (as : List (Finset Window)) : List Bool :=
  [decide (false ∈ B), decide (true ∈ B)] ++ as.reverse.flatMap mask

def regs (src cur saved scratch history : List Bool) : Registers 6 :=
  fun j => if j = 0 then cur else if j = 1 then src else if j = 4 then saved
    else if j = 5 then scratch else if j = 6 then history else []

private theorem regs_set0 (src cur saved scratch history bs : List Bool) :
    set (regs src cur saved scratch history) 0 bs = regs src bs saved scratch history := by
  funext j; fin_cases j <;> simp [StackMachine.set, regs]

private theorem regs_set1 (src cur saved scratch history bs : List Bool) :
    set (regs src cur saved scratch history) 1 bs = regs bs cur saved scratch history := by
  funext j; fin_cases j <;> simp [StackMachine.set, regs]

private theorem regs_set4 (src cur saved scratch history bs : List Bool) :
    set (regs src cur saved scratch history) 4 bs = regs src cur bs scratch history := by
  funext j; fin_cases j <;> simp [StackMachine.set, regs]

private theorem regs_set5 (src cur saved scratch history bs : List Bool) :
    set (regs src cur saved scratch history) 5 bs = regs src cur saved bs history := by
  funext j; fin_cases j <;> simp [StackMachine.set, regs]

private theorem regs_set6 (src cur saved scratch history bs : List Bool) :
    set (regs src cur saved scratch history) 6 bs = regs src cur saved scratch bs := by
  funext j; fin_cases j <;> simp [StackMachine.set, regs]

/-- Physically copy the current row into the table, with explicit row and bit markers. -/
def saveScan : Program 6 (Fin 8) where
  start := 0
  code q := if q = 0 then .pop 0 1 2 3
    else if q = 1 then .push 4 false 7
    else if q = 2 then .push 5 false 4
    else if q = 3 then .push 5 true 5
    else if q = 4 then .push 4 false 6
    else if q = 5 then .push 4 true 6
    else if q = 6 then .push 4 true 0
    else .halt true

def save := seq saveScan (transfer (k := 6) 5 0)
def saveEncoding := (Encoding.fin 7).sum (Encoding.fin 3)

private theorem exec_saveScan (xs src saved scratch history : List Bool) :
    Exec saveScan 0 (regs src xs saved scratch history) (4 * xs.length + 3)
      (true, regs src [] (pack xs ++ saved) (xs.reverse ++ scratch) history) := by
  induction xs generalizing saved scratch with
  | nil =>
      apply Exec.next (q' := 1) (r' := regs src [] saved scratch history)
      · simp [StackProgram.step, saveScan, regs, branch, regs_set0]
      apply Exec.next (q' := 7) (r' := regs src [] (false :: saved) scratch history)
      · simp [StackProgram.step, saveScan, regs, regs_set4]
      exact .halt (by simp [StackProgram.step, saveScan, pack])
  | cons b xs ih =>
      have ht := ih (true :: b :: saved) (b :: scratch)
      have h0 : StackProgram.step saveScan 0 (regs src (b :: xs) saved scratch history) =
          .inr ((if b then 3 else 2), regs src xs saved scratch history) := by
        cases b <;> simp [StackProgram.step, saveScan, regs, branch, regs_set0]
      have h1 : StackProgram.step saveScan (if b then 3 else 2)
          (regs src xs saved scratch history) =
          .inr ((if b then 5 else 4), regs src xs saved (b :: scratch) history) := by
        cases b <;> simp [StackProgram.step, saveScan, regs, regs_set5]
      have h2 : StackProgram.step saveScan (if b then 5 else 4)
          (regs src xs saved (b :: scratch) history) =
          .inr (6, regs src xs (b :: saved) (b :: scratch) history) := by
        cases b <;> simp [StackProgram.step, saveScan, regs, regs_set4]
      have hh := Exec.next h0 (Exec.next h1 (Exec.next h2
        (Exec.next (by simp [StackProgram.step, saveScan, regs, regs_set4]) ht)))
      convert hh using 1
      simp [pack, List.reverse_cons, List.flatMap_append, List.append_assoc]

private theorem exec_save (src xs saved history : List Bool) :
    Exec save save.start (regs src xs saved [] history) (6 * xs.length + 5)
      (true, regs src xs (pack xs ++ saved) [] history) := by
  have h0 := exec_saveScan xs src saved [] history
  have h1 := exec_transfer (k := 6) 5 0 (by decide)
    (regs src [] (pack xs ++ saved) xs.reverse history)
  have h1' : Exec (transfer (k := 6) 5 0) 0
      (regs src [] (pack xs ++ saved) xs.reverse history) (2 * xs.length + 2)
      (true, regs src xs (pack xs ++ saved) [] history) := by
    simpa [regs, regs_set5, regs_set0] using h1
  have hh := exec_seq saveScan (transfer (k := 6) 5 0) (by simpa using h0) h1'
  convert hh using 1 <;> first | rfl | omega

/-- The row subroutine uses just its original two registers, inside the table frame. -/
def rowRegister (j : Fin 2) : Fin 7 := if j = 0 then 0 else 2

def advanceProgram := StackFrame.lift rowRegister NativeBinaryRow.program

private theorem exec_advance (a : Finset Window) (xs : List Column)
    (src saved history : List Bool) :
    Exec advanceProgram advanceProgram.start
      (regs src (NativeBinaryRow.input a xs) saved [] history) (8 * xs.length + 28)
      (true, regs src (serialize (columns a (0, 0) xs)) saved [] history) := by
  have hinj : Function.Injective rowRegister := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [rowRegister]
  have hp : StackFrame.pull rowRegister
      (regs src (NativeBinaryRow.input a xs) saved [] history) =
      NativeBinaryRow.registers (NativeBinaryRow.input a xs) [] := by
    funext j; fin_cases j <;> simp [StackFrame.pull, rowRegister, regs, NativeBinaryRow.registers]
  obtain ⟨out, he, ho, hf⟩ := StackFrame.exec_lift rowRegister hinj NativeBinaryRow.program
    (NativeBinaryRow.exec_program a xs) _ hp
  have hout : out = regs src (serialize (columns a (0, 0) xs)) saved [] history := by
    funext j
    by_cases h0 : j = 0
    · subst j
      have h := congrFun ho 0
      simpa [StackFrame.pull, rowRegister, NativeBinaryRow.registers, regs] using h
    · by_cases h2 : j = 2
      · subst j
        have h := congrFun ho 1
        simpa [StackFrame.pull, rowRegister, NativeBinaryRow.registers, regs] using h
      · rw [hf j]
        · simp [regs, h0]
        · intro i; fin_cases i <;> simpa [rowRegister] using (show j ≠ _ from by assumption)
  simpa only [advanceProgram, StackFrame.lift, hout] using he

private def putLabel (n : ℕ) (hn : n < 6) (a : Finset Window) : NativeBinaryRow.Control :=
  .scan a (⟨n % 5, Nat.mod_lt _ (by decide)⟩, ⟨n / 5, by omega⟩)

/-- The existing finite row labels also encode the permission loader. -/
def loadMask : Program 6 NativeBinaryRow.Control where
  start := .load 0 ∅
  code q := match q with
    | .load n a => if h : n.val < 5 then
        .pop 1 .fail (.second a (⟨n.val, h⟩, 0) false) (.second a (⟨n.val, h⟩, 0) true)
      else .goto (putLabel 5 (by decide) a)
    | .second a c b => .push 6 b
        (.load ⟨c.1.val + 1, by have := c.1.isLt; omega⟩
          (NativeBinaryRow.insertBit a (modes[c.1.val]'(by simpa [modes] using c.1.isLt)) b))
    | .scan a c =>
        let n := c.1.val + 5 * c.2.val
        if h : n < 6 then
          if hz : n = 0 then .halt true
          else .push 0 (decide ((modes[n - 1]'(by simp [modes]; omega)) ∈ a))
            (putLabel (n - 1) (by omega) a)
        else .halt false
    | _ => .halt false

def body := seq loadMask (seq advanceProgram save)
def bodyEncoding := NativeBinaryRow.controlEncoding.sum (NativeBinaryRow.encoding.sum saveEncoding)

private theorem exec_put (n : ℕ) (hn : n < 6) (a : Finset Window)
    (src cur saved history : List Bool) :
    Exec loadMask (putLabel n hn a) (regs src cur saved [] history) (n + 1)
      (true, regs src ((mask a).take n ++ cur) saved [] history) := by
  induction n generalizing cur with
  | zero => exact .halt (by simp [StackProgram.step, loadMask, putLabel])
  | succ n ih =>
      have hn5 : n < 5 := by omega
      have hm : n < (mask a).length := by simp [mask, modes]; omega
      have ht := ih (by omega) ((mask a)[n] :: cur)
      apply Exec.next (q' := putLabel n (by omega) a)
        (r' := regs src ((mask a)[n] :: cur) saved [] history)
      · simp only [StackProgram.step, loadMask, putLabel, Nat.mod_add_div]
        simp [hn, regs, regs_set0, mask, List.getElem_map]
      · have hp := List.take_concat_get' (mask a) n hm
        have hlist : (mask a).take n ++ (mask a)[n] :: cur = (mask a).take (n + 1) ++ cur := by
          calc
            _ = ((mask a).take n ++ [(mask a)[n]]) ++ cur :=
              (List.append_assoc _ _ _).symm
            _ = _ := congrArg (fun bs : List Bool => bs ++ cur) hp
        simpa only [hlist] using ht

private theorem exec_load_next (n : ℕ) (hn : n < 5) (a : Finset Window)
    (v : Bool) (src cur saved history : List Bool) (t : ℕ)
    (out : Bool × Registers 6)
    (h : Exec loadMask
      (.load ⟨n + 1, by omega⟩
        (NativeBinaryRow.insertBit a (modes[n]'(by simp [modes]; omega)) v))
      (regs src cur saved [] (v :: history)) t out) :
    Exec loadMask (.load ⟨n, by omega⟩ a)
      (regs (v :: src) cur saved [] history) (t + 2) out := by
  apply Exec.next (q' := .second a (⟨n, hn⟩, 0) v)
    (r' := regs src cur saved [] history)
  · cases v <;> simp [StackProgram.step, loadMask, hn, regs, branch, regs_set1]
  apply Exec.next (rest := h)
  simp [StackProgram.step, loadMask, regs, regs_set6]

private theorem exec_load (a : Finset Window) (src cur saved history : List Bool) :
    Exec loadMask loadMask.start (regs (mask a ++ src) cur saved [] history) 17
      (true, regs src (mask a ++ cur) saved [] ((mask a).reverse ++ history)) := by
  let v0 := decide (Window.zero ∈ a)
  let v1 := decide (Window.low ∈ a)
  let v2 := decide (Window.middle ∈ a)
  let v3 := decide (Window.high ∈ a)
  let v4 := decide (Window.ends ∈ a)
  let a1 := NativeBinaryRow.insertBit ∅ Window.zero v0
  let a2 := NativeBinaryRow.insertBit a1 Window.low v1
  let a3 := NativeBinaryRow.insertBit a2 Window.middle v2
  let a4 := NativeBinaryRow.insertBit a3 Window.high v3
  let a5 := NativeBinaryRow.insertBit a4 Window.ends v4
  have ha : a5 = a := by
    ext b; cases b <;>
      simp [a5, a4, a3, a2, a1, v0, v1, v2, v3, v4, NativeBinaryRow.insertBit] <;>
      split_ifs <;> simp_all
  have hp := exec_put 5 (by decide) a src cur saved
    (v4 :: v3 :: v2 :: v1 :: v0 :: history)
  have h5 : Exec loadMask (.load 5 a5)
      (regs src cur saved [] (v4 :: v3 :: v2 :: v1 :: v0 :: history)) 7
      (true, regs src (mask a ++ cur) saved [] ((mask a).reverse ++ history)) := by
    rw [ha]
    apply Exec.next (q' := putLabel 5 (by decide) a)
      (r' := regs src cur saved [] (v4 :: v3 :: v2 :: v1 :: v0 :: history))
    · simp [StackProgram.step, loadMask]
    simpa [mask, modes, v0, v1, v2, v3, v4] using hp
  have h4 := exec_load_next 4 (by decide) a4 v4 _ _ _ _ _ _ h5
  have h3 := exec_load_next 3 (by decide) a3 v3 _ _ _ _ _ _ h4
  have h2 := exec_load_next 2 (by decide) a2 v2 _ _ _ _ _ _ h3
  have h1 := exec_load_next 1 (by decide) a1 v1 _ _ _ _ _ _ h2
  have h0 := exec_load_next 0 (by decide) ∅ v0 _ _ _ _ _ _ h1
  simpa [loadMask, mask, modes, v0, v1, v2, v3, v4] using h0

private theorem exec_load_empty (cur saved history : List Bool) :
    Exec loadMask loadMask.start (regs [] cur saved [] history) 2
      (false, regs [] cur saved [] history) := by
  apply Exec.next (q' := .fail) (r' := regs [] cur saved [] history)
  · simp [StackProgram.step, loadMask, regs, branch, regs_set1]
  exact .halt rfl

/-- All terminal bits are read from the physical input, including the empty-horizon case. -/
def initProgram : Program 6 (Fin 6 × (Bool × Bool)) where
  start := (0, false, false)
  code q := if q.1 = 0 then .pop 1 (5, false, false) (1, false, false) (1, true, false)
    else if q.1 = 1 then .pop 1 (5, false, false) (2, q.2.1, false) (2, q.2.1, true)
    else if q.1 = 2 then .push 0 q.2.2 (3, q.2.1, q.2.2)
    else if q.1 = 3 then .push 0 q.2.1 (4, q.2.1, q.2.2)
    else .halt (q.1 == 4)

def program := seq (StackControl.moveWord (k := 6) 0 1 5)
  (seq initProgram (seq save (seq (loop body) (StackControl.moveWord (k := 6) 4 0 5))))

def encoding := StackControl.moveEncoding.sum
  (((Encoding.fin 5).prod (Encoding.bool.prod Encoding.bool)).sum
    (saveEncoding.sum (bodyEncoding.sum StackControl.moveEncoding)))

def stackMachine := StackProgram.compile program encoding
def binaryMachine := StackCompile.compile stackMachine

private theorem row_length (B : Finset Bool) (as : List (Finset Window)) :
    (row B as).length = 1 + 3 * as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [row, NativeBinaryRow.columns_length, ih]; omega

theorem row_value (B : Finset Bool) (as : List (Finset Window)) :
    value (row B as) = counts B as := by
  induction as with
  | nil =>
      simp [row, terminalColumns, value, Lax51Proofs.RamToTM.bitsValue,
        NativeSuffixAcquisition.counts, table, NativeSuffixAcquisition.terminal,
        Nat.bit_val]
      split_ifs <;> simp_all
  | cons a as ih =>
      have h := (NativeBinaryRow.native_binary_row a (row B as)).2.2.1
      simpa [NativeBinaryRow.decode, NativeBinaryRow.parse_serialize, ih,
        row, NativeSuffixAcquisition.counts, table] using h

private theorem records_cons (B : Finset Bool) (a : Finset Window)
    (as : List (Finset Window)) :
    records B (a :: as) = pack (serialize (row B (a :: as))) ++ records B as := rfl

theorem pack_length (bs : List Bool) : (pack bs).length = 1 + 2 * bs.length := by
  simp [pack, List.length_flatMap, Nat.mul_comm, Nat.add_comm]

private theorem records_length (B : Finset Bool) (as : List (Finset Window)) :
    (records B as).length = (as.length + 1) * (6 * as.length + 5) := by
  induction as with
  | nil => simp [records, rows, pack_length, NativeBinaryRow.serialize_length, row_length]
  | cons a as ih =>
      rw [records_cons, List.length_append, pack_length, NativeBinaryRow.serialize_length,
        row_length, ih]
      simp only [List.length_cons]
      ring

private theorem mask_length (a : Finset Window) : (mask a).length = 5 := rfl

private theorem masks_length (as : List (Finset Window)) :
    (as.flatMap mask).length = 5 * as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, mask_length, ih]; omega

private theorem exec_body (a : Finset Window) (B : Finset Bool)
    (as : List (Finset Window)) (src history : List Bool) :
    Exec body body.start (regs (mask a ++ src) (serialize (row B as)) (records B as) [] history)
      (106 + 60 * as.length)
      (true, regs src (serialize (row B (a :: as))) (records B (a :: as)) []
        ((mask a).reverse ++ history)) := by
  have h0 := exec_load a src (serialize (row B as)) (records B as) history
  have h1 := exec_advance a (row B as) src (records B as) ((mask a).reverse ++ history)
  have h2 := exec_save src (serialize (columns a (0, 0) (row B as)))
    (records B as) ((mask a).reverse ++ history)
  have hh := exec_seq loadMask (seq advanceProgram save) h0
    (exec_seq advanceProgram save (by simpa [NativeBinaryRow.input, mask] using h1) h2)
  have hc : 17 + (8 * (row B as).length + 28 +
      (6 * (serialize (columns a (0, 0) (row B as))).length + 5)) = 106 + 60 * as.length := by
    rw [NativeBinaryRow.serialize_length, NativeBinaryRow.columns_length, row_length]
    ring
  rw [hc] at hh
  exact hh

private def loopCost (n k : ℕ) : ℕ := 2 + 76 * n + 60 * n * k + 30 * n * n

private theorem exec_iterations (pending suffix : List (Finset Window))
    (B : Finset Bool) (history : List Bool) :
    Exec (loop body) (loop body).start
      (regs (pending.flatMap mask) (serialize (row B suffix)) (records B suffix) [] history)
      (loopCost pending.length suffix.length)
      (true, regs [] (serialize (row B (pending.reverse ++ suffix)))
        (records B (pending.reverse ++ suffix)) [] ((pending.flatMap mask).reverse ++ history)) := by
  induction pending generalizing suffix history with
  | nil =>
      have hh := exec_seq_failure loadMask (seq advanceProgram save)
        (exec_load_empty (serialize (row B suffix)) (records B suffix) history)
      simpa [loopCost, body, loop, seq] using exec_loop_exit body hh
  | cons a pending ih =>
      have hb := exec_body a B suffix (pending.flatMap mask) history
      have ht := ih (a :: suffix) ((mask a).reverse ++ history)
      have hh := exec_loop_next body hb ht
      have hc : 106 + 60 * suffix.length + loopCost pending.length (a :: suffix).length =
          loopCost (a :: pending).length suffix.length := by
        simp only [List.length_cons, loopCost]
        ring
      rw [hc] at hh
      simpa only [StackProgram.loop, List.flatMap_cons, List.reverse_cons, List.reverse_append,
        List.append_assoc, List.singleton_append] using hh

private theorem exec_initProgram (B : Finset Bool) (src : List Bool) :
    Exec initProgram initProgram.start
      (regs ([decide (false ∈ B), decide (true ∈ B)] ++ src) [] [] [] []) 5
      (true, regs src (serialize (terminalColumns B)) [] [] []) := by
  generalize h0 : decide (false ∈ B) = b0
  generalize h1 : decide (true ∈ B) = b1
  apply Exec.next (q' := (1, b0, false)) (r' := regs (b1 :: src) [] [] [] [])
  · cases b0 <;> simp [StackProgram.step, initProgram, regs, branch, regs_set1]
  apply Exec.next (q' := (2, b0, b1)) (r' := regs src [] [] [] [])
  · cases b1 <;> simp [StackProgram.step, initProgram, regs, branch, regs_set1]
  apply Exec.next (q' := (3, b0, b1)) (r' := regs src [b1] [] [] [])
  · simp [StackProgram.step, initProgram, regs, regs_set0]
  apply Exec.next (q' := (4, b0, b1)) (r' := regs src [b0, b1] [] [] [])
  · simp [StackProgram.step, initProgram, regs, regs_set0]
  apply Exec.halt
  simp [StackProgram.step, initProgram, terminalColumns, serialize, h0, h1]

theorem exec_table (B : Finset Bool) (as : List (Finset Window)) :
    ∃ fuel out, fuel ≤ 256 * (as.length + 1) ^ 2 ∧
      Exec program program.start (regs [] (input B as) [] [] [])
        fuel (true, out) ∧ out 0 = records B as := by
  let n := as.length
  have hin : (input B as).length = 2 + 5 * n := by
    simp only [input, List.length_append, List.length_cons, List.length_nil,
      masks_length, List.length_reverse]
    omega
  have h0 := StackControl.exec_moveWord (k := 6) 0 1 5 (by decide) (by decide) (by decide)
    (regs [] (input B as) [] [] []) rfl
  have h0' : Exec (StackControl.moveWord (k := 6) 0 1 5) (StackControl.moveWord (k := 6) 0 1 5).start
      (regs [] (input B as) [] [] []) (4 * (input B as).length + 6)
      (true, regs (input B as) [] [] [] []) := by
    simpa [regs, regs_set0, regs_set1] using h0
  have h1 := exec_initProgram B (as.reverse.flatMap mask)
  have h2 := exec_save (as.reverse.flatMap mask) (serialize (terminalColumns B)) [] []
  have h3 := exec_iterations as.reverse [] B []
  have h4 := StackControl.exec_moveWord (k := 6) 4 0 5 (by decide) (by decide) (by decide)
    (regs [] (serialize (row B as)) (records B as) [] ((as.reverse.flatMap mask).reverse)) rfl
  have h4' : Exec (StackControl.moveWord (k := 6) 4 0 5) (StackControl.moveWord (k := 6) 4 0 5).start
      (regs [] (serialize (row B as)) (records B as) [] ((as.reverse.flatMap mask).reverse))
      ((serialize (row B as)).length + 4 * (records B as).length + 6)
      (true, regs [] (records B as) [] [] ((as.reverse.flatMap mask).reverse)) := by
    simpa [regs, regs_set4, regs_set0] using h4
  have hh := exec_seq _ _ h0' (exec_seq _ _ h1
    (exec_seq _ _ (by simpa [records, rows, row] using h2)
      (exec_seq _ _ (by simpa [records, rows, row] using h3) h4')))
  refine ⟨_, _, ?_, hh, by simp [regs]⟩
  · change 4 * (input B as).length + 6 + (5 +
        ((6 * (serialize (terminalColumns B)).length + 5) +
        (loopCost as.length 0 +
        ((serialize (row B as)).length + 4 * (records B as).length + 6)))) ≤ _
    simp only [hin, records_length, NativeBinaryRow.serialize_length, row_length,
      terminalColumns, List.length_cons, List.length_nil, loopCost, n, pow_two]
    nlinarith

/-- Read the bits at one explicitly addressed, known-width row in the retained table. -/
def read (w : ℕ) (bs : List Bool) : NativeSuffixAcquisition.Row :=
  NativeBinaryRow.decode ((NativeBinaryRow.parse ((bs.drop 1).take (2 * w))).map Prod.snd).reverse

/-- Successive row widths are determined by the finite horizon, not by an oracle. -/
def decodeTable : ℕ → List Bool → List NativeSuffixAcquisition.Row
  | 0, bs => [read 2 bs]
  | n + 1, bs => read (2 * (1 + 3 * (n + 1))) bs ::
      decodeTable n (bs.drop (1 + 4 * (1 + 3 * (n + 1))))

private theorem marked_length (bs : List Bool) :
    (bs.flatMap (fun b => [true, b])).length = 2 * bs.length := by
  simp [List.length_flatMap, Nat.mul_comm]

private theorem marked_serialize (bs : List Bool) :
    bs.flatMap (fun b => [true, b]) = serialize (bs.map (fun b => (true, b))) := by
  simp [serialize, List.flatMap_map]

private theorem read_pack (bs rest : List Bool) :
    read bs.length (pack bs ++ rest) = NativeBinaryRow.decode bs := by
  simp only [read, pack, List.cons_append, List.drop_succ_cons, List.drop_zero]
  have hw : (bs.reverse.flatMap (fun b => [true, b])).length = 2 * bs.length := by
    rw [marked_length, List.length_reverse]
  rw [← hw]
  rw [List.take_left, marked_serialize, NativeBinaryRow.parse_serialize]
  simp

private theorem decode_records (B : Finset Bool) (as : List (Finset Window)) :
    decodeTable as.length (records B as) = table B as := by
  have hc : ∀ xs : List Column, NativeBinaryRow.decode (serialize xs) = value xs := by
    intro xs; simp [NativeBinaryRow.decode, NativeBinaryRow.parse_serialize]
  induction as with
  | nil =>
      change [read 2 (pack (serialize (row B [])) ++ [])] = _
      have hw : (serialize (row B [])).length = 2 := by
        rw [NativeBinaryRow.serialize_length, row_length]; rfl
      rw [← hw, read_pack, hc, row_value]
      rfl
  | cons a as ih =>
      have hw : (serialize (row B (a :: as))).length = 2 * (1 + 3 * (as.length + 1)) := by
        rw [NativeBinaryRow.serialize_length, row_length]; rfl
      have hp : (pack (serialize (row B (a :: as)))).length =
          1 + 4 * (1 + 3 * (as.length + 1)) := by rw [pack_length, hw]; ring
      simp only [List.length_cons, decodeTable, records_cons]
      rw [← hw, read_pack, hc, row_value, ← hp, List.drop_left, ih]
      rfl

/-- Full deterministic initialization and binary acquisition of all suffix rows.
The output is the retained table itself; successful-word output is a separate obligation. -/
theorem native_binary_table (L : ℕ) (A : Fin L → Finset Window) (B : Finset Bool) :
    let as := List.ofFn A
    (input B as).length = 2 + 5 * L ∧
    (records B as).length = (L + 1) * (6 * L + 5) ∧
    decodeTable L (records B as) = table B as ∧
    (∀ (t : Fin (L + 1)) (s : Bool),
      (decodeTable L (records B as))[t.val]? = some (counts B (as.drop t.val)) ∧
      entry (counts B (as.drop t.val)) s = (completions B (as.drop t.val) s).card ∧
      entry (counts B (as.drop t.val)) s ≤ 5 ^ (L - t.val)) ∧
    ∃ time tape, time ≤ 2097152 * (L + 1) ^ 4 ∧
      Complexity.runInput binaryMachine time (input B as) = some (true, tape) ∧
      tape.output = records B as := by
  dsimp only
  let as := List.ofFn A
  have hl : as.length = L := List.length_ofFn
  have hin : (input B as).length = 2 + 5 * L := by
    simp only [input, List.length_append, List.length_cons, List.length_nil,
      masks_length, List.length_reverse, hl]
  have hd : decodeTable L (records B as) = table B as := hl ▸ decode_records B as
  refine ⟨hin, by simpa [hl] using records_length B as, hd, ?_, ?_⟩
  · intro t s
    have h := (NativeSuffixAcquisition.native_suffix_acquisition L A B).2.1 t s
    rw [hd]
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · obtain ⟨fuel, out, hf, he, ho⟩ := exec_table B as
    have hr : StackMachine.runInput stackMachine fuel (input B as) = some (true, out) := by
      change StackMachine.run stackMachine fuel (StackMachine.initial stackMachine _) = _
      have hx := StackProgram.compile_exec encoding he
      have hir : regs [] (input B as) [] [] [] =
          (fun j : Fin 7 => if j = 0 then input B as else []) := by
        funext j
        simp only [regs]
        split_ifs <;> rfl
      rw [hir] at hx
      exact hx
    obtain ⟨time, tape, ht, hrun, hout⟩ := StackCompile.simulate stackMachine fuel
      (input B as) (true, out) hr
    refine ⟨time, tape, ht.trans ?_, hrun, hout.trans ho⟩
    let m := (L + 1) ^ 2
    have hm : 1 ≤ m := by dsimp [m]; nlinarith
    have hn : (input B as).length ≤ 7 * m := by rw [hin]; dsimp [m]; nlinarith
    have hfu : fuel ≤ 256 * m := by simpa only [hl] using hf
    have hi : StackInit.initBudget stackMachine.stacks (input B as).length ≤ 35 * m := by
      change 2 * (input B as).length + 2 * 6 + 9 ≤ _
      omega
    have hs : StackSimulation.instructionBudget stackMachine
        ((input B as).length + fuel) ≤ 7409 * m := by
      change 4 * (7 * ((input B as).length + fuel + 1) + 1) + 13 ≤ _
      omega
    have hp := Nat.mul_le_mul hfu hs
    change StackInit.initBudget stackMachine.stacks (input B as).length +
      fuel * StackSimulation.instructionBudget stackMachine ((input B as).length + fuel) ≤ _
    have hpow : (L + 1) ^ 4 = m * m := by dsimp [m]; ring
    rw [hpow]
    nlinarith

#print axioms native_binary_table

end D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryTable
