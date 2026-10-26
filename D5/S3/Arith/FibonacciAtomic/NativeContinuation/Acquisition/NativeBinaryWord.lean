/- GID: D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord
   mirror-E: none(waiver:unbounded-symbolic-execution)
   anchors: []
   utility: none
   digest: Physical initial-seam selection and original successful-word output. -/

import D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryTable
import Mathlib.Tactic.DeriveFintype

/-! A finite controller scans acquired binary rows and prints original windows. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryWord

open LiteralWindowEnd (Window bits first last)
open NativeSuffixAcquisition (Row entry counts table pick reconstruct Allowed modes)
open NativeBinaryRow (Column serialize value)
open Complexity StackProgram StackWords
open StackMachine (Registers set branch)

private def join (p q : Column) : Column := (p.1 || q.1, p.2 || q.2)
private def signals (xs : List Column) : Column := xs.foldr join (false, false)
private def payload (xs : List Column) : List Bool :=
  xs.flatMap (fun p => [true, p.2, true, p.1])

private theorem join_assoc (p q r : Column) : join (join p q) r = join p (join q r) := by
  simp [join, Bool.or_assoc]

private theorem signals_append (xs ys : List Column) :
    signals (xs ++ ys) = join (signals xs) (signals ys) := by
  induction xs with
  | nil => simp [signals, join]
  | cons p xs ih => simpa only [signals, List.foldr_cons, List.foldr_append] using
      (join_assoc p (signals xs) (signals ys)).symm

private theorem signals_reverse (xs : List Column) : signals xs.reverse = signals xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
      rw [List.reverse_cons, signals_append, ih]
      simp [signals, join, Bool.or_comm]

private theorem signals_value (xs : List Column) :
    signals xs = (decide (0 < (value xs).1), decide (0 < (value xs).2)) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
      obtain ⟨x,y⟩ := p
      simp only [signals, List.foldr_cons]
      change join (x,y) (signals xs) = _
      rw [ih]
      cases x <;> cases y <;>
        simp [join, value, Lax51Proofs.RamToTM.bitsValue, Nat.bit_val]

private theorem pack_payload (xs : List Column) :
    NativeBinaryTable.pack (serialize xs) = false :: payload xs.reverse := by
  have h (ys : List Column) :
      (serialize ys).reverse.flatMap (fun b => [true,b]) = payload ys.reverse := by
    induction ys with
    | nil => rfl
    | cons p ys ih =>
        simp [serialize, List.reverse_append, List.flatMap_append, payload, ih]
  exact congrArg (List.cons false) (h xs)

private def registers (fixed : Registers 8) (src masks word : List Bool) : Registers 8 :=
  fun j => if j = 1 then src else if j = 6 then masks else if j = 8 then word else fixed j

private theorem set1 (fixed : Registers 8) (src masks word bs : List Bool) :
    set (registers fixed src masks word) 1 bs = registers fixed bs masks word := by
  funext j; fin_cases j <;> simp [set, registers]
private theorem set6 (fixed : Registers 8) (src masks word bs : List Bool) :
    set (registers fixed src masks word) 6 bs = registers fixed src bs word := by
  funext j; fin_cases j <;> simp [set, registers]
private theorem set8 (fixed : Registers 8) (src masks word bs : List Bool) :
    set (registers fixed src masks word) 8 bs = registers fixed src masks bs := by
  funext j; fin_cases j <;> simp [set, registers]

/-- Every component of the reconstruction controller is finite. -/
inductive Control where
  | start
  | header (s : Bool)
  | scan (initial s : Bool) (p : Column)
  | trueBit (initial s : Bool) (p : Column)
  | falseMark (initial s : Bool) (p : Column)
  | falseBit (initial s : Bool) (p : Column)
  | done (initial s : Bool) (p : Column) (next : Bool)
  | load (s : Bool) (p : Column) (next : Bool) (n : Fin 6) (a : Finset Window)
  | emit (b : Window) (p : Column) (next : Bool) (n : Fin 4)
  | fail
  deriving DecidableEq, Fintype

/-- The table scan only tests zero; integer counts remain physically stored. -/
def walk : Program 8 Control where
  start := .start
  code q := match q with
    | .start => .pop 8 .fail (.header false) (.header true)
    | .header s => .pop 1 .fail (.scan true s (false,false)) .fail
    | .scan i s p => .pop 1 (.done i s p false) (.done i s p true) (.trueBit i s p)
    | .trueBit i s p => .pop 1 .fail (.falseMark i s p)
        (.falseMark i s (p.1,true))
    | .falseMark i s p => .pop 1 .fail .fail (.falseBit i s p)
    | .falseBit i s p => .pop 1 .fail (.scan i s p) (.scan i s (true,p.2))
    | .done i s p next => if i then
        if (if s then p.2 else p.1) then
          if next then .goto (.scan false s (false,false)) else .halt true
        else .halt false
      else .goto (.load s p next 0 ∅)
    | .load s p next n a => if h : n.val < 5 then
        let b := modes[4 - n.val]'(by simp [modes]; omega)
        let n' : Fin 6 := ⟨n.val+1,by omega⟩
        .pop 6 .fail (.load s p next n' a) (.load s p next n' (insert b a))
      else match pick a (p.1.toNat,p.2.toNat) s with
        | none => .halt false
        | some b => .goto (.emit b p next 0)
    | .emit b p next n => if h : n.val < 3 then
        .push 8 ((bits b)[n.val]'(by cases b <;> simp [bits]; omega))
          (.emit b p next ⟨n.val+1,by omega⟩)
      else .goto (.done true (first b) p next)
    | .fail => .halt false

private def labels : List Control := (Finset.univ : Finset Control).toList

def walkEncoding : Encoding Control where
  states := labels.length
  encode q := ⟨labels.idxOf q, Nat.lt_succ_of_le (List.idxOf_le_length (l := labels) (a := q))⟩
  decode q := (labels[q.val]?).getD .fail
  decode_encode q := by simp [labels]

private theorem exec_scan (i s : Bool) (p : Column) (xs : List Column)
    (next : Bool) (rest masks word : List Bool) (fixed : Registers 8)
    (t : ℕ) (out : Bool × Registers 8)
    (h : Exec walk (.done i s (join p (signals xs)) next)
      (registers fixed (if next then rest else []) masks word) t out) :
    Exec walk (.scan i s p)
      (registers fixed (payload xs ++ if next then false :: rest else []) masks word)
      (4 * xs.length + 1 + t) out := by
  induction xs generalizing p with
  | nil =>
      have he : join p (signals []) = p := by simp [join, signals]
      rw [he] at h
      have hh : StackProgram.step walk (.scan i s p)
          (registers fixed (if next then false :: rest else []) masks word) =
          .inr (.done i s p next, registers fixed (if next then rest else []) masks word) := by
        cases next <;> simp [StackProgram.step,walk,registers,branch,set1]
      simpa [payload, Nat.add_comm] using Exec.next hh h
  | cons c xs ih =>
      obtain ⟨x,y⟩ := c
      have ht := ih (join p (x,y)) (by
        simpa only [signals, List.foldr_cons, join_assoc] using h)
      have hh := Exec.next (p := walk)
        (q := .scan i s p) (q' := .trueBit i s p)
        (r' := registers fixed (y :: true :: x :: (payload xs ++ if next then false::rest else [])) masks word)
        (by simp [StackProgram.step,walk,payload,registers,branch,set1])
        (Exec.next (q' := .falseMark i s (p.1,p.2 || y))
          (r' := registers fixed (true :: x :: (payload xs ++ if next then false::rest else [])) masks word)
          (by cases y <;> simp [StackProgram.step,walk,registers,branch,set1])
          (Exec.next (q' := .falseBit i s (p.1,p.2 || y))
            (r' := registers fixed (x :: (payload xs ++ if next then false::rest else [])) masks word)
            (by simp [StackProgram.step,walk,registers,branch,set1])
            (Exec.next (by cases x <;> simp [StackProgram.step,walk,registers,branch,set1,join]) ht)))
      convert hh using 1 <;> simp only [List.length_cons] <;> omega

end D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryWord
