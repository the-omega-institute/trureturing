/- GID: D5/S0/Computability/BinaryMachine/TapeToStacks
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/TapeToStacks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed finite binary machine TapeToStacks supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4,
immutable revision 3e603e795b44fedcf7d6dd65b7d1e30547ead925, Complexity/TapeToStacks.lean.
Apache-2.0; full license and finite replacement contract:
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Only module imports and this repository header are adapted.
-/

public import D5.S0.Computability.BinaryMachine.StackSimulation
public import D5.S0.Computability.BinaryMachine.StackWords
import Lean.Elab.Tactic.Omega

/-!
A concrete simulation of a single tape by Boolean stacks. The current symbol
is stored in finite control; the left and right tails are encoded by two bits
per tape symbol. No instruction traverses or replaces an entire stack.
-/

@[expose] public section

namespace Complexity.TapeToStacks

open StackProgram

set_option backward.isDefEq.respectTransparency false

def high : Symbol → Bool
  | .blank | .bit false => false
  | .bit true | .sep => true

def low : Symbol → Bool
  | .blank | .bit true => false
  | .bit false | .sep => true

def pairSymbol : Bool → Bool → Symbol
  | false, false => .blank
  | false, true => .bit false
  | true, false => .bit true
  | true, true => .sep

@[simp] theorem pairSymbol_bits (a : Symbol) : pairSymbol (high a) (low a) = a := by
  cases a with
  | blank => rfl
  | sep => rfl
  | bit b => cases b <;> rfl

def symbols : List Symbol → List Bool
  | [] => []
  | a :: rest => high a :: low a :: symbols rest

@[simp] theorem symbols_length (xs : List Symbol) : (symbols xs).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [symbols, ih, Nat.mul_add]

def regs (io left right : List Bool) : StackMachine.Registers 2 :=
  fun i => if i = 0 then io else if i = 1 then left else right

@[simp] theorem regs_zero (io left right : List Bool) : regs io left right 0 = io := rfl
@[simp] theorem regs_one (io left right : List Bool) : regs io left right 1 = left := rfl
@[simp] theorem regs_two (io left right : List Bool) : regs io left right 2 = right := rfl

theorem fin_three_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have hi := i.isLt
  have hn : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases hn with hn | hn | hn
  · exact Or.inl (Fin.ext hn)
  · exact Or.inr (Or.inl (Fin.ext hn))
  · exact Or.inr (Or.inr (Fin.ext hn))

@[simp] theorem set_regs_zero (io left right xs : List Bool) :
    StackMachine.set (regs io left right) 0 xs = regs xs left right := by
  funext i
  rcases fin_three_cases i with rfl | rfl | rfl <;> simp [StackMachine.set]

@[simp] theorem set_regs_one (io left right xs : List Bool) :
    StackMachine.set (regs io left right) 1 xs = regs io xs right := by
  funext i
  rcases fin_three_cases i with rfl | rfl | rfl <;> simp [StackMachine.set]

@[simp] theorem set_regs_two (io left right xs : List Bool) :
    StackMachine.set (regs io left right) 2 xs = regs io left xs := by
  funext i
  rcases fin_three_cases i with rfl | rfl | rfl <;> simp [StackMachine.set]

inductive Label (M : Machine) where
  | read (q : Fin (M.states + 1)) (fromLeft : Bool)
  | readLow (q : Fin (M.states + 1)) (fromLeft first : Bool)
  | main (q : Fin (M.states + 1)) (head : Symbol)
  | writeHigh (q : Fin (M.states + 1)) (goLeft first : Bool)
  | haltHigh (decision first : Bool)
  | done (decision : Bool)

abbrev LabelSum (M : Machine) :=
  Sum (Fin (M.states + 1) × Bool)
    (Sum (Fin (M.states + 1) × (Bool × Bool))
      (Sum (Fin (M.states + 1) × Symbol)
        (Sum (Fin (M.states + 1) × (Bool × Bool)) (Sum (Bool × Bool) Bool))))

def Label.toSum {M : Machine} : Label M → LabelSum M
  | .read q b => .inl (q, b)
  | .readLow q b c => .inr (.inl (q, b, c))
  | .main q a => .inr (.inr (.inl (q, a)))
  | .writeHigh q b c => .inr (.inr (.inr (.inl (q, b, c))))
  | .haltHigh b c => .inr (.inr (.inr (.inr (.inl (b, c)))))
  | .done b => .inr (.inr (.inr (.inr (.inr b))))

def Label.ofSum {M : Machine} : LabelSum M → Label M
  | .inl (q, b) => .read q b
  | .inr (.inl (q, b, c)) => .readLow q b c
  | .inr (.inr (.inl (q, a))) => .main q a
  | .inr (.inr (.inr (.inl (q, b, c)))) => .writeHigh q b c
  | .inr (.inr (.inr (.inr (.inl (b, c))))) => .haltHigh b c
  | .inr (.inr (.inr (.inr (.inr b)))) => .done b

@[simp] theorem Label.ofSum_toSum {M : Machine} (q : Label M) :
    Label.ofSum q.toSum = q := by cases q <;> rfl

def symbolEncoding : Encoding Symbol where
  states := 3
  encode := fun a => match a with
    | .blank => 0
    | .bit false => 1
    | .bit true => 2
    | .sep => 3
  decode := fun q => match q.val with
    | 0 => .blank
    | 1 => .bit false
    | 2 => .bit true
    | _ => .sep
  decode_encode := by intro a; cases a with
    | blank => rfl
    | sep => rfl
    | bit b => cases b <;> rfl

def labelSumEncoding (M : Machine) : Encoding (LabelSum M) :=
  let q := Encoding.fin M.states
  let bb := Encoding.bool.prod Encoding.bool
  (q.prod Encoding.bool).sum ((q.prod bb).sum ((q.prod symbolEncoding).sum
    ((q.prod bb).sum (bb.sum Encoding.bool))))

def labelEncoding (M : Machine) : Encoding (Label M) where
  states := (labelSumEncoding M).states
  encode q := (labelSumEncoding M).encode q.toSum
  decode q := Label.ofSum ((labelSumEncoding M).decode q)
  decode_encode q := by simp [(labelSumEncoding M).decode_encode]

/-- The intermediate simulation uses only individual stack pops and pushes,
plus finite-control jumps and halts. `true` means the left tape stack. -/
def core (M : Machine) : Program 2 (Label M) where
  start := .read M.start false
  code label := match label with
    | .read q side =>
      .pop (if side then 1 else 2) (.main q .blank)
        (.readLow q side false) (.readLow q side true)
    | .readLow q side first =>
      .pop (if side then 1 else 2) (.done false)
        (.main q (pairSymbol first false)) (.main q (pairSymbol first true))
    | .main q a => match M.code q a with
      | .halt b => .push 2 (low a) (.haltHigh b (high a))
      | .step a .stay q' => .goto (.main q' a)
      | .step a .left q' => .push 2 (low a) (.writeHigh q' true (high a))
      | .step a .right q' => .push 1 (low a) (.writeHigh q' false (high a))
    | .writeHigh q side first =>
      .push (if side then 2 else 1) first (.read q side)
    | .haltHigh b first => .push 2 first (.done b)
    | .done b => .halt b

def readCost : List Symbol → Nat
  | [] => 1
  | _ :: _ => 2

theorem readCost_le (xs : List Symbol) : readCost xs ≤ 2 := by cases xs <;> simp [readCost]

/-- The right-head decoder costs one instruction for an implicit blank and two
instructions for an encoded symbol. -/
theorem exec_read_right (M : Machine) (q : Fin (M.states + 1))
    (io left : List Bool) (right : List Symbol) (time : Nat) (result : Bool × StackMachine.Registers 2)
    (h : Exec (core M) (.main q (right.headD .blank))
      (regs io left (symbols (right.drop 1))) time result) :
    Exec (core M) (.read q false) (regs io left (symbols right))
      (time + readCost right) result := by
  cases right with
  | nil =>
    exact .next (by simp [StackProgram.step, core, symbols, StackMachine.branch]) h
  | cons a rest =>
    have hs : StackProgram.step (core M) (.read q false) (regs io left (symbols (a :: rest))) =
        .inr (.readLow q false (high a), regs io left (low a :: symbols rest)) := by
      cases hhigh : high a <;> simp [StackProgram.step, core, symbols, StackMachine.branch, hhigh]
    have ht : StackProgram.step (core M) (.readLow q false (high a))
        (regs io left (low a :: symbols rest)) =
        .inr (.main q a, regs io left (symbols rest)) := by
      cases hlow : low a <;>
        simpa [StackProgram.step, core, StackMachine.branch, hlow] using pairSymbol_bits a
    exact .next hs (.next ht h)

theorem exec_read_left (M : Machine) (q : Fin (M.states + 1))
    (io right : List Bool) (left : List Symbol) (time : Nat) (result : Bool × StackMachine.Registers 2)
    (h : Exec (core M) (.main q (left.headD .blank))
      (regs io (symbols (left.drop 1)) right) time result) :
    Exec (core M) (.read q true) (regs io (symbols left) right)
      (time + readCost left) result := by
  cases left with
  | nil =>
    exact .next (by simp [StackProgram.step, core, symbols, StackMachine.branch]) h
  | cons a rest =>
    have hs : StackProgram.step (core M) (.read q true) (regs io (symbols (a :: rest)) right) =
        .inr (.readLow q true (high a), regs io (low a :: symbols rest) right) := by
      cases hhigh : high a <;> simp [StackProgram.step, core, symbols, StackMachine.branch, hhigh]
    have ht : StackProgram.step (core M) (.readLow q true (high a))
        (regs io (low a :: symbols rest) right) =
        .inr (.main q a, regs io (symbols rest) right) := by
      cases hlow : low a <;>
        simpa [StackProgram.step, core, StackMachine.branch, hlow] using pairSymbol_bits a
    exact .next hs (.next ht h)

theorem exec_halt (M : Machine) (q : Fin (M.states + 1)) (a : Symbol)
    (io left : List Bool) (right : List Symbol) (b : Bool)
    (hc : M.code q a = .halt b) :
    Exec (core M) (.main q a) (regs io left (symbols right)) 3
      (b, regs io left (symbols (a :: right))) := by
  apply Exec.next (q' := .haltHigh b (high a))
    (r' := regs io left (low a :: symbols right))
  · simp [StackProgram.step, core, hc]
  apply Exec.next (q' := .done b) (r' := regs io left (symbols (a :: right)))
  · simp [StackProgram.step, core, symbols]
  · exact .halt (by simp [StackProgram.step, core])

theorem exec_move_right (M : Machine) (q q' : Fin (M.states + 1))
    (scan a : Symbol) (hc : M.code q scan = .step a .right q')
    (io : List Bool) (left right : List Symbol) (time : Nat)
    (result : Bool × StackMachine.Registers 2)
    (h : Exec (core M) (.read q' false)
      (regs io (symbols (a :: left)) (symbols right)) time result) :
    Exec (core M) (.main q scan) (regs io (symbols left) (symbols right))
      (time + 2) result := by
  apply Exec.next (q' := .writeHigh q' false (high a))
    (r' := regs io (low a :: symbols left) (symbols right))
  · simp [StackProgram.step, core, hc]
  apply Exec.next (q' := .read q' false)
    (r' := regs io (symbols (a :: left)) (symbols right))
  · simp [StackProgram.step, core, symbols]
  · exact h

theorem exec_move_left (M : Machine) (q q' : Fin (M.states + 1))
    (scan a : Symbol) (hc : M.code q scan = .step a .left q')
    (io : List Bool) (left right : List Symbol) (time : Nat)
    (result : Bool × StackMachine.Registers 2)
    (h : Exec (core M) (.read q' true)
      (regs io (symbols left) (symbols (a :: right))) time result) :
    Exec (core M) (.main q scan) (regs io (symbols left) (symbols right))
      (time + 2) result := by
  apply Exec.next (q' := .writeHigh q' true (high a))
    (r' := regs io (symbols left) (low a :: symbols right))
  · simp [StackProgram.step, core, hc]
  apply Exec.next (q' := .read q' true)
    (r' := regs io (symbols left) (symbols (a :: right)))
  · simp [StackProgram.step, core, symbols]
  · exact h

/-- The current symbol is carried in finite control during the main simulation. -/
def mainRegs (io : List Bool) (t : Tape) : StackMachine.Registers 2 :=
  regs io (symbols t.left) (symbols (t.right.drop 1))

/-- Before halting, the current symbol is restored to the right stack. -/
def resultRegs (io : List Bool) (t : Tape) : StackMachine.Registers 2 :=
  regs io (symbols t.left) (symbols (t.read :: t.right.drop 1))

/-- Each genuine tape instruction is simulated by at most four elementary
stack instructions. The final decision and the whole tape are represented. -/
theorem simulate_main (M : Machine) (fuel : Nat) (c : Config M)
    (b : Bool) (out : Tape) (hrun : Complexity.run M fuel c = some (b, out))
    (io : List Bool) :
    ∃ time, time ≤ 4 * fuel ∧
      Exec (core M) (.main c.state c.tape.read) (mainRegs io c.tape) time
        (b, resultRegs io out) := by
  induction fuel generalizing c with
  | zero => simp [Complexity.run] at hrun
  | succ fuel ih =>
    cases hc : M.code c.state c.tape.read with
    | halt decision =>
      have heq : (decision, c.tape) = (b, out) := by simpa [Complexity.run, hc] using hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨3, by omega, exec_halt M c.state c.tape.read io (symbols c.tape.left)
        (c.tape.right.drop 1) decision hc⟩
    | step a d q =>
      have hnext : Complexity.run M fuel ⟨q, (c.tape.write a).move d⟩ = some (b, out) := by
        simpa only [Complexity.run, hc] using hrun
      obtain ⟨time, ht, he⟩ := ih ⟨q, (c.tape.write a).move d⟩ hnext
      cases d with
      | stay =>
        have he' : Exec (core M) (.main q a) (mainRegs io c.tape) time (b, resultRegs io out) := by
          simpa only [mainRegs, Tape.move, Tape.write, Tape.read, List.headD_cons,
            List.drop_succ_cons, List.drop_zero] using he
        refine ⟨time + 1, by omega, Exec.next ?_ he'⟩
        simp [StackProgram.step, core, hc]
      | right =>
        have he' : Exec (core M) (.main q ((c.tape.right.drop 1).headD .blank))
            (regs io (symbols (a :: c.tape.left)) (symbols ((c.tape.right.drop 1).drop 1)))
            time (b, resultRegs io out) := by
          simpa only [mainRegs, Tape.move, Tape.write, Tape.read] using he
        have hread := exec_read_right M q io (symbols (a :: c.tape.left))
          (c.tape.right.drop 1) time (b, resultRegs io out) he'
        have hp := exec_move_right M c.state q c.tape.read a hc io c.tape.left
          (c.tape.right.drop 1) _ _ hread
        have hcost := readCost_le (c.tape.right.drop 1)
        exact ⟨time + readCost (c.tape.right.drop 1) + 2, by omega, hp⟩
      | left =>
        have he' : Exec (core M) (.main q (c.tape.left.headD .blank))
            (regs io (symbols (c.tape.left.drop 1)) (symbols (a :: c.tape.right.drop 1)))
            time (b, resultRegs io out) := by
          rw [Tape.move_left_eq] at he
          simpa only [mainRegs, Tape.write, Tape.read, List.headD_cons,
            List.drop_succ_cons, List.drop_zero] using he
        have hread := exec_read_left M q io (symbols (a :: c.tape.right.drop 1))
          c.tape.left time (b, resultRegs io out) he'
        have hp := exec_move_left M c.state q c.tape.read a hc io c.tape.left
          (c.tape.right.drop 1) _ _ hread
        have hcost := readCost_le c.tape.left
        exact ⟨time + readCost c.tape.left + 2, by omega, hp⟩

theorem simulate_core (M : Machine) (fuel : Nat) (input : List Bool)
    (b : Bool) (out : Tape) (hrun : runInput M fuel input = some (b, out))
    (io : List Bool) :
    ∃ time, time ≤ 4 * fuel + 2 ∧
      Exec (core M) (core M).start (regs io [] (symbols (input.map Symbol.bit))) time
        (b, resultRegs io out) := by
  obtain ⟨time, ht, he⟩ := simulate_main M fuel (initial M input) b out hrun io
  have hp := exec_read_right M M.start io [] (input.map Symbol.bit) time (b, resultRegs io out) he
  have hcost := readCost_le (input.map Symbol.bit)
  exact ⟨time + readCost (input.map Symbol.bit), by omega, hp⟩

@[simp] theorem symbols_append (xs ys : List Symbol) :
    symbols (xs ++ ys) = symbols xs ++ symbols ys := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [symbols, ih]

/-- Expand raw bits to symbol pairs by three counted instructions per bit. -/
def expand : Program 2 (Fin 6) where
  start := 0
  code q := if q = 0 then .pop 1 1 2 4
    else if q = 1 then .halt true
    else if q = 2 then .push 2 true 3
    else if q = 3 then .push 2 false 0
    else if q = 4 then .push 2 false 5
    else .push 2 true 0

theorem exec_expand (io xs right : List Bool) :
    Exec expand 0 (regs io xs right) (3 * xs.length + 2)
      (true, regs io [] (symbols (xs.reverse.map Symbol.bit) ++ right)) := by
  induction xs generalizing right with
  | nil =>
    exact .next (q' := 1) (r' := regs io [] right)
      (by simp [StackProgram.step, expand, StackMachine.branch])
      (.halt (by simp [StackProgram.step, expand, symbols]))
  | cons b xs ih =>
    have h := ih (high (.bit b) :: low (.bit b) :: right)
    have hpop : StackProgram.step expand 0 (regs io (b :: xs) right) =
        .inr ((if b then 4 else 2), regs io xs right) := by
      cases b <;> simp [StackProgram.step, expand, StackMachine.branch]
    have hlow : StackProgram.step expand (if b then 4 else 2) (regs io xs right) =
        .inr ((if b then 5 else 3), regs io xs (low (.bit b) :: right)) := by
      cases b <;> simp [StackProgram.step, expand, low]
    have hhigh : StackProgram.step expand (if b then 5 else 3)
        (regs io xs (low (.bit b) :: right)) =
        .inr (0, regs io xs (high (.bit b) :: low (.bit b) :: right)) := by
      cases b <;> simp [StackProgram.step, expand, high]
    simpa [List.reverse_cons, List.map_append, symbols, List.append_assoc,
      Nat.mul_add, Nat.add_assoc] using Exec.next hpop (Exec.next hlow (Exec.next hhigh h))

def initializer : Program 2 (Sum (Fin 4) (Fin 6)) :=
  seq (StackWords.transfer 0 1) expand

theorem exec_initializer (input : List Bool) :
    Exec initializer initializer.start (regs input [] []) (5 * input.length + 4)
      (true, regs [] [] (symbols (input.map Symbol.bit))) := by
  have ht := StackWords.exec_transfer (k := 2) 0 1 (by decide) (regs input [] [])
  simp only [regs_zero, regs_one, set_regs_zero, set_regs_one, List.append_nil] at ht
  have he := exec_expand [] input.reverse []
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil] at he
  simpa [initializer, seq, expand, StackWords.transfer, Nat.mul_add, Nat.add_assoc,
    show 2 * input.length + 2 + (3 * input.length + 2) = 5 * input.length + 4 by omega]
    using exec_seq (StackWords.transfer 0 1) expand ht he

/-- Consume consecutive bit symbols. A delimiter is consumed, and the remainder
is subsequently erased by a separate counted clearing loop. -/
def trim : Program 2 (Fin 6) where
  start := 0
  code q := if q = 0 then .pop 2 1 2 3
    else if q = 1 then .halt true
    else if q = 2 then .pop 2 1 1 4
    else if q = 3 then .pop 2 1 5 1
    else if q = 4 then .push 1 false 0
    else .push 1 true 0

def afterBits : List Symbol → List Symbol
  | [] => []
  | .bit _ :: xs => afterBits xs
  | _ :: xs => xs

def trimCost : List Symbol → Nat
  | [] => 2
  | .bit _ :: xs => trimCost xs + 3
  | _ :: _ => 3

theorem afterBits_length_le (xs : List Symbol) : (afterBits xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [afterBits]
  | cons a xs ih => cases a <;> simp [afterBits] <;> omega

theorem trimCost_le (xs : List Symbol) : trimCost xs ≤ 3 * xs.length + 3 := by
  induction xs with
  | nil => simp [trimCost]
  | cons a xs ih => cases a <;> simp [trimCost] <;> omega

theorem exec_trim (io accum : List Bool) (xs : List Symbol) :
    Exec trim 0 (regs io accum (symbols xs)) (trimCost xs)
      (true, regs io ((Tape.bits xs).reverse ++ accum) (symbols (afterBits xs))) := by
  induction xs generalizing accum with
  | nil =>
    exact .next (q' := 1) (r' := regs io accum [])
      (by simp [StackProgram.step, trim, symbols, StackMachine.branch])
      (.halt (by simp [StackProgram.step, trim, Tape.bits, afterBits, symbols]))
  | cons a xs ih =>
    cases a with
    | blank =>
      apply Exec.next (q' := 2) (r' := regs io accum (false :: symbols xs))
      · simp [StackProgram.step, trim, symbols, high, low, StackMachine.branch]
      apply Exec.next (q' := 1) (r' := regs io accum (symbols xs))
      · simp [StackProgram.step, trim, StackMachine.branch]
      exact .halt (by simp [StackProgram.step, trim, Tape.bits, afterBits])
    | sep =>
      apply Exec.next (q' := 3) (r' := regs io accum (true :: symbols xs))
      · simp [StackProgram.step, trim, symbols, high, low, StackMachine.branch]
      apply Exec.next (q' := 1) (r' := regs io accum (symbols xs))
      · simp [StackProgram.step, trim, StackMachine.branch]
      exact .halt (by simp [StackProgram.step, trim, Tape.bits, afterBits])
    | bit b =>
      have h := ih (b :: accum)
      have hhigh : StackProgram.step trim 0 (regs io accum (symbols (.bit b :: xs))) =
          .inr ((if b then 3 else 2), regs io accum (low (.bit b) :: symbols xs)) := by
        cases b <;> simp [StackProgram.step, trim, symbols, high, low, StackMachine.branch]
      have hlow : StackProgram.step trim (if b then 3 else 2)
          (regs io accum (low (.bit b) :: symbols xs)) =
          .inr ((if b then 5 else 4), regs io accum (symbols xs)) := by
        cases b <;> simp [StackProgram.step, trim, low, StackMachine.branch]
      have hpush : StackProgram.step trim (if b then 5 else 4) (regs io accum (symbols xs)) =
          .inr (0, regs io (b :: accum) (symbols xs)) := by
        cases b <;> simp [StackProgram.step, trim]
      simpa [Tape.bits, afterBits, trimCost, List.reverse_cons, List.append_assoc,
        Nat.add_assoc] using Exec.next hhigh (Exec.next hlow (Exec.next hpush h))

abbrev ExtractLabel := Sum Bool (Sum (Fin 6) (Sum Bool (Fin 4)))

def extractor : Program 2 ExtractLabel :=
  seq (StackWords.clear 1) (seq trim (seq (StackWords.clear 2) (StackWords.transfer 1 0)))

def extractCost (left xs : List Symbol) : Nat :=
  2 * left.length + 2 + (trimCost xs +
    (2 * (afterBits xs).length + 2 + (2 * (Tape.bits xs).length + 2)))

theorem exec_extractor (left xs : List Symbol) :
    Exec extractor extractor.start (regs [] (symbols left) (symbols xs))
      (extractCost left xs) (true, regs (Tape.bits xs) [] []) := by
  have hleft := StackWords.exec_clear (k := 2) 1 (regs [] (symbols left) (symbols xs))
  simp only [regs_one, symbols_length, set_regs_one] at hleft
  have ht := exec_trim [] [] xs
  simp only [List.append_nil] at ht
  have hright := StackWords.exec_clear (k := 2) 2
    (regs [] (Tape.bits xs).reverse (symbols (afterBits xs)))
  simp only [regs_two, symbols_length, set_regs_two] at hright
  have hout := StackWords.exec_transfer (k := 2) 1 0 (by decide)
    (regs [] (Tape.bits xs).reverse [])
  simp only [regs_one, regs_zero, List.length_reverse, List.reverse_reverse,
    List.append_nil, set_regs_one, set_regs_zero] at hout
  exact exec_seq _ _ hleft (exec_seq _ _ ht (exec_seq _ _ hright hout))

theorem extractCost_le (left xs : List Symbol) :
    extractCost left xs ≤ 2 * left.length + 7 * xs.length + 9 := by
  have ha := afterBits_length_le xs
  have hc := trimCost_le xs
  have hb := Tape.bits_length_le xs
  unfold extractCost
  omega

@[simp] theorem bits_restore_head (t : Tape) :
    Tape.bits (t.read :: t.right.drop 1) = t.output := by
  cases t with | mk left right => cases right <;> simp [Tape.read, Tape.bits, Tape.output]

theorem restore_head_length_le (t : Tape) :
    (t.read :: t.right.drop 1).length ≤ t.right.length + 1 := by
  cases t with | mk left right => cases right <;> simp

abbrev NormalLabel (M : Machine) :=
  Sum (Sum (Fin 4) (Fin 6)) (Sum (Label M) ExtractLabel)

def normalized (M : Machine) : Program 2 (NormalLabel M) :=
  seq initializer (seq (core M) extractor)

def normalEncoding (M : Machine) : Encoding (NormalLabel M) :=
  Encoding.sum (Encoding.sum (Encoding.fin 3) (Encoding.fin 5))
    (Encoding.sum (labelEncoding M)
      (Encoding.sum Encoding.bool
        (Encoding.sum (Encoding.fin 5) (Encoding.sum Encoding.bool (Encoding.fin 3)))))

/-- The complete simulator starts from raw binary input and returns precisely the
contiguous binary output, with both work registers empty. Erasing work data and
stopping at the first output delimiter are counted computations. -/
theorem exec_normalized (M : Machine) (fuel : Nat) (input : List Bool) (out : Tape)
    (h : runInput M fuel input = some (true, out)) :
    ∃ time, time ≤ 18 * (input.length + fuel + 2) ∧
      Exec (normalized M) (normalized M).start (regs input [] []) time
        (true, regs out.output [] []) := by
  obtain ⟨time, ht, he⟩ := simulate_core M fuel input true out h []
  have hout := exec_extractor out.left (out.read :: out.right.drop 1)
  rw [bits_restore_head] at hout
  have hfull := exec_seq initializer (seq (core M) extractor) (exec_initializer input)
    (exec_seq (core M) extractor he hout)
  have hcost := extractCost_le out.left (out.read :: out.right.drop 1)
  have hlen := restore_head_length_le out
  have hsize := run_size_le M fuel (initial M input) (true, out) h
  simp only [initial, Tape.size_ofInput] at hsize
  simp only [Tape.size] at hsize
  refine ⟨5 * input.length + 4 + (time + extractCost out.left (out.read :: out.right.drop 1)),
    by omega, hfull⟩

def normalizedMachine (M : Machine) : StackMachine.Machine :=
  compile (normalized M) (normalEncoding M)

theorem registers_initial (input : List Bool) :
    (fun j : Fin 3 => if j = 0 then input else []) = regs input [] [] := by
  funext j
  rcases fin_three_cases j with rfl | rfl | rfl <;> rfl

theorem run_normalizedMachine (M : Machine) (fuel : Nat) (input : List Bool) (out : Tape)
    (h : runInput M fuel input = some (true, out)) :
    ∃ time, time ≤ 18 * (input.length + fuel + 2) ∧
      StackMachine.runInput (normalizedMachine M) time input = some (true, regs out.output [] []) := by
  obtain ⟨time, ht, he⟩ := exec_normalized M fuel input out h
  exact ⟨time, ht, by
    simpa only [StackMachine.runInput, StackMachine.initial, normalizedMachine, compile,
      registers_initial] using compile_exec (normalEncoding M) he⟩

/-- Composition of two arbitrary tape transducers, with explicit cleanup between
them, on a fixed three-register Boolean stack machine. -/
def compositionProgram (first second : Machine) :
    Program 2 (Sum (NormalLabel first) (NormalLabel second)) :=
  seq (normalized first) (normalized second)

def compositionMachine (first second : Machine) : StackMachine.Machine :=
  compile (compositionProgram first second)
    (Encoding.sum (normalEncoding first) (normalEncoding second))

theorem run_compositionMachine (first second : Machine)
    (firstFuel secondFuel : Nat) (input : List Bool) (middle out : Tape)
    (hfirst : runInput first firstFuel input = some (true, middle))
    (hsecond : runInput second secondFuel middle.output = some (true, out)) :
    ∃ time, time ≤ 72 * (input.length + firstFuel + secondFuel + 1) ∧
      StackMachine.runInput (compositionMachine first second) time input =
        some (true, regs out.output [] []) := by
  obtain ⟨t, ht, he⟩ := exec_normalized first firstFuel input middle hfirst
  obtain ⟨s, hs, hf⟩ := exec_normalized second secondFuel middle.output out hsecond
  have hm := runInput_output_length_le first firstFuel input (true, middle) hfirst
  simp only at hm
  have hh := compile_exec (Encoding.sum (normalEncoding first) (normalEncoding second))
    (exec_seq (normalized first) (normalized second) he hf)
  refine ⟨t + s, by omega, ?_⟩
  simpa only [StackMachine.runInput, StackMachine.initial, compositionMachine,
    compositionProgram, compile, seq, registers_initial] using hh

end Complexity.TapeToStacks
