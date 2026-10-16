/- GID: D5/S0/Computability/BinaryMachine/StackSimulation
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/StackSimulation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed finite binary machine StackSimulation supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4,
immutable revision 3e603e795b44fedcf7d6dd65b7d1e30547ead925, Complexity/StackSimulation.lean.
Apache-2.0; full license and finite replacement contract:
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Only module imports and this repository header are adapted.
-/

public import D5.S0.Computability.BinaryMachine.StackProgram
public import D5.S0.Computability.BinaryMachine.StackCompiler
public import D5.S0.Computability.BinaryMachine.StackPop
public import D5.S0.Computability.BinaryMachine.StackEncoding
public import D5.S0.Computability.BinaryMachine.TapeEquiv
import Lean.Elab.Tactic.Omega

/-!
# Finite control for stack-to-tape compilation

This module develops the explicit finite controller and its timed simulation.
Every target instruction is one of the original single-tape machine's local
instructions; finite label encodings affect control only.
-/

@[expose] public section

namespace Complexity.StackProgram

def Encoding.prod {A B : Type} (a : Encoding A) (b : Encoding B) : Encoding (A × B) where
  states := (a.states + 1) * (b.states + 1)
  encode q := ⟨(a.encode q.1).val * (b.states + 1) + (b.encode q.2).val, by
    have ha := (a.encode q.1).isLt
    have hb := (b.encode q.2).isLt
    have hm := Nat.mul_le_mul_right (b.states + 1) (Nat.succ_le_of_lt ha)
    have hlt : (a.encode q.1).val * (b.states + 1) + (b.encode q.2).val <
        ((a.encode q.1).val + 1) * (b.states + 1) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt hlt) hm)⟩
  decode q :=
    (a.decode ⟨q.val / (b.states + 1) % (a.states + 1), Nat.mod_lt _ (by omega)⟩,
     b.decode ⟨q.val % (b.states + 1), Nat.mod_lt _ (by omega)⟩)
  decode_encode := by
    intro ⟨x, y⟩
    have ha := (a.encode x).isLt
    have hb := (b.encode y).isLt
    have hd : ((a.encode x).val * (b.states + 1) + (b.encode y).val) /
        (b.states + 1) = (a.encode x).val := by
      rw [Nat.mul_comm (a.encode x).val (b.states + 1), Nat.mul_add_div (by omega),
        Nat.div_eq_of_lt hb, Nat.add_zero]
    have hm : ((a.encode x).val * (b.states + 1) + (b.encode y).val) %
        (b.states + 1) = (b.encode y).val := Nat.mul_add_mod_of_lt hb
    simp only [hd, hm, Nat.mod_eq_of_lt ha, a.decode_encode, b.decode_encode]

end Complexity.StackProgram

namespace Complexity.StackSimulation

open Complexity.StackProgram (Encoding)

inductive Op (Label : Type) where
  | halt (decision : Bool)
  | step (write : Symbol) (move : Move) (next : Label)

structure Program (Label : Type) where
  start : Label
  code : Label → Symbol → Op Label

def run {L : Type} (p : Program L) : Nat → L → Tape → Option (Bool × Tape)
  | 0, _, _ => none
  | fuel + 1, q, t => match p.code q t.read with
    | .halt b => some (b, t)
    | .step a d q' => run p fuel q' ((t.write a).move d)

def compileOp {L : Type} (e : Encoding L) : Op L → Instruction (e.states + 1)
  | .halt b => .halt b
  | .step a d q => .step a d (e.encode q)

def compile {L : Type} (p : Program L) (e : Encoding L) : Machine where
  states := e.states
  start := e.encode p.start
  code q a := compileOp e (p.code (e.decode q) a)

theorem compile_code {L : Type} (p : Program L) (e : Encoding L)
    (q : L) (a : Symbol) :
    (compile p e).code (e.encode q) a = compileOp e (p.code q a) := by
  simp [compile, e.decode_encode]

theorem compile_run {L : Type} (p : Program L) (e : Encoding L)
    (fuel : Nat) (q : L) (t : Tape) :
    Complexity.run (compile p e) fuel ⟨e.encode q, t⟩ = run p fuel q t := by
  induction fuel generalizing q t with
  | zero => rfl
  | succ fuel ih =>
    simp only [Complexity.run, compile, e.decode_encode]
    cases hc : p.code q t.read with
    | halt b => simp [compileOp, run, hc]
    | step a d q' =>
      simp only [run, hc]
      exact ih q' ((t.write a).move d)

open Complexity.StackCompiler

inductive Control (M : StackMachine.Machine) where
  | main (source : Fin (M.states + 1))
  | seek (source : Fin (M.states + 1)) (counter : Fin (M.stacks + 2))
  | inspect (source : Fin (M.states + 1))
  | push (next : Fin (M.states + 1)) (value : Bool) (phase : Fin (M.stacks + 9))
  | delete (next : Fin (M.states + 1)) (phase : Fin 13)
  | rewind (next : Fin (M.states + 1)) (phase : Fin 2)
  | finish (decision : Bool)

abbrev ControlSum (M : StackMachine.Machine) :=
  Sum (Fin (M.states + 1))
    (Sum (Fin (M.states + 1) × Fin (M.stacks + 2))
      (Sum (Fin (M.states + 1))
        (Sum (Fin (M.states + 1) × (Bool × Fin (M.stacks + 9)))
          (Sum (Fin (M.states + 1) × Fin 13)
            (Sum (Fin (M.states + 1) × Fin 2) Bool)))))

def Control.toSum {M : StackMachine.Machine} : Control M → ControlSum M
  | .main q => .inl q
  | .seek q c => .inr (.inl (q, c))
  | .inspect q => .inr (.inr (.inl q))
  | .push q b p => .inr (.inr (.inr (.inl (q, b, p))))
  | .delete q p => .inr (.inr (.inr (.inr (.inl (q, p)))))
  | .rewind q p => .inr (.inr (.inr (.inr (.inr (.inl (q, p))))))
  | .finish b => .inr (.inr (.inr (.inr (.inr (.inr b)))))

def Control.ofSum {M : StackMachine.Machine} : ControlSum M → Control M
  | .inl q => .main q
  | .inr (.inl (q, c)) => .seek q c
  | .inr (.inr (.inl q)) => .inspect q
  | .inr (.inr (.inr (.inl (q, b, p)))) => .push q b p
  | .inr (.inr (.inr (.inr (.inl (q, p))))) => .delete q p
  | .inr (.inr (.inr (.inr (.inr (.inl (q, p)))))) => .rewind q p
  | .inr (.inr (.inr (.inr (.inr (.inr b))))) => .finish b

@[simp] theorem Control.ofSum_toSum {M : StackMachine.Machine} (q : Control M) :
    Control.ofSum q.toSum = q := by
  cases q <;> rfl

def controlSumEncoding (M : StackMachine.Machine) : Encoding (ControlSum M) :=
  let q := Encoding.fin M.states
  Encoding.sum q (Encoding.sum (Encoding.prod q (Encoding.fin (M.stacks + 1)))
    (Encoding.sum q (Encoding.sum (Encoding.prod q (Encoding.prod Encoding.bool
      (Encoding.fin (M.stacks + 8)))) (Encoding.sum (Encoding.prod q (Encoding.fin 12))
        (Encoding.sum (Encoding.prod q (Encoding.fin 1)) Encoding.bool)))))

def controlEncoding (M : StackMachine.Machine) : Encoding (Control M) where
  states := (controlSumEncoding M).states
  encode q := (controlSumEncoding M).encode q.toSum
  decode q := Control.ofSum ((controlSumEncoding M).decode q)
  decode_encode q := by simp [(controlSumEncoding M).decode_encode]

def liftMacro {n : Nat} {L : Type} (rename : Fin n → L)
    (onHalt : Bool → Op L) : Instruction n → Op L
  | .halt b => onHalt b
  | .step a d q => .step a d (rename q)

def readBranch {L : Type} (a : Symbol) (empty zero one : L) : L :=
  match a with
  | .bit false => zero
  | .bit true => one
  | _ => empty

def pushStart (M : StackMachine.Machine) (k : Fin (M.stacks + 1)) (b : Bool) :
    Fin (M.stacks + 9) :=
  sequenceLeft (seekMachine M.stacks) (insertRewindMachine (.bit b))
    ⟨k.val + 1, by change k.val + 1 < M.stacks + 1 + 1; have := k.isLt; omega⟩

/-- The finite controller for already encoded registers. Initial serialization
is a separate prefix computation. No whole-stack operation occurs in this code. -/
def controller (M : StackMachine.Machine) : Program (Control M) where
  start := .main M.start
  code label a :=
    match label with
    | .main q => match M.code q with
      | .halt b => .step a .right (.finish b)
      | .goto next => .step a .stay (.main next)
      | .push k b next => .step a .stay (.push next b (pushStart M k b))
      | .pop k _ _ _ | .peek k _ _ _ =>
        .step a .stay (.seek q ⟨k.val + 1, by have := k.isLt; omega⟩)
    | .seek q counter =>
      liftMacro (Control.seek q)
        (fun b => if b then .step a .stay (.inspect q) else .halt false)
        ((seekMachine M.stacks).code counter a)
    | .inspect q => match M.code q with
      | .pop _ e z o =>
        match a with
        | .blank => .halt false
        | .sep => .step a .stay (.rewind e 0)
        | .bit b => .step a .stay (.delete (if b then o else z) deleteRewindMachine.start)
      | .peek _ e z o =>
        if a = .blank then .halt false
        else .step a .stay (.rewind (readBranch a e z o) 0)
      | _ => .halt false
    | .push next b phase =>
      liftMacro (Control.push next b)
        (fun ok => if ok then .step a .stay (.main next) else .halt false)
        ((pushMachine M.stacks b).code phase a)
    | .delete next phase =>
      liftMacro (Control.delete next)
        (fun ok => if ok then .step a .stay (.main next) else .halt false)
        (deleteRewindMachine.code phase a)
    | .rewind next phase =>
      liftMacro (Control.rewind next)
        (fun ok => if ok then .step a .stay (.main next) else .halt false)
        (rewindMachine.code phase a)
    | .finish b => .halt b

/-- A concrete machine containing the complete finite dispatch table. -/
def compiledController (M : StackMachine.Machine) : Machine :=
  compile (controller M) (controlEncoding M)

theorem compile_liftMacro {L : Type} (e : Encoding L) {n : Nat}
    (rename : Fin n → L) (next : L) (a : Symbol) (i : Instruction n) :
    compileOp e (liftMacro rename (fun b => if b then .step a .stay next else .halt false) i) =
      continueInstruction (fun q => e.encode (rename q)) (e.encode next) a i := by
  cases i with
  | halt b => cases b <;> rfl
  | step _ _ _ => rfl

theorem push_code (M : StackMachine.Machine) (next : Fin (M.states + 1))
    (b : Bool) (phase : Fin (M.stacks + 9)) (a : Symbol) :
    (compiledController M).code ((controlEncoding M).encode (.push next b phase)) a =
      continueInstruction (fun q => (controlEncoding M).encode (.push next b q))
        ((controlEncoding M).encode (.main next)) a ((pushMachine M.stacks b).code phase a) := by
  exact (compile_code (controller M) (controlEncoding M) (.push next b phase) a).trans
    (compile_liftMacro (controlEncoding M) (Control.push next b) (.main next) a _)

theorem delete_code (M : StackMachine.Machine) (next : Fin (M.states + 1))
    (phase : Fin 13) (a : Symbol) :
    (compiledController M).code ((controlEncoding M).encode (.delete next phase)) a =
      continueInstruction (fun q => (controlEncoding M).encode (.delete next q))
        ((controlEncoding M).encode (.main next)) a (deleteRewindMachine.code phase a) := by
  exact (compile_code (controller M) (controlEncoding M) (.delete next phase) a).trans
    (compile_liftMacro (controlEncoding M) (Control.delete next) (.main next) a _)

theorem rewind_code (M : StackMachine.Machine) (next : Fin (M.states + 1))
    (phase : Fin 2) (a : Symbol) :
    (compiledController M).code ((controlEncoding M).encode (.rewind next phase)) a =
      continueInstruction (fun q => (controlEncoding M).encode (.rewind next q))
        ((controlEncoding M).encode (.main next)) a (rewindMachine.code phase a) := by
  exact (compile_code (controller M) (controlEncoding M) (.rewind next phase) a).trans
    (compile_liftMacro (controlEncoding M) (Control.rewind next) (.main next) a _)

theorem seek_code (M : StackMachine.Machine) (source : Fin (M.states + 1))
    (phase : Fin (M.stacks + 2)) (a : Symbol) :
    (compiledController M).code ((controlEncoding M).encode (.seek source phase)) a =
      continueInstruction (fun q => (controlEncoding M).encode (.seek source q))
        ((controlEncoding M).encode (.inspect source)) a ((seekMachine M.stacks).code phase a) := by
  exact (compile_code (controller M) (controlEncoding M) (.seek source phase) a).trans
    (compile_liftMacro (controlEncoding M) (Control.seek source) (.inspect source) a _)

/-- A bounded halting assertion retaining a predicate on the actual returned
decision and tape. The bound always counts the concrete machine's instructions. -/
def HaltsWithin (N : Machine) (budget : Nat) (q : Fin (N.states + 1))
    (t : Tape) (post : Bool × Tape → Prop) : Prop :=
  ∃ time result, time ≤ budget ∧ Complexity.run N time ⟨q, t⟩ = some result ∧ post result

theorem HaltsWithin.mono {N : Machine} {budget budget' : Nat}
    {q : Fin (N.states + 1)} {t : Tape} {post : Bool × Tape → Prop}
    (h : HaltsWithin N budget q t post) (hb : budget ≤ budget') :
    HaltsWithin N budget' q t post := by
  obtain ⟨time, result, ht, hr, hp⟩ := h
  exact ⟨time, result, Nat.le_trans ht hb, hr, hp⟩

theorem HaltsWithin.post {N : Machine} {budget : Nat}
    {q : Fin (N.states + 1)} {t : Tape} {post post' : Bool × Tape → Prop}
    (h : HaltsWithin N budget q t post) (hp : ∀ result, post result → post' result) :
    HaltsWithin N budget q t post' := by
  obtain ⟨time, result, ht, hr, hp'⟩ := h
  exact ⟨time, result, ht, hr, hp result hp'⟩

theorem HaltsWithin.step {N : Machine} {budget : Nat}
    {q q' : Fin (N.states + 1)} {t : Tape} {a : Symbol} {d : Move}
    {post : Bool × Tape → Prop}
    (hc : N.code q t.read = .step a d q')
    (h : HaltsWithin N budget q' ((t.write a).move d) post) :
    HaltsWithin N (budget + 1) q t post := by
  obtain ⟨time, result, ht, hr, hp⟩ := h
  refine ⟨time + 1, result, by omega, ?_, hp⟩
  simpa only [Complexity.run, hc] using hr

theorem right_nonempty_of_read_ne_blank (t : Tape) (h : t.read ≠ .blank) :
    t.right ≠ [] := by
  intro he
  apply h
  simp [Tape.read, he]

/-- Execute a verified macro on any equivalent tape representation, then use
its actual returned tape in the continuation. The budget adds; equivalence does
not conceal any tape rewrite or zero-cost machine operation. -/
theorem macro_continue_equivalent (P N : Machine)
    (rename : Fin (P.states + 1) → Fin (N.states + 1))
    (next : Fin (N.states + 1))
    (hcode : ∀ q a, N.code (rename q) a = continueInstruction rename next a (P.code q a))
    (fuel budget : Nat) (q : Fin (P.states + 1)) (input output actual : Tape)
    (hrun : Complexity.run P fuel ⟨q, input⟩ = some (true, output))
    (hi : input.Equivalent actual) (ho : output.read ≠ .blank)
    (post : Bool × Tape → Prop)
    (hnext : ∀ t, output.Equivalent t → HaltsWithin N budget next t post) :
    HaltsWithin N (fuel + budget) (rename q) actual post := by
  obtain ⟨actualOutput, hr, he⟩ :=
    run_some_of_equivalent P fuel q input actual hi true output hrun
  obtain ⟨nextTime, result, ht, hn, hp⟩ := hnext actualOutput he
  have hne : actualOutput.right ≠ [] := by
    apply right_nonempty_of_read_ne_blank
    rw [← he.read]
    exact ho
  exact ⟨fuel + nextTime, result, by omega,
    run_continue P N rename next hcode fuel ⟨q, actual⟩ actualOutput hr hne nextTime result hn, hp⟩

def regionTape (before : List (List Bool)) (right : List Symbol) : Tape :=
  ⟨[.blank], stackPrefix before ++ .sep :: right⟩

@[simp] theorem regionTape_read (before : List (List Bool)) (right : List Symbol) :
    (regionTape before right).read = .sep := by
  cases before <;> rfl

theorem main_code_push (M : StackMachine.Machine) (q next : Fin (M.states + 1))
    (k : Fin (M.stacks + 1)) (b : Bool) (hc : M.code q = .push k b next) (a : Symbol) :
    (compiledController M).code ((controlEncoding M).encode (.main q)) a =
      .step a .stay ((controlEncoding M).encode (.push next b (pushStart M k b))) := by
  have hop : (controller M).code (.main q) a =
      .step a .stay (.push next b (pushStart M k b)) := by
    change (match M.code q with
      | .halt b => _
      | .goto next => _
      | .push k b next => _
      | .pop k _ _ _ | .peek k _ _ _ => _) = _
    rw [hc]
  exact (compile_code (controller M) (controlEncoding M) (.main q) a).trans
    (congrArg (compileOp (controlEncoding M)) hop)

/-- The source push instruction is implemented by actual target instructions,
including entry into the macro and its return to the main dispatcher. -/
theorem controller_push (M : StackMachine.Machine) (q next : Fin (M.states + 1))
    (k : Fin (M.stacks + 1)) (b : Bool) (hc : M.code q = .push k b next)
    (before : List (List Bool)) (hk : before.length = k.val) (right : List Symbol)
    (hr : ∀ a ∈ right, a ≠ .blank) (hne : right ≠ [])
    (actual : Tape) (hi : (regionTape before right).Equivalent actual)
    (budget : Nat) (post : Bool × Tape → Prop)
    (hnext : ∀ t, (regionTape before (.bit b :: right)).Equivalent t →
      HaltsWithin (compiledController M) budget ((controlEncoding M).encode (.main next)) t post) :
    HaltsWithin (compiledController M)
      ((2 * ((stackPrefix before).length + 1 + right.length) + 6 + budget) + 1)
      ((controlEncoding M).encode (.main q)) actual post := by
  have hcap : before.length ≤ M.stacks := by have := k.isLt; omega
  have hpush := push_register_run_general M.stacks before hcap b right hr hne
  have hrun : Complexity.run (pushMachine M.stacks b)
      (2 * ((stackPrefix before).length + 1 + right.length) + 6)
      ⟨pushStart M k b, regionTape before right⟩ =
      some (true, regionTape before (.bit b :: right)) := by
    simpa only [pushStart, hk, regionTape] using hpush
  have hmacro := macro_continue_equivalent (pushMachine M.stacks b) (compiledController M)
    (fun phase => (controlEncoding M).encode (.push next b phase))
    ((controlEncoding M).encode (.main next)) (push_code M next b)
    (2 * ((stackPrefix before).length + 1 + right.length) + 6) budget
    (pushStart M k b) (regionTape before right) (regionTape before (.bit b :: right)) actual
    hrun hi (by simp) post hnext
  have hneActual : actual.right ≠ [] := by
    apply right_nonempty_of_read_ne_blank
    rw [← hi.read]
    simp
  have hw : (actual.write actual.read).move .stay = actual := by
    simpa [Tape.move] using write_read_of_nonempty actual hneActual
  apply HaltsWithin.step (main_code_push M q next k b hc actual.read)
  rw [hw]
  exact hmacro

theorem main_code (M : StackMachine.Machine) (q : Fin (M.states + 1)) (a : Symbol) :
    (compiledController M).code ((controlEncoding M).encode (.main q)) a =
      compileOp (controlEncoding M)
        (match M.code q with
        | .halt b => .step a .right (.finish b)
        | .goto next => .step a .stay (.main next)
        | .push k b next => .step a .stay (.push next b (pushStart M k b))
        | .pop k _ _ _ | .peek k _ _ _ =>
          .step a .stay (.seek q ⟨k.val + 1, by have := k.isLt; omega⟩)) :=
  compile_code (controller M) (controlEncoding M) (.main q) a

theorem finish_code (M : StackMachine.Machine) (b : Bool) (a : Symbol) :
    (compiledController M).code ((controlEncoding M).encode (.finish b)) a = .halt b :=
  compile_code (controller M) (controlEncoding M) (.finish b) a

theorem controller_goto (M : StackMachine.Machine) (q next : Fin (M.states + 1))
    (hc : M.code q = .goto next) (t : Tape) (ht : t.read ≠ .blank)
    (budget : Nat) (post : Bool × Tape → Prop)
    (hn : HaltsWithin (compiledController M) budget
      ((controlEncoding M).encode (.main next)) t post) :
    HaltsWithin (compiledController M) (budget + 1)
      ((controlEncoding M).encode (.main q)) t post := by
  have hcode := main_code M q t.read
  rw [hc] at hcode
  apply HaltsWithin.step hcode
  have hw := write_read_of_nonempty t (right_nonempty_of_read_ne_blank t ht)
  simpa only [Tape.move, hw] using hn

theorem controller_halt (M : StackMachine.Machine) (q : Fin (M.states + 1))
    (b : Bool) (hc : M.code q = .halt b) (canonical actual : Tape)
    (hi : canonical.Equivalent actual) (ht : canonical.read ≠ .blank) :
    HaltsWithin (compiledController M) 2 ((controlEncoding M).encode (.main q)) actual
      (fun result => result.1 = b ∧ (canonical.move .right).Equivalent result.2) := by
  have hcode := main_code M q actual.read
  rw [hc] at hcode
  have hw : actual.write actual.read = actual := by
    apply write_read_of_nonempty
    apply right_nonempty_of_read_ne_blank
    rw [← hi.read]
    exact ht
  apply HaltsWithin.step hcode
  rw [hw]
  refine ⟨1, (b, actual.move .right), by omega, ?_, rfl, hi.move .right⟩
  simp only [Complexity.run, finish_code]

def seekedTape (before : List (List Bool)) (right : List Symbol) : Tape :=
  ⟨.sep :: ((stackPrefix before).reverse ++ [.blank]), right⟩

theorem controller_rewind (M : StackMachine.Machine) (next : Fin (M.states + 1))
    (before : List (List Bool)) (head : Symbol) (right : List Symbol)
    (hh : head ≠ .blank) (actual : Tape)
    (hi : (seekedTape before (head :: right)).Equivalent actual)
    (budget : Nat) (post : Bool × Tape → Prop)
    (hnext : ∀ t, (regionTape before (head :: right)).Equivalent t →
      HaltsWithin (compiledController M) budget ((controlEncoding M).encode (.main next)) t post) :
    HaltsWithin (compiledController M) ((stackPrefix before).length + 4 + budget)
      ((controlEncoding M).encode (.rewind next 0)) actual post := by
  exact macro_continue_equivalent rewindMachine (compiledController M)
    (fun phase => (controlEncoding M).encode (.rewind next phase))
    ((controlEncoding M).encode (.main next)) (rewind_code M next)
    ((stackPrefix before).length + 4) budget 0
    (seekedTape before (head :: right)) (regionTape before (head :: right)) actual
    (rewind_register_run before head right hh) hi (by simp) post hnext

theorem inspect_code_peek (M : StackMachine.Machine) (q e z o : Fin (M.states + 1))
    (k : Fin (M.stacks + 1)) (hc : M.code q = .peek k e z o)
    (a : Symbol) (ha : a ≠ .blank) :
    (compiledController M).code ((controlEncoding M).encode (.inspect q)) a =
      .step a .stay ((controlEncoding M).encode (.rewind (readBranch a e z o) 0)) := by
  have hop : (controller M).code (.inspect q) a =
      .step a .stay (.rewind (readBranch a e z o) 0) := by
    change (match M.code q with
      | .pop _ _ _ _ => _
      | .peek _ _ _ _ => _
      | _ => _) = _
    simp only [hc, ha, ↓reduceIte]
  exact (compile_code (controller M) (controlEncoding M) (.inspect q) a).trans
    (congrArg (compileOp (controlEncoding M)) hop)

theorem controller_inspect_peek (M : StackMachine.Machine)
    (q e z o : Fin (M.states + 1)) (k : Fin (M.stacks + 1))
    (hc : M.code q = .peek k e z o) (before : List (List Bool))
    (head : Symbol) (right : List Symbol) (hh : head ≠ .blank)
    (actual : Tape) (hi : (seekedTape before (head :: right)).Equivalent actual)
    (budget : Nat) (post : Bool × Tape → Prop)
    (hnext : ∀ t, (regionTape before (head :: right)).Equivalent t →
      HaltsWithin (compiledController M) budget
        ((controlEncoding M).encode (.main (readBranch head e z o))) t post) :
    HaltsWithin (compiledController M) (((stackPrefix before).length + 4 + budget) + 1)
      ((controlEncoding M).encode (.inspect q)) actual post := by
  have hread : actual.read = head := hi.read.symm
  have hcode := inspect_code_peek M q e z o k hc actual.read (by simpa [hread] using hh)
  rw [hread] at hcode
  have hw : (actual.write head).move .stay = actual := by
    rw [← hread]
    simpa [Tape.move] using write_read_of_nonempty actual
      (right_nonempty_of_read_ne_blank actual (by simpa [hread] using hh))
  apply HaltsWithin.step (by simpa only [hread] using hcode)
  rw [hw]
  exact controller_rewind M (readBranch head e z o) before head right hh actual hi budget post hnext

theorem controller_seek (M : StackMachine.Machine) (q e z o : Fin (M.states + 1))
    (k : Fin (M.stacks + 1))
    (hc : M.code q = .pop k e z o ∨ M.code q = .peek k e z o)
    (before : List (List Bool)) (hk : before.length = k.val)
    (head : Symbol) (right : List Symbol) (hh : head ≠ .blank)
    (actual : Tape) (hi : (regionTape before (head :: right)).Equivalent actual)
    (budget : Nat) (post : Bool × Tape → Prop)
    (hnext : ∀ t, (seekedTape before (head :: right)).Equivalent t →
      HaltsWithin (compiledController M) budget ((controlEncoding M).encode (.inspect q)) t post) :
    HaltsWithin (compiledController M) (((stackPrefix before).length + 2 + budget) + 1)
      ((controlEncoding M).encode (.main q)) actual post := by
  have hb : before.length + 1 < M.stacks + 1 + 1 := by have := k.isLt; omega
  have hs := seek_run M.stacks before hb [.blank] (head :: right)
  have hs' : Complexity.run (seekMachine M.stacks) ((stackPrefix before).length + 2)
      ⟨⟨k.val + 1, by change k.val + 1 < M.stacks + 1 + 1; have := k.isLt; omega⟩,
        regionTape before (head :: right)⟩ =
      some (true, seekedTape before (head :: right)) := by
    simpa only [regionTape, seekedTape, hk] using hs
  have hmacro := macro_continue_equivalent (seekMachine M.stacks) (compiledController M)
    (fun phase => (controlEncoding M).encode (.seek q phase))
    ((controlEncoding M).encode (.inspect q)) (seek_code M q)
    ((stackPrefix before).length + 2) budget
    ⟨k.val + 1, by change k.val + 1 < M.stacks + 1 + 1; have := k.isLt; omega⟩
    (regionTape before (head :: right)) (seekedTape before (head :: right)) actual
    hs' hi hh post hnext
  have hcode : (compiledController M).code ((controlEncoding M).encode (.main q)) actual.read =
      .step actual.read .stay ((controlEncoding M).encode (.seek q
        ⟨k.val + 1, by have := k.isLt; omega⟩)) := by
    have h := main_code M q actual.read
    rcases hc with hc | hc <;> rw [hc] at h <;> exact h
  have hw : (actual.write actual.read).move .stay = actual := by
    simpa [Tape.move] using write_read_of_nonempty actual
      (right_nonempty_of_read_ne_blank actual (by rw [← hi.read]; simp))
  apply HaltsWithin.step hcode
  rw [hw]
  exact hmacro

theorem inspect_code_pop (M : StackMachine.Machine) (q e z o : Fin (M.states + 1))
    (k : Fin (M.stacks + 1)) (hc : M.code q = .pop k e z o) (a : Symbol) :
    (compiledController M).code ((controlEncoding M).encode (.inspect q)) a =
      compileOp (controlEncoding M) (match a with
        | .blank => .halt false
        | .sep => .step a .stay (.rewind e 0)
        | .bit b => .step a .stay (.delete (if b then o else z) deleteRewindMachine.start)) := by
  have hop : (controller M).code (.inspect q) a =
      (match a with
        | .blank => .halt false
        | .sep => .step a .stay (.rewind e 0)
        | .bit b => .step a .stay (.delete (if b then o else z) deleteRewindMachine.start)) := by
    change (match M.code q with
      | .pop _ _ _ _ => _
      | .peek _ _ _ _ => _
      | _ => _) = _
    rw [hc]
  exact (compile_code (controller M) (controlEncoding M) (.inspect q) a).trans
    (congrArg (compileOp (controlEncoding M)) hop)

theorem controller_inspect_pop_empty (M : StackMachine.Machine)
    (q e z o : Fin (M.states + 1)) (k : Fin (M.stacks + 1))
    (hc : M.code q = .pop k e z o) (before : List (List Bool)) (right : List Symbol)
    (actual : Tape) (hi : (seekedTape before (.sep :: right)).Equivalent actual)
    (budget : Nat) (post : Bool × Tape → Prop)
    (hnext : ∀ t, (regionTape before (.sep :: right)).Equivalent t →
      HaltsWithin (compiledController M) budget ((controlEncoding M).encode (.main e)) t post) :
    HaltsWithin (compiledController M) (((stackPrefix before).length + 4 + budget) + 1)
      ((controlEncoding M).encode (.inspect q)) actual post := by
  have hread : actual.read = .sep := hi.read.symm
  have hcode := inspect_code_pop M q e z o k hc actual.read
  rw [hread] at hcode
  have hw : (actual.write .sep).move .stay = actual := by
    rw [← hread]
    simpa [Tape.move] using write_read_of_nonempty actual
      (right_nonempty_of_read_ne_blank actual (by simp [hread]))
  have hcode' : (compiledController M).code ((controlEncoding M).encode (.inspect q)) actual.read =
      .step .sep .stay ((controlEncoding M).encode (.rewind e 0)) := by
    rw [hread]
    exact hcode
  apply HaltsWithin.step hcode'
  rw [hw]
  exact controller_rewind M e before .sep right (by simp) actual hi budget post hnext

theorem controller_inspect_pop_bit (M : StackMachine.Machine)
    (q e z o : Fin (M.states + 1)) (k : Fin (M.stacks + 1))
    (hc : M.code q = .pop k e z o) (before : List (List Bool))
    (bit : Bool) (right : List Symbol) (hr : ∀ a ∈ right, a ≠ .blank)
    (actual : Tape) (hi : (seekedTape before (.bit bit :: right)).Equivalent actual)
    (budget : Nat) (post : Bool × Tape → Prop)
    (hnext : ∀ t, (regionTape before right).Equivalent t →
      HaltsWithin (compiledController M) budget
        ((controlEncoding M).encode (.main (if bit then o else z))) t post) :
    HaltsWithin (compiledController M) (((stackPrefix before).length + 4 * right.length + 9 + budget) + 1)
      ((controlEncoding M).encode (.inspect q)) actual post := by
  have hpop := pop_register_run before bit right hr
  have hpop' : Complexity.run deleteRewindMachine
      ((stackPrefix before).length + 4 * right.length + 9)
      ⟨deleteRewindMachine.start, seekedTape before (.bit bit :: right)⟩ =
      some (true, regionTape before (right ++ [Symbol.blank, Symbol.blank])) := hpop
  have hpad : (regionTape before (right ++ [.blank, .blank])).Equivalent
      (regionTape before right) := by
    refine ⟨BlankEq.refl _, ?_⟩
    simpa [regionTape, List.append_assoc] using
      BlankEq.append_blanks (stackPrefix before ++ .sep :: right) 2
  have hmacro := macro_continue_equivalent deleteRewindMachine (compiledController M)
    (fun phase => (controlEncoding M).encode (.delete (if bit then o else z) phase))
    ((controlEncoding M).encode (.main (if bit then o else z))) (delete_code M _)
    ((stackPrefix before).length + 4 * right.length + 9) budget deleteRewindMachine.start
    (seekedTape before (.bit bit :: right)) (regionTape before (right ++ [Symbol.blank, Symbol.blank])) actual
    hpop' hi (by simp) post (fun t ht => hnext t (hpad.symm.trans ht))
  have hread : actual.read = .bit bit := hi.read.symm
  have hcode := inspect_code_pop M q e z o k hc actual.read
  rw [hread] at hcode
  have hw : (actual.write (.bit bit)).move .stay = actual := by
    rw [← hread]
    simpa [Tape.move] using write_read_of_nonempty actual
      (right_nonempty_of_read_ne_blank actual (by simp [hread]))
  have hcode' : (compiledController M).code ((controlEncoding M).encode (.inspect q)) actual.read =
      .step (.bit bit) .stay
        ((controlEncoding M).encode (.delete (if bit then o else z) deleteRewindMachine.start)) := by
    rw [hread]
    exact hcode
  apply HaltsWithin.step hcode'
  rw [hw]
  exact hmacro

theorem controller_peek (M : StackMachine.Machine) (q e z o : Fin (M.states + 1))
    (k : Fin (M.stacks + 1)) (hc : M.code q = .peek k e z o)
    (before : List (List Bool)) (hk : before.length = k.val)
    (head : Symbol) (right : List Symbol) (hh : head ≠ .blank)
    (actual : Tape) (hi : (regionTape before (head :: right)).Equivalent actual)
    (budget : Nat) (post : Bool × Tape → Prop)
    (hnext : ∀ t, (regionTape before (head :: right)).Equivalent t →
      HaltsWithin (compiledController M) budget
        ((controlEncoding M).encode (.main (readBranch head e z o))) t post) :
    HaltsWithin (compiledController M) (2 * (stackPrefix before).length + 8 + budget)
      ((controlEncoding M).encode (.main q)) actual post := by
  have h := controller_seek M q e z o k (Or.inr hc) before hk head right hh actual hi
    (((stackPrefix before).length + 4 + budget) + 1) post (fun t ht =>
      controller_inspect_peek M q e z o k hc before head right hh t ht budget post hnext)
  exact h.mono (by omega)

theorem controller_pop_empty (M : StackMachine.Machine) (q e z o : Fin (M.states + 1))
    (k : Fin (M.stacks + 1)) (hc : M.code q = .pop k e z o)
    (before : List (List Bool)) (hk : before.length = k.val) (right : List Symbol)
    (actual : Tape) (hi : (regionTape before (.sep :: right)).Equivalent actual)
    (budget : Nat) (post : Bool × Tape → Prop)
    (hnext : ∀ t, (regionTape before (.sep :: right)).Equivalent t →
      HaltsWithin (compiledController M) budget ((controlEncoding M).encode (.main e)) t post) :
    HaltsWithin (compiledController M) (2 * (stackPrefix before).length + 8 + budget)
      ((controlEncoding M).encode (.main q)) actual post := by
  have h := controller_seek M q e z o k (Or.inl hc) before hk .sep right (by simp) actual hi
    (((stackPrefix before).length + 4 + budget) + 1) post (fun t ht =>
      controller_inspect_pop_empty M q e z o k hc before right t ht budget post hnext)
  exact h.mono (by omega)

theorem controller_pop_bit (M : StackMachine.Machine) (q e z o : Fin (M.states + 1))
    (k : Fin (M.stacks + 1)) (hc : M.code q = .pop k e z o)
    (before : List (List Bool)) (hk : before.length = k.val)
    (bit : Bool) (right : List Symbol) (hr : ∀ a ∈ right, a ≠ .blank)
    (actual : Tape) (hi : (regionTape before (.bit bit :: right)).Equivalent actual)
    (budget : Nat) (post : Bool × Tape → Prop)
    (hnext : ∀ t, (regionTape before right).Equivalent t →
      HaltsWithin (compiledController M) budget
        ((controlEncoding M).encode (.main (if bit then o else z))) t post) :
    HaltsWithin (compiledController M)
      (2 * (stackPrefix before).length + 4 * right.length + 13 + budget)
      ((controlEncoding M).encode (.main q)) actual post := by
  have h := controller_seek M q e z o k (Or.inl hc) before hk (.bit bit) right (by simp) actual hi
    (((stackPrefix before).length + 4 * right.length + 9 + budget) + 1) post (fun t ht =>
      controller_inspect_pop_bit M q e z o k hc before bit right hr t ht budget post hnext)
  exact h.mono (by omega)

/-- Enough capacity for every remaining possible one-bit push. -/
def Room {stacks : Nat} (r : StackMachine.Registers stacks) (fuel capacity : Nat) : Prop :=
  ∀ k, (r k).length + fuel ≤ capacity

theorem Room.bound {stacks fuel capacity : Nat} {r : StackMachine.Registers stacks}
    (h : Room r fuel capacity) : ∀ k, (r k).length ≤ capacity := by
  intro k
  have := h k
  omega

theorem Room.next {stacks fuel capacity : Nat} {r : StackMachine.Registers stacks}
    (h : Room r (fuel + 1) capacity) : Room r fuel capacity := by
  intro k
  have := h k
  omega

theorem Room.push {stacks fuel capacity : Nat} {r : StackMachine.Registers stacks}
    (h : Room r (fuel + 1) capacity) (j : Fin (stacks + 1)) (b : Bool) :
    Room (StackMachine.set r j (b :: r j)) fuel capacity := by
  intro k
  by_cases hk : k = j
  · subst k
    simpa only [StackMachine.set_same, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 fuel] using h j
  · simpa only [StackMachine.set_other _ hk] using h.next k

theorem Room.pop {stacks fuel capacity : Nat} {r : StackMachine.Registers stacks}
    (h : Room r (fuel + 1) capacity) (j : Fin (stacks + 1)) :
    Room (StackMachine.set r j (r j).tail) fuel capacity := by
  intro k
  by_cases hk : k = j
  · subst k
    simp only [StackMachine.set_same, List.length_tail]
    have := h j
    omega
  · simpa only [StackMachine.set_other _ hk] using h.next k

def instructionBudget (M : StackMachine.Machine) (capacity : Nat) : Nat :=
  4 * ((M.stacks + 1) * (capacity + 1) + 1) + 13

theorem homeTape_region {stacks : Nat} (r : StackMachine.Registers stacks)
    (k : Fin (stacks + 1)) :
    StackEncoding.homeTape r = regionTape (StackEncoding.before r k) (StackEncoding.suffix r k) := by
  unfold StackEncoding.homeTape regionTape
  rw [StackEncoding.encodeRegisters_split r k]

theorem homeTape_set_region {stacks : Nat} (r : StackMachine.Registers stacks)
    (k : Fin (stacks + 1)) (value : List Bool) :
    StackEncoding.homeTape (StackMachine.set r k value) =
      regionTape (StackEncoding.before r k) (value.map Symbol.bit ++ StackEncoding.tail r k) := by
  unfold StackEncoding.homeTape regionTape
  rw [StackEncoding.encodeRegisters_set]

theorem encodeRegisters_split_length {stacks : Nat} (r : StackMachine.Registers stacks)
    (k : Fin (stacks + 1)) :
    (StackEncoding.encodeRegisters r).length =
      (stackPrefix (StackEncoding.before r k)).length + 1 + (StackEncoding.suffix r k).length := by
  rw [StackEncoding.encodeRegisters_split r k]
  simp only [List.length_append, List.length_cons]
  omega

theorem set_current {stacks : Nat} (r : StackMachine.Registers stacks)
    (k : Fin (stacks + 1)) : StackMachine.set r k (r k) = r := by
  funext j
  by_cases hj : j = k <;> simp [StackMachine.set, hj]

def OutputMatches {stacks : Nat} (source : Bool × StackMachine.Registers stacks)
    (target : Bool × Tape) : Prop :=
  target.1 = source.1 ∧ target.2.output = StackMachine.output source.2

theorem readBranch_suffix {stacks : Nat} {L : Type} (r : StackMachine.Registers stacks)
    (k : Fin (stacks + 1)) (e z o : L) :
    readBranch ((StackEncoding.suffix r k).headD .blank) e z o =
      StackMachine.branch (r k) e z o := by
  cases hx : r k with
  | nil =>
    simp only [StackEncoding.suffix, hx, List.map_nil, List.nil_append, StackMachine.branch]
    rw [StackEncoding.tail_head]
    rfl
  | cons b rest => cases b <;> simp [StackEncoding.suffix, hx, readBranch, StackMachine.branch]

/-- Full bounded simulation of the finite stack controller on encoded
registers. The capacity hypothesis supplies a uniform linear bound for every
tape macro throughout the source computation. -/
theorem controller_simulates (M : StackMachine.Machine) (fuel : Nat)
    (c : StackMachine.Config M) (result : Bool × StackMachine.Registers M.stacks)
    (hrun : StackMachine.run M fuel c = some result) (capacity : Nat)
    (hroom : Room c.registers fuel capacity) (actual : Tape)
    (hi : (StackEncoding.homeTape c.registers).Equivalent actual) :
    HaltsWithin (compiledController M) (fuel * instructionBudget M capacity)
      ((controlEncoding M).encode (.main c.state)) actual (OutputMatches result) := by
  induction fuel generalizing c actual with
  | zero => simp [StackMachine.run] at hrun
  | succ fuel ih =>
    have hlength := StackEncoding.encodeRegisters_length_le c.registers capacity hroom.bound
    have hcost : 4 * (StackEncoding.encodeRegisters c.registers).length + 13 ≤
        instructionBudget M capacity :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 4 hlength) 13
    cases hc : M.code c.state with
    | halt b =>
      have he : (b, c.registers) = result := by simpa [StackMachine.run, hc] using hrun
      rw [← he]
      have hh := controller_halt M c.state b hc (StackEncoding.homeTape c.registers)
        actual hi (by simp)
      have hh' := hh.post (fun out hout => show OutputMatches (b, c.registers) out from
        ⟨hout.1, hout.2.output.symm.trans (StackEncoding.output_move_right c.registers)⟩)
      apply hh'.mono
      rw [Nat.succ_mul fuel (instructionBudget M capacity)]
      omega
    | goto next =>
      simp only [StackMachine.run, hc] at hrun
      have hn := ih ⟨next, c.registers⟩ hrun hroom.next actual hi
      have hh := controller_goto M c.state next hc actual
        (by rw [← hi.read]; simp) (fuel * instructionBudget M capacity) _ hn
      apply hh.mono
      rw [Nat.succ_mul fuel (instructionBudget M capacity)]
      omega
    | push k b next =>
      simp only [StackMachine.run, hc] at hrun
      have hsplit := encodeRegisters_split_length c.registers k
      have hin : (regionTape (StackEncoding.before c.registers k)
          (StackEncoding.suffix c.registers k)).Equivalent actual := by
        rw [← homeTape_region]
        exact hi
      have hn : ∀ t, (regionTape (StackEncoding.before c.registers k)
          (.bit b :: StackEncoding.suffix c.registers k)).Equivalent t →
          HaltsWithin (compiledController M) (fuel * instructionBudget M capacity)
            ((controlEncoding M).encode (.main next)) t (OutputMatches result) := by
        intro t ht
        apply ih ⟨next, StackMachine.set c.registers k (b :: c.registers k)⟩
          hrun (hroom.push k b) t
        rw [homeTape_set_region]
        simpa only [List.map_cons, List.cons_append, StackEncoding.suffix] using ht
      have hh := controller_push M c.state next k b hc (StackEncoding.before c.registers k)
        (StackEncoding.before_length ..) (StackEncoding.suffix c.registers k)
        (StackEncoding.suffix_nonblank c.registers k) (StackEncoding.suffix_ne_nil c.registers k)
        actual hin (fuel * instructionBudget M capacity) _ hn
      apply hh.mono
      rw [Nat.succ_mul fuel (instructionBudget M capacity)]
      omega
    | peek k e z o =>
      simp only [StackMachine.run, hc] at hrun
      have hsplit := encodeRegisters_split_length c.registers k
      obtain ⟨head, rest, hs⟩ : ∃ head rest,
          StackEncoding.suffix c.registers k = head :: rest := by
        cases hs : StackEncoding.suffix c.registers k with
        | nil => exact False.elim (StackEncoding.suffix_ne_nil c.registers k hs)
        | cons a xs => exact ⟨a, xs, rfl⟩
      have hhhead : head ≠ .blank :=
        StackEncoding.suffix_nonblank c.registers k head (by simp [hs])
      have hb : readBranch head e z o = StackMachine.branch (c.registers k) e z o := by
        simpa [hs] using readBranch_suffix c.registers k e z o
      have hin : (regionTape (StackEncoding.before c.registers k) (head :: rest)).Equivalent actual := by
        rw [← hs, ← homeTape_region]
        exact hi
      have hn : ∀ t, (regionTape (StackEncoding.before c.registers k) (head :: rest)).Equivalent t →
          HaltsWithin (compiledController M) (fuel * instructionBudget M capacity)
            ((controlEncoding M).encode (.main (readBranch head e z o))) t (OutputMatches result) := by
        intro t ht
        rw [hb]
        apply ih ⟨StackMachine.branch (c.registers k) e z o, c.registers⟩ hrun hroom.next t
        rw [homeTape_region c.registers k, hs]
        exact ht
      have hh := controller_peek M c.state e z o k hc (StackEncoding.before c.registers k)
        (StackEncoding.before_length ..) head rest hhhead actual hin
        (fuel * instructionBudget M capacity) _ hn
      apply hh.mono
      rw [Nat.succ_mul fuel (instructionBudget M capacity)]
      omega
    | pop k e z o =>
      simp only [StackMachine.run, hc] at hrun
      have hsplit := encodeRegisters_split_length c.registers k
      cases hx : c.registers k with
      | nil =>
        have hset : StackMachine.set c.registers k [] = c.registers := by
          rw [← hx]
          exact set_current c.registers k
        have hr : StackMachine.run M fuel ⟨e, c.registers⟩ = some result := by
          simpa only [hx, StackMachine.branch, List.tail_nil, hset] using hrun
        obtain ⟨rest, htail⟩ := StackEncoding.tail_eq_cons c.registers k
        have hs : StackEncoding.suffix c.registers k = .sep :: rest := by
          simp [StackEncoding.suffix, hx, htail]
        have hin : (regionTape (StackEncoding.before c.registers k) (.sep :: rest)).Equivalent actual := by
          rw [← hs, ← homeTape_region]
          exact hi
        have hn : ∀ t, (regionTape (StackEncoding.before c.registers k) (.sep :: rest)).Equivalent t →
            HaltsWithin (compiledController M) (fuel * instructionBudget M capacity)
              ((controlEncoding M).encode (.main e)) t (OutputMatches result) := by
          intro t ht
          apply ih ⟨e, c.registers⟩ hr hroom.next t
          rw [homeTape_region c.registers k, hs]
          exact ht
        have hh := controller_pop_empty M c.state e z o k hc (StackEncoding.before c.registers k)
          (StackEncoding.before_length ..) rest actual hin (fuel * instructionBudget M capacity) _ hn
        apply hh.mono
        rw [Nat.succ_mul fuel (instructionBudget M capacity)]
        omega
      | cons b rest =>
        let remaining := rest.map Symbol.bit ++ StackEncoding.tail c.registers k
        have hs : StackEncoding.suffix c.registers k = .bit b :: remaining := by
          simp only [StackEncoding.suffix, hx, List.map_cons, List.cons_append, remaining]
        have hr : StackMachine.run M fuel
            ⟨if b then o else z, StackMachine.set c.registers k rest⟩ = some result := by
          cases b <;> simpa only [hx, StackMachine.branch, List.tail_cons, Bool.false_eq_true,
            ↓reduceIte] using hrun
        have hroom' : Room (StackMachine.set c.registers k rest) fuel capacity := by
          simpa only [hx, List.tail_cons] using hroom.pop k
        have hremaining : ∀ a ∈ remaining, a ≠ .blank := by
          intro a ha
          exact StackEncoding.suffix_nonblank c.registers k a (by simp [hs, ha])
        have hin : (regionTape (StackEncoding.before c.registers k) (.bit b :: remaining)).Equivalent actual := by
          rw [← hs, ← homeTape_region]
          exact hi
        have hn : ∀ t, (regionTape (StackEncoding.before c.registers k) remaining).Equivalent t →
            HaltsWithin (compiledController M) (fuel * instructionBudget M capacity)
              ((controlEncoding M).encode (.main (if b then o else z))) t (OutputMatches result) := by
          intro t ht
          apply ih ⟨if b then o else z, StackMachine.set c.registers k rest⟩ hr hroom' t
          rw [homeTape_set_region]
          exact ht
        have hh := controller_pop_bit M c.state e z o k hc (StackEncoding.before c.registers k)
          (StackEncoding.before_length ..) b remaining hremaining actual hin
          (fuel * instructionBudget M capacity) _ hn
        apply hh.mono
        have hslen : (StackEncoding.suffix c.registers k).length = remaining.length + 1 := by
          rw [hs]
          rfl
        rw [Nat.succ_mul fuel (instructionBudget M capacity)]
        omega

end Complexity.StackSimulation
