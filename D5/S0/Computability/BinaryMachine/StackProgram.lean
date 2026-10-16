/- GID: D5/S0/Computability/BinaryMachine/StackProgram
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/StackProgram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed finite binary machine StackProgram supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4,
immutable revision 3e603e795b44fedcf7d6dd65b7d1e30547ead925, Complexity/StackProgram.lean.
Apache-2.0; full license and finite replacement contract:
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Only module imports and this repository header are adapted.
-/

public import D5.S0.Computability.BinaryMachine.StackMachine
import Lean.Elab.Tactic.Omega

/-!
# A finite-control stack-program algebra

Control labels may be structured types, but compilation requires an explicit
encoding into a finite set.  The instruction syntax contains only halt, jump,
one-bit push, pop, and peek.  In particular it has no instruction executing an
arbitrary function on words or natural numbers.

Sequential composition and feedback below construct finite instruction graphs.
Their counted semantics includes every instruction, including jumps and halts.
-/

@[expose] public section

namespace Complexity.StackProgram

open Complexity.StackMachine (Registers set branch)

inductive Op (stacks : Nat) (Label : Type) where
  | halt (decision : Bool)
  | goto (next : Label)
  | push (register : Fin (stacks + 1)) (value : Bool) (next : Label)
  | pop (register : Fin (stacks + 1)) (empty zero one : Label)
  | peek (register : Fin (stacks + 1)) (empty zero one : Label)

structure Program (stacks : Nat) (Label : Type) where
  start : Label
  code : Label → Op stacks Label

/-- An explicit finite representation of all source control labels. -/
structure Encoding (Label : Type) where
  states : Nat
  encode : Label → Fin (states + 1)
  decode : Fin (states + 1) → Label
  decode_encode : ∀ q, decode (encode q) = q

def Encoding.unit : Encoding Unit where
  states := 0
  encode := fun _ => 0
  decode := fun _ => ()
  decode_encode := by intro q; cases q; rfl

def Encoding.fin (n : Nat) : Encoding (Fin (n + 1)) where
  states := n
  encode := id
  decode := id
  decode_encode := by intro q; rfl

def Encoding.bool : Encoding Bool where
  states := 1
  encode := fun b => if b then 1 else 0
  decode := fun q => q.val == 1
  decode_encode := by intro q; cases q <;> rfl

def Encoding.sum {A B : Type} (a : Encoding A) (b : Encoding B) : Encoding (Sum A B) where
  states := a.states + b.states + 1
  encode := fun q => match q with
    | .inl x => ⟨(a.encode x).val, by have := (a.encode x).isLt; omega⟩
    | .inr y => ⟨a.states + 1 + (b.encode y).val, by have := (b.encode y).isLt; omega⟩
  decode := fun q => if h : q.val < a.states + 1 then
      .inl (a.decode ⟨q.val, h⟩)
    else .inr (b.decode ⟨q.val - (a.states + 1), by have := q.isLt; omega⟩)
  decode_encode := by
    intro q
    cases q with
    | inl x => simp [a.decode_encode]
    | inr y =>
      have hn : ¬ a.states + 1 + (b.encode y).val < a.states + 1 := by omega
      simp [hn, b.decode_encode]

def step {k : Nat} {L : Type} (p : Program k L) (q : L) (r : Registers k) :
    Sum (Bool × Registers k) (L × Registers k) :=
  match p.code q with
  | .halt b => .inl (b, r)
  | .goto q' => .inr (q', r)
  | .push j b q' => .inr (q', set r j (b :: r j))
  | .pop j e z o => .inr (branch (r j) e z o, set r j (r j).tail)
  | .peek j e z o => .inr (branch (r j) e z o, r)

/-- Every constructor accounts for exactly one primitive instruction. -/
inductive Exec {k : Nat} {L : Type} (p : Program k L) :
    L → Registers k → Nat → (Bool × Registers k) → Prop where
  | halt {q r result} (h : step p q r = .inl result) : Exec p q r 1 result
  | next {q r q' r' t result}
      (h : step p q r = .inr (q', r')) (rest : Exec p q' r' t result) :
      Exec p q r (t + 1) result

def run {k : Nat} {L : Type} (p : Program k L) :
    Nat → L → Registers k → Option (Bool × Registers k)
  | 0, _, _ => none
  | fuel + 1, q, r => match step p q r with
    | .inl result => some result
    | .inr (q', r') => run p fuel q' r'

theorem Exec.run {k : Nat} {L : Type} {p : Program k L} {q r t result}
    (h : Exec p q r t result) : run p t q r = some result := by
  induction h with
  | halt hs => simp [StackProgram.run, hs]
  | next hs _ ih => simp [StackProgram.run, hs, ih]

theorem run_exists_exec {k : Nat} {L : Type} (p : Program k L)
    (fuel : Nat) (q : L) (r : Registers k) (result : Bool × Registers k)
    (h : run p fuel q r = some result) :
    ∃ t, t ≤ fuel ∧ Exec p q r t result := by
  induction fuel generalizing q r with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hs : step p q r with
    | inl out =>
      have heq : out = result := by simpa [run, hs] using h
      subst out
      exact ⟨1, by omega, .halt hs⟩
    | inr next =>
      obtain ⟨q', r'⟩ := next
      have hr : run p fuel q' r' = some result := by simpa [run, hs] using h
      obtain ⟨t, ht, he⟩ := ih q' r' hr
      exact ⟨t + 1, by omega, .next hs he⟩

def compileOp {k : Nat} {L : Type} (e : Encoding L) :
    Op k L → Complexity.StackMachine.Instruction k e.states
  | .halt b => .halt b
  | .goto q => .goto (e.encode q)
  | .push j b q => .push j b (e.encode q)
  | .pop j a b c => .pop j (e.encode a) (e.encode b) (e.encode c)
  | .peek j a b c => .peek j (e.encode a) (e.encode b) (e.encode c)

def compile {k : Nat} {L : Type} (p : Program k L) (e : Encoding L) :
    Complexity.StackMachine.Machine where
  stacks := k
  states := e.states
  start := e.encode p.start
  code := fun q => compileOp e (p.code (e.decode q))

theorem branch_map {A B : Type} (f : A → B) (xs : List Bool) (e z o : A) :
    branch xs (f e) (f z) (f o) = f (branch xs e z o) := by
  cases xs with
  | nil => rfl
  | cons b xs => cases b <;> rfl

/-- Compilation preserves the exact fuelled interpreter, not just eventual acceptance. -/
theorem compile_run {k : Nat} {L : Type} (p : Program k L) (e : Encoding L)
    (fuel : Nat) (q : L) (r : Registers k) :
    Complexity.StackMachine.run (compile p e) fuel ⟨e.encode q, r⟩ = run p fuel q r := by
  induction fuel generalizing q r with
  | zero => rfl
  | succ fuel ih =>
    cases hc : p.code q <;>
      simp [Complexity.StackMachine.run, compile, e.decode_encode, compileOp,
        run, step, hc, branch_map]
    all_goals exact ih _ _

theorem compile_exec {k : Nat} {L : Type} {p : Program k L} (e : Encoding L)
    {q r t result} (h : Exec p q r t result) :
    Complexity.StackMachine.run (compile p e) t ⟨e.encode q, r⟩ = some result := by
  rw [compile_run]
  exact h.run

/-- Relabel finite control and replace terminal instructions by explicit handlers. -/
def mapOp {k : Nat} {A B : Type} (f : A → B) (onHalt : Bool → Op k B) : Op k A → Op k B
  | .halt b => onHalt b
  | .goto q => .goto (f q)
  | .push j b q => .push j b (f q)
  | .pop j e z o => .pop j (f e) (f z) (f o)
  | .peek j e z o => .peek j (f e) (f z) (f o)

/-- Success returns into the second program; failure returns immediately. -/
def seq {k : Nat} {A B : Type} (p : Program k A) (q : Program k B) : Program k (Sum A B) where
  start := .inl p.start
  code := fun label => match label with
    | .inl a => mapOp Sum.inl (fun b => if b then .goto (.inr q.start) else .halt false) (p.code a)
    | .inr b => mapOp Sum.inr Op.halt (q.code b)

theorem step_seq_left {k : Nat} {A B : Type} (p : Program k A) (q : Program k B)
    (a : A) (r : Registers k) :
    step (seq p q) (.inl a) r = match step p a r with
      | .inl (true, out) => .inr (.inr q.start, out)
      | .inl (false, out) => .inl (false, out)
      | .inr (a', out) => .inr (.inl a', out) := by
  cases hc : p.code a with
  | halt b => cases b <;> simp [step, seq, hc, mapOp]
  | goto a' => simp [step, seq, hc, mapOp]
  | push j b a' => simp [step, seq, hc, mapOp]
  | pop j e z o => simp [step, seq, hc, mapOp, branch_map]
  | peek j e z o => simp [step, seq, hc, mapOp, branch_map]

theorem step_seq_right {k : Nat} {A B : Type} (p : Program k A) (q : Program k B)
    (b : B) (r : Registers k) :
    step (seq p q) (.inr b) r = match step q b r with
      | .inl result => .inl result
      | .inr (b', out) => .inr (.inr b', out) := by
  cases hc : q.code b <;> simp [step, seq, hc, mapOp, branch_map]

theorem exec_seq_right {k : Nat} {A B : Type} (p : Program k A) (q : Program k B)
    {b r t result} (h : Exec q b r t result) : Exec (seq p q) (.inr b) r t result := by
  induction h with
  | halt hs => exact .halt (by rw [step_seq_right, hs])
  | next hs _ ih => exact .next (by rw [step_seq_right, hs]) ih

/-- A control-flow simulation with an explicitly counted terminal continuation. -/
theorem exec_link {k : Nat} {A B : Type} (p : Program k A) (q : Program k B)
    (f : A → B) {a r t result s target} (h : Exec p a r t result)
    (hstep : ∀ a r a' r', step p a r = .inr (a', r') →
      step q (f a) r = .inr (f a', r'))
    (hhalt : ∀ a r, step p a r = .inl result → Exec q (f a) r (s + 1) target) :
    Exec q (f a) r (t + s) target := by
  induction h with
  | halt hs => simpa [Nat.add_comm] using hhalt _ _ hs
  | next hs _ ih =>
    have hh := Exec.next (hstep _ _ _ _ hs) (ih hhalt)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem exec_seq_failure {k : Nat} {A B : Type} (p : Program k A) (q : Program k B)
    {a r t out} (h : Exec p a r t (false, out)) :
    Exec (seq p q) (.inl a) r t (false, out) := by
  have hh := exec_link p (seq p q) Sum.inl (s := 0) h
    (by intro a r a' r' hs; rw [step_seq_left, hs])
    (by intro a r hs; exact .halt (by rw [step_seq_left, hs]))
  simpa using hh

/-- Sequential composition adds exact instruction counts, including its connecting jump. -/
theorem exec_seq {k : Nat} {A B : Type} (p : Program k A) (q : Program k B)
    {a r t middle s result} (hp : Exec p a r t (true, middle))
    (hq : Exec q q.start middle s result) :
    Exec (seq p q) (.inl a) r (t + s) result := by
  apply exec_link p (seq p q) Sum.inl hp
  · intro a r a' r' hs
    rw [step_seq_left, hs]
  · intro a r hs
    exact .next (by rw [step_seq_left, hs]) (exec_seq_right p q hq)

/-- Repeat a guarded body: true means repeat, false means return successfully. -/
def loop {k : Nat} {L : Type} (p : Program k L) : Program k L where
  start := p.start
  code := fun a => mapOp id (fun b => if b then .goto p.start else .halt true) (p.code a)

theorem step_loop {k : Nat} {L : Type} (p : Program k L) (a : L) (r : Registers k) :
    step (loop p) a r = match step p a r with
      | .inl (true, out) => .inr (p.start, out)
      | .inl (false, out) => .inl (true, out)
      | .inr next => .inr next := by
  cases hc : p.code a with
  | halt b => cases b <;> simp [step, loop, hc, mapOp]
  | goto a' => simp [step, loop, hc, mapOp]
  | push j b a' => simp [step, loop, hc, mapOp]
  | pop j e z o => simp [step, loop, hc, mapOp]
  | peek j e z o => simp [step, loop, hc, mapOp]

theorem exec_loop_exit {k : Nat} {L : Type} (p : Program k L)
    {a r t out} (h : Exec p a r t (false, out)) : Exec (loop p) a r t (true, out) := by
  have hh := exec_link p (loop p) id (s := 0) (target := (true, out)) h
    (by intro a r a' r' hs; simp only [id_eq, step_loop, hs])
    (by intro a r hs; exact .halt (by simp only [id_eq, step_loop, hs]))
  simpa using hh

theorem exec_loop_next {k : Nat} {L : Type} (p : Program k L)
    {a r t middle s result} (hp : Exec p a r t (true, middle))
    (hq : Exec (loop p) p.start middle s result) :
    Exec (loop p) a r (t + s) result := by
  apply exec_link p (loop p) id hp
  · intro a r a' r' hs
    simp only [id_eq, step_loop, hs]
  · intro a r hs
    exact .next (by simp only [id_eq, step_loop, hs]) hq

/-- A one-instruction terminating program. -/
def stop (k : Nat) (b : Bool) : Program k Unit where
  start := ()
  code := fun _ => .halt b

theorem exec_stop (k : Nat) (b : Bool) (r : Registers k) :
    Exec (stop k b) () r 1 (b, r) := .halt rfl

/-- Push one bit, then return successfully: exactly two instructions. -/
def push {k : Nat} (j : Fin (k + 1)) (b : Bool) : Program k Bool where
  start := false
  code := fun q => if q then .halt true else .push j b true

theorem exec_push {k : Nat} (j : Fin (k + 1)) (b : Bool) (r : Registers k) :
    Exec (push j b) false r 2 (true, set r j (b :: r j)) :=
  .next rfl (.halt rfl)

/-- Discard the top bit if any, then return successfully. -/
def pop {k : Nat} (j : Fin (k + 1)) : Program k Bool where
  start := false
  code := fun q => if q then .halt true else .pop j true true true

theorem exec_pop {k : Nat} (j : Fin (k + 1)) (r : Registers k) :
    Exec (pop j) false r 2 (true, set r j (r j).tail) := by
  apply Exec.next (q' := true) (r' := set r j (r j).tail)
  · simp [step, pop, branch]
    cases r j with
    | nil => rfl
    | cons b rest => cases b <;> rfl
  · exact .halt rfl

theorem step_embed {k : Nat} {A B : Type} (p : Program k A) (q : Program k B)
    (f : A → B) (hc : ∀ a, q.code (f a) = mapOp f Op.halt (p.code a))
    (a : A) (r : Registers k) :
    step q (f a) r = match step p a r with
      | .inl result => .inl result
      | .inr (a', out) => .inr (f a', out) := by
  cases hp : p.code a <;> simp [step, hc, hp, mapOp, branch_map]

/-- Relabeling finite control costs no extra instructions. -/
theorem exec_embed {k : Nat} {A B : Type} (p : Program k A) (q : Program k B)
    (f : A → B) (hc : ∀ a, q.code (f a) = mapOp f Op.halt (p.code a))
    {a r t result} (h : Exec p a r t result) : Exec q (f a) r t result := by
  induction h with
  | halt hs => exact .halt (by rw [step_embed p q f hc, hs])
  | next hs _ ih => exact .next (by rw [step_embed p q f hc, hs]) ih

/-- Peek once, then enter the empty, false, or true branch without changing any stack. -/
def peekCase {k : Nat} {A B C : Type} (j : Fin (k + 1))
    (empty : Program k A) (zero : Program k B) (one : Program k C) :
    Program k (Sum Unit (Sum A (Sum B C))) where
  start := .inl ()
  code := fun q => match q with
    | .inl _ => .peek j (.inr (.inl empty.start))
        (.inr (.inr (.inl zero.start))) (.inr (.inr (.inr one.start)))
    | .inr (.inl a) => mapOp (fun x => .inr (.inl x)) Op.halt (empty.code a)
    | .inr (.inr (.inl b)) => mapOp (fun x => .inr (.inr (.inl x))) Op.halt (zero.code b)
    | .inr (.inr (.inr c)) => mapOp (fun x => .inr (.inr (.inr x))) Op.halt (one.code c)

theorem exec_peekCase_empty {k : Nat} {A B C : Type} (j : Fin (k + 1))
    (empty : Program k A) (zero : Program k B) (one : Program k C)
    {r t result} (hr : r j = []) (h : Exec empty empty.start r t result) :
    Exec (peekCase j empty zero one) (.inl ()) r (t + 1) result := by
  apply Exec.next (q' := .inr (.inl empty.start)) (r' := r)
  · simp [step, peekCase, hr, branch]
  · exact exec_embed empty (peekCase j empty zero one)
      (fun a => .inr (.inl a)) (by intro a; rfl) h

theorem exec_peekCase_zero {k : Nat} {A B C : Type} (j : Fin (k + 1))
    (empty : Program k A) (zero : Program k B) (one : Program k C)
    {r tail t result} (hr : r j = false :: tail) (h : Exec zero zero.start r t result) :
    Exec (peekCase j empty zero one) (.inl ()) r (t + 1) result := by
  apply Exec.next (q' := .inr (.inr (.inl zero.start))) (r' := r)
  · simp [step, peekCase, hr, branch]
  · exact exec_embed zero (peekCase j empty zero one)
      (fun a => .inr (.inr (.inl a))) (by intro a; rfl) h

theorem exec_peekCase_one {k : Nat} {A B C : Type} (j : Fin (k + 1))
    (empty : Program k A) (zero : Program k B) (one : Program k C)
    {r tail t result} (hr : r j = true :: tail) (h : Exec one one.start r t result) :
    Exec (peekCase j empty zero one) (.inl ()) r (t + 1) result := by
  apply Exec.next (q' := .inr (.inr (.inr one.start))) (r' := r)
  · simp [step, peekCase, hr, branch]
  · exact exec_embed one (peekCase j empty zero one)
      (fun a => .inr (.inr (.inr a))) (by intro a; rfl) h

/-- A finite number of guarded iterations, with the actual sum of instruction costs. -/
inductive LoopExec {k : Nat} {L : Type} (p : Program k L) : Registers k → Nat → Registers k → Prop where
  | exit {r t out} (h : Exec p p.start r t (false, out)) : LoopExec p r t out
  | next {r t middle s out} (h : Exec p p.start r t (true, middle))
      (rest : LoopExec p middle s out) : LoopExec p r (t + s) out

theorem loop_exec {k : Nat} {L : Type} (p : Program k L) {r t out}
    (h : LoopExec p r t out) : Exec (loop p) p.start r t (true, out) := by
  induction h with
  | exit hs => exact exec_loop_exit p hs
  | next hs _ ih => exact exec_loop_next p hs ih

/-- Pop one counter cell per iteration. Empty means success; body failure propagates. -/
def whileCounter {k : Nat} {L : Type} (j : Fin (k + 1)) (body : Program k L) :
    Program k (Sum Bool L) where
  start := .inl false
  code := fun q => match q with
    | .inl false => .pop j (.inl true) (.inr body.start) (.inr body.start)
    | .inl true => .halt true
    | .inr a => mapOp Sum.inr
        (fun b => if b then .goto (.inl false) else .halt false) (body.code a)

theorem step_whileCounter_body {k : Nat} {L : Type} (j : Fin (k + 1))
    (body : Program k L) (a : L) (r : Registers k) :
    step (whileCounter j body) (.inr a) r = match step body a r with
      | .inl (true, out) => .inr (.inl false, out)
      | .inl (false, out) => .inl (false, out)
      | .inr (a', out) => .inr (.inr a', out) := by
  cases hc : body.code a with
  | halt b => cases b <;> simp [step, whileCounter, hc, mapOp]
  | goto a' => simp [step, whileCounter, hc, mapOp]
  | push j b a' => simp [step, whileCounter, hc, mapOp]
  | pop j e z o => simp [step, whileCounter, hc, mapOp, branch_map]
  | peek j e z o => simp [step, whileCounter, hc, mapOp, branch_map]

theorem exec_whileCounter_done {k : Nat} {L : Type} (j : Fin (k + 1))
    (body : Program k L) (r : Registers k) (hr : r j = []) :
    Exec (whileCounter j body) (.inl false) r 2 (true, r) := by
  have hset : set r j [] = r := by
    funext a
    by_cases ha : a = j
    · subst a; simp [hr]
    · simp [StackMachine.set, ha]
  apply Exec.next (q' := .inl true) (r' := r)
  · simp [step, whileCounter, hr, branch, hset]
  · exact .halt rfl

theorem exec_whileCounter_next {k : Nat} {L : Type} (j : Fin (k + 1))
    (body : Program k L) {r b tail t middle s result} (hr : r j = b :: tail)
    (hb : Exec body body.start (set r j tail) t (true, middle))
    (hrest : Exec (whileCounter j body) (.inl false) middle s result) :
    Exec (whileCounter j body) (.inl false) r (t + s + 1) result := by
  apply Exec.next (q' := .inr body.start) (r' := set r j tail)
  · cases b <;> simp [step, whileCounter, hr, branch]
  · apply exec_link body (whileCounter j body) Sum.inr hb
    · intro a r a' r' hs
      rw [step_whileCounter_body, hs]
    · intro a r hs
      exact .next (by rw [step_whileCounter_body, hs]) hrest

theorem exec_whileCounter_failure {k : Nat} {L : Type} (j : Fin (k + 1))
    (body : Program k L) {r b tail t out} (hr : r j = b :: tail)
    (hb : Exec body body.start (set r j tail) t (false, out)) :
    Exec (whileCounter j body) (.inl false) r (t + 1) (false, out) := by
  apply Exec.next (q' := .inr body.start) (r' := set r j tail)
  · cases b <;> simp [step, whileCounter, hr, branch]
  · have hh := exec_link body (whileCounter j body) Sum.inr (s := 0)
        (target := (false, out)) hb
        (by intro a r a' r' hs; rw [step_whileCounter_body, hs])
        (by intro a r hs; exact .halt (by rw [step_whileCounter_body, hs]))
    simpa using hh

end Complexity.StackProgram
