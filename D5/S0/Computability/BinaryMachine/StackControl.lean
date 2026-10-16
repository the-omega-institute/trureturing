/- GID: D5/S0/Computability/BinaryMachine/StackControl
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/StackControl
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Counted decision continuations and framed word movement. -/

import D5.S0.Computability.BinaryMachine.StackWords
import D5.S0.Computability.BinaryMachine.TapeToStacks

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Complexity.StackControl
open StackMachine (Registers)
open StackProgram

def choose {k : Nat} {A B : Type} (test : Program k A) (yes no : Program k B) :
    Program k (Sum A (Bool × B)) where
  start := .inl test.start
  code := fun q => match q with
    | .inl a => mapOp Sum.inl
        (fun b => .goto (.inr (b, (if b then yes else no).start))) (test.code a)
    | .inr (b, a) => mapOp (fun q => .inr (b, q)) Op.halt ((if b then yes else no).code a)

def chooseEncoding {A B : Type} (a : Encoding A) (b : Encoding B) : Encoding (Sum A (Bool × B)) :=
  a.sum (Encoding.bool.prod b)

private theorem step_choose_left {k : Nat} {A B : Type} (p : Program k A) (yes no : Program k B)
    (q : A) (r : Registers k) :
    StackProgram.step (choose p yes no) (.inl q) r =
      match StackProgram.step p q r with
      | .inl (b, out) => .inr (.inr (b, (if b then yes else no).start), out)
      | .inr (q', out) => .inr (.inl q', out) := by
  cases hc : p.code q <;> simp [StackProgram.step, choose, hc, mapOp, branch_map]

/-- Both decisions dispatch to their own continuation, counting the terminal
jump instead of discarding the rejecting computation. -/
theorem exec_choose {k : Nat} {A B : Type} (p : Program k A) (yes no : Program k B)
    {q : A} {r middle out : Registers k} {t s : Nat} {b d : Bool}
    (hp : Exec p q r t (b, middle))
    (hq : Exec (if b then yes else no) (if b then yes else no).start middle s (d, out)) :
    Exec (choose p yes no) (.inl q) r (t + s) (d, out) := by
  apply exec_link p (choose p yes no) Sum.inl hp
  · intro a r a' r' hs
    rw [step_choose_left, hs]
  · intro a r hs
    have he : Exec (choose p yes no) (.inr (b, (if b then yes else no).start)) middle s (d, out) := by
      apply exec_embed (if b then yes else no) (choose p yes no) (fun q => .inr (b, q))
      · intro a; rfl
      · exact hq
    exact .next (by rw [step_choose_left, hs]) he

def moveWord {k : Nat} (src dst scratch : Fin (k + 1)) :=
  seq (StackWords.clear dst)
    (seq (StackWords.transfer src scratch) (StackWords.transfer scratch dst))

def moveEncoding := Encoding.bool.sum ((Encoding.fin 3).sum (Encoding.fin 3))

/-- A whole word is moved without reversal. Scratch starts and ends empty;
other registers are unchanged, and every primitive instruction is counted. -/
theorem exec_moveWord {k : Nat} (src dst scratch : Fin (k + 1))
    (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
    (r : Registers k) (hempty : r scratch = []) :
    Exec (moveWord src dst scratch) (moveWord src dst scratch).start r
      ((r dst).length + 4 * (r src).length + 6)
      (true, StackMachine.set (StackMachine.set r src []) dst (r src)) := by
  let r₁ := StackMachine.set r dst []
  let r₂ := StackMachine.set (StackMachine.set r₁ src []) scratch ((r₁ src).reverse ++ r₁ scratch)
  have h₁ := StackWords.exec_clear dst r
  have h₂ := StackWords.exec_transfer src scratch hst r₁
  have h₃ := StackWords.exec_transfer scratch dst (Ne.symm hdt) r₂
  have hh := exec_seq _ _ h₁ (exec_seq _ _ h₂ h₃)
  have hout : StackMachine.set (StackMachine.set r₂ scratch []) dst ((r₂ scratch).reverse ++ r₂ dst) =
      StackMachine.set (StackMachine.set r src []) dst (r src) := by
    funext a
    by_cases hd : a = dst
    · subst a; simp [r₂, r₁, StackMachine.set, hsd, Ne.symm hsd, hdt, Ne.symm hdt, hempty]
    · by_cases hs : a = src
      · subst a; simp [r₂, r₁, hd, hst]
      · by_cases ht : a = scratch
        · subst a; simp [r₂, r₁, hd, hs, hempty]
        · simp [r₂, r₁, StackMachine.set, hd, hs, ht]
  change Exec _ _ _ _ (true, _) at hh
  rw [hout] at hh
  have hcost : (r dst).length + 2 + (2 * (r₁ src).length + 2 + (2 * (r₂ scratch).length + 2)) =
      (r dst).length + 4 * (r src).length + 6 := by
    simp [r₂, r₁, StackMachine.set, hsd, Ne.symm hsd, hdt, Ne.symm hdt, hempty]
    omega
  rw [hcost] at hh
  exact hh

def WriteLabel : List Bool → Type
  | [] => Unit
  | _ :: xs => Sum (WriteLabel xs) Bool

def write {k : Nat} (j : Fin (k + 1)) : (xs : List Bool) → Program k (WriteLabel xs)
  | [] => stop k true
  | b :: xs => seq (write j xs) (push j b)

def writeEncoding : (xs : List Bool) → Encoding (WriteLabel xs)
  | [] => Encoding.unit
  | _ :: xs => (writeEncoding xs).sum Encoding.bool

/-- A fixed finite word is installed by literal one-bit instructions. -/
theorem exec_write {k : Nat} (j : Fin (k + 1)) (xs : List Bool) (r : Registers k) :
    Exec (write j xs) (write j xs).start r (2 * xs.length + 1)
      (true, StackMachine.set r j (xs ++ r j)) := by
  induction xs with
  | nil =>
    have hsame : StackMachine.set r j (r j) = r := StackWords.set_unchanged r j
    simpa [write, WriteLabel, stop, hsame] using exec_stop k true r
  | cons b xs ih =>
    have hp := exec_push j b (StackMachine.set r j (xs ++ r j))
    have hh := exec_seq (write j xs) (push j b) ih hp
    have ho : StackMachine.set (StackMachine.set r j (xs ++ r j)) j
        (b :: StackMachine.set r j (xs ++ r j) j) = StackMachine.set r j ((b :: xs) ++ r j) := by
      funext a
      by_cases h : a = j <;> simp [StackMachine.set, h]
    rw [ho] at hh
    simpa [write, WriteLabel, seq, Nat.mul_add, Nat.add_assoc] using hh


/-- Disjoint labels allow decision branches to have unrelated finite controls. -/
def widenLeft {k : Nat} {A B : Type} (p : Program k A) : Program k (Sum A B) where
  start := .inl p.start
  code := fun q => match q with
    | .inl a => mapOp Sum.inl Op.halt (p.code a)
    | .inr _ => .halt false

def widenRight {k : Nat} {A B : Type} (p : Program k B) : Program k (Sum A B) where
  start := .inr p.start
  code := fun q => match q with
    | .inl _ => .halt false
    | .inr b => mapOp Sum.inr Op.halt (p.code b)

theorem exec_widenLeft {k : Nat} {A B : Type} (p : Program k A)
    {r out : Registers k} {t : Nat} {b : Bool}
    (h : Exec p p.start r t (b, out)) :
    Exec (widenLeft (B := B) p) (widenLeft p).start r t (b, out) := by
  exact exec_embed p (widenLeft p) Sum.inl (fun _ => rfl) h

theorem exec_widenRight {k : Nat} {A B : Type} (p : Program k B)
    {r out : Registers k} {t : Nat} {b : Bool}
    (h : Exec p p.start r t (b, out)) :
    Exec (widenRight (A := A) p) (widenRight p).start r t (b, out) := by
  exact exec_embed p (widenRight p) Sum.inr (fun _ => rfl) h

end Complexity.StackControl
