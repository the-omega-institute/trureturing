/- GID: D5/S0/Computability/BinaryMachine/StackFrame
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/StackFrame
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Register injection preserves counted finite stack execution and its frame. -/

import D5.S0.Computability.BinaryMachine.StackProgram

set_option autoImplicit false
namespace Complexity.StackFrame
open StackMachine (Registers branch)
open StackProgram

def pull {k m : Nat} (i : Fin (k + 1) → Fin (m + 1)) (r : Registers m) : Registers k :=
  fun j => r (i j)

def liftOp {k m : Nat} {L : Type} (i : Fin (k + 1) → Fin (m + 1)) : Op k L → Op m L
  | .halt b => .halt b
  | .goto q => .goto q
  | .push j b q => .push (i j) b q
  | .pop j e z o => .pop (i j) e z o
  | .peek j e z o => .peek (i j) e z o

def lift {k m : Nat} {L : Type} (i : Fin (k + 1) → Fin (m + 1))
    (p : Program k L) : Program m L :=
  ⟨p.start, fun q => liftOp i (p.code q)⟩

private theorem pull_set {k m : Nat} (i : Fin (k + 1) → Fin (m + 1))
    (hi : Function.Injective i) (r : Registers m) (j : Fin (k + 1)) (w : List Bool) :
    pull i (StackMachine.set r (i j) w) = StackMachine.set (pull i r) j w := by
  funext a
  simp only [pull, StackMachine.set]
  have he : i a = i j ↔ a = j := ⟨fun h => hi h, congrArg i⟩
  simp only [he]

private theorem halt_lift {k m : Nat} {L : Type} (i : Fin (k + 1) → Fin (m + 1))
    (p : Program k L) (q : L) (r : Registers m) (b : Bool) (out : Registers k)
    (h : StackProgram.step p q (pull i r) = .inl (b, out)) :
    StackProgram.step (lift i p) q r = .inl (b, r) ∧ pull i r = out := by
  cases hc : p.code q <;> simp [StackProgram.step, hc] at h
  rcases h with ⟨rfl, rfl⟩
  exact ⟨by simp [StackProgram.step, lift, liftOp, hc], rfl⟩

private theorem next_lift {k m : Nat} {L : Type} (i : Fin (k + 1) → Fin (m + 1))
    (hi : Function.Injective i) (p : Program k L) (q q' : L)
    (r : Registers m) (out : Registers k)
    (h : StackProgram.step p q (pull i r) = .inr (q', out)) :
    ∃ out', StackProgram.step (lift i p) q r = .inr (q', out') ∧ pull i out' = out ∧
      ∀ a, (∀ j, a ≠ i j) → out' a = r a := by
  cases hc : p.code q with
  | halt b => simp [StackProgram.step, hc] at h
  | goto a =>
    have he : a = q' ∧ pull i r = out := by simpa [StackProgram.step, hc] using h
    rcases he with ⟨rfl, rfl⟩
    exact ⟨r, by simp [StackProgram.step, lift, liftOp, hc], rfl, by intros; rfl⟩
  | push j b a =>
    have he : a = q' ∧ StackMachine.set (pull i r) j (b :: pull i r j) = out := by
      simpa [StackProgram.step, hc] using h
    rcases he with ⟨rfl, rfl⟩
    refine ⟨StackMachine.set r (i j) (b :: r (i j)), by simp [StackProgram.step, lift, liftOp, hc], ?_, ?_⟩
    · exact pull_set i hi r j _
    · intro a ha; simp [ha j]
  | pop j e z o =>
    have he : branch (pull i r j) e z o = q' ∧ StackMachine.set (pull i r) j (pull i r j).tail = out := by
      simpa [StackProgram.step, hc] using h
    rcases he with ⟨rfl, rfl⟩
    refine ⟨StackMachine.set r (i j) (r (i j)).tail, by simp [StackProgram.step, lift, liftOp, hc, pull], ?_, ?_⟩
    · exact pull_set i hi r j _
    · intro a ha; simp [ha j]
  | peek j e z o =>
    have he : branch (pull i r j) e z o = q' ∧ pull i r = out := by simpa [StackProgram.step, hc] using h
    rcases he with ⟨rfl, rfl⟩
    exact ⟨r, by simp [StackProgram.step, lift, liftOp, hc, pull], rfl, by intros; rfl⟩

/-- Every execution, including rejection, lifts with identical instruction count;
all registers outside the image retain their complete original words. -/
theorem exec_lift {k m : Nat} {L : Type} (i : Fin (k + 1) → Fin (m + 1))
    (hi : Function.Injective i) (p : Program k L)
    {q : L} {r out : Registers k} {t : Nat} {b : Bool}
    (h : Exec p q r t (b, out)) (big : Registers m) (hr : pull i big = r) :
    ∃ result, Exec (lift i p) q big t (b, result) ∧ pull i result = out ∧
      ∀ a, (∀ j, a ≠ i j) → result a = big a := by
  generalize he : (b, out) = result at h
  induction h generalizing big b out with
  | halt hs =>
    cases he
    rw [← hr] at hs
    obtain ⟨hs', ho⟩ := halt_lift i p _ big b out hs
    exact ⟨big, .halt hs', ho, by intros; rfl⟩
  | next hs rest ih =>
    rw [← hr] at hs
    obtain ⟨middle, hm, hp, hf⟩ := next_lift i hi p _ _ big _ hs
    obtain ⟨last, hl, ho, hframe⟩ := ih middle hp he
    exact ⟨last, .next hm hl, ho, fun a ha => (hframe a ha).trans (hf a ha)⟩

/-- An identity injection with two genuinely disjoint frame registers. -/
def includeRegister (j : Fin 7) : Fin 9 := ⟨j.val, by have := j.isLt; omega⟩

def extend (r : Registers 6) (a b : List Bool) : Registers 8 :=
  fun j => if h : j.val < 7 then r ⟨j.val, h⟩ else if j = 7 then a else b

/-- Seven-register programs retain both extra frame words, including on rejection. -/
theorem exec_extend {L : Type} (p : Program 6 L) {q : L} {r out : Registers 6}
    {t : Nat} {b : Bool} (h : Exec p q r t (b, out)) (a saved : List Bool) :
    Exec (lift includeRegister p) q (extend r a saved) t (b, extend out a saved) := by
  have hinj : Function.Injective includeRegister := by
    intro i j he
    apply Fin.ext
    simpa [includeRegister] using congrArg (fun x : Fin 9 => x.val) he
  have hp : pull includeRegister (extend r a saved) = r := by
    funext j
    simp [pull, extend, includeRegister, j.isLt]
  obtain ⟨result, he, ho, hf⟩ := exec_lift includeRegister hinj p h (extend r a saved) hp
  have hh : result = extend out a saved := by
    funext j
    by_cases hj : j.val < 7
    · let i : Fin 7 := ⟨j.val, hj⟩
      have heq : includeRegister i = j := Fin.ext rfl
      have hv := congrFun ho i
      simpa [pull, heq, extend, hj, i] using hv
    · have hh := hf j (by intro i heq; have := i.isLt; have := congrArg Fin.val heq; simp [includeRegister] at *; omega)
      simpa [extend, hj] using hh
  simpa [hh] using he

end Complexity.StackFrame
