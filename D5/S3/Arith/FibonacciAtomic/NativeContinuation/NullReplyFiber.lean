/- GID: D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Appended null replies zero precisely on all-null natural window histories. -/

import D5.S3.Arith.FibonacciAtomic.ImmediateWindowStateCapacity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber

open LiteralWindowEnd (Window bits first last)
open GraftAffineClosure (step quantity residue)
open ImmediateWindowStateCapacity (clock displacement rawTransition rawOutput rawMachine task)
open D5.S3.Arith.ZeckendorfFutureKernel (value legal)

/-- Expand each window in the actual high-to-low reading order, keeping every position. -/
def highBits (w : List Window) : List Bool := w.flatMap (fun b => (bits b).reverse)

/-- The two natural coefficients of a window's existing Fibonacci bit evaluator. -/
def bitComposition (b : Window) : ℕ × ℕ :=
  (value 1 0 (bits b), value 0 1 (bits b))

/-- Natural source histories have the original guard and three actual Fibonacci steps.
The relation retains the full word and imposes no final-seam or leading-window condition. -/
inductive NativeHistory : Bool → (ℕ × ℕ) → List Window → Bool → (ℕ × ℕ) → Prop
  | nil (s : Bool) (c : ℕ × ℕ) : NativeHistory s c [] s c
  | cons {s t : Bool} {c d : ℕ × ℕ} {b : Window} {w : List Window}
      (guard : ¬ (s = true ∧ last b = true))
      (tail : NativeHistory (first b) (step (step (step c)) + bitComposition b) w t d) :
      NativeHistory s c (b :: w) t d

private theorem history_cons (s t : Bool) (c d : ℕ × ℕ) (b : Window) (w : List Window) :
    NativeHistory s c (b :: w) t d ↔
      ¬ (s = true ∧ last b = true) ∧
        NativeHistory (first b) (step (step (step c)) + bitComposition b) w t d := by
  constructor
  · intro h
    cases h with
    | cons guard tail => exact ⟨guard, tail⟩
  · rintro ⟨guard, tail⟩
    exact .cons guard tail

private theorem window_legal (s : Bool) (b : Window) (w : List Window) :
    legal s (highBits (b :: w)) ↔
      ¬ (s = true ∧ last b = true) ∧ legal (first b) (highBits w) := by
  cases s <;> cases b <;> simp [highBits, bits, first, last, legal]

private theorem cast_update (c : ℕ × ℕ) (b : Window) :
    clock (residue 0 c) + displacement b =
      residue 0 (step (step (step c)) + bitComposition b) := by
  cases b <;> ext <;>
    simp [clock, step, residue, displacement, bitComposition, bits, value]

private theorem dead_execution (w : List Window) :
    (rawMachine 0).toDFA.evalFrom none w = none := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [DFA.evalFrom_cons, rawMachine, rawTransition] using ih

/-- The existing integer reader realizes exactly the natural source histories.
Errors are exactly illegal bit histories; every successful state has actual natural coordinates. -/
theorem native_execution (s : Bool) (c : ℕ × ℕ) (w : List Window) :
    ((rawMachine 0).toDFA.evalFrom (some (s, residue 0 c)) w = none ↔
      ¬ legal s (highBits w)) ∧
    (∀ (t : Bool) (x : ZMod 0 × ZMod 0),
      (rawMachine 0).toDFA.evalFrom (some (s, residue 0 c)) w = some (t, x) ↔
        ∃ d : ℕ × ℕ, NativeHistory s c w t d ∧ x = residue 0 d) := by
  induction w generalizing s c with
  | nil =>
    constructor
    · simp [DFA.evalFrom_nil, highBits, legal]
    · intro t x
      constructor
      · intro h
        have hpair := Option.some.inj h
        cases hpair
        exact ⟨c, .nil s c, rfl⟩
      · rintro ⟨d, h, hx⟩
        cases h
        simp [hx]
  | cons b w ih =>
    rw [DFA.evalFrom_cons]
    change ((rawMachine 0).toDFA.evalFrom (rawTransition (some (s, residue 0 c)) b) w =
      none ↔ ¬ legal s (highBits (b :: w))) ∧
      (∀ (t : Bool) (x : ZMod 0 × ZMod 0),
        (rawMachine 0).toDFA.evalFrom (rawTransition (some (s, residue 0 c)) b) w =
          some (t, x) ↔ ∃ d : ℕ × ℕ, NativeHistory s c (b :: w) t d ∧ x = residue 0 d)
    by_cases guard : s = true ∧ last b = true
    · have hb : (s && last b) = true := by simp [guard.1, guard.2]
      simp only [rawTransition, hb, ↓reduceIte, dead_execution]
      constructor
      · simp [window_legal, guard]
      · intro t x
        simp [history_cons, guard]
    · have hb : (s && last b) = false := by
        cases s <;> cases hlast : last b <;> simp_all
      simp only [rawTransition, hb, Bool.false_eq_true, ↓reduceIte, cast_update]
      constructor
      · simpa [window_legal, guard] using (ih (first b)
          (step (step (step c)) + bitComposition b)).1
      · intro t x
        simpa [history_cons, guard] using (ih (first b)
          (step (step (step c)) + bitComposition b)).2 t x

private theorem history_zero {s t : Bool} {c d : ℕ × ℕ} {w : List Window}
    (h : NativeHistory s c w t d) :
    d = (0, 0) ↔ c = (0, 0) ∧ ∀ b ∈ w, b = .zero := by
  induction h with
  | nil s c => simp
  | @cons s t c d b w guard tail ih =>
    rw [ih]
    cases b <;> simp [bitComposition, bits, value, step, Prod.ext_iff]
    omega

/-- The actual appended null reply is zero exactly on all-null finite initialized words. -/
theorem null_reply_zero_iff (w : List Window) :
    task 0 (w ++ [.zero]) = some 0 ↔ ∀ b ∈ w, b = .zero := by
  have source := native_execution false (0, 0) w
  have appended : task 0 (w ++ [.zero]) =
      rawOutput (rawTransition ((rawMachine 0).toDFA.eval w) .zero) := by
    change rawOutput ((rawMachine 0).toDFA.evalFrom _ (w ++ [.zero])) = _
    rw [DFA.evalFrom_append_singleton]
    rfl
  cases hr : (rawMachine 0).toDFA.eval w with
  | none =>
    have nozeros : ¬ (∀ b ∈ w, b = .zero) := by
      intro hz
      have hlegal : legal false (highBits w) := by
        clear source appended hr
        induction w with
        | nil => simp [highBits, legal]
        | cons b w ih =>
          have hb : b = .zero := hz b (by simp)
          rw [window_legal, hb]
          exact ⟨by simp [last], ih (fun a ha => hz a (by simp [ha]))⟩
      exact (source.1.mp hr) hlegal
    simp [appended, hr, rawTransition, rawOutput, nozeros]
  | some q =>
    rcases q with ⟨s, x⟩
    obtain ⟨c, hc, hx⟩ := (source.2 s x).mp hr
    rw [appended, hr, hx]
    have zero_quantity : quantity (clock (residue 0 c)) = 0 ↔ c = (0, 0) := by
      have cast : ((8 * c.1 + 13 * c.2 : ℕ) : ZMod 0) =
          quantity (clock (residue 0 c)) := by
        simp [quantity, clock, step, residue]
        ring
      constructor
      · intro h
        have hi : ((8 * c.1 + 13 * c.2 : ℕ) : ℤ) = 0 := cast.trans h
        have hn : 8 * c.1 + 13 * c.2 = 0 := by exact_mod_cast hi
        apply Prod.ext <;> dsimp <;> omega
      · rintro rfl
        simp [quantity, clock, step, residue]
    simpa [rawTransition, last, first, displacement, rawOutput, Prod.mk_zero_zero,
      zero_quantity] using history_zero hc

end D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber
