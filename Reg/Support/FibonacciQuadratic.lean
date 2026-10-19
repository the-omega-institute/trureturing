import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry

namespace Reg.Support.FibonacciQuadratic
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
noncomputable section

/-- Rational coordinates in the original basis (1,t). -/
def eval (a : ℚ × ℚ) : ℝ := (a.1 : ℝ) + (a.2 : ℝ) * t

def mul (a b : ℚ × ℚ) : ℚ × ℚ :=
  (a.1 * b.1 + a.2 * b.2, a.1 * b.2 + a.2 * b.1 - a.2 * b.2)

theorem eval_mul (a b : ℚ × ℚ) : eval (mul a b) = eval a * eval b := by
  dsimp [eval, mul]
  push_cast
  have ht := tail_arithmetic.1
  calc
    _ = (a.1 : ℝ) * b.1 + ((a.1 : ℝ) * b.2 + (a.2 : ℝ) * b.1) * t +
        (a.2 : ℝ) * b.2 * t^2 := by rw [ht]; ring
    _ = _ := by ring

def power (a : ℚ × ℚ) : ℕ → ℚ × ℚ
  | 0 => (1,0)
  | n+1 => mul (power a n) a

theorem eval_power (a : ℚ × ℚ) (n : ℕ) : eval (power a n) = eval a ^ n := by
  induction n with
  | zero => simp [power, eval]
  | succ n ih => rw [power, eval_mul, ih, pow_succ]

def shiftPair : Label → ℚ × ℚ
  | .L3 => (0,-1)
  | .L0 => (0,0)
  | .L5 => (1,-1)
  | .L2 => (1,0)
  | .L25 => (2,-1)

def step (l : Label) (a : ℚ × ℚ) : ℚ × ℚ :=
  ((shiftPair l).fst + a.fst - 2*a.snd,
    (shiftPair l).snd - 2*a.fst + 3*a.snd)

-- The pair notation keeps the original affine branch, including its negative slope.
theorem eval_step (l : Label) (a : ℚ × ℚ) : eval (step l a) = branch l (eval a) := by
  have ht := tail_arithmetic.1
  cases l <;> dsimp [step, shiftPair, eval, branch, shift, T2, g] <;>
    push_cast <;> ring_nf <;> rw [ht] <;> ring

def composePair : List Label → (ℚ × ℚ) → ℚ × ℚ
  | [], a => a
  | l :: w, a => step l (composePair w a)

theorem compose_eval (w : List Label) (a : ℚ × ℚ) :
    compose w (eval a) = eval (composePair w a) := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [compose, ih, composePair, eval_step]

theorem t_bounds : (61803398874989484820 / 100000000000000000000 : ℝ) < t ∧
    t < 61803398874989484821 / 100000000000000000000 := by
  rcases tail_arithmetic with ⟨ht, hp, _, _, _, _⟩
  constructor <;> nlinarith

#print axioms compose_eval
#print axioms t_bounds
end
end Reg.Support.FibonacciQuadratic
