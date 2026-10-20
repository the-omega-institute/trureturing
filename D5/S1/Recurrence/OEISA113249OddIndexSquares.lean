/- GID: D5/S1/Recurrence/OEISA113249OddIndexSquares
   generality: I
   mirror-B: D5/B/S1/Recurrence/OEISA113249OddIndexSquares
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every odd-index term in Dement's fourth-order integer family is a square. -/

/-
Direct frozen dependencies: none (every declaration).
escape_witness: none; admission uses the external named settlement.
The amended mechanisms on #19316 are odd_rec, b_sq_rec, and odd_window.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19434

Per-declaration proof_shape and consumers:
- a: bind-only (source definition); consumers: claim, a_rec, odd_window.
- claim: bind-only (source proposition); consumer: result.
- b: bind-only (recursive construction); consumers: b_rec, b_sq_rec, odd_window, result.
- a_rec: bind-only (definitional recurrence); consumer: odd_rec.
- b_rec: bind-only (definitional recurrence); consumer: b_sq_rec.
- odd_rec: bind-only (three recurrence instances and polynomial normalization);
  consumer: odd_window.
- b_sq_rec: bind-only (two recurrence instances and polynomial normalization);
  consumer: odd_window.
- odd_window: bind-only (pinned recurrence uniqueness plus normalization);
  consumer: result.
- result: bind-only (recurrence uniqueness, normalization, and IsSquare.sq);
  admission_basis: open-problem-resolution (#19316).

The source recurrence and integer initial values are used without replacing their expressions.
The auxiliary b sequence is private; IsSquare is Mathlib's existing predicate.
-/

import Mathlib.Algebra.LinearRecurrence
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace D5.S1.Recurrence.OEISA113249OddIndexSquares

/-- Dement's integer-valued fourth-order family, including all four initial values. -/
def a (m : ℕ) : ℕ → ℤ
  | 0 => -1
  | 1 => 4
  | 2 => -13 + 6 * ((m : ℤ) - 1) + 3 * ((m : ℤ) - 1) ^ 2
  | 3 => (-8 + (m : ℤ) ^ 2) ^ 2
  | n + 4 => (m : ℤ) ^ 4 * a m n + (2 * (m : ℤ)) ^ 2 * a m (n + 1) - 4 * a m (n + 3)

/-- "Conjecture: a(m, 2*n+1) is a perfect square for all m, n." (OEIS A113249, Comments.) -/
def claim : Prop := ∀ m n : ℕ, IsSquare (a m (2 * n + 1))

private def b (m : ℕ) : ℕ → ℤ
  | 0 => 2
  | 1 => (m : ℤ) ^ 2 - 8
  | n + 2 => -4 * b m (n + 1) - (m : ℤ) ^ 2 * b m n

private theorem a_rec (m k : ℕ) :
    a m (k + 4) = (m : ℤ) ^ 4 * a m k + (2 * (m : ℤ)) ^ 2 * a m (k + 1) -
      4 * a m (k + 3) := by
  rfl

private theorem b_rec (m k : ℕ) :
    b m (k + 2) = -4 * b m (k + 1) - (m : ℤ) ^ 2 * b m k := by
  rfl

private theorem odd_rec (m k : ℕ) :
    a m (k + 6) = (16 - (m : ℤ) ^ 2) * a m (k + 4) +
      ((m : ℤ) ^ 4 - 16 * (m : ℤ) ^ 2) * a m (k + 2) + (m : ℤ) ^ 6 * a m k := by
  have h0 := a_rec m k
  have h1 := a_rec m (k + 1)
  have h2 := a_rec m (k + 2)
  linear_combination h2 - 4 * h1 + (m : ℤ) ^ 2 * h0

private theorem b_sq_rec (m k : ℕ) :
    b m (k + 3) ^ 2 = (16 - (m : ℤ) ^ 2) * b m (k + 2) ^ 2 +
      ((m : ℤ) ^ 4 - 16 * (m : ℤ) ^ 2) * b m (k + 1) ^ 2 +
      (m : ℤ) ^ 6 * b m k ^ 2 := by
  rw [b_rec m (k + 1), b_rec m k]
  ring

private theorem odd_window (m n : ℕ) :
    a m (2 * n + 1) = b m n ^ 2 ∧
    a m (2 * n + 3) = b m (n + 1) ^ 2 ∧
    a m (2 * n + 5) = b m (n + 2) ^ 2 := by
  let E : LinearRecurrence ℤ :=
    ⟨3, ![(m : ℤ) ^ 6, (m : ℤ) ^ 4 - 16 * (m : ℤ) ^ 2, 16 - (m : ℤ) ^ 2]⟩
  let u : ℕ → ℤ := fun j => a m (2 * j + 1)
  let v : ℕ → ℤ := fun j => b m j ^ 2
  have hu : E.IsSolution u := by
    intro j
    change a m (2 * (j + 3) + 1) = ∑ i : Fin 3, E.coeffs i * u (j + i)
    simp only [Fin.sum_univ_three]
    dsimp [E, u]
    simpa only [Nat.mul_add, Nat.add_assoc, mul_zero, add_zero, mul_one,
      Nat.reduceAdd, Nat.reduceMul, add_comm, add_left_comm, add_assoc]
      using odd_rec m (2 * j + 1)
  have hv : E.IsSolution v := by
    intro j
    change b m (j + 3) ^ 2 = ∑ i : Fin 3, E.coeffs i * v (j + i)
    simp only [Fin.sum_univ_three]
    dsimp [E, v]
    simpa only [add_zero, add_comm, add_left_comm, add_assoc] using b_sq_rec m j
  have initial_agreement : Set.EqOn u v (Finset.range E.order) := by
    intro j hj
    have hj' : j < 3 := Finset.mem_range.mp hj
    rcases j with _ | _ | _ | j
    · norm_num [u, v, a, b]
    · norm_num [u, v, a, b]
      ring
    · norm_num [u, v, a, b]
      ring
    · exact False.elim ((Nat.not_lt.mpr (Nat.le_add_left 3 j)) hj')
  have huv : u = v := (E.eq_iff_eqOn_range_order u v hu hv).2 initial_agreement
  refine ⟨congrFun huv n, ?_, ?_⟩
  · simpa [u, v, Nat.mul_add, Nat.add_assoc] using congrFun huv (n + 1)
  · simpa [u, v, Nat.mul_add, Nat.add_assoc] using congrFun huv (n + 2)

/-- Every odd-index term is an integer square, uniformly in the natural parameter. -/
theorem result : claim := by
  intro m n
  rw [(odd_window m n).1]
  exact IsSquare.sq (b m n)

end D5.S1.Recurrence.OEISA113249OddIndexSquares
