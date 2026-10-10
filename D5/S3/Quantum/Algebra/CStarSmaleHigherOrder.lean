/- GID: D5/S3/Quantum/Algebra/CStarSmaleHigherOrder
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CStarSmaleHigherOrder
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/CStarSmaleHigherOrder.claim; result=D5/S3/Quantum/Algebra/CStarSmaleHigherOrder.result; claim=D5/S3/Quantum/Algebra/CStarSmaleHigherOrder.claim
   digest: Refutes the higher-order C*-algebraic Smale conjecture in C x C at degree three. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#14982; Refuted)
Direct frozen dependencies: none; all imports are pinned Mathlib.
Definitions: smalePoly, claim; private witness has type Fin 3 -> Complex x Complex.
Private auxiliary classifications (all bind-only; live consumers):
  sqrt437_sq -> witness_mul; sqrt3_sq -> witness_mul.
  witness_sum -> witness_poly; witness_mul -> witness_poly.
  witness_poly -> witness_eval, witness_derivative_eval, witness_second_eval.
  witness_eval -> critical_gap.
  witness_derivative_eval -> critical_set, derivative_zero.
  witness_second_eval -> second_zero; sqrt438_sq -> critical_set.
  critical_set -> critical_gap; derivative_zero -> derivative_norm, result.
  second_zero -> second_norm; derivative_norm -> failing_term.
  second_norm -> failing_term; critical_gap -> failing_term; failing_term -> result.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The source is Krishna, arXiv:2206.08154v1, Section 2, Conjecture HIGHERMEAN.
The encoding follows #14982: the factor product is a Polynomial and derivatives
are iterates of Polynomial.derivative. The roots give (x^3+21x^2+x, y^3-3y).
Every critical point has second coordinate 1 or -1, hence the critical-value gap
has norm at least 2. At zero the first and second derivative norms are 3 and 42,
so the k = 2 term exceeds 4. No other conjecture of the source is settled here.
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Polynomial.Derivative

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Algebra.CStarSmaleHigherOrder

def smalePoly {A : Type} [CommRing A] {n : ℕ} (a : Fin n → A) : Polynomial A :=
  ∏ j, (Polynomial.X - Polynomial.C (a j))

def claim : Prop :=
  ∀ (A : Type) [CommCStarAlgebra A] (n : ℕ), 2 ≤ n → ∀ (a : Fin n → A) (z : A),
    (Polynomial.derivative (smalePoly a)).eval z ≠ 0 →
    ∃ w : A, (Polynomial.derivative (smalePoly a)).eval w = 0 ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ n →
        ‖((Polynomial.derivative)^[k] (smalePoly a)).eval z‖ / (k.factorial : ℝ) *
          (‖(smalePoly a).eval z - (smalePoly a).eval w‖ ^ (k - 1) /
            ‖(Polynomial.derivative (smalePoly a)).eval z‖ ^ k) ≤ 4 ^ (k - 1)

private def witness : Fin 3 → ℂ × ℂ :=
  ![(0, 0), (((-21 + Real.sqrt 437) / 2 : ℝ), (Real.sqrt 3 : ℝ)),
    (((-21 - Real.sqrt 437) / 2 : ℝ), -(Real.sqrt 3 : ℝ))]

private theorem sqrt437_sq : (Real.sqrt 437 : ℂ) ^ 2 = 437 := by
  exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 437 by norm_num)

private theorem sqrt3_sq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
  exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)

private theorem witness_sum : witness 1 + witness 2 = ((-21 : ℂ), 0) := by
  ext <;> simp [witness] <;> ring

private theorem witness_mul : witness 1 * witness 2 = ((1 : ℂ), -3) := by
  ext <;> simp [witness]
  · calc
      _ = ((21 : ℂ)^2 - (Real.sqrt 437 : ℂ)^2) / 4 := by ring
      _ = 1 := by rw [sqrt437_sq]; norm_num
  · rw [← pow_two, sqrt3_sq]

private theorem witness_poly : smalePoly witness =
    Polynomial.X ^ 3 + Polynomial.C ((21 : ℂ), 0) * Polynomial.X ^ 2 +
      Polynomial.C ((1 : ℂ), -3) * Polynomial.X := by
  have h0 : witness 0 = 0 := rfl
  simp only [smalePoly, Fin.prod_univ_succ, h0, map_zero, sub_zero,
    Fin.prod_univ_zero, mul_one]
  change Polynomial.X * ((Polynomial.X - Polynomial.C (witness 1)) *
      (Polynomial.X - Polynomial.C (witness 2))) = _
  calc
    _ = Polynomial.X ^ 3 - Polynomial.C (witness 1 + witness 2) * Polynomial.X ^ 2 +
        Polynomial.C (witness 1 * witness 2) * Polynomial.X := by
      simp only [Polynomial.C_add, Polynomial.C_mul]; ring
    _ = _ := by
      rw [witness_sum, witness_mul]
      have hn : ((-21 : ℂ), (0 : ℂ)) = -((21 : ℂ), (0 : ℂ)) := by ext <;> simp
      rw [hn, Polynomial.C_neg]; ring

private theorem witness_eval (w : ℂ × ℂ) : (smalePoly witness).eval w =
    (w.1 ^ 3 + 21 * w.1 ^ 2 + w.1, w.2 ^ 3 - 3 * w.2) := by
  rw [witness_poly]
  ext <;> simp <;> ring

private theorem witness_derivative_eval (w : ℂ × ℂ) :
    (Polynomial.derivative (smalePoly witness)).eval w =
      (3 * w.1 ^ 2 + 42 * w.1 + 1, 3 * w.2 ^ 2 - 3) := by
  rw [witness_poly]
  simp only [Polynomial.derivative_add, Polynomial.derivative_X_pow,
    Polynomial.derivative_C_mul, Polynomial.derivative_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  norm_num
  ext <;> simp <;> ring

private theorem witness_second_eval (w : ℂ × ℂ) :
    ((Polynomial.derivative)^[2] (smalePoly witness)).eval w =
      (6 * w.1 + 42, 6 * w.2) := by
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
    Function.iterate_zero_apply, witness_poly]
  simp only [Polynomial.derivative_add, Polynomial.derivative_X_pow,
    Polynomial.derivative_X,
    Polynomial.derivative_C, Polynomial.derivative_mul,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  norm_num
  ext <;> simp <;> ring

private theorem sqrt438_sq : (Real.sqrt 438 : ℂ) ^ 2 = 438 := by
  exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 438 by norm_num)

private theorem critical_set (w : ℂ × ℂ) :
    (Polynomial.derivative (smalePoly witness)).eval w = 0 ↔
    w = (-7 + (Real.sqrt 438 : ℂ) / 3, 1) ∨
    w = (-7 + (Real.sqrt 438 : ℂ) / 3, -1) ∨
    w = (-7 - (Real.sqrt 438 : ℂ) / 3, 1) ∨
    w = (-7 - (Real.sqrt 438 : ℂ) / 3, -1) := by
  rw [witness_derivative_eval]
  have hf : 3 * w.1 ^ 2 + 42 * w.1 + 1 =
      3 * (w.1 - (-7 + (Real.sqrt 438 : ℂ) / 3)) *
        (w.1 - (-7 - (Real.sqrt 438 : ℂ) / 3)) := by
    linear_combination (1 / 3 : ℂ) * sqrt438_sq
  have hs : 3 * w.2 ^ 2 - 3 = 3 * (w.2 - 1) * (w.2 - -1) := by ring
  change (3 * w.1 ^ 2 + 42 * w.1 + 1, 3 * w.2 ^ 2 - 3) = (0, 0) ↔ _
  rw [Prod.mk.injEq, hf, hs]
  simp only [mul_eq_zero, sub_eq_zero]
  norm_num
  simp only [Prod.ext_iff]
  tauto

private theorem derivative_zero :
    (Polynomial.derivative (smalePoly witness)).eval 0 = ((1 : ℂ), -3) := by
  rw [witness_derivative_eval]; norm_num

private theorem second_zero :
    ((Polynomial.derivative)^[2] (smalePoly witness)).eval 0 = ((42 : ℂ), 0) := by
  rw [witness_second_eval]; norm_num

private theorem derivative_norm :
    ‖(Polynomial.derivative (smalePoly witness)).eval 0‖ = 3 := by
  rw [derivative_zero, Prod.norm_def]; norm_num

private theorem second_norm :
    ‖((Polynomial.derivative)^[2] (smalePoly witness)).eval 0‖ = 42 := by
  rw [second_zero, Prod.norm_def]; norm_num

private theorem critical_gap (w : ℂ × ℂ)
    (hw : (Polynomial.derivative (smalePoly witness)).eval w = 0) :
    2 ≤ ‖(smalePoly witness).eval 0 - (smalePoly witness).eval w‖ := by
  have hn := norm_snd_le ((smalePoly witness).eval 0 - (smalePoly witness).eval w)
  rcases (critical_set w).mp hw with rfl | rfl | rfl | rfl <;>
    rw [witness_eval, witness_eval] at hn ⊢ <;>
    norm_num at hn ⊢

private theorem failing_term (w : ℂ × ℂ)
    (hw : (Polynomial.derivative (smalePoly witness)).eval w = 0) :
    4 < ‖((Polynomial.derivative)^[2] (smalePoly witness)).eval 0‖ / ((2 : ℕ).factorial : ℝ) *
          (‖(smalePoly witness).eval 0 - (smalePoly witness).eval w‖ ^ (2 - 1) /
            ‖(Polynomial.derivative (smalePoly witness)).eval 0‖ ^ 2) := by
  have hg := critical_gap w hw
  rw [second_norm, derivative_norm]
  norm_num
  nlinarith

theorem result : ¬ claim := by
  intro h
  have hz : (Polynomial.derivative (smalePoly witness)).eval 0 ≠ 0 := by
    rw [derivative_zero]
    norm_num
  obtain ⟨w, hw, hbound⟩ := h (ℂ × ℂ) 3 (by norm_num) witness 0 hz
  have hk := hbound 2 (by norm_num) (by norm_num)
  apply (not_le_of_gt (failing_term w hw))
  simpa only [Nat.reduceSub, pow_one] using hk


end D5.S3.Quantum.Algebra.CStarSmaleHigherOrder
