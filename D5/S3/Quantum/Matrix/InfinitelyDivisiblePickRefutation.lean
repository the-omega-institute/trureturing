/- GID: D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.claim; result=D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.result; claim=D5/S3/Quantum/Matrix/InfinitelyDivisiblePickRefutation.claim
   digest: A positive Pick function sends a 4×4 SIDM to a matrix with a negative entry. -/

/- Source: Johnson–Mondal–Tsatsomeros, arXiv:2609.06298v1, Table 2, row 12.
   escape_witness: the 4×4 SIDM E(1) and f(z)=2z/(1+z), with f[A] (1,4) entry −1/24.
   Direct frozen dependencies: none (pinned Mathlib only).
   admission_basis: open-problem-resolution (#15918; Refuted)
   Per-declaration proof_shape and live consumers:
     IsSIDM: definition; consumers=claim, sidm_E_one, result
     pickFun: definition; consumers=claim, pick_positive
     pickCalc: definition; consumers=claim, calc_negative
     claim: definition; consumer=result
     E: definition; consumers=E_zero, E_mul, E_pow, E_nonneg, E_det, sidm_E_one, shifted_inverse, calc_negative, result
     C: definition; consumers=shifted_inverse, calc_negative
     E_zero: bind-only; consumer=E_pow
     E_mul: bind-only; consumer=E_pow
     E_pow: content; consumer=sidm_E_one
     E_nonneg: bind-only; consumer=sidm_E_one
     E_det: bind-only; consumer=sidm_E_one
     sidm_E_one: content; consumer=result
     shifted_inverse: bind-only; consumer=calc_negative
     pick_positive: bind-only; consumer=result
     calc_negative: bind-only; consumer=result
     result: verifies an explicit finite construction by exact computation. -/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Matrix
namespace D5.S3.Quantum.Matrix.InfinitelyDivisiblePickRefutation

/-- Definition 3.25: strongly infinitely divisible matrix. -/
def IsSIDM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ IsUnit A.det ∧
    ∀ m : ℕ, 0 < m → ∃ K : Matrix (Fin n) (Fin n) ℝ, (∀ i j, 0 ≤ K i j) ∧ K ^ m = A
/-- Lemma 2.8 with a finitely supported measure: a Pick function on the real axis. -/
noncomputable def pickFun {k : ℕ} (a b : ℝ) (t w : Fin k → ℝ) (x : ℝ) : ℝ :=
  a + b * x + ∑ i, w i * ((t i * x - 1) / (t i + x))
/-- Remark 2.9: the matrix f[A] for that Pick function. -/
noncomputable def pickCalc {n k : ℕ} (a b : ℝ) (t w : Fin k → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  a • (1 : Matrix (Fin n) (Fin n) ℝ) + b • A +
    ∑ i, w i • (t i • (1 : Matrix (Fin n) (Fin n) ℝ) - (1 + t i ^ 2) • (A + t i • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹)
/-- Preservation of SIDM by Pick functions (Table 2, row 12), restricted to Pick functions with
finitely supported measure that are positive on (0, ∞), and to upper-triangular matrices with
positive diagonal, whose spectrum lies in (0, ∞) ⊂ D; refuting this restriction refutes the
general preservation statement. -/
def claim : Prop :=
  ∀ (k : ℕ) (a b : ℝ) (t w : Fin k → ℝ), 0 ≤ b → (∀ i, 0 < t i) → (∀ i, 0 ≤ w i) →
    (∀ x : ℝ, 0 < x → 0 < pickFun a b t w x) →
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), IsSIDM A →
      (∀ i j, j < i → A i j = 0) → (∀ i, 0 < A i i) →
      IsSIDM (pickCalc a b t w A)

private def E (s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, s, s ^ 2 / 2, s ^ 3 / 6;
     0, 1, s, s ^ 2 / 2;
     0, 0, 1, s;
     0, 0, 0, 1]

private def C : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 / 2, -1 / 4, 0, 1 / 48;
     0, 1 / 2, -1 / 4, 0;
     0, 0, 1 / 2, -1 / 4;
     0, 0, 0, 1 / 2]

private lemma E_zero : E 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [E, Matrix.one_apply]

private lemma E_mul (s u : ℝ) : E s * E u = E (s + u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private lemma E_pow (s : ℝ) (m : ℕ) : E s ^ m = E ((m : ℝ) * s) := by
  induction m with
  | zero => simp [E_zero]
  | succ m ih => rw [pow_succ, ih, E_mul]; congr 1; push_cast; ring

private lemma E_nonneg (s : ℝ) (hs : 0 ≤ s) : ∀ i j, 0 ≤ E s i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [E] <;> positivity

private lemma E_det (s : ℝ) : (E s).det = 1 := by
  have hu : (E s).IsUpperTriangular := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [E]
  rw [Matrix.det_of_isUpperTriangular hu]
  norm_num [E, Fin.prod_univ_succ]

private lemma sidm_E_one : IsSIDM (E 1) := by
  refine ⟨E_nonneg 1 (by norm_num), ?_, ?_⟩
  · rw [E_det]; exact isUnit_one
  · intro m hm
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    refine ⟨E (1 / (m : ℝ)), E_nonneg _ (by positivity), ?_⟩
    rw [E_pow, mul_one_div_cancel hmR]

private lemma shifted_inverse :
    (E 1 + (1 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ))⁻¹ = C := by
  have hc3 (a : ℝ) (v : Fin 3 → ℝ) :
      Matrix.vecCons a v (3 : Fin 4) = v 2 := rfl
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E, C, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four, Fin.reduceFinMk]
  all_goals norm_num [Fin.ext_iff, Matrix.cons_val_two, hc3]

private lemma pick_positive : ∀ x : ℝ, 0 < x →
    0 < pickFun 1 0 (![1] : Fin 1 → ℝ) (![1] : Fin 1 → ℝ) x := by
  intro x hx
  have hd : 0 < 1 + x := by positivity
  simp only [pickFun, Fin.sum_univ_one, Matrix.cons_val_zero, zero_mul, add_zero,
    one_mul]
  have he : 1 + (x - 1) / (1 + x) = 2 * x / (1 + x) := by
    rw [one_add_div (ne_of_gt hd)]
    congr 1
    ring
  rw [he]
  positivity

private lemma calc_negative :
    pickCalc 1 0 (![1] : Fin 1 → ℝ) (![1] : Fin 1 → ℝ) (E 1) 0 3 = -1 / 24 := by
  simp only [pickCalc, Fin.sum_univ_one, Matrix.cons_val_zero]
  rw [shifted_inverse]
  norm_num [C, Matrix.one_apply, Fin.ext_iff]

theorem result : ¬ claim := by
  intro h
  have hout := h 1 1 0 ![1] ![1] (by norm_num)
    (by intro i; fin_cases i; norm_num)
    (by intro i; fin_cases i; norm_num) pick_positive 4 (E 1) sidm_E_one
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [E])
    (by intro i; fin_cases i <;> norm_num [E])
  have hn := hout.1 0 3
  rw [calc_negative] at hn
  norm_num at hn

end D5.S3.Quantum.Matrix.InfinitelyDivisiblePickRefutation
