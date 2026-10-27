/- GID: D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation; result=D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.result; claim=D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.claim
   digest: Seven-qubit diagonal correlance exceeds Hedemann's normalization bound. -/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The diagonal probability-vector model of Hedemann's raw correlance. -/

set_option autoImplicit false
set_option linter.style.longLine false
open scoped BigOperators

@[expose] public section

namespace D5.S3.Quantum.Information.DiagonalCorrelanceNormalizationRefutation

def IsProbability {n : ℕ} (p : (Fin n → Bool) → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

def marginal {n : ℕ} (p : (Fin n → Bool) → ℝ) (i : Fin n) (b : Bool) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => x i = b), p x

def reductionProduct {n : ℕ} (p : (Fin n → Bool) → ℝ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  Matrix.diagonal (fun x => ∏ i, marginal p i (x i))

def correlanceRaw {n : ℕ} (p : (Fin n → Bool) → ℝ) : ℝ :=
  Matrix.trace ((Matrix.diagonal p - reductionProduct p) ^ 2)

def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p : (Fin n → Bool) → ℝ, IsProbability p →
    correlanceRaw p ≤ 1 / 2 - 1 / 2 ^ n

private noncomputable def witness (x : Fin 7 → Bool) : ℝ :=
  (if x = fun _ => false then 3 / 5 else 0) +
    (if x = fun _ => true then 2 / 5 else 0)

private lemma correlanceRaw_eq_sum {n : ℕ} (p : (Fin n → Bool) → ℝ) :
    correlanceRaw p = ∑ x, (p x - ∏ i, marginal p i (x i)) ^ 2 := by
  classical
  unfold correlanceRaw reductionProduct
  rw [Matrix.diagonal_sub, Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

private lemma witness_probability : IsProbability witness := by
  classical
  constructor
  · intro x
    simp only [witness]
    split <;> split <;> norm_num
  · simp [witness, Finset.sum_add_distrib, Finset.sum_ite_eq']
    norm_num

private lemma witness_marginal (i : Fin 7) (b : Bool) :
    marginal witness i b = if b = false then 3 / 5 else 2 / 5 := by
  classical
  unfold marginal
  cases b <;> simp [witness, Finset.sum_add_distrib, Finset.sum_ite_eq']

private noncomputable def q (b : Bool) : ℝ := if b = false then 3 / 5 else 2 / 5

private lemma witness_product (x : Fin 7 → Bool) :
    ∏ i, marginal witness i (x i) = ∏ i, q (x i) := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [witness_marginal]
  rfl

private lemma sum_q_square : (∑ b : Bool, q b ^ 2) = 13 / 25 := by
  simp [q]
  norm_num

private lemma sum_product_q_square :
    (∑ x : Fin 7 → Bool, (∏ i, q (x i)) ^ 2) = (13 / 25) ^ 7 := by
  have hpow (x : Fin 7 → Bool) :
      (∏ i, q (x i)) ^ 2 = ∏ i, q (x i) ^ 2 := by
    rw [pow_two, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [pow_two]
  simp_rw [hpow]
  rw [← Fintype.prod_sum (fun (_ : Fin 7) (b : Bool) => q b ^ 2)]
  norm_num [q]

private lemma sum_witness_square :
    (∑ x : Fin 7 → Bool, witness x ^ 2) = 13 / 25 := by
  have h01 : (fun _ : Fin 7 => false) ≠ fun _ => true := by
    intro h
    have h' := congrFun h (0 : Fin 7)
    cases h'
  have hterm (x : Fin 7 → Bool) : witness x ^ 2 =
      (if x = fun _ => false then (3 / 5 : ℝ) ^ 2 else 0) +
        (if x = fun _ => true then (2 / 5 : ℝ) ^ 2 else 0) := by
    by_cases h0 : x = fun _ => false
    · subst x
      simp [witness, h01]
    · by_cases h1 : x = fun _ => true
      · simp [witness, h0, h1, h01, Ne.symm h01]
      · simp [witness, h0, h1]
  simp_rw [hterm]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq']
  norm_num

private lemma sum_witness_product :
    (∑ x : Fin 7 → Bool, witness x * ∏ i, q (x i)) =
      (3 / 5) ^ 8 + (2 / 5) ^ 8 := by
  have h01 : (fun _ : Fin 7 => false) ≠ fun _ => true := by
    intro h
    have h' := congrFun h (0 : Fin 7)
    cases h'
  have hterm (x : Fin 7 → Bool) : witness x * ∏ i, q (x i) =
      (if x = fun _ => false then (3 / 5 : ℝ) ^ 8 else 0) +
        (if x = fun _ => true then (2 / 5 : ℝ) ^ 8 else 0) := by
    by_cases h0 : x = fun _ => false
    · subst x
      simp [witness, q, h01]
      norm_num
    · by_cases h1 : x = fun _ => true
      · simp [witness, q, h0, h1, h01, Ne.symm h01]
        norm_num
      · simp [witness, q, h0, h1]
  simp_rw [hterm]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq']

private lemma witness_raw : correlanceRaw witness = 3023545392 / 6103515625 := by
  rw [correlanceRaw_eq_sum]
  simp_rw [witness_product]
  calc
    (∑ x : Fin 7 → Bool, (witness x - ∏ i : Fin 7, q (x i)) ^ 2) =
        ∑ x : Fin 7 → Bool, (witness x ^ 2 -
          2 * (witness x * ∏ i : Fin 7, q (x i)) +
          (∏ i : Fin 7, q (x i)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (∑ x : Fin 7 → Bool, witness x ^ 2) -
          2 * (∑ x : Fin 7 → Bool, (witness x *
            (∏ i : Fin 7, q (x i)))) +
          ∑ x : Fin 7 → Bool, ((∏ i : Fin 7, q (x i)) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = 3023545392 / 6103515625 := by
      rw [sum_witness_square, sum_witness_product, sum_product_q_square]
      norm_num

theorem result : ¬ claim := by
  intro h
  have hb := h 7 (by norm_num) witness witness_probability
  rw [witness_raw] at hb
  norm_num at hb

end D5.S3.Quantum.Information.DiagonalCorrelanceNormalizationRefutation
