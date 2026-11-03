/- GID: D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.claim; result=D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.result; claim=D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.claim
   digest: Seven-qubit diagonal correlance exceeds Hedemann's normalization bound. -/

import D5.S0.Computability.Coding.BiasedMassFrontier
import D5.S3.TotalVariation.CycleSingleCutMinimax

/-! The diagonal probability-vector model of Hedemann's raw correlance. -/

set_option autoImplicit false
set_option linter.style.longLine false
open scoped BigOperators
open D5.S0.Computability.Coding.BiasedMassFrontier (letterMass)
open D5.S3.TotalVariation.CycleSingleCutMinimax (Probability)

namespace D5.S3.Quantum.Information.DiagonalCorrelanceNormalizationRefutation

noncomputable def reductionProduct {n : ℕ} (p : (Fin n → Bool) → ℝ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  Matrix.diagonal (fun x => ∏ i, FunOnFinite.map (fun y => y i) p (x i))

noncomputable def correlanceRaw {n : ℕ} (p : (Fin n → Bool) → ℝ) : ℝ :=
  Matrix.trace ((Matrix.diagonal p - reductionProduct p) ^ 2)

def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p : (Fin n → Bool) → ℝ, Probability p →
    correlanceRaw p ≤ 1 / 2 - 1 / 2 ^ n

private noncomputable def witness (x : Fin 7 → Bool) : ℝ :=
  (if x = fun _ => false then 3 / 5 else 0) +
    (if x = fun _ => true then 2 / 5 else 0)

private lemma correlanceRaw_eq_sum {n : ℕ} (p : (Fin n → Bool) → ℝ) :
    correlanceRaw p = ∑ x, (p x - ∏ i, FunOnFinite.map (fun y => y i) p (x i)) ^ 2 := by
  classical
  unfold correlanceRaw reductionProduct
  rw [Matrix.diagonal_sub, Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

private lemma witness_probability : Probability witness := by
  classical
  constructor
  · intro x
    rw [witness.eq_1]
    split <;> split <;> norm_num
  · simp [witness, Finset.sum_add_distrib, Finset.sum_ite_eq']
    norm_num

private lemma witness_marginal (i : Fin 7) (b : Bool) :
    FunOnFinite.map (fun y => y i) witness b = letterMass (3 / 5) (2 / 5) b := by
  classical
  rw [FunOnFinite.map_apply_apply]
  cases b <;> simp [witness, letterMass, Finset.sum_add_distrib, Finset.sum_ite_eq']

private lemma witness_product (x : Fin 7 → Bool) :
    ∏ i, FunOnFinite.map (fun y => y i) witness (x i) = ∏ i, letterMass (3 / 5) (2 / 5) (x i) := by
  exact Finset.prod_congr rfl fun i _ => witness_marginal i (x i)

private lemma sum_product_q_square :
    (∑ x : Fin 7 → Bool, (∏ i, letterMass (3 / 5) (2 / 5) (x i)) ^ 2) = (13 / 25) ^ 7 := by
  have hpow (x : Fin 7 → Bool) :
      (∏ i, letterMass (3 / 5) (2 / 5) (x i)) ^ 2 = ∏ i, letterMass (3 / 5) (2 / 5) (x i) ^ 2 := by
    exact (Finset.prod_pow _ _ _).symm
  simp_rw [hpow]
  rw [← Fintype.prod_sum (fun (_ : Fin 7) (b : Bool) => letterMass (3 / 5) (2 / 5) b ^ 2)]
  norm_num [letterMass]

private lemma sum_witness_square :
    (∑ x : Fin 7 → Bool, witness x ^ 2) = 13 / 25 := by
  have h01 : (fun _ : Fin 7 => false) ≠ fun _ => true :=
    Function.const_injective.ne Bool.false_ne_true
  have hterm (x : Fin 7 → Bool) : witness x ^ 2 =
      (if x = fun _ => false then (3 / 5 : ℝ) ^ 2 else 0) +
        (if x = fun _ => true then (2 / 5 : ℝ) ^ 2 else 0) := by
    by_cases h0 : x = fun _ => false
    · subst x
      simp [witness, h01]
    · by_cases h1 : x = fun _ => true
      · simp [witness, h1, Ne.symm h01]
      · simp [witness, h0, h1]
  simp_rw [hterm]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq']
  norm_num

private lemma sum_witness_product :
    (∑ x : Fin 7 → Bool, witness x * ∏ i, letterMass (3 / 5) (2 / 5) (x i)) =
      (3 / 5) ^ 8 + (2 / 5) ^ 8 := by
  have h01 : (fun _ : Fin 7 => false) ≠ fun _ => true :=
    Function.const_injective.ne Bool.false_ne_true
  have hterm (x : Fin 7 → Bool) : witness x * ∏ i, letterMass (3 / 5) (2 / 5) (x i) =
      (if x = fun _ => false then (3 / 5 : ℝ) ^ 8 else 0) +
        (if x = fun _ => true then (2 / 5 : ℝ) ^ 8 else 0) := by
    by_cases h0 : x = fun _ => false
    · subst x
      simp [witness, letterMass, h01]
      norm_num
    · by_cases h1 : x = fun _ => true
      · simp [witness, letterMass, h1, Ne.symm h01]
        norm_num
      · simp [witness, letterMass, h0, h1]
  simp_rw [hterm]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq']

private lemma witness_raw : correlanceRaw witness = 3023545392 / 6103515625 := by
  rw [correlanceRaw_eq_sum]
  simp_rw [witness_product]
  calc
    (∑ x : Fin 7 → Bool, (witness x - ∏ i : Fin 7, letterMass (3 / 5) (2 / 5) (x i)) ^ 2) =
        ∑ x : Fin 7 → Bool, (witness x ^ 2 -
          2 * (witness x * ∏ i : Fin 7, letterMass (3 / 5) (2 / 5) (x i)) +
          (∏ i : Fin 7, letterMass (3 / 5) (2 / 5) (x i)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x hx
      simpa only [mul_assoc] using sub_sq (witness x) (∏ i, letterMass (3 / 5) (2 / 5) (x i))
    _ = (∑ x : Fin 7 → Bool, witness x ^ 2) -
          2 * (∑ x : Fin 7 → Bool, (witness x *
            (∏ i : Fin 7, letterMass (3 / 5) (2 / 5) (x i)))) +
          ∑ x : Fin 7 → Bool, ((∏ i : Fin 7, letterMass (3 / 5) (2 / 5) (x i)) ^ 2) := by
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
