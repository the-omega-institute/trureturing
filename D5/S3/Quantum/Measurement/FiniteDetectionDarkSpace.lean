/- GID: D5/S3/Quantum/Measurement/FiniteDetectionDarkSpace
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/FiniteDetectionDarkSpace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Repeated-detection dark vectors form the kernel of the dimension-step survival defect. -/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- For a complete finite family consisting of one no-click operator and
finitely many click operators, annihilation by every time-shifted click
operator is equivalent to lying in the kernel of the dimension-step survival
defect. The statement includes the zero-dimensional case. -/
theorem dark_space_eq_survival_defect_kernel
    {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1)
    (ψ : Fin d → ℂ) :
    (∀ n : ℕ, ∀ x : ι, (L x * Q ^ n).mulVec ψ = 0) ↔
      (1 - (Qᴴ) ^ d * Q ^ d).mulVec ψ = 0 := by
  classical
  have hclick : ∑ x, (L x)ᴴ * L x = 1 - Qᴴ * Q := by
    exact eq_sub_of_add_eq (by simpa only [add_comm] using hcomp)
  have honeStep (n : ℕ) :
      ∑ x, (L x * Q ^ n)ᴴ * (L x * Q ^ n) =
        (Qᴴ) ^ n * Q ^ n - (Qᴴ) ^ (n + 1) * Q ^ (n + 1) := by
    calc
      ∑ x, (L x * Q ^ n)ᴴ * (L x * Q ^ n) =
          (Qᴴ) ^ n * (∑ x, (L x)ᴴ * L x) * Q ^ n := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_pow,
          Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
      _ = (Qᴴ) ^ n * Q ^ n - (Qᴴ) ^ (n + 1) * Q ^ (n + 1) := by
        rw [hclick]
        simp only [mul_sub, sub_mul, mul_one, pow_succ, Matrix.mul_assoc]
        rw [show Q * Q ^ n = Q ^ n * Q by
          exact (pow_succ' Q n).symm.trans (pow_succ Q n)]
  have htelescoping (N : ℕ) :
      (∑ n ∈ Finset.range N, ∑ x, (L x * Q ^ n)ᴴ * (L x * Q ^ n)) +
          (Qᴴ) ^ N * Q ^ N = 1 := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, honeStep]
        simpa only [add_assoc, sub_add_cancel] using ih
  have hgram :
      ∑ n ∈ Finset.range d, ∑ x, (L x * Q ^ n)ᴴ * (L x * Q ^ n) =
        1 - (Qᴴ) ^ d * Q ^ d := by
    exact eq_sub_of_add_eq (htelescoping d)
  constructor
  · intro hall
    rw [← hgram, Matrix.sum_mulVec]
    apply Finset.sum_eq_zero
    intro n hn
    rw [Matrix.sum_mulVec]
    apply Finset.sum_eq_zero
    intro x hx
    exact (Matrix.conjTranspose_mul_self_mulVec_eq_zero (L x * Q ^ n) ψ).mpr
      (hall n x)
  · intro hdefect
    have hquad :
        star ψ ⬝ᵥ
            ((∑ n ∈ Finset.range d,
              ∑ x, (L x * Q ^ n)ᴴ * (L x * Q ^ n)) *ᵥ ψ) = 0 := by
      rw [hgram, hdefect]
      simp
    rw [Matrix.sum_mulVec, dotProduct_sum] at hquad
    have hprefix : ∀ n < d, ∀ x : ι, (L x * Q ^ n).mulVec ψ = 0 := by
      intro n hn x
      have hnquad :
          star ψ ⬝ᵥ
              ((∑ x, (L x * Q ^ n)ᴴ * (L x * Q ^ n)) *ᵥ ψ) = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg (fun k hk =>
          (Matrix.posSemidef_sum (Finset.univ : Finset ι) (fun y _ =>
            Matrix.posSemidef_conjTranspose_mul_self (L y * Q ^ k))).dotProduct_mulVec_nonneg ψ)).mp
            hquad n (Finset.mem_range.mpr hn)
      rw [Matrix.sum_mulVec, dotProduct_sum] at hnquad
      have hxquad :
          star ψ ⬝ᵥ (((L x * Q ^ n)ᴴ * (L x * Q ^ n)) *ᵥ ψ) = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg (fun y hy =>
          (Matrix.posSemidef_conjTranspose_mul_self (L y * Q ^ n)).dotProduct_mulVec_nonneg ψ)).mp
            hnquad x (Finset.mem_univ x)
      have hxgram : ((L x * Q ^ n)ᴴ * (L x * Q ^ n)).mulVec ψ = 0 :=
        ((Matrix.posSemidef_conjTranspose_mul_self (L x * Q ^ n)).dotProduct_mulVec_zero_iff ψ).mp
          hxquad
      exact (Matrix.conjTranspose_mul_self_mulVec_eq_zero (L x * Q ^ n) ψ).mp hxgram
    have hmatrixRecurrence :
        Q ^ d = -∑ k ∈ Finset.range d, Q.charpoly.coeff k • Q ^ k := by
      have hLeading : Q.charpoly.coeff d = 1 := by
        simpa [Matrix.charpoly_natDegree_eq_dim] using
          Q.charpoly_monic.coeff_natDegree
      have hCayley :
          (∑ k ∈ Finset.range d, Q.charpoly.coeff k • Q ^ k) + Q ^ d = 0 := by
        simpa [Polynomial.aeval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim,
          Finset.sum_range_succ, hLeading] using
          Matrix.aeval_self_charpoly Q
      exact eq_neg_of_add_eq_zero_right hCayley
    have hpowerRecurrence (m : ℕ) :
        Q ^ (d + m) =
          -∑ k ∈ Finset.range d, Q.charpoly.coeff k • Q ^ (k + m) := by
      calc
        Q ^ (d + m) = Q ^ d * Q ^ m := pow_add Q d m
        _ = (-∑ k ∈ Finset.range d, Q.charpoly.coeff k • Q ^ k) * Q ^ m := by
          rw [hmatrixRecurrence]
        _ = -∑ k ∈ Finset.range d, Q.charpoly.coeff k • Q ^ (k + m) := by
          simp [Finset.sum_mul, pow_add]
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x
        by_cases hn : n < d
        · exact hprefix n hn x
        · have hdn : d ≤ n := Nat.le_of_not_gt hn
          let m := n - d
          have hdm : d + m = n := by
            dsimp [m]
            omega
          rw [← hdm, hpowerRecurrence]
          simp only [Matrix.mul_neg, Matrix.mul_sum, Matrix.mul_smul,
            Matrix.neg_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec]
          apply neg_eq_zero.mpr
          apply Finset.sum_eq_zero
          intro k hk
          rw [ih (k + m) (by
            have hkd : k < d := Finset.mem_range.mp hk
            omega) x]
          simp

/-- The hypotheses are inhabited already in dimension two: take a zero
no-click operator and the identity as the sole click operator. -/
example :
    ∃ (Q : Matrix (Fin 2) (Fin 2) ℂ)
      (L : Unit → Matrix (Fin 2) (Fin 2) ℂ),
      Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1 := by
  refine ⟨0, fun _ => 1, ?_⟩
  simp

#print axioms dark_space_eq_survival_defect_kernel

end D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace
