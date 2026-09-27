/- GID: D5/S3/Quantum/Measurement/FiniteDetectionDarkSpace
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/FiniteDetectionDarkSpace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Repeated-detection dark vectors form the kernel of the dimension-step survival defect. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace

open Matrix
open scoped ComplexOrder

/-- **The dark space is the kernel of the dimension-step survival defect.** Let `Q` be the no-click
operator and `L x` the click operators of a finite outcome family on `ℂᵈ`, with
`Qᴴ Q + ∑ₓ (L x)ᴴ L x = I`. A vector has vanishing click amplitude `L x Qⁿ ψ` at every round `n`
and outcome `x` exactly when it lies in the kernel of `I - (Qᴴ)ᵈ Qᵈ`. The dimension `d = 0` is
included. -/
theorem dark_space_eq_survival_defect_kernel {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℂ) (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1) (ψ : Fin d → ℂ) :
    (∀ n : ℕ, ∀ x : ι, (L x * Q ^ n) *ᵥ ψ = 0) ↔ (1 - (Qᴴ) ^ d * Q ^ d) *ᵥ ψ = 0 := by
  classical
  -- (i) the survival defect telescopes into the Gram operators of the event amplitudes
  have hgram : 1 - (Qᴴ) ^ d * Q ^ d = ∑ n ∈ Finset.range d, ∑ x, (L x * Q ^ n)ᴴ * (L x * Q ^ n) := by
    have hstep : ∀ n, ∑ x, (L x * Q ^ n)ᴴ * (L x * Q ^ n) =
        (Qᴴ) ^ n * Q ^ n - (Qᴴ) ^ (n + 1) * Q ^ (n + 1) := by
      intro n
      have hclick : ∑ x, (L x)ᴴ * L x = 1 - Qᴴ * Q := eq_sub_of_add_eq' hcomp
      calc ∑ x, (L x * Q ^ n)ᴴ * (L x * Q ^ n)
          = (Qᴴ) ^ n * (∑ x, (L x)ᴴ * L x) * Q ^ n := by
            simp only [conjTranspose_mul, conjTranspose_pow, Finset.mul_sum, Finset.sum_mul,
              Matrix.mul_assoc]
        _ = (Qᴴ) ^ n * Q ^ n - (Qᴴ) ^ (n + 1) * Q ^ (n + 1) := by
            rw [hclick, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, pow_succ, pow_succ',
              Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    have htel : ∀ N, ∑ n ∈ Finset.range N, ∑ x, (L x * Q ^ n)ᴴ * (L x * Q ^ n) =
        1 - (Qᴴ) ^ N * Q ^ N := by
      intro N
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, ih, hstep]; abel
    exact (htel d).symm
  -- (ii) positivity: the defect annihilates `ψ` exactly when every early amplitude vanishes
  have hearly : (1 - (Qᴴ) ^ d * Q ^ d) *ᵥ ψ = 0 ↔ ∀ n < d, ∀ x, (L x * Q ^ n) *ᵥ ψ = 0 := by
    have hnonneg : ∀ n x, 0 ≤ star ψ ⬝ᵥ (((L x * Q ^ n)ᴴ * (L x * Q ^ n)) *ᵥ ψ) := fun n x =>
      (posSemidef_conjTranspose_mul_self _).dotProduct_mulVec_nonneg ψ
    have hpsd : (1 - (Qᴴ) ^ d * Q ^ d).PosSemidef := by
      rw [hgram]
      exact posSemidef_sum _ fun n _ => posSemidef_sum _ fun x _ =>
        posSemidef_conjTranspose_mul_self _
    rw [← hpsd.dotProduct_mulVec_zero_iff, hgram, Matrix.sum_mulVec, dotProduct_sum,
      Finset.sum_eq_zero_iff_of_nonneg fun n _ => by
        rw [Matrix.sum_mulVec, dotProduct_sum]
        exact Finset.sum_nonneg fun x _ => hnonneg n x]
    refine forall_congr' fun n => ?_
    rw [Finset.mem_range, Matrix.sum_mulVec, dotProduct_sum,
      Finset.sum_eq_zero_iff_of_nonneg fun x _ => hnonneg n x]
    refine imp_congr_right fun _ => forall_congr' fun x => ?_
    rw [(posSemidef_conjTranspose_mul_self _).dotProduct_mulVec_zero_iff,
      conjTranspose_mul_self_mulVec_eq_zero]
    simp
  -- (iii) Cayley–Hamilton: every power from `d` on is a combination of the `d` preceding ones
  have hcayley : ∀ m, Q ^ (d + m) = -∑ k ∈ Finset.range d, Q.charpoly.coeff k • Q ^ (k + m) := by
    have hlead : Q.charpoly.coeff d = 1 := by
      simpa [charpoly_natDegree_eq_dim] using Q.charpoly_monic.coeff_natDegree
    have hzero : (∑ k ∈ Finset.range d, Q.charpoly.coeff k • Q ^ k) + Q ^ d = 0 := by
      simpa [Polynomial.aeval_eq_sum_range, charpoly_natDegree_eq_dim, Finset.sum_range_succ,
        hlead] using aeval_self_charpoly Q
    intro m
    rw [pow_add, eq_neg_of_add_eq_zero_right hzero, Matrix.neg_mul, Finset.sum_mul]
    simp only [Matrix.smul_mul, pow_add]
  rw [hearly]
  refine ⟨fun h n _ x => h n x, fun h n => ?_⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x
      by_cases hn : n < d
      · exact h n hn x
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
        rw [hcayley, Matrix.mul_neg, Matrix.mul_sum, Matrix.neg_mulVec, Matrix.sum_mulVec,
          neg_eq_zero]
        refine Finset.sum_eq_zero fun k hk => ?_
        rw [Matrix.mul_smul, Matrix.smul_mulVec, ih (k + m) (by
          have := Finset.mem_range.mp hk
          omega) x, smul_zero]

#print axioms dark_space_eq_survival_defect_kernel

end D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace
