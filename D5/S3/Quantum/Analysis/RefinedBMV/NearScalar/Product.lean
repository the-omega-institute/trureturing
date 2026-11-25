/- GID: D5/S3/Quantum/Analysis/RefinedBMV/NearScalar/Product
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proof component of the four-copy refined BMV comparison near a scalar. -/

import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.Taylor
import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.AnalyticTail
import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.Quadratic
import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.TailAssembly

/-! The dimension-free near-scalar bound for the uniform four-part composition mean. -/

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace D5.S3.Quantum.Analysis.RefinedBMVNearScalarProduct

open NormedSpace (exp)
open RefinedBMVNearScalarTaylor (orderedProd hasSum_traceCoeff)
open RefinedBMVNearScalarQuadratic
  (compositionMean defectCoeff defectCoeff_zero defectCoeff_one defectCoeff_two_ge)

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- An exponential block at a natural gap is a power of the single-step exponential. -/
theorem exp_natCast_smul (H : Matrix n n ℂ) (g : ℕ) :
    exp ((g : ℝ) • H) = exp H ^ g := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Matrix n n ℂ)
  rw [Nat.cast_smul_eq_nsmul ℝ, NormedSpace.exp_nsmul]

private theorem defectCoeff_eq_tailAssembly (p : ℕ) (H B : Matrix n n ℂ) (m : ℕ) :
    defectCoeff p H B m = RefinedBMVNearScalarTailAssembly.defectCoeff p H B m := by
  simp only [defectCoeff, compositionMean, RefinedBMVNearScalarTailAssembly.defectCoeff,
    Finset.expect_eq_sum_div_card]

/-- The Taylor coefficients sum to the mean real trace minus the real trace at equal gaps. -/
theorem hasSum_defectCoeff (p : ℕ) (H B : Matrix n n ℂ) :
    HasSum (defectCoeff p H B)
      (compositionMean p (fun g =>
        (Matrix.trace (orderedProd fun i => exp ((g i : ℝ) • H) * B)).re) -
        (Matrix.trace (orderedProd fun _ : Fin 4 => exp (((p : ℝ) / 4) • H) * B)).re) := by
  have hsum := hasSum_sum (s := Finset.Nat.antidiagonalTuple 4 p)
    (fun g _ => hasSum_traceCoeff (fun i => (g i : ℝ)) H B)
  have hmean := hsum.div_const ((Finset.Nat.antidiagonalTuple 4 p).card : ℝ)
  unfold defectCoeff
  simpa only [compositionMean] using
    hmean.sub (hasSum_traceCoeff (fun _ => (p : ℝ) / 4) H B)

open scoped Matrix.Norms.Frobenius

local notation "opNorm" =>
  fun A : Matrix n n ℂ => ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A‖

/-- The uniform composition trace exceeds the trace at equal gaps by a commutator bound. -/
theorem compositionMean_sub_balanced_ge (p : ℕ) (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.PosSemidef) (hx : (p : ℝ) * opNorm H ≤ 1 / 100000) :
    (p : ℝ) ^ 2 * ‖B * (H * B - B * H)‖ ^ 2 / 25 ≤
      compositionMean p (fun g =>
        (Matrix.trace (orderedProd fun i => exp ((g i : ℝ) • H) * B)).re) -
        (Matrix.trace (orderedProd fun _ : Fin 4 => exp (((p : ℝ) / 4) • H) * B)).re := by
  have hquad : (3 / 40) * ((p : ℝ) ^ 2 * ‖B * (H * B - B * H)‖ ^ 2) ≤
      defectCoeff p H B 2 := by
    calc
      _ ≤ ((p : ℝ) * ((p : ℝ) + 4) / 40) * (3 * ‖B * (H * B - B * H)‖ ^ 2) := by
        have hnonneg : 0 ≤ (p : ℝ) * ‖B * (H * B - B * H)‖ ^ 2 := by positivity
        nlinarith only [hnonneg]
      _ ≤ _ := defectCoeff_two_ge p H B hH hB
  obtain ⟨htail, hbound⟩ := RefinedBMVNearScalarAnalyticTail.quadratic_add_tail_ge
    (f := fun j => defectCoeff p H B (j + 3))
    (p := (p : ℝ)) (K := ‖B * (H * B - B * H)‖) (x := (p : ℝ) * opNorm H)
    (quadratic := defectCoeff p H B 2)
    (mul_nonneg (Nat.cast_nonneg p) (norm_nonneg _)) hx
    (fun j => by
      simpa only [← defectCoeff_eq_tailAssembly, show j + 3 - 2 = j + 1 by omega] using
        RefinedBMVNearScalarTailAssembly.abs_defectCoeff_le H B hH hB.isHermitian p
          (j + 3) (by omega)) hquad
  have hseries : HasSum (defectCoeff p H B)
      (defectCoeff p H B 2 + (∑' j : ℕ, defectCoeff p H B (j + 3))) := by
    have hfull := (hasSum_nat_add_iff 3 (f := defectCoeff p H B)).1 htail
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, defectCoeff_zero,
      defectCoeff_one, zero_add, add_zero, add_comm] using hfull
  calc
    _ ≤ _ := hbound
    _ = _ := hseries.unique (hasSum_defectCoeff p H B)

end D5.S3.Quantum.Analysis.RefinedBMVNearScalarProduct
