/- GID: D5/S3/Quantum/Schatten/ExpandingNormProduct
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/ExpandingNormProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lower bounds on expanding matrices imply inverse-adjoint norm product bounds. -/

import D5.S3.Quantum.Schatten.UINormContinuity
import D5.S3.Quantum.Schatten.ExpandingAverage

/-! The inverse-adjoint balance transfers expanding-factor lower bounds to products. -/

noncomputable section
open Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Schatten.UINorm

/-- A uniform norm lower bound on expanding middle factors gives the balanced product bound. -/
theorem sq_le_product_of_expanding_lower_bound {n : ℕ} (ν : UINorm n)
    (A B : Matrix (Fin n) (Fin n) ℂ) (m : ℝ) (hm : 0 ≤ m)
    (hlower : ∀ T : Matrix (Fin n) (Fin n) ℂ, (Tᴴ * T - 1).PosSemidef →
      m ≤ ν.N (A * T * B))
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : IsUnit W.det) :
    m ^ 2 ≤ ν.N (A * W * B) * ν.N (A * (W⁻¹)ᴴ * B) := by
  apply sq_le_mul_of_balanced_bounds m _ _ hm (ν.nonneg _) (ν.nonneg _)
  intro t ht
  have hreal (c : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) (hc : 0 ≤ c) :
      ν.N (c • X) = c * ν.N X := by
    have heq : c • X = (c : ℂ) • X := by
      ext i j
      simp [Complex.real_smul]
    rw [heq, ν.smul_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  have heq : A * inverseAdjointAverage W t * B =
      (1 / 2 : ℝ) • (t • (A * W * B) + t⁻¹ • (A * (W⁻¹)ᴴ * B)) := by
    simp only [inverseAdjointAverage, mul_smul_comm, smul_mul_assoc, mul_add, add_mul]
  have hl := hlower (inverseAdjointAverage W t) (inverseAdjointAverage_expanding W hW t ht)
  have hu : ν.N (A * inverseAdjointAverage W t * B) ≤
      (1 / 2 : ℝ) * (t * ν.N (A * W * B) + t⁻¹ * ν.N (A * (W⁻¹)ᴴ * B)) := by
    rw [heq, hreal _ _ (by norm_num)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc
      ν.N (t • (A * W * B) + t⁻¹ • (A * (W⁻¹)ᴴ * B)) ≤
          ν.N (t • (A * W * B)) + ν.N (t⁻¹ • (A * (W⁻¹)ᴴ * B)) := ν.add_le _ _
      _ = t * ν.N (A * W * B) + t⁻¹ * ν.N (A * (W⁻¹)ᴴ * B) := by
        rw [hreal t _ ht.le, hreal t⁻¹ _ (inv_nonneg.mpr ht.le)]
  linarith

end D5.S3.Quantum.Schatten.UINorm
