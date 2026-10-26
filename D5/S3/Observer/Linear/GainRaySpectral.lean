/- GID: D5/S3/Observer/Linear/GainRaySpectral
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRaySpectral
   mirror-E: none(waiver:literal-source-weighted-spectral-expansion)
   anchors: [mathlib/module/Mathlib.NumberTheory.Real.GoldenRatio]
   utility: none
   digest: The literal M trajectory has its source-weighted golden spectral expansion without a contracting-weight sign restriction. -/

import D5.S3.Observer.Linear.GainRaySources
import D5.S0.Observation.MatrixTracePowerSum
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
Native gain-ray spectral identities.
-/

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace D5.S3.Observer.Linear.GainRay

abbrev phi : ℝ := Real.goldenRatio
abbrev psi : ℝ := Real.goldenConj

def spectralPlus : Mat := (phi - psi)⁻¹ • (action false - psi • (1 : Mat))
def spectralMinus : Mat := (phi - psi)⁻¹ • (phi • (1 : Mat) - action false)
def alpha (S : Mat) : ℝ := Matrix.trace (spectralPlus * S)
def eta (S : Mat) : ℝ := Matrix.trace (spectralMinus * S)

private theorem spectral_gap : 0 < phi - psi :=
  sub_pos.mpr (lt_trans Real.goldenConj_neg Real.goldenRatio_pos)

private theorem spectral_sum : spectralPlus + spectralMinus = (1 : Mat) := by
  unfold spectralPlus spectralMinus
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  field_simp
  <;> ring

private theorem spectral_first : phi • spectralPlus + psi • spectralMinus = action false := by
  unfold spectralPlus spectralMinus
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  field_simp
  <;> ring

private theorem native_trace_det : Matrix.trace (action false) = 1 ∧
    Matrix.det (action false) = -1 := by
  norm_num [action, D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
    D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
    Matrix.trace, Fin.sum_univ_two, Matrix.det_fin_two]

private theorem spectral_power (i : ℕ) :
    action false ^ i = phi ^ i • spectralPlus + psi ^ i • spectralMinus := by
  induction i using Nat.twoStepInduction with
  | zero => simpa using spectral_sum.symm
  | one => simpa using spectral_first.symm
  | more n ih₀ ih₁ =>
    rw [D5.S0.Observation.MatrixTracePowerSum.pow_add_two,
      native_trace_det.1, native_trace_det.2, one_smul, neg_one_smul, sub_neg_eq_add,
      ih₀, ih₁]
    have hφ : phi ^ (n + 2) = phi ^ (n + 1) + phi ^ n := by
      rw [pow_add _ n 2, Real.goldenRatio_sq, pow_succ]; ring
    have hψ : psi ^ (n + 2) = psi ^ (n + 1) + psi ^ n := by
      rw [pow_add _ n 2, Real.goldenConj_sq, pow_succ]; ring
    rw [hφ, hψ, add_smul, add_smul]
    abel

/-- The expansion is for the source-weighted trace, on every auxiliary matrix. -/
theorem pureM_spectral (S : Mat) (i : ℕ) :
    Matrix.trace (acquisition (List.replicate i false) * S) =
      alpha S * phi ^ i + eta S * psi ^ i := by
  rw [acquisition_pure, spectral_power, Matrix.add_mul, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
  simp only [alpha, eta, smul_eq_mul]
  ring

/-- Only the expanding source weight has a positivity requirement. -/
theorem legal_spectral_weights (P : Mat) (hP : LegalSource P) :
    0 < alpha P ∧ alpha P + eta P = 1 := by
  have hsum : alpha P + eta P = Matrix.trace P := by
    rw [alpha, eta, ← Matrix.trace_add, ← Matrix.add_mul, spectral_sum, one_mul]
  refine ⟨?_, hsum.trans hP.2.2⟩
  have hi : 0 < (phi - psi)⁻¹ := inv_pos.mpr spectral_gap
  have hp (i j : Fin 2) : 0 < spectralPlus i j := by
    change 0 < (phi - psi)⁻¹ * (action false - psi • (1 : Mat)) i j
    apply mul_pos hi
    fin_cases i <;> fin_cases j <;>
      norm_num [action, D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
        D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM] <;>
      linarith [Real.goldenConj_neg]
  unfold alpha
  simpa [Matrix.trace, Matrix.mul_apply, dotProduct, Fin.sum_univ_two] using
    add_pos (add_pos (mul_pos (hp 0 0) (hP.1 0 0))
      (mul_pos (hp 0 1) (hP.1 1 0)))
      (add_pos (mul_pos (hp 1 0) (hP.1 0 1)) (mul_pos (hp 1 1) (hP.1 1 1)))

/-- Auxiliary projectors separate the two source functionals in universal identities. -/
theorem spectral_basis_weights :
    alpha spectralPlus = 1 ∧ eta spectralPlus = 0 ∧
      alpha spectralMinus = 0 ∧ eta spectralMinus = 1 := by
  have hψ : psi = 1 - phi := by linarith [Real.goldenRatio_add_goldenConj]
  have hz : phi - psi ≠ 0 := ne_of_gt spectral_gap
  have hsq := Real.goldenRatio_sq
  unfold alpha eta spectralPlus spectralMinus
  norm_num [action, D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
    D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
    Matrix.trace, Matrix.mul_apply, dotProduct, Fin.sum_univ_two]
  rw [hψ] at hz ⊢
  field_simp
  repeat' constructor
  all_goals nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

/-- Every bounded prefix uses its original clock, including the initial clock zero. -/
theorem pureM_readAt {d : ℕ} (W : World d) (n i : ℕ) (hi : i ≤ n) :
    readAt W (List.replicate n false) i =
      (gain d W.coeff).eval (i : ℝ) *
        (alpha W.source * phi ^ i + eta W.source * psi ^ i) + W.drift := by
  simp only [readAt, List.take_replicate, min_eq_left hi]
  rw [pureM_spectral]

#print axioms pureM_spectral
#print axioms legal_spectral_weights
#print axioms pureM_readAt
end D5.S3.Observer.Linear.GainRay
