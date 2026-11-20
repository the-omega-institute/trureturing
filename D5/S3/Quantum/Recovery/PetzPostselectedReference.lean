import D5.S3.Quantum.Recovery.PetzPostselectionSpectralJensen
import D5.S3.Quantum.Recovery.PetzSingularInputLimit
import D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
import D5.S3.Quantum.Lieb.PositiveMapJensen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Exact identities for postselected references

The symmetric Schatten bound controls the trace norm of a Gram difference
by the overlap of two unit amplitudes. For a commuting postselection, the
square-root product and the finite trace-log loss are determined by its weight.
-/

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_add_le traceNorm_nonneg)
open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (entryNormSq)
open D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM (traceNorm_gram_le)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_smul_nonneg)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (density_posSemidef)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
  (finiteTraceLogRelativeEntropy)
open D5.S3.Quantum.Lieb.PositiveMapJensen (cfc_intertwining)
open PetzPostselectionSpectralJensen (stateMatrix)

namespace PetzPostselectedReference

section Amplitudes

variable {m n : Type*} [Fintype m] [Fintype n]

private theorem entryNormSq_eq_frobenius_sq (X : Matrix m n ℂ) :
    entryNormSq X = ‖X‖ ^ 2 := by
  change (∑ i, ∑ j, ‖X i j‖ ^ 2) =
    ‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (X i))‖ ^ 2
  simp only [PiLp.norm_sq_eq_of_L2]

private theorem traceNorm_mul_adjoint_le_frobenius (X Y : Matrix m n ℂ) :
    traceNorm (X * Yᴴ) ≤ ‖X‖ * ‖Y‖ := by
  simpa only [Matrix.conjTranspose_conjTranspose, entryNormSq_eq_frobenius_sq,
    Real.sqrt_sq_eq_abs, abs_norm, Matrix.frobenius_norm_conjTranspose] using
    traceNorm_gram_le Xᴴ Yᴴ

private theorem trace_adjoint_mul_self_re (X : Matrix m n ℂ) :
    (Xᴴ * X).trace.re = ‖X‖ ^ 2 := by
  have h : ((‖X‖ ^ 2 : ℝ) : ℂ) = (Xᴴ * X).trace := by
    rw [← entryNormSq_eq_frobenius_sq, entryNormSq, Complex.ofReal_sum]
    simp_rw [Complex.ofReal_sum]
    simp only [Complex.ofReal_pow, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_mul']
    rw [Finset.sum_comm]
  simpa only [Complex.ofReal_re] using (congrArg Complex.re h).symm

/-- The symmetric product identity gives the squared trace error in terms of
the real Hilbert–Schmidt overlap of two unit amplitudes. -/
theorem traceNorm_gram_sub_sq_le [DecidableEq m] (A B : Matrix m n ℂ)
    (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) :
    traceNorm (A * Aᴴ - B * Bᴴ) ^ 2 ≤ 4 * (1 - (Aᴴ * B).trace.re ^ 2) := by
  let X := A - B
  let Y := A + B
  let D := A * Aᴴ - B * Bᴴ
  let c := (Aᴴ * B).trace.re
  have hsym : ((2 : ℝ) : ℂ) • D = X * Yᴴ + Y * Xᴴ := by
    rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num, two_smul]
    simp only [D, X, Y, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add]
    abel
  have hdouble : 2 * traceNorm D ≤ 2 * (‖X‖ * ‖Y‖) := by
    calc
      _ = traceNorm (((2 : ℝ) : ℂ) • D) := (traceNorm_smul_nonneg D 2 (by norm_num)).symm
      _ = traceNorm (X * Yᴴ + Y * Xᴴ) := by rw [hsym]
      _ ≤ traceNorm (X * Yᴴ) + traceNorm (Y * Xᴴ) := traceNorm_add_le _ _
      _ ≤ ‖X‖ * ‖Y‖ + ‖Y‖ * ‖X‖ :=
        add_le_add (traceNorm_mul_adjoint_le_frobenius X Y) (traceNorm_mul_adjoint_le_frobenius Y X)
      _ = _ := by ring
  have hcross : (Bᴴ * A).trace.re = c := by
    have hs : (Aᴴ * B)ᴴ = Bᴴ * A := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [← hs, Matrix.trace_conjTranspose] <;> rfl
  have hX : ‖X‖ ^ 2 = 2 - 2 * c := by
    rw [← trace_adjoint_mul_self_re]
    simp only [X, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.trace_sub, Complex.sub_re, trace_adjoint_mul_self_re, hcross, hA, hB]
    change (1 : ℝ) ^ 2 - c - (c - 1 ^ 2) = _
    ring
  have hY : ‖Y‖ ^ 2 = 2 + 2 * c := by
    rw [← trace_adjoint_mul_self_re]
    simp only [Y, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
      Matrix.trace_add, Complex.add_re, trace_adjoint_mul_self_re, hcross, hA, hB]
    change (1 : ℝ) ^ 2 + c + (c + 1 ^ 2) = _
    ring
  have hbound : traceNorm D ≤ ‖X‖ * ‖Y‖ := by linarith only [hdouble]
  change traceNorm D ^ 2 ≤ 4 * (1 - c ^ 2)
  calc
    _ ≤ (‖X‖ * ‖Y‖) ^ 2 := pow_le_pow_left₀ (traceNorm_nonneg _) hbound 2
    _ = 4 * (1 - c ^ 2) := by rw [mul_pow, hX, hY]; ring

end Amplitudes

section Postselection

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R S P : Matrix n n ℂ} {t : ℝ}

omit [DecidableEq n] in
private theorem postselection_intertwines (hSP : Commute S P) (hPP : P * P = P)
    (hR : R = t⁻¹ • (S * P)) (ht : 0 < t) :
    Commute R S ∧ R * S = (t • R) * R := by
  have hscaled : t • R = S * P := by rw [hR, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hRP : R * P = R := by rw [hR, Matrix.smul_mul, Matrix.mul_assoc, hPP]
  have hcomm : Commute R S := by
    change R * S = S * R
    rw [hR, Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    rw [Matrix.mul_assoc, ← hSP.eq, ← Matrix.mul_assoc]
  refine ⟨hcomm, ?_⟩
  calc
    R * S = (R * P) * S := by rw [hRP]
    _ = R * (S * P) := by rw [Matrix.mul_assoc, ← hSP.eq]
    _ = (t • R) * R := by rw [← hscaled, Matrix.mul_smul, Matrix.smul_mul]

private theorem cfc_sqrt_eq_sqrt {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    cfc Real.sqrt X = CFC.sqrt X := by
  symm
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ _ hX.nonneg]
  apply cfc_congr
  intro x hx
  change (NNReal.sqrt x.toNNReal : ℝ) = Real.sqrt x
  rw [Real.coe_sqrt, Real.coe_toNNReal x (spectrum_nonneg_of_nonneg hX.nonneg hx)]

/-- On a commuting postselection, the two square roots multiply to a
scalar multiple of the normalized input. -/
theorem sqrt_mul_sqrt_of_postselection (hRpos : R.PosSemidef) (hSpos : S.PosSemidef)
    (hSP : Commute S P) (hPP : P * P = P) (ht : 0 < t)
    (hR : R = t⁻¹ • (S * P)) :
    cfc Real.sqrt R * cfc Real.sqrt S = Real.sqrt t • R := by
  obtain ⟨hcomm, hRS⟩ := postselection_intertwines hSP hPP hR ht
  rw [cfc_sqrt_eq_sqrt hRpos, cfc_sqrt_eq_sqrt hSpos]
  let U := CFC.sqrt R
  let V := CFC.sqrt S
  have hUV : Commute U V := by
    dsimp only [U, V]
    simp only [CFC.sqrt_eq_cfc]
    exact ((hcomm.cfc_nnreal NNReal.sqrt).symm.cfc_nnreal NNReal.sqrt).symm
  have hsq : (U * V) * (U * V) = R * S := by
    calc
      _ = U * (V * U) * V := by simp only [Matrix.mul_assoc]
      _ = (U * U) * (V * V) := by rw [hUV.symm.eq]; simp only [Matrix.mul_assoc]
      _ = R * S := by
        rw [show U * U = R from CFC.sqrt_mul_sqrt_self R hRpos.nonneg,
          show V * V = S from CFC.sqrt_mul_sqrt_self S hSpos.nonneg]
  have hsq' : (Real.sqrt t • R) * (Real.sqrt t • R) = R * S := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt ht.le,
      hRS, Matrix.smul_mul]
  exact (CFC.sqrt_unique hsq
    (Commute.mul_nonneg (CFC.sqrt_nonneg R) (CFC.sqrt_nonneg S) hUV)).symm.trans
      (CFC.sqrt_unique hsq' (hRpos.smul (Real.sqrt_nonneg t)).nonneg)

/-- The finite spectral logarithms on the input and the reference differ by
the scalar `-log t` after multiplication by the postselected input. -/
private theorem mul_log_sub_log_of_postselection (hRpos : R.PosSemidef)
    (hSpos : S.PosSemidef) (hSP : Commute S P) (hPP : P * P = P) (ht : 0 < t)
    (hR : R = t⁻¹ • (S * P)) :
    R * (cfc Real.log R - cfc Real.log S) = (-Real.log t) • R := by
  obtain ⟨_, hRS⟩ := postselection_intertwines hSP hPP hR ht
  have hscaled := (cfc_comp_const_mul t Real.log R
    ((R.finite_real_spectrum.image (t * ·)).continuousOn _)
    hRpos.isHermitian.isSelfAdjoint).symm
  have hlog := cfc_intertwining (t • R) S (hRpos.smul ht.le).isHermitian
    hSpos.isHermitian R hRS.symm Real.log
  rw [hscaled] at hlog
  have hcross : R * cfc Real.log S = R * cfc (fun x : ℝ => Real.log (t * x)) R :=
    hlog.symm.trans (((Commute.refl R).cfc_real (fun x : ℝ => Real.log (t * x))).eq)
  have hid := cfc_id' ℝ R hRpos.isHermitian.isSelfAdjoint
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ R) :=
    R.finite_real_spectrum.continuousOn _
  calc
    _ = R * cfc (fun x : ℝ => Real.log x - Real.log (t * x)) R := by
      rw [Matrix.mul_sub, hcross, cfc_sub Real.log (fun x : ℝ => Real.log (t * x)) R
        (hcont _) (hcont _), Matrix.mul_sub]
    _ = cfc (fun x : ℝ => x * (Real.log x - Real.log (t * x))) R := by
      rw [cfc_mul (fun x : ℝ => x) (fun x => Real.log x - Real.log (t * x)) R
        (hcont _) (hcont _), hid]
    _ = cfc (fun x : ℝ => -Real.log t * x) R := by
      apply cfc_congr
      intro x _
      change x * (Real.log x - Real.log (t * x)) = -Real.log t * x
      by_cases hx : x = 0
      · simp [hx]
      · rw [Real.log_mul ht.ne' hx]; ring
    _ = _ := by rw [cfc_const_mul (-Real.log t) (fun x : ℝ => x) R (hcont _), hid]

theorem finiteTraceLogRelativeEntropy_of_postselection (ρ σ : DensityState n)
    (hSP : Commute (stateMatrix σ) P) (hPP : P * P = P) (ht : 0 < t)
    (hρ : stateMatrix ρ = t⁻¹ • (stateMatrix σ * P)) :
    finiteTraceLogRelativeEntropy ρ σ = -Real.log t := by
  have h := mul_log_sub_log_of_postselection
    (density_posSemidef ρ) (density_posSemidef σ) hSP hPP ht hρ
  have htr : (stateMatrix ρ).trace = 1 := ρ.2.2
  rw [PetzSingularInputLimit.finiteTraceLog_eq_raw,
    PetzOverlapEntropyDerivative.faithfulRelativeEntropy, h, Matrix.trace_smul, htr]
  simp only [Complex.real_smul, mul_one, Complex.ofReal_re]

end Postselection

end PetzPostselectedReference
