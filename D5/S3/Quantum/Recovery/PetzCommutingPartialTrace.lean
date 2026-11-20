import D5.S3.Quantum.Recovery.PetzTriangularOrbit
import D5.S3.Quantum.Recovery.PetzFaithfulDimensionRecovery
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Ordinary Petz recovery for commuting retained matrices

For the physical right partial trace, commutation of the actual marginals
makes every rotated Petz output a conjugate of the ordinary output by the
joint reference's modular unitary. The physical upper-strip amplitude then
bounds the triangular divergence along that orbit.

The research dependencies of `PetzFaithfulDimensionRecovery` are
`PetzPhysicalAmplitude`, `PetzPhysicalCoordinates`,
`PetzOverlapEntropyDerivative`, and `PetzBoundaryTraceConsumer`. These five
files use the module prefix `D5.S3.Quantum.Recovery`. The partial-trace
positivity and duality lemmas come from `UmegakiKernelContraction`.
-/

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory
open CStarMatrix (ofMatrix)
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (partialTraceRight_posDef)
open D5.S3.Quantum.GNSMatrix (frobenius_norm_sq_eq_trace)
open D5.S3.Quantum.Recovery.PetzTriangularOrbit
  (phase modularUnitary conjugate conjugateState tracePair hsSq triangular
    triangular_le_two_upperDeficit triangular_le_twice_integral_modularOrbit
    traceNorm_sub_sq_le_two_triangular)
open PetzPhysicalAmplitude
open PetzPhysicalCoordinates (weighted_evaluation_physical_boundary)
open PetzOverlapEntropyDerivative (entropyLoss)
open PetzExponentialBoundaryEvaluation (petzWeight)
open PetzFaithfulDimensionRecovery (upper_boundary_integral_le_entropyLoss)

namespace PetzCommutingPartialTrace

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}

/-- Apply real functional calculus to the two components of each complex
spectral value. This also handles degenerate eigenvalues. -/
private theorem spectralCPow_commute (hX : X.PosDef) (hXY : Commute X Y) (z : ℂ) :
    Commute (spectralCPow hX z) Y := by
  let rePower : ℝ → ℝ := fun x => ((x : ℂ) ^ z).re
  let imPower : ℝ → ℝ := fun x => ((x : ℂ) ^ z).im
  have hDiag :
      Matrix.diagonal (fun i => (hX.isHermitian.eigenvalues i : ℂ) ^ z) =
        Matrix.diagonal (fun i => (rePower (hX.isHermitian.eigenvalues i) : ℂ)) +
          Complex.I • Matrix.diagonal (fun i => (imPower (hX.isHermitian.eigenvalues i) : ℂ)) := by
    rw [← Matrix.diagonal_smul, Matrix.diagonal_add]
    apply congrArg Matrix.diagonal
    funext i
    let w := (hX.isHermitian.eigenvalues i : ℂ) ^ z
    change w = (w.re : ℂ) + Complex.I * (w.im : ℂ)
    rw [mul_comm Complex.I]
    exact (Complex.re_add_im w).symm
  have hPower :
      spectralCPow hX z = cfc rePower X + Complex.I • cfc imPower X := by
    unfold spectralCPow
    rw [hDiag, map_add, map_smul] <;>
      simp only [hX.isHermitian.cfc_eq, Matrix.IsHermitian.cfc, Function.comp_def,
        RCLike.ofReal_eq_complex_ofReal]
  have hRe : Commute (cfc rePower X) Y := hXY.cfc_real rePower
  have hIm : Commute (cfc imPower X) Y := hXY.cfc_real imPower
  have hScaled : Commute (Complex.I • cfc imPower X) Y := by
    change (Complex.I • cfc imPower X) * Y = Y * (Complex.I • cfc imPower X)
    rw [Matrix.smul_mul, Matrix.mul_smul, hIm.eq]
  rw [hPower]
  exact hRe.add_left hScaled

/-- The positive reference power uses the same sign and time parameter as the
modular orbit of the triangular divergence. -/
theorem spectralCPow_imaginary_eq_modularUnitary (hX : X.PosDef) (t : ℝ) :
    spectralCPow hX ((t : ℂ) * Complex.I) =
      (modularUnitary hX.isHermitian.eigenvectorUnitary
        (fun i => Real.log (hX.isHermitian.eigenvalues i)) t).val := by
  let U := hX.isHermitian.eigenvectorUnitary
  have hDiag :
      Matrix.diagonal (fun i => (hX.isHermitian.eigenvalues i : ℂ) ^ ((t : ℂ) * Complex.I)) =
        Matrix.diagonal (fun i => phase (Real.log (hX.isHermitian.eigenvalues i)) t) := by
    apply congrArg Matrix.diagonal
    funext i
    have hi := hX.eigenvalues_pos i
    rw [phase, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hi.ne'),
      ← Complex.ofReal_log hi.le, Complex.ofReal_mul, mul_assoc]
  change Unitary.conjStarAlgAut ℂ _ U
      (Matrix.diagonal (fun i => (hX.isHermitian.eigenvalues i : ℂ) ^ ((t : ℂ) * Complex.I))) =
    U.val * Matrix.diagonal (fun i => phase (Real.log (hX.isHermitian.eigenvalues i)) t) * U.valᴴ
  rw [hDiag, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]

private theorem upperExponent_add_star_eq_one (t : ℝ) :
    upperExponent t + star (upperExponent t) = 1 := by
  have hstar : star (upperExponent t) = ((1 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I := by
    simp only [upperExponent, star_add, Complex.star_def, map_mul, Complex.conj_ofReal,
      Complex.conj_I, mul_neg, sub_eq_add_neg]
  calc
    _ = ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) := by rw [hstar, upperExponent]; ring
    _ = 1 := by rw [← Complex.ofReal_add, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
      Complex.ofReal_one]

private def densityOfMatrix (X : Matrix n n ℂ) (hX : X.PosSemidef) (htrace : X.trace = 1) :
    DensityState n :=
  ⟨ofMatrix X, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hX.nonneg, htrace⟩

private theorem frobenius_sq_eq_hsSq (X : Matrix n n ℂ) : ‖X‖ ^ 2 = hsSq X := by
  simpa only [hsSq, tracePair, Complex.ofReal_re] using
    congrArg Complex.re (frobenius_norm_sq_eq_trace X)

end Spectral

section PartialTrace

universe u

variable {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {ρ σ : Matrix (A × B) (A × B) ℂ}

section NonemptyErased

variable [Nonempty B]

/-- With commuting actual marginals, the rotated Petz state is exactly the
joint-reference modular conjugate of the ordinary Petz state. -/
theorem rotatedPetz_eq_modularOrbit (hσ : σ.PosDef)
    (hcomm : Commute (partialTraceRight ρ) (partialTraceRight σ)) (t : ℝ) :
    rotatedPetz ρ hσ t =
      conjugate (modularUnitary hσ.isHermitian.eigenvectorUnitary
          (fun i => Real.log (hσ.isHermitian.eigenvalues i)) t)
        (ordinaryPetz σ (partialTraceRight ρ)) := by
  let hq := partialTraceRight_posDef (R := A) (a := B) σ hσ
  have hRetained (s : ℝ) :
      spectralCPow hq (-(upperExponent s)) * partialTraceRight ρ *
          spectralCPow hq (-(star (upperExponent s))) =
        partialTraceRight ρ * spectralCPow hq (-1) := by
    have h := spectralCPow_commute hq hcomm.symm (-(upperExponent s))
    rw [h.eq, Matrix.mul_assoc, spectralCPow_mul, ← neg_add, upperExponent_add_star_eq_one]
  have hRotated (s : ℝ) :
      rotatedPetz ρ hσ s = spectralCPow hσ (upperExponent s) *
        lift (partialTraceRight ρ * spectralCPow hq (-1)) *
        (spectralCPow hσ (upperExponent s))ᴴ := by
    change spectralCPow hσ (upperExponent s) *
        lift (spectralCPow hq (-(upperExponent s)) * partialTraceRight ρ *
          spectralCPow hq (-(star (upperExponent s)))) *
        spectralCPow hσ (star (upperExponent s)) = _
    rw [hRetained s, spectralCPow_conjTranspose]
  have hZero : upperExponent 0 = ((1 / 2 : ℝ) : ℂ) := by
    simp only [upperExponent, Complex.ofReal_zero, zero_mul, add_zero]
  have hOuter :
      spectralCPow hσ (upperExponent t) =
        spectralCPow hσ ((t : ℂ) * Complex.I) * spectralCPow hσ (((1 / 2 : ℝ) : ℂ)) := by
    rw [spectralCPow_mul, upperExponent, add_comm ((t : ℂ) * Complex.I)]
  rw [conjugate, ← spectralCPow_imaginary_eq_modularUnitary hσ t,
    ← rotatedPetz_zero (ρ := ρ) hσ, hRotated t, hRotated 0, hOuter, hZero,
    Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

private theorem upperDeficit_eq_frobenius_sq (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (htrace : ρ.trace = 1) (t : ℝ) :
    2 * (1 - tracePair (cfc Real.sqrt ρ) (gamma hρ hσ (upperExponent t))) =
      ‖cfc Real.sqrt ρ - gamma hρ hσ (upperExponent t)‖ ^ 2 := by
  let S := cfc Real.sqrt ρ
  let G := gamma hρ hσ (upperExponent t)
  have hS : ‖S‖ = 1 := sqrt_frobenius_eq_one hρ htrace
  have hG : ‖G‖ = 1 := gamma_upper_frobenius_eq_one hρ hσ htrace t
  have hCross : (Gᴴ * S).trace.re = (Sᴴ * G).trace.re := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Complex.star_def, Complex.conj_re] using
      congrArg Complex.re (Matrix.trace_conjTranspose (Sᴴ * G))
  change 2 * (1 - tracePair S G) = ‖S - G‖ ^ 2
  symm
  calc
    _ = ((Sᴴ * S).trace.re - (Sᴴ * G).trace.re) -
        ((Gᴴ * S).trace.re - (Gᴴ * G).trace.re) := by
      rw [frobenius_sq_eq_hsSq]
      simp only [hsSq, tracePair, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.trace_sub, Complex.sub_re]
      ring
    _ = _ := by
      rw [hCross]
      change hsSq S - tracePair S G - (tracePair S G - hsSq G) = _
      rw [← frobenius_sq_eq_hsSq S, ← frobenius_sq_eq_hsSq G, hS, hG]
      ring

end NonemptyErased

/-- For faithful physical inputs with commuting retained matrices, the
ordinary Petz squared trace-norm error is at most eight times the actual
relative entropy lost by taking the right partial trace. -/
theorem traceNorm_sub_ordinaryPetz_sq_le_eight (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (htrace : ρ.trace = 1)
    (hcomm : Commute (partialTraceRight ρ) (partialTraceRight σ)) :
    traceNorm (ρ - ordinaryPetz σ (partialTraceRight ρ)) ^ 2 ≤
      8 * entropyLoss ρ σ := by
  letI : Nonempty B := Classical.byContradiction fun h => by
    have hzero : ρ.trace = 0 := by
      unfold Matrix.trace
      exact Finset.sum_eq_zero (fun i _ => (h ⟨i.2⟩).elim)
    exact one_ne_zero (htrace.symm.trans hzero)
  let R := ordinaryPetz σ (partialTraceRight ρ)
  have hRpos : R.PosSemidef := by
    change (ordinaryPetz σ (partialTraceRight ρ)).PosSemidef
    rw [← gamma_half_gram hρ hσ]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  have hRtrace : R.trace = 1 := by
    change (ordinaryPetz σ (partialTraceRight ρ)).trace = 1
    rw [← rotatedPetz_zero (ρ := ρ) hσ, rotatedPetz_trace, htrace]
  let X := densityOfMatrix ρ hρ.posSemidef htrace
  let T := densityOfMatrix R hRpos hRtrace
  let U := hσ.isHermitian.eigenvectorUnitary
  let κ := fun i => Real.log (hσ.isHermitian.eigenvalues i)
  let G := fun t => gamma hρ hσ (upperExponent t)
  have hGram (t : ℝ) :
      G t * (G t)ᴴ = ofMatrix.symm (conjugateState (modularUnitary U κ t) T).1 := by
    change G t * (G t)ᴴ = conjugate (modularUnitary U κ t) R
    exact (gamma_upper_gram hρ hσ t).trans (rotatedPetz_eq_modularOrbit hσ hcomm t)
  have hSqrt : CFC.sqrt ρ = cfc Real.sqrt ρ := by
    rw [CFC.sqrt_eq_real_sqrt ρ hρ.posSemidef.nonneg,
      cfcₙ_eq_cfc (a := ρ) Real.continuous_sqrt.continuousOn Real.sqrt_zero]
  have hPoint (t : ℝ) :
      triangular X (conjugateState (modularUnitary U κ t) T) ≤
        2 * ‖cfc Real.sqrt ρ - G t‖ ^ 2 := by
    have h := triangular_le_two_upperDeficit X _ (G t) (hGram t)
    change triangular X (conjugateState (modularUnitary U κ t) T) ≤
      2 * (2 * (1 - tracePair (CFC.sqrt ρ) (G t))) at h
    rw [hSqrt, upperDeficit_eq_frobenius_sq hρ hσ htrace t] at h
    exact h
  obtain ⟨hOrbitIntegrable, hOrbit⟩ := triangular_le_twice_integral_modularOrbit X T U κ
  have hDeficitIntegrable :
      Integrable (fun t : ℝ => petzWeight t * ‖cfc Real.sqrt ρ - G t‖ ^ 2) :=
    (weighted_evaluation_physical_boundary hρ hσ).1
  have hUpper :
      (∫ t, petzWeight t * triangular X (conjugateState (modularUnitary U κ t) T)) ≤
        2 * ∫ t, petzWeight t * ‖cfc Real.sqrt ρ - G t‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono hOrbitIntegrable (hDeficitIntegrable.const_mul 2) fun t => ?_
    change petzWeight t * triangular X (conjugateState (modularUnitary U κ t) T) ≤
      2 * (petzWeight t * ‖cfc Real.sqrt ρ - G t‖ ^ 2)
    rw [mul_left_comm (2 : ℝ) (petzWeight t)]
    exact mul_le_mul_of_nonneg_left (hPoint t)
      (div_pos Real.pi_pos (add_pos (Real.cosh_pos _) zero_lt_one)).le
  have hNorm : traceNorm (ρ - R) ^ 2 ≤ 2 * triangular X T :=
    traceNorm_sub_sq_le_two_triangular X T
  have hLoss : (∫ t, petzWeight t * ‖cfc Real.sqrt ρ - G t‖ ^ 2) ≤ entropyLoss ρ σ :=
    upper_boundary_integral_le_entropyLoss hρ hσ htrace
  change traceNorm (ρ - R) ^ 2 ≤ 8 * entropyLoss ρ σ
  linarith only [hNorm, hOrbit, hUpper, hLoss]

end PartialTrace

/-!
## Singular supported channel extension

The target for every finite CPTP `Φ` and density states `X,Y` with
`SupportContained X Y` and `Commute (act Φ (raw X)) (act Φ (raw Y))`
is
`traceNorm (raw X - channelOrdinaryPetz Φ (raw Y) (act Φ (raw X))) ^ 2`
bounded by eight times
`finiteTraceLogRelativeEntropy X Y -
  finiteTraceLogRelativeEntropy (Φ.mapState X) (Φ.mapState Y)`.

First extend the partial-trace bound on a product with faithful retained
reference. The common path `PetzCommonUniformNoise.uniformNoise` sends both
retained matrices to `(1-t) • p + t • uniformMatrix A` and
`(1-t) • q + t • uniformMatrix A` by `marginalRight_uniformNoise` and
`uniformNoise_raw`. The identity term commutes with both matrices, so
expanding the two products preserves the original commutator up to the
factor `(1-t)^2`. For `0<t<1`, both full states are positive definite by
`faithfulMixture_posDef` applied to their raw paths and the positive scalar
identity. Apply `traceNorm_sub_ordinaryPetz_sq_le_eight` and express its
entropy loss through `PetzSingularInputLimit.finiteTraceLog_eq_raw`.
Use `le_of_tendsto_of_tendsto` on `𝓝[>] 0` with
`tendsto_traceNorm_sub_ordinaryPetz_sq_uniformNoise`,
`tendsto_finiteTraceLog_uniformNoise`, and
`tendsto_marginal_finiteTraceLog_uniformNoise`, as in
`PetzCommonUniformNoise.traceNorm_sub_ordinaryPetz_sq_le_finiteTraceLog`.
The noise calculus requires the retained inverse square root only on the
faithful compressed carrier.

For the channel, use `exists_retainedFirst_stinespring` and the support
compression already used in
`PetzChannelDimensionRecovery.traceNorm_sub_channelOrdinaryPetz_sq_le_finiteTraceLog`.
If `U` includes the positive spectral carrier of `act Φ (raw Y)`, then
the actual output matrices are `U * p' * Uᴴ` and `U * q' * Uᴴ`, where
`p',q'` are the partial traces of the compressed joint states.
The isometry equation `Uᴴ * U = 1` shows that embedding preserves products
and is injective (sandwich the embedded equality by `Uᴴ` and `U`).
Thus the actual commutator gives `Commute p' q'`, with `q'` faithful.
Apply the singular partial-trace bound to the compressed states. The
existing transports identify both entropy terms and the trace norm exactly,
using `ordinaryPetz_retained_embed` and `ordinaryPetz_embed` to carry the
recovered matrix back to the original channel input. This uses the
support-aware inverse square root and retains the same coefficient eight.
The uniform-noise positivity helper and several channel transport helpers
are private to their current files. Their arguments can be reused there
or made accessible when implementing the two extensions.
-/

end PetzCommutingPartialTrace

