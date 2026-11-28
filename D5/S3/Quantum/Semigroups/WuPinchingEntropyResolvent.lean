/- GID: D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuPinchingEntropyResolvent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict one-eighth relative entropy bounds for faithful binary pinchings and their ordered composition. -/

/-
proof_shape: content
admission_basis: escape-witness
escape_witness: At each positive shift, inverse-square-root congruence gives
one Hermitian spectral sum for both Hessian kernels. A nonzero perturbation
makes the symmetrized kernel strictly increase. Integrating the strict chord
bound for the entropy derivative gives the strict one-eighth loss estimate.

The following helpers have proof_shape: bind-only. The names on the right are
their consumers. All names are in WuPinchingEntropyResolvent.
conjugate_posDef -> pinch_posDef, pinch_bound_matrix_strict
trace_W_conjugate -> pinchState, pinch_bound_matrix_strict
log_W_conjugate -> relativeEntropy_pinch_split, pinch_bound_matrix_strict
pinch_fixed -> relativeEntropy_pinch_split, two_pinching_entropy_comparison, pinch_bound_matrix_strict
trace_mul_pinch_fixed -> relativeEntropy_pinch_split, pinch_bound_matrix_strict
pinch_posDef -> pinchState, relativeEntropy_pinch_split, two_pinching_entropy_comparison,
  pinch_bound_matrix_strict, relativeEntropy_pinch_bound, two_pinching_entropy_bound
relativeEntropy_on_matrices -> relativeEntropy_pinch_split, relativeEntropy_pinch_bound
relativeEntropy_pinch_split -> two_pinching_entropy_comparison
pinchChannel_act -> pinchChannel_mapState -> two_pinching_entropy_comparison
two_pinching_entropy_comparison -> two_pinching_entropy_bound
realDiagonal_mul, realDiagonal_one_add_smul, trace_realDiagonal,
  trace_conjugate -> normalized_trace
trace_normalized_product -> evenKernel_spectral
evenTerm_rational -> evenTerm_lt
pairingMap_apply -> kernel_integrable, integral_kernel, symmetric_entropy_lt
kernel_integrable, integral_kernel -> integral_evenKernel
integral_evenKernel -> integral_evenKernel_lt, symmetric_entropy_lt

The strict estimate flows through evenKernel_spectral, evenKernel_strict,
integral_evenKernel_lt, symmetric_entropy_lt and pinch_bound_matrix_strict
into pinch_bound_matrix. The theorem relativeEntropy_pinch_bound transports
the estimate to faithful density states. The theorem two_pinching_entropy_bound
uses it on both original pinching losses, with the exact split and channel data
processing supplying the comparison to the ordered loss.
-/

import D5.S3.Quantum.Divergence.UmegakiBKMPath
import D5.S3.Quantum.ProcessReconstruction.HiddenProcessSemigroup

/-!
# Relative entropy under binary pinching

For a Hermitian involution W, the projectors (I + W)/2 and (I - W)/2
give a binary projective pinching that acts by (X + W X W)/2. The exact
split against a faithful fixed reference is the faithful binary case of
`DiagonalDiscordMonotonicity.extendedQuantumRelativeEntropy_pinch_pythagoras`.
Canonical channel data processing bounds the ordered two-pinching loss by the
sum of the original losses, as in (5) of `wu-tracial-full-rank-interior.txt`.

The single-pinching estimate uses the affine CFC-log derivative
(`log_hasDerivAt_affine_of_lower_bound`), its Bochner resolvent formula, and
the trace-entropy chain rule (`hasDerivAt_trace_mul_log`). Averaging the two
signs of the affine perturbation before tracing the Hessian gives a scalar
sum that is strictly increasing whenever the perturbation is nonzero. The
resulting strict chord bound yields the one-eighth estimate for each loss.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator CStarAlgebra

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (quantumRelativeEntropy)
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)

namespace WuPinchingEntropyResolvent

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace

section EntropyComposition

open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
  (extendedQuantumRelativeEntropy_eq_coe_of_support support_of_posDef finiteTraceLogRelativeEntropy)
open D5.S3.Quantum.Divergence.CanonicalChannelDPI (extended_quantum_relative_entropy_channel_dpi)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (act)

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Binary pinching by a Hermitian involution, expressed as the mean of its
two conjugation-orbit points. -/
def pinch {n : ℕ} (W X : Mat n) : Mat n :=
  (1 / 2 : ℝ) • (X + W * X * W)

private def asUnitary {n : ℕ} (W : Mat n) (hW : W.IsHermitian)
    (hWW : W * W = 1) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨W, Matrix.mem_unitaryGroup_iff.mpr (by rw [Matrix.star_eq_conjTranspose, hW.eq, hWW])⟩

lemma conjugate_posDef {n : ℕ} (W X : Mat n) (hW : W.IsHermitian)
    (hWW : W * W = 1) (hX : X.PosDef) : (W * X * W).PosDef := by
  have h := hX.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit (Unitary.isUnit_coe (U := asUnitary W hW hWW)))
  change (Wᴴ * X * W).PosDef at h
  simpa only [hW.eq] using h

lemma trace_W_conjugate {n : ℕ} (W X : Mat n) (hWW : W * W = 1) :
    (W * X * W).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, hWW, one_mul]

lemma log_W_conjugate {n : ℕ} (W X : Mat n) (hW : W.IsHermitian)
    (hWW : W * W = 1) (hX : X.IsHermitian) :
    CFC.log (W * X * W) = W * CFC.log X * W := by
  let U := asUnitary W hW hWW
  let φ := Unitary.conjStarAlgAut ℂ (Mat n) U
  have hs : IsSelfAdjoint X := hX
  have hc := StarAlgHomClass.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    φ Real.log X (X.finite_real_spectrum.continuousOn _)
    φ.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional hs (hs.map φ)
  simpa only [CFC.log, φ, U, Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose, asUnitary, hW.eq] using hc.symm

lemma pinch_fixed {n : ℕ} (W X : Mat n) (hWW : W * W = 1) :
    W * pinch W X * W = pinch W X := by
  have h2 : W * (W * X * W) * W = X := by
    calc
      _ = (W * W) * X * (W * W) := by simp only [mul_assoc]
      _ = X := by rw [hWW, one_mul, mul_one]
  simp only [pinch, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, h2]
  rw [add_comm (W * X * W) X]

lemma trace_mul_pinch_fixed {n : ℕ} (W X L : Mat n) (hL : W * L * W = L) :
    (pinch W X * L).trace.re = (X * L).trace.re := by
  have htr : (W * X * W * L).trace = (X * L).trace := by
    calc
      _ = (W * (X * (W * L))).trace := by simp only [mul_assoc]
      _ = (X * (W * L) * W).trace := Matrix.trace_mul_comm _ _
      _ = (X * (W * L * W)).trace := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hL]
  simp only [pinch, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul, Matrix.trace_add,
    htr, Complex.smul_re, Complex.add_re, smul_eq_mul]
  ring

/-- Pinching preserves positive definiteness on the full matrix algebra. -/
theorem pinch_posDef {n : ℕ} (W X : Mat n) (hW : W.IsHermitian)
    (hWW : W * W = 1) (hX : X.PosDef) : (pinch W X).PosDef :=
  (hX.add_posSemidef (conjugate_posDef W X hW hWW hX).posSemidef).smul (by norm_num)

lemma relativeEntropy_on_matrices {n : ℕ} (ρ σ : DensityState (Fin n))
    (hρ : (CStarMatrix.ofMatrix.symm ρ.1).IsHermitian)
    (hσ : (CStarMatrix.ofMatrix.symm σ.1).IsHermitian) :
    quantumRelativeEntropy ρ σ =
      (CStarMatrix.ofMatrix.symm ρ.1 * (CFC.log (CStarMatrix.ofMatrix.symm ρ.1) -
        CFC.log (CStarMatrix.ofMatrix.symm σ.1))).trace.re := by
  let X := CStarMatrix.ofMatrix.symm ρ.1
  let Y := CStarMatrix.ofMatrix.symm σ.1
  have mapLog (M : Mat n) (hM : M.IsHermitian) :
      CStarMatrix.ofMatrix (CFC.log M) = CFC.log (CStarMatrix.ofMatrix M) :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log M
      (M.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous hM hM
  unfold quantumRelativeEntropy
  change (CStarMatrix.ofMatrix X * (CFC.log (CStarMatrix.ofMatrix X) -
    CFC.log (CStarMatrix.ofMatrix Y)) : CStarMatrix (Fin n) (Fin n) ℂ).trace.re = _
  rw [← mapLog X hρ, ← mapLog Y hσ]
  rfl

/-- The density state obtained by pinching a faithful state. -/
def pinchState {n : ℕ} (W : Mat n) (hW : W.IsHermitian) (hWW : W * W = 1)
    (ρ : DensityState (Fin n)) (hρ : (CStarMatrix.ofMatrix.symm ρ.1).PosDef) :
    DensityState (Fin n) := by
  let X := CStarMatrix.ofMatrix.symm ρ.1
  refine ⟨CStarMatrix.ofMatrix (pinch W X), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (pinch_posDef W X hW hWW hρ).posSemidef.nonneg
  · change (pinch W X).trace = 1
    have htr : X.trace = 1 := ρ.2.2
    rw [pinch, Matrix.trace_smul, Matrix.trace_add, trace_W_conjugate W X hWW, htr]
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.real_smul, ← Complex.ofReal_mul]
    norm_num

set_option maxHeartbeats 600000 in
/-- The pinching entropy identity against any faithful reference fixed by the
same conjugation. This is the equality in (5) when the reference is the twirl. -/
theorem relativeEntropy_pinch_split {n : ℕ} (W : Mat n) (hW : W.IsHermitian)
    (hWW : W * W = 1) (ρ τ : DensityState (Fin n))
    (hρ : (CStarMatrix.ofMatrix.symm ρ.1).PosDef)
    (hτ : (CStarMatrix.ofMatrix.symm τ.1).PosDef)
    (hfixed : W * CStarMatrix.ofMatrix.symm τ.1 * W = CStarMatrix.ofMatrix.symm τ.1) :
    let σ := pinchState W hW hWW ρ hρ
    quantumRelativeEntropy ρ τ = quantumRelativeEntropy ρ σ + quantumRelativeEntropy σ τ := by
  dsimp only
  let X := CStarMatrix.ofMatrix.symm ρ.1
  let T := CStarMatrix.ofMatrix.symm τ.1
  let A := pinch W X
  let σ := pinchState W hW hWW ρ hρ
  have hA : A.PosDef := pinch_posDef W X hW hWW hρ
  have hlogA : W * CFC.log A * W = CFC.log A := by
    rw [← log_W_conjugate W A hW hWW hA.isHermitian, pinch_fixed W X hWW]
  have hlogT : W * CFC.log T * W = CFC.log T := by
    rw [← log_W_conjugate W T hW hWW hτ.isHermitian, hfixed]
  rw [relativeEntropy_on_matrices ρ τ hρ.isHermitian hτ.isHermitian,
    relativeEntropy_on_matrices ρ σ hρ.isHermitian hA.isHermitian,
    relativeEntropy_on_matrices σ τ hA.isHermitian hτ.isHermitian]
  change (X * (CFC.log X - CFC.log T)).trace.re =
    (X * (CFC.log X - CFC.log A)).trace.re +
      (A * (CFC.log A - CFC.log T)).trace.re
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [trace_mul_pinch_fixed W X _ hlogA, trace_mul_pinch_fixed W X _ hlogT]
  ring

private def pinchChannel {n : ℕ} (W : Mat n) (hW : W.IsHermitian) (hWW : W * W = 1) :
    QuantumChannel (Fin n) (Fin n) :=
  UnitaryReconstruction.GibbsHiddenProcess.mix (1 / 2) (by norm_num) (by norm_num)
    UnitaryReconstruction.GibbsHiddenProcess.identity
    (UnitaryReconstruction.conjugation (asUnitary W hW hWW))

private lemma pinchChannel_act {n : ℕ} (W X : Mat n) (hW : W.IsHermitian) (hWW : W * W = 1) :
    act (pinchChannel W hW hWW) X = pinch W X := by
  let I : QuantumChannel (Fin n) (Fin n) := UnitaryReconstruction.GibbsHiddenProcess.identity
  let U := asUnitary W hW hWW
  have hi : act I X = X := rfl
  have hu : act (UnitaryReconstruction.conjugation U) X = W * X * W := by
    simpa only [act, U, asUnitary, hW.eq] using UnitaryReconstruction.conjugation_apply U X
  ext i j
  unfold pinchChannel
  rw [UnitaryReconstruction.GibbsHiddenProcess.mix_entry]
  change (((1 / 2 : ℝ) : ℂ) * act I X i j +
    ((1 - 1 / 2 : ℝ) : ℂ) * act (UnitaryReconstruction.conjugation U) X i j) =
      pinch W X i j
  rw [hi, hu, show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
  simp [pinch, Complex.real_smul]

private lemma pinchChannel_mapState {n : ℕ} (W : Mat n) (hW : W.IsHermitian) (hWW : W * W = 1)
    (ρ : DensityState (Fin n)) (hρ : (CStarMatrix.ofMatrix.symm ρ.1).PosDef) :
    (pinchChannel W hW hWW).mapState ρ = pinchState W hW hWW ρ hρ := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  exact pinchChannel_act W (CStarMatrix.ofMatrix.symm ρ.1) hW hWW

set_option maxHeartbeats 600000 in
/-- The two-pinching comparison (5), with the twirled state taken in the order
`P_U (P_V ρ)`. In the manuscript the conjugations commute, so this is the
common twirl. The inequality follows from data processing by the first pinching. -/
theorem two_pinching_entropy_comparison {n : ℕ} [Nonempty (Fin n)] (U V : Mat n)
    (hU : U.IsHermitian) (hUU : U * U = 1)
    (hV : V.IsHermitian) (hVV : V * V = 1) (ρ : DensityState (Fin n))
    (hρ : (CStarMatrix.ofMatrix.symm ρ.1).PosDef) :
    let ρU := pinchState U hU hUU ρ hρ
    let ρV := pinchState V hV hVV ρ hρ
    let hρV : (CStarMatrix.ofMatrix.symm ρV.1).PosDef :=
      pinch_posDef V (CStarMatrix.ofMatrix.symm ρ.1) hV hVV hρ
    let F := pinchState U hU hUU ρV hρV
    quantumRelativeEntropy ρ F = quantumRelativeEntropy ρ ρU + quantumRelativeEntropy ρU F ∧
      quantumRelativeEntropy ρ F ≤ quantumRelativeEntropy ρ ρU + quantumRelativeEntropy ρ ρV := by
  dsimp only
  let X := CStarMatrix.ofMatrix.symm ρ.1
  let ρU := pinchState U hU hUU ρ hρ
  let ρV := pinchState V hV hVV ρ hρ
  have hρV : (CStarMatrix.ofMatrix.symm ρV.1).PosDef := pinch_posDef V X hV hVV hρ
  let F := pinchState U hU hUU ρV hρV
  have hF : (CStarMatrix.ofMatrix.symm F.1).PosDef :=
    pinch_posDef U (CStarMatrix.ofMatrix.symm ρV.1) hU hUU hρV
  have hsplit : quantumRelativeEntropy ρ F =
      quantumRelativeEntropy ρ ρU + quantumRelativeEntropy ρU F :=
    relativeEntropy_pinch_split U hU hUU ρ F hρ hF
      (pinch_fixed U (CStarMatrix.ofMatrix.symm ρV.1) hUU)
  refine ⟨hsplit, ?_⟩
  have hdpi := extended_quantum_relative_entropy_channel_dpi
    (pinchChannel U hU hUU) ρ ρV
  rw [pinchChannel_mapState U hU hUU ρ hρ, pinchChannel_mapState U hU hUU ρV hρV] at hdpi
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support (support_of_posDef ρU F hF),
    extendedQuantumRelativeEntropy_eq_coe_of_support (support_of_posDef ρ ρV hρV)] at hdpi
  have hle : quantumRelativeEntropy ρU F ≤ quantumRelativeEntropy ρ ρV := by
    simpa only [WithTop.coe_le_coe, finiteTraceLogRelativeEntropy, quantumRelativeEntropy] using hdpi
  rw [hsplit]
  exact add_le_add_right hle (quantumRelativeEntropy ρ ρU)

end EntropyComposition

open MeasureTheory Filter Set
open scoped Topology BigOperators

open D5.S3.Divergence
open D5.S3.Divergence.LogDerivTrace (logDeriv_integrable)
open D5.S3.Divergence.AudenaertBinaryHolevoBound
  (log_hasDerivAt_affine_of_lower_bound mix_lower_bound)
open D5.S3.Quantum.Divergence.TraceEntropyCalculus (hasDerivAt_trace_mul_log)
open D5.S3.Quantum.Divergence.UmegakiBKMPath (common_floor)

private def realDiagonal {n : ℕ} (d : Fin n → ℝ) : Mat n :=
  Matrix.diagonal (fun i => (d i : ℂ))

private def kernel {n : ℕ} (A K : Mat n) (t z : ℝ) : ℝ :=
  let R := (A + t • K + z • (1 : Mat n))⁻¹
  (K * R * K * R).trace.re

private def evenKernel {n : ℕ} (A K : Mat n) (t z : ℝ) : ℝ :=
  (kernel A K t z + kernel A K (-t) z) / 2

private def evenTerm (c t : ℝ) : ℝ :=
  (c ^ 2 / (1 + t * c) ^ 2 + c ^ 2 / (1 - t * c) ^ 2) / 2

private lemma realDiagonal_mul {n : ℕ} (f g : Fin n → ℝ) :
    realDiagonal f * realDiagonal g = realDiagonal (fun i => f i * g i) := by
  simp only [realDiagonal, Matrix.diagonal_mul_diagonal, Complex.ofReal_mul]

private lemma realDiagonal_one_add_smul {n : ℕ} (f : Fin n → ℝ) (t : ℝ) :
    1 + t • realDiagonal f = realDiagonal (fun i => 1 + t * f i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [realDiagonal, Complex.real_smul]
  · simp [realDiagonal, hij]

private lemma trace_realDiagonal {n : ℕ} (f : Fin n → ℝ) :
    (realDiagonal f).trace.re = ∑ i, f i := by
  simp [realDiagonal, Complex.re_sum]

private lemma trace_conjugate {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (X : Mat n) :
    ((U : Mat n) * X * (U : Mat n)ᴴ).trace = X.trace := by
  have hU : (U : Mat n)ᴴ * (U : Mat n) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.prop
  rw [Matrix.trace_mul_cycle, hU, one_mul]

set_option maxHeartbeats 1200000 in
-- Extra heartbeats for elaborating unitary conjugation and inverting the shifted diagonal.
/-- The exact real trace of the squared normalized resolvent product. -/
private lemma normalized_trace {n : ℕ} (C : Mat n) (hC : C.IsHermitian)
    (t : ℝ) (ht : (1 + t • C).PosDef) :
    (∀ i, 0 < 1 + t * hC.eigenvalues i) ∧
    (C * (1 + t • C)⁻¹ * C * (1 + t • C)⁻¹).trace.re =
      ∑ i, hC.eigenvalues i ^ 2 / (1 + t * hC.eigenvalues i) ^ 2 := by
  let U := hC.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ (Mat n) U
  let c := hC.eigenvalues
  let d : Fin n → ℝ := fun i => 1 + t * c i
  have hCeq : C = φ (realDiagonal c) := hC.spectral_theorem
  have hQeq : 1 + t • C = φ (realDiagonal d) := by
    have hsmul : φ (t • realDiagonal c) = t • φ (realDiagonal c) := by
      rw [← Complex.coe_smul t (realDiagonal c), map_smul, Complex.coe_smul]
    change 1 + t • C = φ (realDiagonal (fun i => 1 + t * c i))
    rw [← realDiagonal_one_add_smul c t, map_add, map_one, hsmul, ← hCeq]
  have huu : (U : Mat n)ᴴ * (U : Mat n) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.prop
  have hu : IsUnit (U : Mat n) := Unitary.isUnit_coe
  have hdpos : (realDiagonal d).PosDef := by
    have h := ht.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
    rw [hQeq, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h
    have he : (U : Mat n)ᴴ * ((U : Mat n) * realDiagonal d * (U : Mat n)ᴴ) *
        (U : Mat n) = realDiagonal d := by
      calc
        _ = ((U : Mat n)ᴴ * (U : Mat n)) * realDiagonal d *
            ((U : Mat n)ᴴ * (U : Mat n)) := by simp only [mul_assoc]
        _ = _ := by rw [huu, one_mul, mul_one]
    rw [he] at h
    exact h
  have hd (i : Fin n) : 0 < d i := by
    have h := (Matrix.posDef_diagonal_iff.mp hdpos) i
    change (0 : ℂ) < (d i : ℂ) at h
    rwa [← Complex.ofReal_zero, Complex.real_lt_real] at h
  refine ⟨hd, ?_⟩
  have hInv : (1 + t • C)⁻¹ = φ (realDiagonal (fun i => (d i)⁻¹)) := by
    apply Matrix.inv_eq_right_inv
    rw [hQeq, ← map_mul, realDiagonal_mul]
    have hOne : realDiagonal (fun i => d i * (d i)⁻¹) = (1 : Mat n) := by
      have hf : (fun i => d i * (d i)⁻¹) = fun _ => (1 : ℝ) := by
        funext i
        exact mul_inv_cancel₀ (hd i).ne'
      calc
        _ = realDiagonal (fun _ => (1 : ℝ)) := congrArg realDiagonal hf
        _ = _ := by simp only [realDiagonal, Complex.ofReal_one, Matrix.diagonal_one]
    rw [hOne, map_one]
  have hTrace (X : Mat n) : (φ X).trace = X.trace := by
    simpa only [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      trace_conjugate U X
  conv_lhs =>
    rw [hInv, hCeq, ← map_mul, ← map_mul, ← map_mul, hTrace]
  simp only [realDiagonal_mul, trace_realDiagonal]
  apply Finset.sum_congr rfl
  intro i _
  unfold d
  rw [div_eq_mul_inv, ← inv_pow]
  ring

private lemma trace_normalized_product {n : ℕ} (K R B : Mat n) :
    (K * (R * B * R) * K * (R * B * R)).trace =
      ((R * K * R) * B * (R * K * R) * B).trace := by
  calc
    _ = ((K * R * B * R * K * R * B) * R).trace :=
      congrArg (Matrix.trace : Mat n → ℂ) (by simp only [mul_assoc])
    _ = (R * (K * R * B * R * K * R * B)).trace := Matrix.trace_mul_comm _ _
    _ = _ := congrArg (Matrix.trace : Mat n → ℂ) (by simp only [mul_assoc])

set_option maxHeartbeats 1200000 in
-- Extra heartbeats for reducing the square-root congruence and transporting both resolvents.
/-- A single dimensionless Hermitian matrix gives the exact sum for both signs. -/
private lemma evenKernel_spectral {n : ℕ} (A K : Mat n) (hA : A.PosDef)
    (hK : K.IsHermitian) (z : ℝ) (hz : 0 < z) (s t : ℝ)
    (hp : ∀ u ∈ Icc (-1 : ℝ) 1, (A + u • K).PosDef)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ (C : Mat n) (hC : C.IsHermitian),
      (C = 0 → K = 0) ∧
      (∀ i, 0 < 1 + s * hC.eigenvalues i ∧ 0 < 1 - s * hC.eigenvalues i ∧
            0 < 1 + t * hC.eigenvalues i ∧ 0 < 1 - t * hC.eigenvalues i) ∧
      evenKernel A K s z = (∑ i, evenTerm (hC.eigenvalues i) s) ∧
      evenKernel A K t z = (∑ i, evenTerm (hC.eigenvalues i) t) := by
  let X := A + z • (1 : Mat n)
  let S := CFC.sqrt X
  let R := S⁻¹
  let C := R * K * R
  have hX : X.PosDef := hA.add_posSemidef (Matrix.PosDef.one.smul hz).posSemidef
  have hS : IsUnit S := (CFC.isUnit_sqrt_iff_isStrictlyPositive).mpr hX.isStrictlyPositive
  have hSdet := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hRS : R * S = 1 := Matrix.nonsing_inv_mul S hSdet
  have hSR : S * R = 1 := Matrix.mul_nonsing_inv S hSdet
  have hR : IsUnit R := Matrix.isUnit_nonsing_inv_iff.mpr hS
  have hRh : Rᴴ = R := ((CFC.sqrt_nonneg X).posSemidef.isHermitian.inv).eq
  have hSS : S * S = X := by
    simpa only [pow_two] using CFC.sq_sqrt X hX.posSemidef.nonneg
  have hRXR : R * X * R = 1 := by
    rw [← hSS]
    calc
      _ = (R * S) * (S * R) := by simp only [mul_assoc]
      _ = _ := by rw [hRS, hSR, one_mul]
  have hC : C.IsHermitian := by
    simpa only [C, hRh] using isHermitian_conjTranspose_mul_mul R hK
  have hKrecover : S * C * S = K := by
    calc
      _ = (S * R) * K * (R * S) := by simp only [C, mul_assoc]
      _ = _ := by rw [hSR, hRS, one_mul, mul_one]
  have hAt (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      (∀ i, 0 < 1 + u * hC.eigenvalues i) ∧
        kernel A K u z = ∑ i, hC.eigenvalues i ^ 2 / (1 + u * hC.eigenvalues i) ^ 2 := by
    let Y := A + u • K + z • (1 : Mat n)
    let Q := 1 + u • C
    have hY : Y.PosDef := (hp u hu).add_posSemidef (Matrix.PosDef.one.smul hz).posSemidef
    have hCong : R * Y * R = Q := by
      have hYX : Y = X + u • K := add_right_comm _ _ _
      rw [hYX, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, hRXR]
    have hQ : Q.PosDef := by
      rw [← hCong]
      simpa only [hRh] using
        hY.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hR)
    have hSQ : S * Q = Y * R := by
      rw [← hCong]
      calc
        _ = (S * R) * Y * R := by simp only [mul_assoc]
        _ = _ := by rw [hSR, one_mul]
    have hQinv : Q * Q⁻¹ = 1 :=
      Matrix.mul_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit)
    have hYinv : Y⁻¹ = R * Q⁻¹ * R := by
      apply Matrix.inv_eq_right_inv
      calc
        _ = (Y * R) * Q⁻¹ * R := by simp only [mul_assoc]
        _ = (S * Q) * Q⁻¹ * R := congrArg (fun M : Mat n => M * Q⁻¹ * R) hSQ.symm
        _ = S * (Q * Q⁻¹) * R := by rw [mul_assoc S Q Q⁻¹]
        _ = _ := by rw [hQinv, mul_one, hSR]
    obtain ⟨hden, htrace⟩ := normalized_trace C hC u hQ
    refine ⟨hden, ?_⟩
    change (K * Y⁻¹ * K * Y⁻¹).trace.re = _
    rw [hYinv, ← htrace]
    exact congrArg Complex.re (trace_normalized_product K R Q⁻¹)
  have hpair (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      (∀ i, 0 < 1 + u * hC.eigenvalues i ∧ 0 < 1 - u * hC.eigenvalues i) ∧
      evenKernel A K u z = ∑ i, evenTerm (hC.eigenvalues i) u := by
    obtain ⟨hplus, hPos⟩ := hAt u ⟨by linarith [hu.1], hu.2⟩
    obtain ⟨hminus, hNeg⟩ := hAt (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
    refine ⟨fun i => ⟨hplus i, by simpa [neg_mul, sub_eq_add_neg] using hminus i⟩, ?_⟩
    rw [evenKernel, hPos, hNeg, ← Finset.sum_add_distrib, Finset.sum_div]
    simp only [evenTerm, neg_mul, sub_eq_add_neg]
  obtain ⟨hds, hes⟩ := hpair s hs
  obtain ⟨hdt, het⟩ := hpair t ht
  refine ⟨C, hC, ?_, fun i => ⟨(hds i).1, (hds i).2, (hdt i).1, (hdt i).2⟩, hes, het⟩
  intro hzero
  simpa [hzero] using hKrecover.symm

private lemma evenTerm_rational {c t : ℝ}
    (hp : 0 < 1 + t * c) (hm : 0 < 1 - t * c) :
    evenTerm c t = c ^ 2 * ((1 + (t * c) ^ 2) / (1 - (t * c) ^ 2) ^ 2) := by
  have hq : 0 < 1 - (t * c) ^ 2 := by nlinarith [mul_pos hp hm]
  have hp2 : (1 + t * c) ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne'
  have hm2 : (1 - t * c) ^ 2 ≠ 0 := pow_ne_zero 2 hm.ne'
  unfold evenTerm
  rw [div_add_div _ _ hp2 hm2, div_div, ← mul_div_assoc]
  apply (div_eq_div_iff (mul_ne_zero (mul_ne_zero hp2 hm2) two_ne_zero)
    (pow_ne_zero 2 hq.ne')).2
  ring

private lemma evenTerm_lt {c s t : ℝ} (hc : c ≠ 0) (hs : 0 ≤ s) (hst : s < t)
    (hsp : 0 < 1 + s * c) (hsm : 0 < 1 - s * c)
    (htp : 0 < 1 + t * c) (htm : 0 < 1 - t * c) :
    evenTerm c s < evenTerm c t := by
  rw [evenTerm_rational hsp hsm, evenTerm_rational htp htm]
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hsq : (s * c) ^ 2 < (t * c) ^ 2 := by
    simpa only [mul_pow] using
      mul_lt_mul_of_pos_right ((sq_lt_sq₀ hs (hs.trans hst.le)).mpr hst) hc2
  have hds : 0 < 1 - (s * c) ^ 2 := by nlinarith [mul_pos hsp hsm]
  have hdt : 0 < 1 - (t * c) ^ 2 := by nlinarith [mul_pos htp htm]
  have hden : (1 - (t * c) ^ 2) ^ 2 ≤ (1 - (s * c) ^ 2) ^ 2 :=
    ((sq_lt_sq₀ hdt.le hds.le).mpr (sub_lt_sub_left hsq 1)).le
  apply mul_lt_mul_of_pos_left _ hc2
  calc
    _ < (1 + (t * c) ^ 2) / (1 - (s * c) ^ 2) ^ 2 :=
      div_lt_div_of_pos_right (add_lt_add_right hsq 1) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hden

private lemma evenKernel_strict {n : ℕ} (A K : Mat n) (hA : A.PosDef)
    (hK : K.IsHermitian) (hne : K ≠ 0) (z : ℝ) (hz : 0 < z)
    (hp : ∀ t ∈ Icc (-1 : ℝ) 1, (A + t • K).PosDef)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s < t) :
    evenKernel A K s z < evenKernel A K t z := by
  obtain ⟨C, hC, hrecover, hden, hes, het⟩ := evenKernel_spectral A K hA hK z hz s t hp hs ht
  have hnonzero : ∃ i, hC.eigenvalues i ≠ 0 := by
    by_contra! hall
    apply hne
    apply hrecover
    have hdiag : Matrix.diagonal (RCLike.ofReal ∘ hC.eigenvalues) = (0 : Mat n) := by
      ext i j
      simp [Matrix.diagonal, hall]
    rw [hC.spectral_theorem, hdiag, map_zero]
  have hlt (i : Fin n) (hi : hC.eigenvalues i ≠ 0) :
      evenTerm (hC.eigenvalues i) s < evenTerm (hC.eigenvalues i) t :=
    evenTerm_lt hi hs.1 hst (hden i).1 (hden i).2.1 (hden i).2.2.1 (hden i).2.2.2
  rw [hes, het]
  obtain ⟨i, hi⟩ := hnonzero
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hj : hC.eigenvalues j = 0
    · simp [hj, evenTerm]
    · exact (hlt j hj).le
  · exact ⟨i, Finset.mem_univ _, hlt i hi⟩

private def traceRealMap (n : ℕ) : Mat n →L[ℝ] ℝ :=
  Complex.reCLM.comp (Matrix.traceLinearMap (Fin n) ℝ ℂ).toContinuousLinearMap

private def pairingMap {n : ℕ} (K : Mat n) : Mat n →L[ℝ] ℝ :=
  (traceRealMap n).comp (LinearMap.mulLeft ℝ K).toContinuousLinearMap

private lemma pairingMap_apply {n : ℕ} (K M : Mat n) :
    pairingMap K M = (K * M).trace.re := rfl

private lemma kernel_integrable {n : ℕ} (A K : Mat n) (t : ℝ) (hp : (A + t • K).PosDef) :
    IntegrableOn (kernel A K t) (Ioi 0) := by
  unfold IntegrableOn
  have hint := (pairingMap K).integrable_comp (logDeriv_integrable (A + t • K) K hp).integrable
  refine hint.congr (Eventually.of_forall ?_)
  intro z
  simp only [pairingMap_apply, kernel, mul_assoc]

private lemma integral_kernel {n : ℕ} (A K : Mat n) (t : ℝ) (hp : (A + t • K).PosDef) :
    (∫ z in Ioi (0 : ℝ), kernel A K t z) = pairingMap K (LogDerivTrace.logDeriv (A + t • K) K) := by
  simpa only [kernel, pairingMap_apply, LogDerivTrace.logDeriv, mul_assoc] using
    (pairingMap K).integral_comp_comm (logDeriv_integrable (A + t • K) K hp)

private lemma integral_evenKernel {n : ℕ} (A K : Mat n) (t : ℝ)
    (hp : (A + t • K).PosDef) (hm : (A + (-t) • K).PosDef) :
    IntegrableOn (evenKernel A K t) (Ioi 0) ∧
      (∫ z in Ioi (0 : ℝ), evenKernel A K t z) =
        (pairingMap K (LogDerivTrace.logDeriv (A + t • K) K) +
          pairingMap K (LogDerivTrace.logDeriv (A + (-t) • K) K)) / 2 := by
  have hi := kernel_integrable A K t hp
  have hj := kernel_integrable A K (-t) hm
  refine ⟨(hi.add hj).div_const 2, ?_⟩
  unfold evenKernel
  rw [MeasureTheory.integral_div, integral_add hi hj, integral_kernel A K t hp,
    integral_kernel A K (-t) hm]

private lemma integral_evenKernel_lt {n : ℕ} (A K : Mat n) (hA : A.PosDef)
    (hK : K.IsHermitian) (hne : K ≠ 0)
    (hp : ∀ t ∈ Icc (-1 : ℝ) 1, (A + t • K).PosDef)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s < t) :
    (∫ z in Ioi (0 : ℝ), evenKernel A K s z) <
      ∫ z in Ioi (0 : ℝ), evenKernel A K t z := by
  have hi (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : IntegrableOn (evenKernel A K u) (Ioi 0) :=
    (integral_evenKernel A K u (hp u ⟨by linarith [hu.1], hu.2⟩)
      (hp (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩)).1
  have hlt (z : ℝ) (hz : z ∈ Ioi (0 : ℝ)) :
      evenKernel A K s z < evenKernel A K t z :=
    evenKernel_strict A K hA hK hne z hz hp hs ht hst
  let μ := volume.restrict (Ioi (0 : ℝ))
  let f : ℝ → ℝ := fun z => evenKernel A K t z - evenKernel A K s z
  have hnonneg : 0 ≤ᵐ[μ] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact sub_nonneg.mpr (hlt z hz).le
  have hsupport : Ioi (0 : ℝ) ⊆ Function.support f :=
    fun z hz => (sub_pos.mpr (hlt z hz)).ne'
  have hμ : 0 < μ (Ioi (0 : ℝ)) := by
    simp [μ, Measure.restrict_apply, measurableSet_Ioi, Real.volume_Ioi]
  have hint : 0 < ∫ z, f z ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hnonneg ((hi t ht).sub (hi s hs))).mpr
      (hμ.trans_le (measure_mono hsupport))
  rw [show (∫ z, f z ∂μ) = (∫ z, evenKernel A K t z ∂μ) -
    (∫ z, evenKernel A K s z ∂μ) from integral_sub (hi t ht) (hi s hs)] at hint
  exact sub_pos.mp hint

private def entropyTrace {n : ℕ} (X : Mat n) : ℝ :=
  (X * CFC.log X).trace.re

private def secantDerivative {n : ℕ} (A K : Mat n) (t : ℝ) : ℝ :=
  (K * (CFC.log (A + t • K) - CFC.log (A + (-t) • K))).trace.re / 2

set_option maxHeartbeats 1200000 in
-- Extra heartbeats for elaborating the matrix-log derivative chain rules and interval comparison.
/-- Strict trapezoid comparison for the entropy along a symmetric affine pencil. -/
private lemma symmetric_entropy_lt {n : ℕ} (A K : Mat n) (hK : K.IsHermitian)
    (hne : K ≠ 0) (hplus : (A + K).PosDef) (hminus : (A - K).PosDef) :
    (entropyTrace (A + K) + entropyTrace (A - K)) / 2 - entropyTrace A <
      secantDerivative A K 1 / 2 := by
  let X : ℝ → Mat n := fun t => A + t • K
  let F : ℝ → ℝ := fun t => entropyTrace (X t)
  let B : ℝ → ℝ := fun t => pairingMap K (CFC.log (X t))
  let E : ℝ → ℝ := fun t => (F t + F (-t)) / 2
  let G := secantDerivative A K
  obtain ⟨c, hc, hcp, hcm⟩ := common_floor (A + K) (A - K) hplus hminus
  have hAherm : A.IsHermitian := by
    simpa using hplus.isHermitian.sub hK
  have hfloor (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : c • (1 : Mat n) ≤ X t := by
    let a := (1 + t) / 2
    have ha : a ∈ Icc (0 : ℝ) 1 := ⟨by dsimp [a]; linarith [ht.1],
      by dsimp [a]; linarith [ht.2]⟩
    have he : X t = a • (A + K) + (1 - a) • (A - K) := by
      dsimp [X, a]
      module
    rw [he]
    exact mix_lower_bound (A + K) (A - K) c a hcp hcm ha
  have hp (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : (X t).PosDef :=
    ((IsStrictlyPositive.smul hc isStrictlyPositive_one).of_le (hfloor t ht)).posDef
  have hX : Continuous X := by dsimp [X]; fun_prop
  have hlog : ContinuousOn (fun t => CFC.log (X t)) (Icc (-1 : ℝ) 1) :=
    CFC.continuousOn_log.comp hX.continuousOn
      (fun t ht => ⟨(hp t ht).isHermitian, (hp t ht).isUnit⟩)
  have hF : ContinuousOn F (Icc (-1 : ℝ) 1) :=
    (traceRealMap n).continuous.comp_continuousOn (hX.continuousOn.mul hlog)
  have hB : ContinuousOn B (Icc (-1 : ℝ) 1) :=
    (pairingMap K).continuous.comp_continuousOn hlog
  have hp_mem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [ht.1], ht.2⟩
  have hm_mem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : -t ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hneg : ContinuousOn (fun t : ℝ => -t) (Icc (0 : ℝ) 1) :=
    continuous_neg.continuousOn
  have hE : ContinuousOn E (Icc (0 : ℝ) 1) :=
    ((hF.mono (fun t ht => hp_mem t ht)).add
      (hF.comp hneg (fun t ht => hm_mem t ht))).div_const 2
  have hGid (t : ℝ) : G t = (B t - B (-t)) / 2 := by
    change (K * (CFC.log (X t) - CFC.log (X (-t)))).trace.re / 2 =
      (pairingMap K (CFC.log (X t)) - pairingMap K (CFC.log (X (-t)))) / 2
    rw [← map_sub, pairingMap_apply]
  have hG : ContinuousOn G (Icc (0 : ℝ) 1) := by
    rw [show G = (fun t => (B t - B (-t)) / 2) from funext hGid]
    exact ((hB.mono (fun t ht => hp_mem t ht)).sub
      (hB.comp hneg (fun t ht => hm_mem t ht))).div_const 2
  have hFd (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      HasDerivAt F (B t + K.trace.re) t := by
    have hXd : HasDerivAt X K t := by
      simpa [X] using ((hasDerivAt_id t).smul_const K).const_add A
    have hd : HasDerivAt F (K * (CFC.log (X t) + 1)).trace.re t :=
      hasDerivAt_trace_mul_log X K t hXd
        (Eventually.of_forall (fun u => hAherm.add (hK.smul (IsSelfAdjoint.all u)))) (hp t ht)
    have he : (K * (CFC.log (X t) + 1)).trace.re = B t + K.trace.re := by
      change _ = pairingMap K (CFC.log (X t)) + K.trace.re
      rw [pairingMap_apply, Matrix.mul_add, Matrix.mul_one, Matrix.trace_add, Complex.add_re]
    exact he ▸ hd
  have hEd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt E (G t) t := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hplus' := hFd t (hp_mem t ht')
    have hminus' := (hFd (-t) (hm_mem t ht')).comp t (hasDerivAt_neg t)
    have h := (hplus'.add hminus').div_const 2
    change HasDerivAt E ((B t + K.trace.re + (B (-t) + K.trace.re) * (-1)) / 2) t at h
    have he : (B t + K.trace.re + (B (-t) + K.trace.re) * (-1)) / 2 = G t := by
      rw [hGid]
      ring
    exact he ▸ h
  have hBd (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt B (pairingMap K (LogDerivTrace.logDeriv (X t) K)) t := by
    have hd := log_hasDerivAt_affine_of_lower_bound A K t c hc (Ioo (-1 : ℝ) 1)
      (isOpen_Ioo.mem_nhds ht) (fun u hu => hfloor u ⟨hu.1.le, hu.2.le⟩)
    exact (pairingMap K).hasFDerivAt.comp_hasDerivAt t hd
  have hGd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt G (∫ z in Ioi (0 : ℝ), evenKernel A K t z) t := by
    have hp' : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
    have hm' : -t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    let d : ℝ → ℝ := fun u => pairingMap K (LogDerivTrace.logDeriv (X u) K)
    have hBneg : HasDerivAt (fun u => B (-u)) (-d (-t)) t := by
      have h := (hBd (-t) hm').comp t (hasDerivAt_neg t)
      change HasDerivAt (fun u => B (-u)) (d (-t) * (-1)) t at h
      simpa only [mul_neg, mul_one] using h
    have hdiff : HasDerivAt (fun u => B u - B (-u)) (d t - (-d (-t))) t :=
      (hBd t hp').fun_sub hBneg
    have hint : (∫ z in Ioi (0 : ℝ), evenKernel A K t z) = (d t + d (-t)) / 2 :=
      (integral_evenKernel A K t (hp t ⟨hp'.1.le, hp'.2.le⟩)
        (hp (-t) ⟨hm'.1.le, hm'.2.le⟩)).2
    rw [hint, show G = (fun u => (B u - B (-u)) / 2) from funext hGid]
    have he : d t - (-d (-t)) = d t + d (-t) := sub_neg_eq_add _ _
    exact congrArg (fun s : ℝ => s / 2) he ▸ hdiff.div_const 2
  have hmono : StrictMonoOn (deriv G) (interior (Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    intro s hs t ht hst
    rw [(hGd s hs).deriv, (hGd t ht).deriv]
    have hA : A.PosDef := by simpa [X] using hp 0 (by norm_num)
    exact integral_evenKernel_lt A K hA hK hne hp
      ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩ hst
  have hconvex := hmono.strictConvexOn_of_deriv (convex_Icc (0 : ℝ) 1) hG
  have hG0 : G 0 = 0 := by rw [hGid]; simp
  have hchord (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : G t < t * G 1 := by
    have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have h : G ((1 - t) • (0 : ℝ) + t • (1 : ℝ)) < (1 - t) • G 0 + t • G 1 :=
      hconvex.2 hzero hone zero_ne_one (sub_pos.mpr ht.2) ht.1 (by ring)
    simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, hG0] using h
  have hle (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : G t ≤ t * G 1 := by
    rcases ht.2.lt_or_eq with h | rfl
    · exact (hchord t ⟨ht.1, h⟩).le
    · simp
  have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := G) (g := fun t => t * G 1) zero_lt_one hG
    (continuous_id.mul continuous_const).continuousOn hle
    ⟨1 / 2, by norm_num, hchord (1 / 2) (by norm_num)⟩
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hE hEd
    (hG.intervalIntegrable_of_Icc zero_le_one)
  have hlinear : (∫ t in (0 : ℝ)..1, t * G 1) = G 1 / 2 := by
    rw [intervalIntegral.integral_mul_const, integral_id]
    ring
  rw [hFT, hlinear] at hlt
  have hE1 : E 1 = (entropyTrace (A + K) + entropyTrace (A - K)) / 2 := by
    simp only [E, F, X, neg_smul, one_smul, sub_eq_add_neg]
  have hE0 : E 0 = entropyTrace A := by
    simp only [E, F, X, neg_zero, zero_smul, add_zero]
    ring
  rwa [hE1, hE0] at hlt

set_option maxHeartbeats 800000 in
-- Extra heartbeats for the matrix module identities and trace rewrites of the conjugated logs.
private lemma pinch_bound_matrix_strict {n : ℕ} (W X : Mat n) (hW : W.IsHermitian)
    (hWW : W * W = 1) (hX : X.PosDef) (hne : pinch W X ≠ X) :
    (X * (CFC.log X - CFC.log (pinch W X))).trace.re <
      ((X - W * X * W) * (CFC.log X - W * CFC.log X * W)).trace.re / 8 := by
  let Y := W * X * W
  let A := pinch W X
  let K : Mat n := (1 / 2 : ℝ) • (X - Y)
  have hplus : A + K = X := by dsimp [A, K, pinch, Y]; module
  have hminus : A - K = Y := by dsimp [A, K, pinch, Y]; module
  have hY := conjugate_posDef W X hW hWW hX
  have hA := pinch_posDef W X hW hWW hX
  have hK : K.IsHermitian :=
    (hX.isHermitian.sub hY.isHermitian).smul (IsSelfAdjoint.all _)
  have hKne : K ≠ 0 := by
    intro hz
    apply hne
    simpa [hz] using hplus
  have hlogY : CFC.log Y = W * CFC.log X * W := log_W_conjugate W X hW hWW hX.isHermitian
  have hlogA : W * CFC.log A * W = CFC.log A := by
    rw [← log_W_conjugate W A hW hWW hA.isHermitian, pinch_fixed W X hWW]
  have hcross := trace_mul_pinch_fixed W X (CFC.log A) hlogA
  have hFY : entropyTrace Y = entropyTrace X := by
    unfold entropyTrace
    rw [hlogY]
    apply congrArg Complex.re
    calc
      _ = (W * X * (W * W) * CFC.log X * W).trace := by simp only [Y, mul_assoc]
      _ = (W * (X * CFC.log X) * W).trace := by simp only [hWW, mul_one, mul_assoc]
      _ = _ := trace_W_conjugate W _ hWW
  have hD : (X * (CFC.log X - CFC.log A)).trace.re = entropyTrace X - entropyTrace A := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, ← hcross]
    rfl
  have hd : X - Y = (2 : ℝ) • K := by dsimp [K]; module
  have hderiv : secantDerivative A K 1 / 2 =
      ((X - Y) * (CFC.log X - W * CFC.log X * W)).trace.re / 8 := by
    have hn : A + (-1 : ℝ) • K = A - K := by rw [neg_smul, one_smul, sub_eq_add_neg]
    let L := CFC.log X - W * CFC.log X * W
    have hscale (M : Mat n) : (((2 : ℝ) • M) * L).trace.re = 2 * (M * L).trace.re := by
      rw [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    change secantDerivative A K 1 / 2 = ((X - Y) * L).trace.re / 8
    calc
      _ = (K * L).trace.re / 2 / 2 := by
        unfold secantDerivative
        rw [one_smul, hn, hplus, hminus, hlogY]
      _ = (2 * (K * L).trace.re) / 8 := by ring
      _ = (((2 : ℝ) • K) * L).trace.re / 8 := by rw [hscale]
      _ = _ := congrArg (fun M : Mat n => (M * L).trace.re / 8) hd.symm
  have h := symmetric_entropy_lt A K hK hKne (by rwa [hplus]) (by rwa [hminus])
  rw [hplus, hminus, hFY, hderiv] at h
  change (X * (CFC.log X - CFC.log A)).trace.re < _
  rw [hD]
  linarith

/-- The factor `1/8` in the faithful binary pinching comparison, with strictness
as soon as the pinching changes the matrix. The expression is homogeneous and
also applies to positive definite matrices without trace normalization. -/
theorem pinch_bound_matrix {n : ℕ} (W X : Mat n) (hW : W.IsHermitian)
    (hWW : W * W = 1) (hX : X.PosDef) :
    (X * (CFC.log X - CFC.log (pinch W X))).trace.re ≤
      ((X - W * X * W) * (CFC.log X - W * CFC.log X * W)).trace.re / 8 ∧
    (pinch W X ≠ X →
      (X * (CFC.log X - CFC.log (pinch W X))).trace.re <
        ((X - W * X * W) * (CFC.log X - W * CFC.log X * W)).trace.re / 8) := by
  refine ⟨?_, pinch_bound_matrix_strict W X hW hWW hX⟩
  by_cases he : pinch W X = X
  · have h : W * X * W = X := by
      have he' := congrArg (fun Z : Mat n => (2 : ℝ) • Z) he
      change (2 : ℝ) • ((1 / 2 : ℝ) • (X + W * X * W)) = (2 : ℝ) • X at he'
      rw [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul] at he'
      exact add_left_cancel (he'.trans (two_smul ℝ X))
    simp [he, h]
  · exact (pinch_bound_matrix_strict W X hW hWW hX he).le

/-- The comparison for the repository's finite-dimensional relative entropy. -/
theorem relativeEntropy_pinch_bound {n : ℕ} (W : Mat n) (hW : W.IsHermitian)
    (hWW : W * W = 1) (ρ : DensityState (Fin n))
    (hρ : (CStarMatrix.ofMatrix.symm ρ.1).PosDef) :
    let X := CStarMatrix.ofMatrix.symm ρ.1
    let σ := pinchState W hW hWW ρ hρ
    let rhs := ((X - W * X * W) * (CFC.log X - W * CFC.log X * W)).trace.re / 8
    quantumRelativeEntropy ρ σ ≤ rhs ∧
      (σ ≠ ρ → quantumRelativeEntropy ρ σ < rhs) := by
  dsimp only
  let X := CStarMatrix.ofMatrix.symm ρ.1
  let σ := pinchState W hW hWW ρ hρ
  have hσ : (CStarMatrix.ofMatrix.symm σ.1).PosDef := pinch_posDef W X hW hWW hρ
  rw [relativeEntropy_on_matrices ρ σ hρ.isHermitian hσ.isHermitian]
  obtain ⟨hle, hlt⟩ := pinch_bound_matrix W X hW hWW hρ
  refine ⟨hle, fun hchange => hlt ?_⟩
  intro he
  apply hchange
  apply Subtype.ext
  change CStarMatrix.ofMatrix (pinch W X) = CStarMatrix.ofMatrix X
  rw [he]

/-- The ordered two-pinching loss is bounded by one eighth of the sum of the
two symmetrized log trace forms evaluated at the original faithful state.
The bound is strict if either original pinching changes that state. -/
theorem two_pinching_entropy_bound {n : ℕ} [Nonempty (Fin n)] (U V : Mat n)
    (hU : U.IsHermitian) (hUU : U * U = 1)
    (hV : V.IsHermitian) (hVV : V * V = 1) (ρ : DensityState (Fin n))
    (hρ : (CStarMatrix.ofMatrix.symm ρ.1).PosDef) :
    let X := CStarMatrix.ofMatrix.symm ρ.1
    let S (W : Mat n) := ((X - W * X * W) * (CFC.log X - W * CFC.log X * W)).trace.re
    let ρU := pinchState U hU hUU ρ hρ
    let ρV := pinchState V hV hVV ρ hρ
    let hρV : (CStarMatrix.ofMatrix.symm ρV.1).PosDef :=
      pinch_posDef V X hV hVV hρ
    let F := pinchState U hU hUU ρV hρV
    quantumRelativeEntropy ρ F ≤ (S U + S V) / 8 ∧
      ((ρU ≠ ρ ∨ ρV ≠ ρ) → quantumRelativeEntropy ρ F < (S U + S V) / 8) := by
  intro X S ρU ρV hρV F
  have hcompare : quantumRelativeEntropy ρ F ≤
      quantumRelativeEntropy ρ ρU + quantumRelativeEntropy ρ ρV :=
    (two_pinching_entropy_comparison U V hU hUU hV hVV ρ hρ).2
  have hboundU : quantumRelativeEntropy ρ ρU ≤ S U / 8 ∧
      (ρU ≠ ρ → quantumRelativeEntropy ρ ρU < S U / 8) :=
    relativeEntropy_pinch_bound U hU hUU ρ hρ
  have hboundV : quantumRelativeEntropy ρ ρV ≤ S V / 8 ∧
      (ρV ≠ ρ → quantumRelativeEntropy ρ ρV < S V / 8) :=
    relativeEntropy_pinch_bound V hV hVV ρ hρ
  simp only [add_div (S U) (S V) 8]
  refine ⟨hcompare.trans (add_le_add hboundU.1 hboundV.1), ?_⟩
  rintro (hchangeU | hchangeV)
  · exact hcompare.trans_lt (add_lt_add_of_lt_of_le (hboundU.2 hchangeU) hboundV.1)
  · exact hcompare.trans_lt (add_lt_add_of_le_of_lt hboundU.1 (hboundV.2 hchangeV))

end WuPinchingEntropyResolvent
