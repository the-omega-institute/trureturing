/- GID: D5/S3/Divergence/AudenaertBinaryHolevoBound
   generality: G
   mirror-B: D5/B/S3/Divergence/AudenaertBinaryHolevoBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The binary Holevo information is bounded by trace distance in every dimension. -/

/- binaryHolevoBound
   proof_shape: content
   escape_witness: log_hasDerivAt_affine_of_lower_bound: dominated differentiation of the
     resolvent integral under a uniform positive lower bound, used by the skew-divergence
     estimate and singular-limit proof
   admission_basis: escape-witness
   Direct frozen dependencies (declaration identities from the scoped Lean report):
     D5/S3/ArithSums/TwoPointSlabSupport — D5.S3.ArithSums.TwoPointSlabSupport.logWidths
       statement_id: sha256:189bd2747ec55979eeaa109e8a25ce976d33c61cba999590c9ac6d19b17d5a3b
     D5/S3/ArithSums/TwoPointSlabSupport — D5.S3.ArithSums.TwoPointSlabSupport.log_widths_bounds
       statement_id: sha256:bcaece7b400e20f09087f962ec91d0d57e3e86b3d2221141bc1ae5c69ae5e642
     D5/S3/Divergence/LogDerivTrace — D5.S3.Divergence.LogDerivTrace.logDeriv
       statement_id: sha256:a90f9dee354f46f189f6580ba1b3ae88bf427894750c54a05e740869b0e89512
     D5/S3/Divergence/LogDerivTrace — D5.S3.Divergence.LogDerivTrace.logDeriv_integrable
       statement_id: sha256:d29e5e978197cc2c2de8ca45a2a7755f2a8e20db18bc426f43ecd264d09883ef
     D5/S3/Divergence/LogDerivTrace — D5.S3.Divergence.LogDerivTrace.pairKernel_integrable
       statement_id: sha256:2d1aa7b386439f55fc7ab6b5c4cba569df303e5472bb677060159813bc77f53c
     D5/S3/Divergence/LogDerivTrace — D5.S3.Divergence.LogDerivTrace.resolvent_eq_spectral
       statement_id: sha256:32418c28ea14eea0ab3014b59c0f7eca014560cee394906ca2dc45ba82bdc469
     D5/S3/Divergence/LogDerivTrace — D5.S3.Divergence.LogDerivTrace.scalarKernel_integrable
       statement_id: sha256:762111bf42f950c5b47a6fd56962947daa7e826439dcce62728a45fbcc7ca303
     D5/S3/Divergence/LogDerivTrace — D5.S3.Divergence.LogDerivTrace.trace_mul_logDeriv
       statement_id: sha256:f6fc2b2f36fe0ff12234183b5817929ace3e6949f49b2e10b7bf0f4ab5c1bbd5
     D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability — D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg
       statement_id: sha256:4e1e2463b054d4f1a17a47dfa173be720d81b8370e9189ac369460319c5840c1
     D5/S3/Quantum/Foundation/FiniteTraceDistance — D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm
       statement_id: sha256:12ad034b5758446e6d628c75121b3ad5f0c80bb305937e8c9ff87e82076bc059
     D5/S3/Quantum/Foundation/FiniteTraceDistance — D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_neg
       statement_id: sha256:d7a81ef774c91a733d963a18aa1a998fd412bb6e352db4f96b70ec875b1b00ec
     D5/S3/Quantum/Foundation/FiniteTraceDistance — D5.S3.Quantum.Foundation.FiniteTraceDistance.trace_norm_jordan_mass
       statement_id: sha256:fdb8cb601f51df385251551cad923f9150a7104b67ce271fcb777ba680d61c61
     D5/S3/Quantum/Subentropy/UniformIntegrals — D5.S3.Quantum.Subentropy.UniformIntegrals.reciprocal_difference
       statement_id: sha256:cc1fc2c5546f64c4f3b667a1256819478938b93163884fe5498e566d0ac44d70
     D5/S3/Weil/ZetaLinear/RankTrace — RHLinalg.trace_mul_nonneg_of_posSemidef
       statement_id: sha256:d0be9623184a0aa6b2753f04a89d828122fe7292de10124c81506a795f6decf6
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17312.
   CoPRelativeQuantumnessRefutation.reg states the affine depolarization formula;
   its I module is not on this module's dependency path. The regularization path
   uses Mathlib AffineMap.lineMap, with normalization proved in its consumers.
   Declarations and actual consumers:
     mix_lower_bound: proof_shape: bind-only; consumers: skew_relative_bound_of_uniform_positive.
     trace_pairing_mono_right: proof_shape: bind-only; consumers: differential_skew_bound, trace_pairing_mono_left.
     positive_jordan_mass_trace_zero: proof_shape: bind-only; consumers: states_positive_jordan_mass.
     log_hasDerivAt_affine_of_lower_bound: proof_shape: content; escape_witness: log_hasDerivAt_affine_of_lower_bound; consumers: skew_relative_bound_of_uniform_positive.
     vonNeumann2_continuous_hermitian_path: proof_shape: bind-only; consumers: qjs2_regularized_continuous, regularized_entropy_continuous.
     logDeriv_self: proof_shape: bind-only; consumers: differential_skew_bound.
     matrix_log_resolvent_integral: proof_shape: bind-only; consumers: log_hasDerivAt_affine_of_lower_bound.
     regularized_difference: proof_shape: bind-only; consumers: regularized_traceNorm_difference.
     scalar_log_resolvent_integral: proof_shape: bind-only; consumers: matrix_log_resolvent_integral.
     logDeriv_positive: proof_shape: bind-only; consumers: differential_skew_bound, logDeriv_mono, logDeriv_self.
     qjs2_relativeNat_identity: proof_shape: bind-only; consumers: uniformPositiveHolevoBound.
     relativeNat: proof_shape: bind-only; consumers: qjs2_relativeNat_identity, skew_relative_bound_of_uniform_positive, uniformPositiveHolevoBound.
     regularized_hermitian: proof_shape: bind-only; consumers: qjs2_regularized_continuous, regularized_entropy_continuous.
     regularized_zero: proof_shape: bind-only; consumers: binaryHolevo_of_uniformPositive.
     regularized_continuous: proof_shape: bind-only; consumers: qjs2_regularized_continuous, regularized_entropy_continuous.
     regularized_traceNorm_difference: proof_shape: bind-only; consumers: binaryHolevo_of_uniformPositive.
     logDeriv_smul: proof_shape: bind-only; consumers: differential_skew_bound.
     states_positive_jordan_mass: proof_shape: bind-only; consumers: skew_relative_bound_of_uniform_positive.
     regularized: proof_shape: bind-only; consumers: binaryHolevo_of_uniformPositive, qjs2_regularized_continuous, regularized_continuous, regularized_difference, regularized_entropy_continuous, regularized_eq_normalized, regularized_hermitian, regularized_isState, regularized_lower_bound, regularized_traceNorm_difference, regularized_zero.
     uniformPositiveHolevoBound: proof_shape: content; escape_witness: skew_relative_bound_of_uniform_positive; consumers: binaryHolevoBound.
     regularized_lower_bound: proof_shape: bind-only; consumers: binaryHolevo_of_uniformPositive.
     binaryHolevoBound: proof_shape: content; escape_witness: log_hasDerivAt_affine_of_lower_bound; consumers: D5.S3.Divergence.CoherenceL1RelativeEntropyBound.result.
     trace_pairing_mono_left: proof_shape: bind-only; consumers: differential_skew_bound.
     scalar_log_kernel_integrable: proof_shape: bind-only; consumers: matrix_log_resolvent_integral.
     inverse_shift_norm_bound: proof_shape: bind-only; consumers: log_hasDerivAt_affine_of_lower_bound.
     hermitian_sandwich_positive: proof_shape: bind-only; consumers: logDeriv_positive.
     logDeriv_mono: proof_shape: bind-only; consumers: differential_skew_bound.
     entropy_bits_trace_log: proof_shape: bind-only; consumers: qjs2_relativeNat_identity.
     regularization_denominator_pos: proof_shape: bind-only; consumers: binaryHolevo_of_uniformPositive, regularized_continuous, regularized_isState, regularized_lower_bound, regularized_traceNorm_difference.
     entropy_kernel_continuous: proof_shape: bind-only; consumers: vonNeumann2_continuous_hermitian_path.
     skew_relative_bound_of_uniform_positive: proof_shape: content; escape_witness: skew_relative_bound_of_uniform_positive; consumers: uniformPositiveHolevoBound.
     qjs2_regularized_continuous: proof_shape: bind-only; consumers: binaryHolevo_of_uniformPositive.
     regularized_isState: proof_shape: bind-only; consumers: binaryHolevo_of_uniformPositive.
     shifted_inverse_hasDerivAt: proof_shape: bind-only; consumers: log_hasDerivAt_affine_of_lower_bound.
     binaryHolevo_of_uniformPositive: proof_shape: content; escape_witness: binaryHolevo_of_uniformPositive; consumers: binaryHolevoBound.
     logDeriv_add: proof_shape: bind-only; consumers: logDeriv_mono.
     trace_logDeriv_pairing: proof_shape: bind-only; consumers: differential_skew_bound, logDeriv_self.
     regularized_entropy_continuous: proof_shape: bind-only; consumers: qjs2_regularized_continuous.
     differential_skew_bound: proof_shape: content; escape_witness: differential_skew_bound; consumers: skew_relative_bound_of_uniform_positive.
     regularized_eq_normalized: proof_shape: bind-only; consumers: regularized_continuous, regularized_difference, regularized_hermitian, regularized_isState, regularized_lower_bound, regularized_zero.
-/

import D5.S3.Divergence.LogDerivTrace
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S3.ArithSums.TwoPointSlabSupport
import D5.S3.Quantum.Subentropy.UniformIntegrals

noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators NNReal Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Divergence.AudenaertBinaryHolevoBound
open MeasureTheory
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 400000
open D5.S3.Divergence.LogDerivTrace

private theorem hermitian_sandwich_positive {n : ℕ} (R X : Matrix (Fin n) (Fin n) ℂ)
    (hR : R.IsHermitian) (hX : X.PosSemidef) : 0 ≤ R*X*R := by
  simpa only [hR.eq] using (hX.mul_mul_conjTranspose_same R).nonneg

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem logDeriv_positive {n : ℕ} (m X : Matrix (Fin n) (Fin n) ℂ)
    (hm : m.PosDef) (hX : X.PosSemidef) : 0 ≤ D5.S3.Divergence.LogDerivTrace.logDeriv m X := by
  unfold D5.S3.Divergence.LogDerivTrace.logDeriv
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hh : (m+t•1).IsHermitian := hm.isHermitian.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all t))
  exact hermitian_sandwich_positive _ _ hh.inv hX

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem logDeriv_add {n : ℕ} (m X Y : Matrix (Fin n) (Fin n) ℂ)
    (hm : m.PosDef) : D5.S3.Divergence.LogDerivTrace.logDeriv m (X+Y) = D5.S3.Divergence.LogDerivTrace.logDeriv m X + D5.S3.Divergence.LogDerivTrace.logDeriv m Y := by
  unfold D5.S3.Divergence.LogDerivTrace.logDeriv
  simp only [Matrix.mul_add, Matrix.add_mul]
  exact integral_add (D5.S3.Divergence.LogDerivTrace.logDeriv_integrable m X hm) (D5.S3.Divergence.LogDerivTrace.logDeriv_integrable m Y hm)

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem logDeriv_mono {n : ℕ} (m X Y : Matrix (Fin n) (Fin n) ℂ)
    (hm : m.PosDef) (hXY : X ≤ Y) : D5.S3.Divergence.LogDerivTrace.logDeriv m X ≤ D5.S3.Divergence.LogDerivTrace.logDeriv m Y := by
  have hz := logDeriv_positive m (Y-X) hm (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hXY))
  have hadd := logDeriv_add m (Y-X) X hm
  rw [sub_add_cancel] at hadd
  rw [← sub_nonneg]
  have he : D5.S3.Divergence.LogDerivTrace.logDeriv m Y - D5.S3.Divergence.LogDerivTrace.logDeriv m X = D5.S3.Divergence.LogDerivTrace.logDeriv m (Y-X) := by rw [hadd, add_sub_cancel_right]
  rw [he]
  exact hz

open MeasureTheory
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Divergence.LogDerivTrace

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem trace_logDeriv_pairing {n : ℕ} (m X Y : Matrix (Fin n) (Fin n) ℂ)
    (hm : m.PosDef) : (X * logDeriv m Y).trace = (Y * logDeriv m X).trace := by
  let TX : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
    ((Matrix.traceLinearMap (Fin n) ℂ ℂ).comp (mulLeftLinearMap (Fin n) ℂ X)).toContinuousLinearMap
  let TY : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
    ((Matrix.traceLinearMap (Fin n) ℂ ℂ).comp (mulLeftLinearMap (Fin n) ℂ Y)).toContinuousLinearMap
  have hx := TX.integral_comp_comm (D5.S3.Divergence.LogDerivTrace.logDeriv_integrable m Y hm)
  have hy := TY.integral_comp_comm (D5.S3.Divergence.LogDerivTrace.logDeriv_integrable m X hm)
  change (∫ t in Set.Ioi (0 : ℝ), (X * ((m+t•1)⁻¹ * Y * (m+t•1)⁻¹)).trace) =
    (X * logDeriv m Y).trace at hx
  change (∫ t in Set.Ioi (0 : ℝ), (Y * ((m+t•1)⁻¹ * X * (m+t•1)⁻¹)).trace) =
    (Y * logDeriv m X).trace at hy
  rw [← hx, ← hy]
  apply integral_congr_ae
  filter_upwards [] with t
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (X * (m+t•1)⁻¹) (Y * (m+t•1)⁻¹)

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Divergence.LogDerivTrace

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem logDeriv_self {n : ℕ} (m : Matrix (Fin n) (Fin n) ℂ) (hm : m.PosDef) :
    D5.S3.Divergence.LogDerivTrace.logDeriv m m=1 := by
  let L := D5.S3.Divergence.LogDerivTrace.logDeriv m m
  have hL : L.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (logDeriv_positive m m hm hm.posSemidef)).isHermitian
  let X := L-1
  have hX : X.IsHermitian := hL.sub Matrix.isHermitian_one
  have hp := trace_logDeriv_pairing m X m hm
  rw [trace_mul_logDeriv m X hm hX] at hp
  have hz : (Xᴴ*X).trace=0 := by
    rw [hX.eq]
    change ((L-1)*(L-1)).trace=0
    rw [Matrix.mul_sub,Matrix.trace_sub,Matrix.mul_one]
    change (X*L).trace-X.trace=0
    exact sub_eq_zero.mpr hp
  have hx := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hz
  exact sub_eq_zero.mp hx

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem logDeriv_smul {n : ℕ} (m X : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) :
    D5.S3.Divergence.LogDerivTrace.logDeriv m (c•X)=
      c•D5.S3.Divergence.LogDerivTrace.logDeriv m X := by
  unfold D5.S3.Divergence.LogDerivTrace.logDeriv
  simp only [Matrix.mul_smul,Matrix.smul_mul]
  exact integral_smul c _

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Divergence.LogDerivTrace
open D5.S3.Quantum.Foundation.FiniteTraceDistance

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem trace_pairing_mono_right {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (hBC : B ≤ C) : (A*B).trace.re ≤ (A*C).trace.re := by
  have h := RHLinalg.trace_mul_nonneg_of_posSemidef hA
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hBC))
  change 0 ≤ (A*(C-B)).trace.re at h
  rw [Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re] at h
  exact sub_nonneg.mp h

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem trace_pairing_mono_left {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℂ)
    (hC : C.PosSemidef) (hAB : A ≤ B) : (A*C).trace.re ≤ (B*C).trace.re := by
  rw [Matrix.trace_mul_comm A C,Matrix.trace_mul_comm B C]
  exact trace_pairing_mono_right C A B hC hAB

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem differential_skew_bound {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => ρ.PosSemidef ∧ ρ.trace = 1) ρ) (hσ : (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => ρ.PosSemidef ∧ ρ.trace = 1) σ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hm : (a•ρ+(1-a)•σ).PosDef) :
    a*((ρ*D5.S3.Divergence.LogDerivTrace.logDeriv (a•ρ+(1-a)•σ) (ρ-σ)).trace.re)
      ≤ ((ρ-σ)⁺).trace.re := by
  let m := a•ρ+(1-a)•σ
  let L := D5.S3.Divergence.LogDerivTrace.logDeriv m ρ
  have hL : L.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (logDeriv_positive m ρ hm hρ.1)
  have hD : IsSelfAdjoint (ρ-σ) := (hρ.1.isHermitian.sub hσ.1.isHermitian).isSelfAdjoint
  have hpos : ((ρ-σ)⁺).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg _)
  have hpair := trace_logDeriv_pairing m ρ (ρ-σ) hm
  have hfirst := trace_pairing_mono_left (ρ-σ) (ρ-σ)⁺ L hL (CFC.le_posPart hD)
  have hmge : a•ρ ≤ m := by
    change a•ρ ≤ a•ρ+(1-a)•σ
    exact le_add_of_nonneg_right (smul_nonneg (sub_nonneg.mpr ha1) hσ.1.nonneg)
  have hsecond := trace_pairing_mono_right (ρ-σ)⁺ (a•L) (1 : Matrix (Fin n) (Fin n) ℂ) hpos (by
    rw [show a•L=D5.S3.Divergence.LogDerivTrace.logDeriv m (a•ρ) by exact (logDeriv_smul m ρ a).symm]
    rw [← logDeriv_self m hm]
    exact logDeriv_mono m (a•ρ) m hm hmge)
  rw [Matrix.mul_smul,Matrix.trace_smul] at hsecond
  simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Matrix.mul_one] at hsecond
  rw [hpair]
  exact (mul_le_mul_of_nonneg_left hfirst ha).trans hsecond

open MeasureTheory Filter
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

private theorem scalar_log_kernel_integrable (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => (1+t)⁻¹-(r+t)⁻¹) (Set.Ioi 0) := by
  have h := (D5.S3.Divergence.LogDerivTrace.pairKernel_integrable 1 r (by norm_num) hr).const_mul (r-1)
  apply IntegrableOn.congr_fun h _ measurableSet_Ioi
  intro t ht
  change 0 < t at ht
  field_simp [(add_pos zero_lt_one ht).ne', (add_pos hr ht).ne']
  ring

private theorem scalar_log_resolvent_integral (r : ℝ) (hr : 0 < r) :
    (∫ t in Set.Ioi (0 : ℝ), (1+t)⁻¹-(r+t)⁻¹) = Real.log r := by
  by_cases h : 1 ≤ r
  · simpa only [one_div, add_comm, Real.log_one, sub_zero] using
      (D5.S3.Quantum.Subentropy.UniformIntegrals.reciprocal_difference
        1 r zero_lt_one h).2
  · have hv := congrArg Neg.neg
      (D5.S3.Quantum.Subentropy.UniformIntegrals.reciprocal_difference
        r 1 hr (le_of_lt (lt_of_not_ge h))).2
    rw [← integral_neg] at hv
    simpa only [one_div, add_comm, neg_sub, Real.log_one, zero_sub, neg_neg] using hv

open Matrix MeasureTheory
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem matrix_log_resolvent_integral {n : ℕ} (m : Matrix (Fin n) (Fin n) ℂ)
    (hm : m.PosDef) :
    IntegrableOn (fun t : ℝ => (1+t)⁻¹•(1 : Matrix (Fin n) (Fin n) ℂ)-(m+t•1)⁻¹) (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ), (1+t)⁻¹•(1 : Matrix (Fin n) (Fin n) ℂ)-(m+t•1)⁻¹)=CFC.log m := by
  let U : Matrix (Fin n) (Fin n) ℂ := hm.isHermitian.eigenvectorUnitary
  let v : ℝ → Fin n → ℂ := fun t i => ((1+t)⁻¹-(hm.isHermitian.eigenvalues i+t)⁻¹ : ℝ)
  let D := Matrix.diagonalLinearMap (Fin n) ℂ ℂ
  let C : (Fin n → ℂ) →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    ((mulRightLinearMap (Fin n) ℂ (star U)).comp
      ((mulLeftLinearMap (Fin n) ℂ U).comp D)).toContinuousLinearMap
  have hv : Integrable v (volume.restrict (Set.Ioi (0:ℝ))) := by
    rw [integrable_pi_iff]
    intro i
    exact (scalar_log_kernel_integrable _ (hm.eigenvalues_pos i)).ofReal
  have he : ∀ t∈Set.Ioi (0:ℝ), C (v t)=(1+t)⁻¹•1-(m+t•1)⁻¹ := by
    intro t ht
    change 0<t at ht
    change U*diagonal (v t)*star U=_
    rw [D5.S3.Divergence.LogDerivTrace.resolvent_eq_spectral m hm t ht.le]
    have hd : diagonal (v t)=(1+t)⁻¹•1-diagonal (fun i => ((hm.isHermitian.eigenvalues i+t : ℝ):ℂ)⁻¹) := by
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
      congr 1
      funext i
      simp [v, Complex.ofReal_sub, Complex.ofReal_inv, Complex.real_smul]
    rw [hd,Matrix.mul_sub,Matrix.sub_mul]
    congr 1
    simp only [Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]
    rw [show U*star U=1 from Unitary.coe_mul_star_self hm.isHermitian.eigenvectorUnitary]
  have hi : IntegrableOn (fun t : ℝ => (1+t)⁻¹•(1 : Matrix (Fin n) (Fin n) ℂ)-(m+t•1)⁻¹) (Set.Ioi 0) :=
    IntegrableOn.congr_fun (C.integrable_comp hv) he measurableSet_Ioi
  refine ⟨hi,?_⟩
  have hval : (∫ t in Set.Ioi (0:ℝ), v t)=fun i => (Real.log (hm.isHermitian.eigenvalues i) : ℂ) := by
    funext i
    have heval := (ContinuousLinearMap.proj i : (Fin n→ℂ) →L[ℂ] ℂ).integral_comp_comm hv
    change (∫ t in Set.Ioi (0:ℝ), v t i)=(∫ t in Set.Ioi (0:ℝ), v t) i at heval
    rw [← heval]
    change (∫ t in Set.Ioi (0:ℝ), (((1+t)⁻¹-(hm.isHermitian.eigenvalues i+t)⁻¹ : ℝ):ℂ))=_
    rw [integral_complex_ofReal,scalar_log_resolvent_integral _ (hm.eigenvalues_pos i)]
  calc
    _ = ∫ t in Set.Ioi (0:ℝ), C (v t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (he t ht).symm
    _ = C (∫ t in Set.Ioi (0:ℝ), v t) := C.integral_comp_comm hv
    _ = CFC.log m := by
      rw [hval]
      change U*diagonal (fun i => (Real.log (hm.isHermitian.eigenvalues i) : ℂ))*star U= cfc Real.log m
      rw [hm.isHermitian.cfc_eq]
      rfl

open Matrix
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem inverse_shift_norm_bound {n : ℕ} (m : Matrix (Fin n) (Fin n) ℂ)
    (c t : ℝ) (hc : 0< c) (ht : 0≤ t) (hm : c•(1 : Matrix (Fin n) (Fin n) ℂ)≤ m) :
    ‖(m+t•1)⁻¹‖≤ (c+t)⁻¹ := by
  have hct : 0< c+t := add_pos_of_pos_of_nonneg hc ht
  have hlo : (c+t)•(1 : Matrix (Fin n) (Fin n) ℂ)≤ m+t•1 := by
    rw [add_smul]
    exact add_le_add hm le_rfl
  have hs : IsStrictlyPositive ((c+t)•(1 : Matrix (Fin n) (Fin n) ℂ)) :=
    IsStrictlyPositive.smul hct isStrictlyPositive_one
  have hp : (m+t•1).PosDef := (hs.of_le hlo).posDef
  have hi := CStarAlgebra.ringInverse_le_ringInverse hlo hs
  have hscalar : (((c+t)•1 : Matrix (Fin n) (Fin n) ℂ)⁻¹)=(c+t)⁻¹•1 := by
    letI : Invertible ((c+t : ℝ) : ℂ) := invertibleOfNonzero (by exact_mod_cast hct.ne')
    have he (a : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) : (a : ℂ) • A = a • A := Complex.coe_smul a A
    simpa only [invOf_eq_inv, ← Complex.ofReal_inv, he, inv_one] using
      (Matrix.inv_smul (A := (1 : Matrix (Fin n) (Fin n) ℂ)) ((c+t : ℝ) : ℂ) (by simp))
  simp only [← Matrix.nonsing_inv_eq_ringInverse,hscalar] at hi
  have hnorm := (CStarAlgebra.norm_le_iff_le_algebraMap ((m+t•1)⁻¹)
    (inv_nonneg.mpr hct.le) hp.inv.posSemidef.nonneg).mpr ?_
  · exact hnorm
  · simpa only [Algebra.algebraMap_eq_smul_one] using hi

open Matrix
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem shifted_inverse_hasDerivAt {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℂ)
    (s t : ℝ) (h : IsUnit (A+s•X+t•1)) :
    HasDerivAt (fun a : ℝ => (A+a•X+t•1)⁻¹)
      (-((A+s•X+t•1)⁻¹*X*(A+s•X+t•1)⁻¹)) s := by
  obtain ⟨u,hu⟩ := h
  have hp : HasDerivAt (fun a : ℝ => A+a•X+t•1) X s := by
    convert! (((hasDerivAt_id s).smul_const X).const_add A).add_const (t•1) using 1 <;> simp
  have hf := hasFDerivAt_ringInverse (𝕜:=ℝ) u
  rw [hu] at hf
  have hh := hf.comp_hasDerivAt s hp
  convert! hh using 1 <;>
    simp [Matrix.nonsing_inv_eq_ringInverse,ContinuousLinearMap.mulLeftRight_apply,Matrix.coe_units_inv,hu,Function.comp_def]

open Matrix MeasureTheory Filter
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem log_hasDerivAt_affine_of_lower_bound {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℂ)
    (a c : ℝ) (hc : 0<c) (s : Set ℝ) (hs : s ∈ 𝓝 a)
    (hlo : ∀ b ∈  s, c • (1 : Matrix (Fin n) (Fin n) ℂ) ≤  A+b • X) :
    HasDerivAt (fun b : ℝ => CFC.log (A+b • X))
      (D5.S3.Divergence.LogDerivTrace.logDeriv (A+a • X) X) a := by
  let M : ℝ → Matrix (Fin n) (Fin n) ℂ := fun b => A+b • X
  let F : ℝ → ℝ → Matrix (Fin n) (Fin n) ℂ := fun b t => (1+t)⁻¹ • 1-(M b+t • 1)⁻¹
  let F' : ℝ → ℝ → Matrix (Fin n) (Fin n) ℂ := fun b t => (M b+t • 1)⁻¹*X*(M b+t • 1)⁻¹
  have ha : a ∈  s := mem_of_mem_nhds hs
  have hpos : ∀ b ∈  s, (M b).PosDef := by
    intro b hb
    exact ((IsStrictlyPositive.smul hc isStrictlyPositive_one).of_le (hlo b hb)).posDef
  have hshift : ∀ b ∈  s, ∀ (t : ℝ), 0 ≤ t → (M b+t • 1).PosDef := by
    intro b hb t ht
    exact (hpos b hb).add_posSemidef (Matrix.nonneg_iff_posSemidef.mp (smul_nonneg ht (zero_le_one : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ 1)))
  have hFm : ∀ᶠ b in 𝓝 a, AEStronglyMeasurable (F b) (volume.restrict (Set.Ioi (0:ℝ))) := by
    filter_upwards [hs] with b hb
    exact (matrix_log_resolvent_integral (M b) (hpos b hb)).1.aestronglyMeasurable
  have hFi : Integrable (F a) (volume.restrict (Set.Ioi (0:ℝ))) :=
    (matrix_log_resolvent_integral (M a) (hpos a ha)).1
  have hF'm := (D5.S3.Divergence.LogDerivTrace.logDeriv_integrable (M a) X (hpos a ha)).aestronglyMeasurable
  have hbd : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0:ℝ))), ∀ b ∈  s,
      ‖F' b t‖ ≤ ‖X‖/(c+t)^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro b hb
    change 0<t at ht
    have hR := inverse_shift_norm_bound (M b) c t hc ht.le (hlo b hb)
    have hp : 0 ≤ (c+t)⁻¹ := inv_nonneg.mpr (add_pos hc ht).le
    calc
      _  ≤  (‖(M b+t • 1)⁻¹‖*‖X‖)*‖(M b+t • 1)⁻¹‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _  ≤  ((c+t)⁻¹*‖X‖)*(c+t)⁻¹ := mul_le_mul
        (mul_le_mul_of_nonneg_right hR (norm_nonneg X)) hR (norm_nonneg _) (mul_nonneg hp (norm_nonneg X))
      _ = ‖X‖/(c+t)^2 := by field_simp [(add_pos hc ht).ne']
  have hbi : Integrable (fun t : ℝ => ‖X‖/(c+t)^2) (volume.restrict (Set.Ioi (0:ℝ))) := by
    have h := (D5.S3.Divergence.LogDerivTrace.scalarKernel_integrable c hc).div_const c
    have h := h.const_mul ‖X‖
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    field_simp [hc.ne']
  have hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0:ℝ))), ∀ b ∈  s,
      HasDerivAt (fun d => F d t) (F' b t) b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro b hb
    have hi := shifted_inverse_hasDerivAt A X b t (hshift b hb t (le_of_lt ht)).isUnit
    convert! hi.const_sub ((1+t)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ)) using 1 <;> simp [F,F',M]
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hFm hFi hF'm hbd hbi hdiff).2
  change HasDerivAt (fun b => ∫ t in Set.Ioi (0:ℝ), F b t)
    (D5.S3.Divergence.LogDerivTrace.logDeriv (M a) X) a at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hs] with b hb
  exact (matrix_log_resolvent_integral (M b) (hpos b hb)).2.symm

open Matrix
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance

private theorem positive_jordan_mass_trace_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (htr : A.trace=0) : (A⁺).trace.re=traceNorm A/2 := by
  have hj := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M.trace.re)
    (CFC.posPart_sub_negPart A hA.isSelfAdjoint)
  rw [Matrix.trace_sub,Complex.sub_re,htr,Complex.zero_re] at hj
  have hn := trace_norm_jordan_mass A hA
  linarith

private theorem states_positive_jordan_mass {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => ρ.PosSemidef ∧ ρ.trace = 1) ρ) (hσ : (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => ρ.PosSemidef ∧ ρ.trace = 1) σ) : ((ρ-σ)⁺).trace.re=traceNorm (ρ-σ)/2 := by
  apply positive_jordan_mass_trace_zero (ρ-σ) (hρ.1.isHermitian.sub hσ.1.isHermitian)
  rw [Matrix.trace_sub,hρ.2,hσ.2,sub_self]

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem entropy_bits_trace_log {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.IsHermitian) : (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) ρ= -((ρ*CFC.log ρ).trace.re)/Real.log 2 := by
  have hcont (f : ℝ→ℝ) : ContinuousOn f (spectrum ℝ ρ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  have he : cfc (fun x : ℝ => x*Real.logb 2 x) ρ=
      (Real.log 2)⁻¹•(ρ*CFC.log ρ) := by
    have hf : (fun x : ℝ => x*Real.logb 2 x)=(fun x : ℝ => (Real.log 2)⁻¹*(x*Real.log x)) := by
      funext x
      rw [Real.logb]
      ring
    rw [hf]
    rw [cfc_const_mul _ _ _ (hcont _),cfc_mul _ _ _ (hcont _) (hcont _),
      cfc_id' (R:=ℝ) ρ hρ.isSelfAdjoint]
    rfl
  dsimp only
  rw [he,Matrix.trace_smul,Complex.smul_re]
  change -((Real.log 2)⁻¹*((ρ*CFC.log ρ).trace.re))=_
  ring

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteTraceDistance
private noncomputable def relativeNat {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (ρ*(CFC.log ρ-CFC.log σ)).trace.re

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem qjs2_relativeNat_identity {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (fun {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) => (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) ((1/2 : ℂ) • (ρ + σ)) - ((fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) ρ + (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) σ) / 2) ρ σ=(relativeNat ρ ((1/2 : ℂ)•(ρ+σ))+relativeNat σ ((1/2 : ℂ)•(ρ+σ)))/(2*Real.log 2) := by
  let m := (1/2 : ℂ)•(ρ+σ)
  have hm : m.IsHermitian := (hρ.add hσ).smul (by rw [isSelfAdjoint_iff]; simp : IsSelfAdjoint (1/2 : ℂ))
  have ht : (m*CFC.log m).trace.re=((ρ*CFC.log m).trace.re+(σ*CFC.log m).trace.re)/2 := by
    simp only [m,Matrix.smul_mul,Matrix.add_mul,Matrix.trace_smul,Matrix.trace_add,
      Complex.smul_re,smul_eq_mul,Complex.mul_re,Complex.div_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
    norm_num
    ring
  dsimp only
  unfold relativeNat
  have e0 := entropy_bits_trace_log _ hm
  have e1 := entropy_bits_trace_log _ hρ
  have e2 := entropy_bits_trace_log _ hσ
  dsimp only at e0 e1 e2
  rw [e0, e1, e2]
  change -((m*CFC.log m).trace.re)/Real.log 2-
    (-((ρ*CFC.log ρ).trace.re)/Real.log 2 + -((σ*CFC.log σ).trace.re)/Real.log 2)/2=_
  rw [ht,Matrix.mul_sub,Matrix.mul_sub,Matrix.trace_sub,Matrix.trace_sub,Complex.sub_re,Complex.sub_re]
  ring

open Matrix MeasureTheory Filter
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteTraceDistance

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem mix_lower_bound {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) (c b : ℝ)
    (hρ : c • (1 : Matrix (Fin n) (Fin n) ℂ)  ≤  ρ)
    (hσ : c • (1 : Matrix (Fin n) (Fin n) ℂ)  ≤  σ) (hb : b ∈ Set.Icc (0:ℝ) 1) :
    c • (1 : Matrix (Fin n) (Fin n) ℂ)  ≤  b • ρ+(1-b) • σ := by
  have h := add_le_add (smul_le_smul_of_nonneg_left hρ hb.1)
    (smul_le_smul_of_nonneg_left hσ (sub_nonneg.mpr hb.2))
  convert! h using 1 <;> module

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem skew_relative_bound_of_uniform_positive {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => ρ.PosSemidef ∧ ρ.trace = 1) ρ) (hσ : (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => ρ.PosSemidef ∧ ρ.trace = 1) σ) (c α : ℝ) (hc : 0<c) (hα : 0<α) (hα1 : α<1)
    (hρc : c • (1 : Matrix (Fin n) (Fin n) ℂ)  ≤  ρ)
    (hσc : c • (1 : Matrix (Fin n) (Fin n) ℂ)  ≤  σ) :
    relativeNat ρ (α • ρ+(1-α) • σ)  ≤  -Real.log α*(traceNorm (ρ-σ)/2) := by
  let M : ℝ→Matrix (Fin n) (Fin n) ℂ := fun a => a • ρ+(1-a) • σ
  let T := traceNorm (ρ-σ)/2
  let f : ℝ→ℝ := fun a => (ρ*CFC.log (M a)).trace.re
  let f' : ℝ→ℝ := fun a => (ρ*D5.S3.Divergence.LogDerivTrace.logDeriv (M a) (ρ-σ)).trace.re
  let g : ℝ→ℝ := fun a => T*Real.log a-f a
  let g' : ℝ→ℝ := fun a => T/a-f' a
  let TC : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
    ((Matrix.traceLinearMap (Fin n) ℂ ℂ).comp (mulLeftLinearMap (Fin n) ℂ ρ)).toContinuousLinearMap
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ := Complex.reCLM.comp (TC.restrictScalars ℝ)
  have hpos : ∀ a ∈ Set.Icc (0:ℝ) 1, (M a).PosDef := by
    intro a ha
    exact ((IsStrictlyPositive.smul hc isStrictlyPositive_one).of_le
      (mix_lower_bound ρ σ c a hρc hσc ha)).posDef
  have hMeq : ∀ a, σ+a • (ρ-σ)=M a := by intro a; dsimp [M]; module
  have hf : ∀ a ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f (f' a) a := by
    intro a ha
    have hlog := log_hasDerivAt_affine_of_lower_bound σ (ρ-σ) a c hc (Set.Ioo (0:ℝ) 1)
      (isOpen_Ioo.mem_nhds ha) (by
        intro b hb
        rw [hMeq b]
        exact mix_lower_bound ρ σ c b hρc hσc ⟨hb.1.le,hb.2.le⟩)
    simp only [hMeq] at hlog
    convert! L.hasFDerivAt.comp_hasDerivAt a hlog using 1
  have hfc : ContinuousOn f (Set.Icc α 1) := by
    have hmc : Continuous M := by unfold M; fun_prop
    have hlc : ContinuousOn (fun a => CFC.log (M a)) (Set.Icc α 1) := CFC.continuousOn_log.comp hmc.continuousOn (by
      intro a ha
      have hp := hpos a ⟨le_trans hα.le ha.1,ha.2⟩
      exact ⟨hp.isHermitian.isSelfAdjoint,hp.isUnit⟩)
    exact L.continuous.comp_continuousOn hlc
  have hgc : ContinuousOn g (Set.Icc α 1) := by
    apply (continuousOn_const.mul (Real.continuousOn_log.mono ?_)).sub hfc
    intro a ha
    exact ne_of_gt (lt_of_lt_of_le hα ha.1)
  have hg : ∀ a ∈ Set.Ioo (0:ℝ) 1, HasDerivAt g (g' a) a := by
    intro a ha
    convert! ((Real.hasDerivAt_log (ne_of_gt ha.1)).const_mul T).sub (hf a ha) using 1 <;>
      simp [g,g',one_div,div_eq_mul_inv]
  have hgpos : ∀ a ∈ Set.Ioo (0:ℝ) 1, 0 ≤ g' a := by
    intro a ha
    have hd := differential_skew_bound ρ σ hρ hσ a ha.1.le ha.2.le (hpos a ⟨ha.1.le,ha.2.le⟩)
    rw [states_positive_jordan_mass ρ σ hρ hσ] at hd
    have hh : f' a ≤ T/a := (le_div_iff₀ ha.1).mpr (by simpa [f',T,M,mul_comm] using hd)
    exact sub_nonneg.mpr hh
  have hmono : MonotoneOn g (Set.Icc α 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc α 1) hgc
      (by
        intro a ha
        rw [interior_Icc] at ha
        exact (hg a ⟨lt_trans hα ha.1,ha.2⟩).hasDerivWithinAt)
      (by
        intro a ha
        rw [interior_Icc] at ha
        exact hgpos a ⟨lt_trans hα ha.1,ha.2⟩)
  have h := hmono ⟨le_rfl,hα1.le⟩ ⟨hα1.le,le_rfl⟩ hα1.le
  have h1 : M 1=ρ := by simp [M]
  simp only [g,f,h1,Real.log_one,mul_zero,zero_sub] at h
  unfold relativeNat
  rw [Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re]
  change (ρ*CFC.log ρ).trace.re-(ρ*CFC.log (M α)).trace.re  ≤  -Real.log α*T
  linarith

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

private theorem entropy_kernel_continuous : Continuous (fun x : ℝ => x * Real.logb 2 x) := by
  have h := Real.continuous_mul_log.div_const (Real.log 2)
  convert h using 1
  funext x
  rw [Real.logb, mul_div_assoc]

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem vonNeumann2_continuous_hermitian_path {n : ℕ} {X : Type*} [TopologicalSpace X]
    (ρ : X → Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (hh : ∀ x, (ρ x).IsHermitian) : Continuous (fun x => (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) (ρ x)) := by
  have hc : Continuous (fun x => cfc (fun t : ℝ => t * Real.logb 2 t) (ρ x)) :=
    Continuous.cfc_of_mem_nhdsSet (s := Set.univ) (p := IsSelfAdjoint)
      (fun t : ℝ => t * Real.logb 2 t) (by simp) hρ hh entropy_kernel_continuous.continuousOn
  let tr : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
    (Matrix.traceLinearMap (Fin n) ℂ ℂ).toContinuousLinearMap
  exact (Complex.continuous_re.comp (tr.continuous.comp hc)).neg

open Matrix Filter
open scoped NNReal Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteTraceDistance

private noncomputable def regularized {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ≥0) : Matrix (Fin n) (Fin n) ℂ :=
  AffineMap.lineMap ρ ((n : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ))
    ((n : ℝ) * (ε : ℝ) / (1 + (n : ℝ) * (ε : ℝ)))

private theorem regularized_eq_normalized {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (ε : ℝ≥0) : regularized ρ ε = (1+(n:ℝ)*(ε:ℝ))⁻¹ • (ρ+(ε:ℝ)•1) := by
  by_cases hn : n = 0
  · subst n; exact Subsingleton.elim _ _
  · have hnR : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hd : (1+(n:ℝ)*(ε:ℝ)) ≠ 0 := ne_of_gt
      (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (Nat.cast_nonneg n) ε.coe_nonneg))
    rw [regularized, AffineMap.lineMap_apply_module]
    simp only [smul_add, smul_smul]
    congr 1
    · congr 1; field_simp [hnR, hd] <;> ring
    · congr 1; field_simp [hnR, hd] <;> ring

private theorem regularization_denominator_pos (n : ℕ) (ε : ℝ≥0) : 0<1+(n:ℝ)*(ε:ℝ) := by
  exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (Nat.cast_nonneg n) ε.coe_nonneg)

private theorem regularized_hermitian {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.IsHermitian) (ε : ℝ≥0) : (regularized ρ ε).IsHermitian := by
  rw [regularized_eq_normalized]
  exact (hρ.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all (ε:ℝ)))).smul (IsSelfAdjoint.all _)

private theorem regularized_isState {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => ρ.PosSemidef ∧ ρ.trace = 1) ρ) (ε : ℝ≥0) : (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => ρ.PosSemidef ∧ ρ.trace = 1) (regularized ρ ε) := by
  rw [regularized_eq_normalized]
  refine ⟨(hρ.1.add (Matrix.nonneg_iff_posSemidef.mp (smul_nonneg ε.coe_nonneg (zero_le_one : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ 1)))).smul
    (inv_nonneg.mpr (regularization_denominator_pos n ε).le),?_⟩
  simp only [regularized_eq_normalized,Matrix.trace_smul,Matrix.trace_add,Matrix.trace_one,hρ.2,Fintype.card_fin]
  have he : (1+(ε:ℝ)•(n:ℂ))=(1+(n:ℝ)*(ε:ℝ):ℝ) := by
    simp only [Complex.real_smul,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_one,Complex.ofReal_natCast]
    ring
  rw [he]
  simp only [Complex.real_smul,← Complex.ofReal_mul,inv_mul_cancel₀ (regularization_denominator_pos n ε).ne',Complex.ofReal_one]

private theorem regularized_lower_bound {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.PosSemidef) (ε : ℝ≥0) :
    ((ε:ℝ)/(1+(n:ℝ)*(ε:ℝ)))•(1 : Matrix (Fin n) (Fin n) ℂ) ≤ regularized ρ ε := by
  simpa only [regularized_eq_normalized, smul_add, div_eq_mul_inv, mul_comm (ε : ℝ), smul_smul] using
    (smul_le_smul_of_nonneg_left
      (le_add_of_nonneg_left hρ.nonneg :
        (ε : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ ρ + (ε : ℝ) • 1)
      (inv_nonneg.mpr (regularization_denominator_pos n ε).le))

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem regularized_continuous {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) : Continuous (regularized ρ) := by
  have hpath : regularized ρ = fun ε : ℝ≥0 =>
      (1+(n:ℝ)*(ε:ℝ))⁻¹ • (ρ+(ε:ℝ)•1) := by
    funext ε
    exact regularized_eq_normalized ρ ε
  rw [hpath]
  have hd : Continuous (fun ε : ℝ≥0 => (1+(n:ℝ)*(ε:ℝ))⁻¹) :=
    (continuous_const.add (continuous_const.mul continuous_subtype_val)).inv₀
      (fun ε => (regularization_denominator_pos n ε).ne')
  exact hd.smul (continuous_const.add (continuous_subtype_val.smul continuous_const))

@[simp] private theorem regularized_zero {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) : regularized ρ 0=ρ := by simp [regularized_eq_normalized]

private theorem regularized_difference {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ≥0) :
    regularized ρ ε-regularized σ ε=(1+(n:ℝ)*(ε:ℝ))⁻¹•(ρ-σ) := by
  simpa only [regularized_eq_normalized, add_sub_add_right_eq_sub] using
    (smul_sub (1 + (n : ℝ) * (ε : ℝ))⁻¹
      (ρ + (ε : ℝ) • 1) (σ + (ε : ℝ) • 1)).symm

private theorem regularized_traceNorm_difference {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ≥0) :
    traceNorm (regularized ρ ε-regularized σ ε)=(1+(n:ℝ)*(ε:ℝ))⁻¹*traceNorm (ρ-σ) := by
  rw [regularized_difference]
  have h := D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg (ρ-σ) (1+(n:ℝ)*(ε:ℝ))⁻¹
    (inv_nonneg.mpr (regularization_denominator_pos n ε).le)
  convert! h using 1

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem regularized_entropy_continuous {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.IsHermitian) : Continuous (fun ε : ℝ≥0 => (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) (regularized ρ ε)) :=
  vonNeumann2_continuous_hermitian_path _ (regularized_continuous ρ) (regularized_hermitian ρ hρ)

open Matrix Filter
open scoped NNReal Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteTraceDistance


attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem qjs2_regularized_continuous {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    Continuous (fun ε : ℝ≥0 => (fun {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) => (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) ((1/2 : ℂ) • (ρ + σ)) - ((fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) ρ + (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) σ) / 2) (regularized ρ ε) (regularized σ ε)) := by
  have hm := vonNeumann2_continuous_hermitian_path
    (fun ε : ℝ≥0 => (1/2:ℂ)•(regularized ρ ε+regularized σ ε))
    ((regularized_continuous ρ).add (regularized_continuous σ) |>.const_smul (1/2:ℂ))
    (fun ε => (regularized_hermitian ρ hρ ε |>.add (regularized_hermitian σ hσ ε)).smul
      (by rw [isSelfAdjoint_iff]; simp))
  exact hm.sub (((regularized_entropy_continuous ρ hρ).add
    (regularized_entropy_continuous σ hσ)).div_const 2)

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem binaryHolevo_of_uniformPositive (hP : (∀ n : ℕ, ∀ ρ σ : Matrix (Fin n) (Fin n) ℂ, (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => ρ.PosSemidef ∧ ρ.trace = 1) ρ → (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => ρ.PosSemidef ∧ ρ.trace = 1) σ → ∀ c : ℝ, 0<c → c•(1 : Matrix (Fin n) (Fin n) ℂ) ≤ ρ → c•(1 : Matrix (Fin n) (Fin n) ℂ) ≤ σ → (fun {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) => (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) ((1/2 : ℂ) • (ρ + σ)) - ((fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) ρ + (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) σ) / 2) ρ σ ≤ traceNorm (ρ-σ)/2)) : (∀ n : ℕ, ∀ σ τ : Matrix (Fin n) (Fin n) ℂ, (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => ρ.PosSemidef ∧ ρ.trace = 1) σ → (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => ρ.PosSemidef ∧ ρ.trace = 1) τ → (fun {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) => (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) ((1/2 : ℂ) • (ρ + σ)) - ((fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) ρ + (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) σ) / 2) σ τ ≤ traceNorm (σ-τ)/2) := by
  intro n ρ σ hρ hσ
  let lhs : ℝ≥0→ℝ := fun ε => (fun {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) => (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) ((1/2 : ℂ) • (ρ + σ)) - ((fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) ρ + (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) σ) / 2) (regularized ρ ε) (regularized σ ε)
  let rhs : ℝ≥0→ℝ := fun ε => (1+(n:ℝ)*(ε:ℝ))⁻¹*traceNorm (ρ-σ)/2
  have hl : Tendsto lhs (𝓝[>] (0:ℝ≥0)) (𝓝 ((fun {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) => (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) ((1/2 : ℂ) • (ρ + σ)) - ((fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) ρ + (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) σ) / 2) ρ σ)) := by
    have hc := qjs2_regularized_continuous ρ σ hρ.1.isHermitian hσ.1.isHermitian
    have ht : Tendsto lhs (𝓝 (0:ℝ≥0)) (𝓝 (lhs 0)) := (show Continuous lhs from hc).continuousAt.tendsto
    simp only [lhs,regularized_zero] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  have hd : Continuous (fun ε : ℝ≥0 => (1+(n:ℝ)*(ε:ℝ))⁻¹) :=
    (continuous_const.add (continuous_const.mul continuous_subtype_val)).inv₀
      (fun ε => (regularization_denominator_pos n ε).ne')
  have hr : Tendsto rhs (𝓝[>] (0:ℝ≥0)) (𝓝 (traceNorm (ρ-σ)/2)) := by
    have hc : Continuous rhs := (hd.mul continuous_const).div_const 2
    have ht : Tendsto rhs (𝓝 (0:ℝ≥0)) (𝓝 (rhs 0)) := hc.continuousAt.tendsto
    simp only [rhs,NNReal.coe_zero,mul_zero,add_zero,inv_one,one_mul] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0<ε at hε
  have he : 0<(ε:ℝ) := hε
  have hp := hP n (regularized ρ ε) (regularized σ ε)
    (regularized_isState ρ hρ ε) (regularized_isState σ hσ ε)
    ((ε:ℝ)/(1+(n:ℝ)*(ε:ℝ))) (div_pos he (regularization_denominator_pos n ε))
    (regularized_lower_bound ρ hρ.1 ε) (regularized_lower_bound σ hσ.1 ε)
  rw [regularized_traceNorm_difference] at hp
  exact hp

open Matrix
open scoped NNReal Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteTraceDistance

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem uniformPositiveHolevoBound : (∀ n : ℕ, ∀ ρ σ : Matrix (Fin n) (Fin n) ℂ, (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => ρ.PosSemidef ∧ ρ.trace = 1) ρ → (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => ρ.PosSemidef ∧ ρ.trace = 1) σ → ∀ c : ℝ, 0<c → c•(1 : Matrix (Fin n) (Fin n) ℂ) ≤ ρ → c•(1 : Matrix (Fin n) (Fin n) ℂ) ≤ σ → (fun {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) => (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) ((1/2 : ℂ) • (ρ + σ)) - ((fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) ρ + (fun {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) => -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re) σ) / 2) ρ σ ≤ traceNorm (ρ-σ)/2) := by
  intro n ρ σ hρ hσ c hc hρc hσc
  rw [qjs2_relativeNat_identity ρ σ hρ.1.isHermitian hσ.1.isHermitian]
  have hr := skew_relative_bound_of_uniform_positive ρ σ hρ hσ c (1/2) hc (by norm_num) (by norm_num) hρc hσc
  have hs := skew_relative_bound_of_uniform_positive σ ρ hσ hρ c (1/2) hc (by norm_num) (by norm_num) hσc hρc
  have hhalf (A B : Matrix (Fin n) (Fin n) ℂ) :
      (1/2:ℝ)•A+(1-(1/2:ℝ))•B=(1/2:ℂ)•(A+B) := by
    rw [show 1-(1/2:ℝ) = 1/2 by norm_num, ← smul_add, ← Complex.coe_smul]
    norm_num
  have hl : -Real.log (1/2:ℝ)=Real.log 2 := by rw [one_div,Real.log_inv,neg_neg]
  rw [hhalf,hl] at hr hs
  rw [add_comm σ ρ,show σ-ρ=-(ρ-σ) by abel,traceNorm_neg] at hs
  have hlog : 0<Real.log 2 :=
    D5.S3.ArithSums.TwoPointSlabSupport.log_widths_bounds.1
  apply (div_le_iff₀ (mul_pos (by norm_num) hlog)).mpr
  nlinarith

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
theorem binaryHolevoBound :
    ∀ (n : ℕ) (σ τ : Matrix (Fin n) (Fin n) ℂ),
      (σ.PosSemidef ∧ σ.trace = 1) → (τ.PosSemidef ∧ τ.trace = 1) →
      -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ((1/2 : ℂ) • (σ + τ)))).re -
        (-(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) σ)).re +
          -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) τ)).re) / 2 ≤
        traceNorm (σ-τ)/2 :=
  binaryHolevo_of_uniformPositive uniformPositiveHolevoBound

end D5.S3.Divergence.AudenaertBinaryHolevoBound
