/- GID: D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementMoments
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centered Pauli scores and qutrit observables give exact product second moments. -/

import D5.S3.Quantum.Information.ComplementaryCorrelations.AnchorMeasurementBKM
import D5.S3.Quantum.Information.ActualPureQubitGeometry
import D5.S3.Quantum.Matrix.Tensor.KroneckerSqrt

/-! Pauli moments and the bridge from the raw qutrit certificate to the
centered moments in the Simpson trace bound. -/

noncomputable section

namespace AnchorMeasurement

open Matrix
open D5.S3.Quantum.Matrix.Tensor.KroneckerSqrt (sqrt_kronecker)
open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (bloch blochMatrix
  blochMatrix_trace bloch_geometry_of_isHermitian)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow (trace_hermitian_product_real)

def center {n : Type*} [Fintype n] [DecidableEq n] (ρ A : Mat n) : Mat n :=
  A - (ρ * A).trace.re • 1

private abbrev Zc (z : ℝ) : Mat Alice := qubitZ - z • 1
private abbrev Xc (x : ℝ) : Mat Alice := qubitX - x • 1

private theorem observable_binary_affine (U : Matrix.unitaryGroup Alice ℂ)
    (a : Alice → ℝ) :
    observable U a = ((a 0 + a 1) / 2) • 1 +
      ((a 0 - a 1) / 2) • observable U (![1, -1] : Alice → ℝ) := by
  let F := Unitary.conjStarAlgAut ℂ (Mat Alice) U
  have hsmul (c : ℝ) (A : Mat Alice) : F (c • A) = c • F A :=
    F.toAlgEquiv.toLinearEquiv.map_smul_of_tower c A
  have hd : diagonal (fun i => (a i : ℂ)) =
      ((a 0 + a 1) / 2) • (1 : Mat Alice) +
        ((a 0 - a 1) / 2) • diagonal (fun i => ((![1, -1] : Alice → ℝ) i : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [Matrix.one_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring
  have h := congrArg F hd
  change F _ = F (_ + _) at h
  rw [map_add, hsmul, hsmul, map_one] at h
  exact h

private theorem observable_aliceQ_sign :
    observable (1 : Matrix.unitaryGroup Alice ℂ) (![1, -1] : Alice → ℝ) = qubitZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [observable, qubitZ]

private theorem observable_aliceR_sign :
    observable aliceR (![1, -1] : Alice → ℝ) = qubitX := by
  have hs : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  change D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard *
    diagonal (fun i => ((![1, -1] : Alice → ℝ) i : ℂ)) *
    D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamardᴴ = qubitX
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard,
      D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      qubitX, qubitZ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;>
    nlinarith only [hs]

private theorem observable_binary_centered (U : Matrix.unitaryGroup Alice ℂ)
    (ρ : Mat Alice) (hρ : ρ.trace = 1) (a : Alice → ℝ)
    (ha : (∑ i, readout U ρ i * a i) = 0) :
    observable U a =
      ((a 0 - a 1) / 2) • center ρ (observable U (![1, -1] : Alice → ℝ)) := by
  have h := trace_observable U ρ a
  rw [ha, observable_binary_affine U a] at h
  simp only [Matrix.mul_add, mul_smul_comm, Matrix.mul_one, Matrix.trace_add,
    Matrix.trace_smul, Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hρ, Complex.one_re, mul_one] at h
  rw [observable_binary_affine]
  unfold center
  rw [smul_sub, smul_smul]
  have hzero :
      (a 0 + a 1) / 2 = -((a 0 - a 1) / 2 *
        (ρ * observable U (![1, -1] : Alice → ℝ)).trace.re) := by linarith only [h]
  rw [hzero, neg_smul]
  abel

/-- Every actual centered Alice score is a real multiple of the corresponding
centered Pauli. The factor can be moved into Bob's test using smul_kronecker. -/
theorem alice_centered_scores (ρ : Mat Alice) (hρ : ρ.trace = 1)
    (aQ aR : Alice → ℝ)
    (hQ : (∑ i, readout (1 : Matrix.unitaryGroup Alice ℂ) ρ i * aQ i) = 0)
    (hR : (∑ i, readout aliceR ρ i * aR i) = 0) :
    observable (1 : Matrix.unitaryGroup Alice ℂ) aQ =
        ((aQ 0 - aQ 1) / 2) • center ρ qubitZ ∧
      observable aliceR aR = ((aR 0 - aR 1) / 2) • center ρ qubitX := by
  constructor
  · simpa only [observable_aliceQ_sign] using observable_binary_centered _ ρ hρ aQ hQ
  · simpa only [observable_aliceR_sign] using observable_binary_centered _ ρ hρ aR hR

/-- Endpoint products in the fixed Z then X order. The imaginary sign follows
from ZX = iY and the pinned Bloch convention. -/
theorem pauli_endpoint (v : EuclideanSpace ℝ (Fin 3)) :
    let α := blochMatrix 1 v
    (α * Zc (v 2) * Zc (v 2)).trace = ((1 - (v 2) ^ 2 : ℝ) : ℂ) ∧
    (α * Xc (v 0) * Xc (v 0)).trace = ((1 - (v 0) ^ 2 : ℝ) : ℂ) ∧
    (α * Zc (v 2) * Xc (v 0)).trace =
      ((-(v 0) * v 2 : ℝ) : ℂ) + Complex.I * (v 1 : ℂ) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩ <;> apply Complex.ext <;>
    simp [blochMatrix, Zc, Xc, qubitX, qubitZ, Matrix.trace, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.div_im, Complex.sub_re, Complex.sub_im, pow_two] <;> ring

theorem pauli_center (v : EuclideanSpace ℝ (Fin 3)) :
    center (blochMatrix 1 v) qubitZ = Zc (v 2) ∧
    center (blochMatrix 1 v) qubitX = Xc (v 0) := by
  have hz : (blochMatrix 1 v * qubitZ).trace.re = v 2 := by
    simp [blochMatrix, qubitZ, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.div_re]
    ring
  have hx : (blochMatrix 1 v * qubitX).trace.re = v 0 := by
    simp [blochMatrix, qubitX, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.div_re]
  simp [center, hz, hx]

private theorem bloch_det (v : EuclideanSpace ℝ (Fin 3)) :
    (blochMatrix 1 v).det.re = (1 - (v 0) ^ 2 - (v 1) ^ 2 - (v 2) ^ 2) / 4 := by
  rw [Matrix.det_fin_two]
  simp [blochMatrix, Complex.mul_re, Complex.div_re, Complex.div_im]
  ring

/-- Closed positive square root of the faithful trace-one qubit. -/
theorem bloch_sqrt (v : EuclideanSpace ℝ (Fin 3)) (hα : (blochMatrix 1 v).PosDef) :
    let t := Real.sqrt (1 - (v 0) ^ 2 - (v 1) ^ 2 - (v 2) ^ 2)
    0 < t ∧
      CFC.sqrt (blochMatrix 1 v) = (Real.sqrt (1 + t))⁻¹ • blochMatrix (1 + t) v := by
  let α := blochMatrix 1 v
  let r := 1 - (v 0) ^ 2 - (v 1) ^ 2 - (v 2) ^ 2
  let t := Real.sqrt r
  have hr : 0 < r := by
    have h := (Complex.pos_iff.mp hα.det_pos).1
    change 0 < (blochMatrix 1 v).det.re at h
    rw [bloch_det] at h
    dsimp [r]
    linarith
  have ht := Real.sqrt_pos.mpr hr
  have ht2 : t ^ 2 = r := Real.sq_sqrt hr.le
  have hs : (Real.sqrt (1 + t)) ^ 2 = 1 + t := Real.sq_sqrt (by positivity)
  have hs0 : 0 < Real.sqrt (1 + t) := by positivity
  let S := blochMatrix (1 + t) v
  have hS : S = α + (t / 2) • (1 : Mat Alice) := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [S, α, blochMatrix, Matrix.one_apply, Complex.div_re, Complex.div_im,
        Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring
  have hsq : S * S = (1 + t) • α := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [S, α, blochMatrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re,
        Complex.mul_im, Complex.div_re, Complex.div_im, Complex.real_smul] <;>
      (try ring) <;> (dsimp only [r] at ht2; nlinarith only [ht2])
  change 0 < t ∧ CFC.sqrt α = (Real.sqrt (1 + t))⁻¹ • S
  refine ⟨ht, CFC.sqrt_unique ?_ ?_⟩
  · rw [smul_mul_assoc, mul_smul_comm, hsq, smul_smul, smul_smul]
    have hscale : (Real.sqrt (1 + t))⁻¹ * (Real.sqrt (1 + t))⁻¹ * (1 + t) = 1 := by
      field_simp [hs0.ne']
      nlinarith only [hs]
    rw [hscale, one_smul]
  · rw [hS]
    exact smul_nonneg (by positivity) (add_nonneg hα.posSemidef.nonneg
      (smul_nonneg (by positivity) zero_le_one))

/-- Real polynomial expansion before dividing by the square-root normalization. -/
private theorem bloch_midpoint_raw (s : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    let S := blochMatrix s v
    let r := (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2
    let k := 1 - 2 * s + (s ^ 2 + r) / 2
    (S * Zc (v 2) * S * Zc (v 2)).trace = (((s ^ 2 - r) / 2 + k * (v 2) ^ 2 : ℝ) : ℂ) ∧
    (S * Xc (v 0) * S * Xc (v 0)).trace = (((s ^ 2 - r) / 2 + k * (v 0) ^ 2 : ℝ) : ℂ) ∧
    (S * Zc (v 2) * S * Xc (v 0)).trace = ((k * v 0 * v 2 : ℝ) : ℂ) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩ <;> apply Complex.ext <;>
    simp [blochMatrix, Zc, Xc, qubitX, qubitZ, Matrix.trace, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.real_smul, pow_two] <;> ring

/-- The three midpoint coefficients used in Simpson Pro equation (4). -/
theorem pauli_midpoint (v : EuclideanSpace ℝ (Fin 3)) (hα : (blochMatrix 1 v).PosDef) :
    let t := Real.sqrt (1 - (v 0) ^ 2 - (v 1) ^ 2 - (v 2) ^ 2)
    let S := CFC.sqrt (blochMatrix 1 v)
    (S * Zc (v 2) * S * Zc (v 2)).trace =
      ((t * (1 - (v 2) ^ 2 / (1 + t)) : ℝ) : ℂ) ∧
    (S * Xc (v 0) * S * Xc (v 0)).trace =
      ((t * (1 - (v 0) ^ 2 / (1 + t)) : ℝ) : ℂ) ∧
    (S * Zc (v 2) * S * Xc (v 0)).trace =
      ((-(t / (1 + t) * v 0 * v 2) : ℝ) : ℂ) := by
  let r := (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2
  let t := Real.sqrt (1 - (v 0) ^ 2 - (v 1) ^ 2 - (v 2) ^ 2)
  obtain ⟨ht, hroot⟩ := bloch_sqrt v hα
  change 0 < t at ht
  change CFC.sqrt (blochMatrix 1 v) =
    (Real.sqrt (1 + t))⁻¹ • blochMatrix (1 + t) v at hroot
  have hnonneg : 0 ≤ 1 - (v 0) ^ 2 - (v 1) ^ 2 - (v 2) ^ 2 :=
    Real.sqrt_pos.mp ht |>.le
  have ht2 : t ^ 2 = 1 - r := by
    dsimp [t, r]
    rw [Real.sq_sqrt hnonneg]
    ring
  have hsum : ((1 + t) ^ 2 - r) / 2 = t * (1 + t) := by nlinarith only [ht2]
  have hcoef : 1 - 2 * (1 + t) + ((1 + t) ^ 2 + r) / 2 = -t := by nlinarith only [ht2]
  have hscale : (Real.sqrt (1 + t))⁻¹ * (Real.sqrt (1 + t))⁻¹ = (1 + t)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  obtain ⟨hZ, hX, hZX⟩ := bloch_midpoint_raw (1 + t) v
  let S := CFC.sqrt (blochMatrix 1 v)
  change (S * Zc (v 2) * S * Zc (v 2)).trace =
      ((t * (1 - (v 2) ^ 2 / (1 + t)) : ℝ) : ℂ) ∧
    (S * Xc (v 0) * S * Xc (v 0)).trace =
      ((t * (1 - (v 0) ^ 2 / (1 + t)) : ℝ) : ℂ) ∧
    (S * Zc (v 2) * S * Xc (v 0)).trace =
      ((-(t / (1 + t) * v 0 * v 2) : ℝ) : ℂ)
  dsimp only [S]
  rw [hroot]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hscale, Matrix.trace_smul]
  rw [hZ, hX, hZX]
  simp only [show (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = r by rfl, hsum, hcoef,
    Complex.real_smul, ← Complex.ofReal_mul]
  refine ⟨?_, ?_, ?_⟩ <;> apply congrArg Complex.ofReal <;>
    field_simp [show 1 + t ≠ 0 by positivity] <;> ring

section Tensor

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

private theorem trace_product_two_slot (A P Q : Mat a) (B C D : Mat b) :
    let O := P ⊗ₖ C + Q ⊗ₖ D
    ((A ⊗ₖ B) * O * O).trace =
      (A * P * P).trace * (B * C * C).trace +
      (A * P * Q).trace * (B * C * D).trace +
      (A * Q * P).trace * (B * D * C).trace +
      (A * Q * Q).trace * (B * D * D).trace := by
  simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_kronecker_mul,
    Matrix.trace_add, Matrix.trace_kronecker]
  ring

private theorem trace_midpoint_two_slot (A P Q : Mat a) (B C D : Mat b) :
    let O := P ⊗ₖ C + Q ⊗ₖ D
    ((A ⊗ₖ B) * O * (A ⊗ₖ B) * O).trace =
      (A * P * A * P).trace * (B * C * B * C).trace +
      (A * P * A * Q).trace * (B * C * B * D).trace +
      (A * Q * A * P).trace * (B * D * B * C).trace +
      (A * Q * A * Q).trace * (B * D * B * D).trace := by
  simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_kronecker_mul,
    Matrix.trace_add, Matrix.trace_kronecker]
  ring

private theorem trace_endpoint_swap {n : Type*} [Fintype n] [DecidableEq n]
    {ρ B D : Mat n} (hρ : ρ.IsHermitian) (hB : B.IsHermitian) (hD : D.IsHermitian) :
    (ρ * D * B).trace = star ((ρ * B * D).trace) := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    hρ.eq, hB.eq, hD.eq, Matrix.trace_mul_cycle', Matrix.mul_assoc]

private theorem trace_midpoint_swap {n : Type*} [Fintype n] [DecidableEq n]
    (S B D : Mat n) : (S * D * S * B).trace = (S * B * S * D).trace := by
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (S * D) (S * B)

end Tensor

/-- Equation (4) for the actual tensor observable and positive square roots. -/
theorem simpson_gap_eq (v : EuclideanSpace ℝ (Fin 3)) (β B D : Mat Bob)
    (hα : (blochMatrix 1 v).PosDef) (hβ : β.PosSemidef)
    (hB : B.IsHermitian) (hD : D.IsHermitian) :
    let x := v 0
    let y := v 1
    let z := v 2
    let t := Real.sqrt (1 - x ^ 2 - y ^ 2 - z ^ 2)
    let α := blochMatrix 1 v
    let T := CFC.sqrt β
    let σ := α ⊗ₖ β
    let O := Zc z ⊗ₖ B + Xc x ⊗ₖ D
    let V := (β * B * B).trace.re
    let W := (β * D * D).trace.re
    let H := (T * B * T * B).trace.re
    let K := (T * D * T * D).trace.re
    let c := (β * B * D).trace.re
    let d := (β * B * D).trace.im
    let m := (T * B * T * D).trace.re
    (3 / 2 : ℝ) * ((1 - z ^ 2) * V + (1 - x ^ 2) * W -
      (σ * O * O).trace.re / 3 - 2 * (CFC.sqrt σ * O * CFC.sqrt σ * O).trace.re / 3) =
        (1 - z ^ 2) * V + (1 - x ^ 2) * W -
        t * (1 - z ^ 2 / (1 + t)) * H - t * (1 - x ^ 2 / (1 + t)) * K +
        x * z * (c + 2 * (t / (1 + t)) * m) + y * d := by
  have hZc : (Zc (v 2)).IsHermitian := by
    apply (show qubitZ.IsHermitian from D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.2.1).sub
    exact (Matrix.isHermitian_one : (1 : Mat Alice).IsHermitian).smul (IsSelfAdjoint.all (v 2))
  have hXc : (Xc (v 0)).IsHermitian := by
    apply (show qubitX.IsHermitian from D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.1).sub
    exact (Matrix.isHermitian_one : (1 : Mat Alice).IsHermitian).smul (IsSelfAdjoint.all (v 0))
  obtain ⟨hZ, hX, hZX⟩ := pauli_endpoint v
  obtain ⟨hZS, hXS, hZXS⟩ := pauli_midpoint v hα
  dsimp only
  rw [sqrt_kronecker _ _ hα.posSemidef hβ,
    trace_product_two_slot, trace_midpoint_two_slot,
    trace_endpoint_swap hα.isHermitian hZc hXc, trace_endpoint_swap hβ.isHermitian hB hD,
    trace_midpoint_swap (CFC.sqrt (blochMatrix 1 v)) (Zc (v 2)) (Xc (v 0)),
    trace_midpoint_swap (CFC.sqrt β) B D, hZ, hX, hZX, hZS, hXS, hZXS]
  simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im, zero_mul, mul_zero,
    one_mul, mul_one, zero_add, add_zero, sub_zero, sub_self] <;> ring

section BobMoments

private theorem trace_endpoint_shift (β b e : Mat Bob) (p q : ℝ) :
    (β * (b - p • 1) * (e - q • 1)).trace =
      (β * b * e).trace - q • (β * b).trace - p • (β * e).trace +
        (p * q) • β.trace := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, mul_smul_comm, smul_mul_assoc, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_smul, smul_sub, smul_smul]
  rw [mul_comm p q]
  abel

private theorem trace_midpoint_shift (T b e : Mat Bob) (p q : ℝ) :
    (T * (b - p • 1) * T * (e - q • 1)).trace =
      (T * b * T * e).trace - q • (T * T * b).trace - p • (T * T * e).trace +
        (p * q) • (T * T).trace := by
  have h : (T * b * T).trace = (T * T * b).trace := Matrix.trace_mul_cycle T b T
  simp only [Matrix.mul_sub, Matrix.sub_mul, mul_smul_comm, smul_mul_assoc, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_smul, h, smul_sub, smul_smul]
  rw [mul_comm p q]
  abel

/-- At a density anchor n = Tr(T²) = 1. These are all seven normalizations
used to restrict the raw polynomial certificate to the physical square root. -/
theorem bob_centered_moments (β b e : Mat Bob)
    (hβ : β.PosSemidef) (htr : β.trace = 1)
    (hb : b.IsHermitian) (he : e.IsHermitian) :
    let T := CFC.sqrt β
    let p := (β * b).trace.re
    let q := (β * e).trace.re
    let B := center β b
    let D := center β e
    (β * B * B).trace.re = (β * b * b).trace.re - p ^ 2 ∧
    (β * D * D).trace.re = (β * e * e).trace.re - q ^ 2 ∧
    (T * B * T * B).trace.re = (T * b * T * b).trace.re - p ^ 2 ∧
    (T * D * T * D).trace.re = (T * e * T * e).trace.re - q ^ 2 ∧
    (β * B * D).trace.re = (β * b * e).trace.re - p * q ∧
    (β * B * D).trace.im = (β * b * e).trace.im ∧
    (T * B * T * D).trace.re = (T * b * T * e).trace.re - p * q := by
  have hT : CFC.sqrt β * CFC.sqrt β = β := CFC.sqrt_mul_sqrt_self β hβ.nonneg
  have hbIm := trace_hermitian_product_real β b hβ.isHermitian hb
  have heIm := trace_hermitian_product_real β e hβ.isHermitian he
  dsimp only
  simp only [center, trace_endpoint_shift, trace_midpoint_shift, hT, htr,
    Complex.real_smul, Complex.mul_re, Complex.sub_re, Complex.add_re, zero_mul, sub_zero,
    Complex.one_re, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_im, hbIm, heIm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- The coefficient 9/4 from the covariance certificate gives the 7/4
inequality used by the analytic reduction. The premise is the raw certificate
specialized at T = sqrt β and Tr(T²) = 1. -/
theorem bob_covariance_of_raw_certificate (β b e : Mat Bob)
    (hβ : β.PosSemidef) (htr : β.trace = 1)
    (hb : b.IsHermitian) (he : e.IsHermitian)
    (hcert :
      let T := CFC.sqrt β
      let p := (β * b).trace.re
      let q := (β * e).trace.re
      ((β * b * e).trace.re + (T * b * T * e).trace.re - 2 * p * q) ^ 2 +
          (9 / 4 : ℝ) * (β * b * e).trace.im ^ 2 ≤
        (3 * (β * b * b).trace.re - 2 * (T * b * T * b).trace.re - p ^ 2) *
        (3 * (β * e * e).trace.re - 2 * (T * e * T * e).trace.re - q ^ 2)) :
    let T := CFC.sqrt β
    let B := center β b
    let D := center β e
    ((β * B * D).trace.re + (T * B * T * D).trace.re) ^ 2 +
        (7 / 4 : ℝ) * (β * B * D).trace.im ^ 2 ≤
      (3 * (β * B * B).trace.re - 2 * (T * B * T * B).trace.re) *
      (3 * (β * D * D).trace.re - 2 * (T * D * T * D).trace.re) := by
  obtain ⟨hV, hW, hH, hK, hc, hd, hm⟩ := bob_centered_moments β b e hβ htr hb he
  dsimp only at hcert ⊢
  rw [hV, hW, hH, hK, hc, hd, hm]
  have him := sq_nonneg (β * b * e).trace.im
  linarith only [hcert, him]

end BobMoments

/-- The actual R observable is circulant in the computational basis.
Its Fourier phase follows the sign convention of the pinned transform. -/
theorem bobR_observable_circulant (a : Bob → ℝ) :
    observable bobR a = Matrix.circulant (fun h : Bob =>
      ∑ k : Bob, ((a k : ℂ) * ZMod.stdAddChar (-(h * k))) / 3) := by
  let W := D5.S3.Quantum.Dynamics.PolygonalFourierCouplings.transform 3
  have hs : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hs0 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 3)
  change W * diagonal (fun i => (a i : ℂ)) * Wᴴ = _
  ext i j
  rw [Matrix.circulant_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  change (ZMod.stdAddChar (-(i * k)) / (Real.sqrt 3 : ℂ) * (a k : ℂ)) *
    star (ZMod.stdAddChar (-(j * k)) / (Real.sqrt 3 : ℂ)) = _
  rw [star_div₀, Complex.star_def, Complex.conj_ofReal, ← AddChar.map_neg_eq_conj, neg_neg]
  have hphase : -(i * k) + j * k = -((i - j) * k) := by ring
  rw [← hphase, AddChar.map_add_eq_mul]
  have hden : (3 : ℂ) = (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) := hs.symm
  rw [hden]
  field_simp [hs0]

/-!
The remaining certificate adapter subtracts the ordinary scalar mean of each
Bob test, matches its coefficients with the Weyl coordinates, and invokes the
certificate and the scalar Bernstein implication. For the all-bases theorem,
transport the local MUB pairs through diagonal phases and permutations.
In the qutrit case dephasing gives 1+u+v=0 and |u|=|v|=1, so re(u)=−1/2 and
v=conj(u), then orthogonality fixes the order.
-/

end AnchorMeasurement
