/- GID: D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementCovariance
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A qutrit covariance inequality controls the Simpson score bound at standard product measurements. -/

import D5.S3.Quantum.Information.ComplementaryCorrelations.AnchorMeasurementMoments
import D5.S3.Quantum.Information.ComplementaryCorrelations.CovarianceToAnchor

/-! Weighted matrix covariance and the standard-basis ACC implication
from the raw diagonal/circulant certificate. -/

noncomputable section

namespace AnchorMeasurement

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator
open Omega.CovarianceToAnchor (LocalCovariance simpsonGap simpson_gap_nonneg)
open D5.S3.Quantum.FiniteDimensional (qubitZ qubitX)
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
  (bloch blochMatrix bloch_geometry_of_isHermitian)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (productState)
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)

section HilbertSchmidt

variable {n : Type*} [Fintype n]

private theorem hs_cauchy (A B : Mat n) :
    (Aᴴ * B).trace.re ^ 2 + (Aᴴ * B).trace.im ^ 2 ≤
      (Aᴴ * A).trace.re * (Bᴴ * B).trace.re := by
  classical
  let I : Mat n := 1
  have hI : I.PosSemidef := Matrix.PosSemidef.one
  let : SeminormedAddCommGroup (Mat n) := I.toMatrixSeminormedAddCommGroup hI
  let : InnerProductSpace ℂ (Mat n) := I.toMatrixInnerProductSpace hI
  have h (X Y : Mat n) : inner ℂ X Y = (Xᴴ * Y).trace := by
    change (Y * I * Xᴴ).trace = _
    rw [show I = 1 by rfl, Matrix.mul_one, Matrix.trace_mul_comm]
  have hc := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) A B) 2
  rw [h, mul_pow, norm_sq_eq_re_inner (𝕜 := ℂ) A, norm_sq_eq_re_inner (𝕜 := ℂ) B,
    h, h, Complex.sq_norm, Complex.normSq_apply] at hc
  simpa only [pow_two, RCLike.re_eq_complex_re] using hc

private theorem hs_nonneg (A : Mat n) : 0 ≤ (Aᴴ * A).trace.re :=
  (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self A).trace_nonneg).1

private theorem endpoint_pair {T B D : Mat n}
    (hT : T.IsHermitian) (hB : B.IsHermitian) :
    ((B * T)ᴴ * (D * T)).trace = (T * T * B * D).trace := by
  rw [Matrix.conjTranspose_mul, hT.eq, hB.eq,
    ← Matrix.mul_assoc, Matrix.trace_mul_cycle, ← Matrix.mul_assoc]

private theorem midpoint_pair {R T B D : Mat n} (hR : R.IsHermitian)
    (hR2 : R * R = T) (hB : B.IsHermitian) :
    ((R * B * R)ᴴ * (R * D * R)).trace = (T * B * T * D).trace := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hR.eq, hB.eq]
  calc
    _ = (R * (B * (R * R) * D) * R).trace := by simp only [Matrix.mul_assoc]
    _ = (T * B * T * D).trace := by
      rw [Matrix.trace_mul_cycle]
      simp only [hR2, Matrix.mul_assoc]

private theorem trace_swap {T B D : Mat n}
    (hT : T.IsHermitian) (hB : B.IsHermitian) (hD : D.IsHermitian) :
    (T * D * B).trace = star ((T * B * D).trace) := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    hT.eq, hB.eq, hD.eq, Matrix.trace_mul_cycle', Matrix.mul_assoc]

private theorem commutator_anticommutator {T B D : Mat n}
    (hT : T.IsHermitian) (hB : B.IsHermitian) (hD : D.IsHermitian) :
    let V := (T * T * B * B).trace.re
    let W := (T * T * D * D).trace.re
    let H := (T * B * T * B).trace.re
    let K := (T * D * T * D).trace.re
    let C := T * B - B * T
    let A := T * D + D * T
    (Cᴴ * C).trace.re = 2 * (V - H) ∧
    (Aᴴ * A).trace.re = 2 * (W + K) ∧
    (Cᴴ * A).trace.im = -2 * (T * T * B * D).trace.im := by
  have h₁ (U V : Mat n) : (U * T * T * V).trace = (T * T * V * U).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm U (T * T * V)
  have h₂ (U V : Mat n) : (U * T * V * T).trace = (T * U * T * V).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (U * T * V) T
  have h₃ (U V : Mat n) : (T * U * V * T).trace = (T * T * U * V).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (T * U * V) T
  have hT2 : (T * T).IsHermitian := by
    change (T * T)ᴴ = T * T
    rw [Matrix.conjTranspose_mul, hT.eq]
  have hswap := trace_swap hT2 hB hD
  dsimp only
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    hT.eq, hB.eq, hD.eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
    ← Matrix.mul_assoc, h₁, h₂, h₃, Matrix.trace_sub, Matrix.trace_add, Complex.sub_re,
    Complex.add_re, Complex.sub_im, Complex.add_im, hswap, Complex.star_def, Complex.conj_im]
  refine ⟨?_, ?_, ?_⟩ <;> ring

end HilbertSchmidt

/-- Actual weighted moments satisfy all three local covariance bounds.
The proof applies even to a singular positive semidefinite weight. -/
theorem localCovariance_of_matrix {n : Type*} [Fintype n] [DecidableEq n]
    (β B D : Mat n) (hβ : β.PosSemidef) (hB : B.IsHermitian) (hD : D.IsHermitian) :
    let T := CFC.sqrt β
    LocalCovariance (β * B * B).trace.re (β * D * D).trace.re
      (T * B * T * B).trace.re (T * D * T * D).trace.re
      (β * B * D).trace.re (β * B * D).trace.im (T * B * T * D).trace.re := by
  let T := CFC.sqrt β
  have hTpos : T.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg β)
  have hT := hTpos.isHermitian
  have hT2 : T * T = β := CFC.sqrt_mul_sqrt_self β hβ.nonneg
  let R := CFC.sqrt T
  have hR := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)).isHermitian
  have hR2 : R * R = T := CFC.sqrt_mul_sqrt_self T hTpos.nonneg
  have hEnd := hs_cauchy (B * T) (D * T)
  rw [endpoint_pair hT hB, endpoint_pair hT hB, endpoint_pair hT hD, hT2] at hEnd
  have hMid := hs_cauchy (R * B * R) (R * D * R)
  rw [midpoint_pair hR hR2 hB, midpoint_pair hR hR2 hB,
    midpoint_pair hR hR2 hD] at hMid
  have hH := hs_nonneg (R * B * R)
  have hK := hs_nonneg (R * D * R)
  rw [midpoint_pair hR hR2 hB] at hH
  rw [midpoint_pair hR hR2 hD] at hK
  have hComm (B D : Mat n) (hB : B.IsHermitian) (hD : D.IsHermitian) :
      ((T * B - B * T)ᴴ * (T * B - B * T)).trace.re =
        2 * ((β * B * B).trace.re - (T * B * T * B).trace.re) := by
    simpa only [hT2] using (commutator_anticommutator hT hB hD).1
  have hImag (B D : Mat n) (hB : B.IsHermitian) (hD : D.IsHermitian) :
      (β * B * D).trace.im ^ 2 ≤
        ((β * B * B).trace.re - (T * B * T * B).trace.re) *
        ((β * D * D).trace.re + (T * D * T * D).trace.re) := by
    obtain ⟨hm, hp, hi⟩ := commutator_anticommutator hT hB hD
    rw [hT2] at hm hp hi
    have h := hs_cauchy (T * B - B * T) (T * D + D * T)
    rw [hm, hp, hi] at h
    nlinarith only [h, sq_nonneg (((T * B - B * T)ᴴ * (T * D + D * T)).trace.re)]
  have hV := hs_nonneg (T * B - B * T)
  have hW := hs_nonneg (T * D - D * T)
  rw [hComm B D hB hD] at hV
  rw [hComm D B hD hB] at hW
  refine ⟨hH, by linarith only [hV], hK, by linarith only [hW],
    hEnd, ?_, hImag B D hB hD, ?_⟩
  · exact (le_add_of_nonneg_right (sq_nonneg _)).trans hMid
  · have h := hImag D B hD hB
    rw [trace_swap hβ.isHermitian hB hD, Complex.star_def, Complex.conj_im, neg_sq] at h
    exact h

/-- The trace-one raw matrix certificate before centering the two scores. -/
private def RawDiagonalCirculantCovariance : Prop :=
  ∀ (β : Mat Bob), β.PosSemidef → β.trace = 1 →
    ∀ (u v : Bob → ℂ), (diagonal u).IsHermitian → (circulant v).IsHermitian →
    let T := CFC.sqrt β
    let b := diagonal u
    let e := circulant v
    let p := (β * b).trace.re
    let q := (β * e).trace.re
    ((β * b * e).trace.re + (T * b * T * e).trace.re - 2 * p * q) ^ 2 +
        (9 / 4 : ℝ) * (β * b * e).trace.im ^ 2 ≤
      (3 * (β * b * b).trace.re - 2 * (T * b * T * b).trace.re - p ^ 2) *
      (3 * (β * e * e).trace.re - 2 * (T * e * T * e).trace.re - q ^ 2)

private theorem observable_one {n : Type*} [Fintype n] [DecidableEq n] (a : n → ℝ) :
    observable (1 : Matrix.unitaryGroup n ℂ) a = diagonal (fun i => (a i : ℂ)) := by
  simp [observable]

private theorem observable_scale {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (s : ℝ) (a : n → ℝ) :
    observable U (fun i => s * a i) = s • observable U a := by
  let F := Unitary.conjStarAlgAut ℂ (Mat n) U
  change F (diagonal (fun i => ((s * a i : ℝ) : ℂ))) = s • F _
  have hscale (M : Mat n) : F (s • M) = s • F M :=
    F.toAlgEquiv.toLinearEquiv.map_smul_of_tower s M
  rw [← hscale]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Complex.real_smul]
  · simp [Matrix.diagonal_apply_ne, hij]

private theorem center_observable_scale {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (β : Mat n) (s : ℝ) (a : n → ℝ)
    (ha : (∑ i, readout U β i * a i) = 0) :
    center β (observable U (fun i => s * a i)) = s • observable U a := by
  have hzero : (β * observable U a).trace.re = 0 := (trace_observable U β a).trans ha
  rw [observable_scale]
  simp [center, mul_smul_comm, Matrix.trace_smul, Complex.real_smul,
    Complex.mul_re, hzero]

/-- Apply the raw certificate to the actual computational and Fourier
observables, then center them using the trace-one moment identities. -/
private theorem physical_covariance_of_raw
    (hraw : RawDiagonalCirculantCovariance) (β : Mat Bob) (hβ : β.PosSemidef)
    (htr : β.trace = 1) (bQ bR : Bob → ℝ) :
    let T := CFC.sqrt β
    let B := center β (observable (1 : Matrix.unitaryGroup Bob ℂ) bQ)
    let D := center β (observable bobR bR)
    ((β * B * D).trace.re + (T * B * T * D).trace.re) ^ 2 +
        (7 / 4 : ℝ) * (β * B * D).trace.im ^ 2 ≤
      (3 * (β * B * B).trace.re - 2 * (T * B * T * B).trace.re) *
      (3 * (β * D * D).trace.re - 2 * (T * D * T * D).trace.re) := by
  have hb := observable_isHermitian (1 : Matrix.unitaryGroup Bob ℂ) bQ
  have he := observable_isHermitian bobR bR
  apply bob_covariance_of_raw_certificate β _ _ hβ htr hb he
  rw [observable_one bQ] at hb
  rw [bobR_observable_circulant bR] at he
  dsimp only
  rw [observable_one bQ, bobR_observable_circulant bR]
  exact hraw β hβ htr _ _ hb he

private theorem simpson_le_of_covariance
    (v : EuclideanSpace ℝ (Fin 3)) (β B D : Mat Bob)
    (hα : (blochMatrix 1 v).PosDef) (hβ : β.PosSemidef)
    (hB : B.IsHermitian) (hD : D.IsHermitian)
    (hL :
      let T := CFC.sqrt β
      ((β * B * D).trace.re + (T * B * T * D).trace.re) ^ 2 +
          (7 / 4 : ℝ) * (β * B * D).trace.im ^ 2 ≤
        (3 * (β * B * B).trace.re - 2 * (T * B * T * B).trace.re) *
        (3 * (β * D * D).trace.re - 2 * (T * D * T * D).trace.re)) :
    let α := blochMatrix 1 v
    let σ := α ⊗ₖ β
    let O := (qubitZ - v 2 • 1) ⊗ₖ B + (qubitX - v 0 • 1) ⊗ₖ D
    (σ * O * O).trace.re / 3 + 2 * (CFC.sqrt σ * O * CFC.sqrt σ * O).trace.re / 3 ≤
      (1 - (v 2) ^ 2) * (β * B * B).trace.re +
      (1 - (v 0) ^ 2) * (β * D * D).trace.re := by
  let r := 1 - (v 0) ^ 2 - (v 1) ^ 2 - (v 2) ^ 2
  let t := Real.sqrt r
  have ht : 0 < t := (bloch_sqrt v hα).1
  have hr : 0 ≤ r := (Real.sqrt_pos.mp ht).le
  have ht_sq : t ^ 2 = r := Real.sq_sqrt hr
  have ht1 : t ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    dsimp [r]
    nlinarith only [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have hBloch : (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = 1 - t ^ 2 := by
    rw [ht_sq]
    dsimp [r]
    ring
  have hgap := simpson_gap_nonneg (localCovariance_of_matrix β B D hβ hB hD) hL
    ht.le ht1 hBloch
  have hEq := simpson_gap_eq v β B D hα hβ hB hD
  dsimp only [simpsonGap] at hgap
  dsimp only at hEq ⊢
  linarith only [hgap, hEq]

private theorem variance_after_scale {A P : Mat Alice} {β b : Mat Bob} (s : ℝ)
    (k : ℝ) (hk : (A * P * P).trace.re = k) :
    (A * (s • P) * (s • P)).trace.re * (β * b * b).trace.re =
      k * (β * (s • b) * (s • b)).trace.re := by
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul, Matrix.trace_smul,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hk]
  ring

/-- Conditional standard-basis ACC for the exact BKM inverse and the two
measurement Fisher forms. The only certificate input is the raw 9/4 inequality. -/
theorem acc₂₃_of_raw_diagonal_circulant
    (hraw : RawDiagonalCirculantCovariance) : ACC₂₃ := by
  intro α β hα hβ Δ hΔ
  apply anchorQuadraticIn_nonneg_of_simpson 1 aliceR 1 bobR α β hα hβ _ hΔ
  intro aQ aR bQ bR haQ haR hbQ hbR
  let A := densityMatrix α
  let S := densityMatrix β
  let v := bloch A
  let sQ := (aQ 0 - aQ 1) / 2
  let sR := (aR 0 - aR 1) / 2
  let P := qubitZ - v 2 • 1
  let Q := qubitX - v 0 • 1
  let b := observable (1 : Matrix.unitaryGroup Bob ℂ) bQ
  let e := observable bobR bR
  have htrA : A.trace = 1 := α.2.2
  have htrS : S.trace = 1 := β.2.2
  have hA : A = blochMatrix 1 v := by
    simpa only [htrA, Complex.one_re] using (bloch_geometry_of_isHermitian A hα.isHermitian).1
  have hv : (blochMatrix 1 v).PosDef := by rwa [← hA]
  obtain ⟨hPauliQ, hPauliR⟩ := alice_centered_scores A htrA aQ aR haQ haR
  obtain ⟨hZ, hX⟩ := pauli_center v
  rw [hA, hZ] at hPauliQ
  rw [hA, hX] at hPauliR
  change observable (1 : Matrix.unitaryGroup Alice ℂ) aQ = sQ • P at hPauliQ
  change observable aliceR aR = sR • Q at hPauliR
  have hb : b.IsHermitian := observable_isHermitian _ _
  have he : e.IsHermitian := observable_isHermitian _ _
  have hL := physical_covariance_of_raw hraw S hβ.posSemidef htrS
    (fun j => sQ * bQ j) (fun j => sR * bR j)
  dsimp only at hL
  rw [center_observable_scale _ S sQ bQ hbQ, center_observable_scale _ S sR bR hbR] at hL
  have hGram := simpson_le_of_covariance v S (sQ • b) (sR • e) hv hβ.posSemidef
    (hb.smul (IsSelfAdjoint.all sQ)) (he.smul (IsSelfAdjoint.all sR)) hL
  obtain ⟨hZ2, hX2, _⟩ := pauli_endpoint v
  have hVarQ : (A * P * P).trace.re = 1 - (v 2) ^ 2 := by
    rw [hA]
    exact congrArg Complex.re hZ2
  have hVarR : (A * Q * Q).trace.re = 1 - (v 0) ^ 2 := by
    rw [hA]
    exact congrArg Complex.re hX2
  dsimp only
  rw [observable_square, observable_square, observable_square, observable_square,
    hPauliQ, hPauliR, Matrix.smul_kronecker, Matrix.smul_kronecker,
    ← Matrix.kronecker_smul, ← Matrix.kronecker_smul]
  change _ ≤ (A * ((sQ • P) * (sQ • P))).trace.re * (S * (b * b)).trace.re +
    (A * ((sR • Q) * (sR • Q))).trace.re * (S * (e * e)).trace.re
  rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc S, ← Matrix.mul_assoc A,
    ← Matrix.mul_assoc S, variance_after_scale sQ _ hVarQ, variance_after_scale sR _ hVarR]
  change ((A ⊗ₖ S) * _ * _).trace.re / 3 +
    2 * (CFC.sqrt (A ⊗ₖ S) * _ * CFC.sqrt (A ⊗ₖ S) * _).trace.re / 3 ≤ _
  rwa [hA]

end AnchorMeasurement
