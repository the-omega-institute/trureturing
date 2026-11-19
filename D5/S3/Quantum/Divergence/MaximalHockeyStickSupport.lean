/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickSupport
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: Actual singular-pair support normalization and positive-overlap bijection. -/

import D5.S3.Quantum.Lieb.SupportPerspectiveTransformer
import D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap

/-! Congruence by the existing spectral inverse square root removes the joint kernel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport
open D5.S3.Quantum.Lieb.SupportPerspectiveTransformer
open D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickSupport

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Normalization uses the existing zero-on-kernel inverse square root. -/
def normalize (S X : Matrix n n ℂ) : Matrix n n ℂ :=
  spectralInverseSqrt S * X * spectralInverseSqrt S

/-- The inverse congruence, defined even when the total weight is singular. -/
def reconstruct (S Y : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt S * Y * CFC.sqrt S

private theorem congruence_pos (K X : Matrix n n ℂ) (hK : K.IsHermitian)
    (hX : X.PosSemidef) : (K * X * K).PosSemidef := by
  simpa only [hK.eq] using hX.conjTranspose_mul_mul_same K

private theorem congruence_le (K : Matrix n n ℂ) (hK : K.IsHermitian)
    {X Y : Matrix n n ℂ} (h : X ≤ Y) : K * X * K ≤ K * Y * K := by
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub, Matrix.sub_mul, hK.eq] using
    (Matrix.le_iff.mp h).conjTranspose_mul_mul_same K

/-- Both original matrices are supported on the actual support of their sum. -/
theorem pair_supported (A B : Matrix n n ℂ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    let P := spectralSupport (A + B)
    P * A = A ∧ A * P = A ∧ P * B = B ∧ B * P = B := by
  dsimp only
  have hS : (A + B).PosSemidef := hA.add hB
  obtain ⟨-, -, hP, -, -, -, hPS, -⟩ := spectral_sqrt_normalization (A + B) hS
  obtain ⟨hPA, hAP⟩ := support_of_nonneg_le_smul (A + B) A
    (spectralSupport (A + B)) hP hPS hA 1 (by simpa only [one_smul] using (show A ≤ A + B from le_add_of_nonneg_right hB.nonneg))
  obtain ⟨hPB, hBP⟩ := support_of_nonneg_le_smul (A + B) B
    (spectralSupport (A + B)) hP hPS hB 1 (by simpa only [one_smul] using (show B ≤ A + B from le_add_of_nonneg_left hA.nonneg))
  exact ⟨hPA, hAP, hPB, hBP⟩

/-- The normalized positive pair sums to its support projection. -/
theorem normalized_pair (A B : Matrix n n ℂ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    (normalize (A + B) A).PosSemidef ∧ (normalize (A + B) B).PosSemidef ∧
      normalize (A + B) A + normalize (A + B) B = spectralSupport (A + B) := by
  have hS := hA.add hB
  obtain ⟨-, hK, -, -, -, -, -, hnorm⟩ := spectral_sqrt_normalization (A + B) hS
  refine ⟨congruence_pos _ _ hK hA, congruence_pos _ _ hK hB, ?_⟩
  simpa only [normalize, Matrix.mul_add, Matrix.add_mul] using hnorm

theorem reconstruct_normalize (S X : Matrix n n ℂ) (hS : S.PosSemidef)
    (hPX : spectralSupport S * X = X) (hXP : X * spectralSupport S = X) :
    reconstruct S (normalize S X) = X := by
  obtain ⟨hRK, hKR, -, -⟩ := spectral_sqrt_inverse_products S hS
  simp only [reconstruct, normalize, ← Matrix.mul_assoc, hRK]
  rw [hPX, Matrix.mul_assoc, hKR, hXP]

private theorem normalize_reconstruct (S Y : Matrix n n ℂ) (hS : S.PosSemidef)
    (hPY : spectralSupport S * Y = Y) (hYP : Y * spectralSupport S = Y) :
    normalize S (reconstruct S Y) = Y := by
  obtain ⟨hRK, hKR, -, -⟩ := spectral_sqrt_inverse_products S hS
  simp only [reconstruct, normalize, ← Matrix.mul_assoc, hKR]
  rw [hPY, Matrix.mul_assoc, hRK, hYP]

/-- Actual PSD overlap sets are in bijection under support normalization.
No faithfulness or orthogonality of the original supports is required. -/
theorem overlap_bijection (A B : Matrix n n ℂ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) (t : ℝ) :
    (∀ X ∈ positiveOverlaps A (t • B),
      normalize (A + B) X ∈ positiveOverlaps (normalize (A + B) A)
        (t • normalize (A + B) B) ∧ reconstruct (A + B) (normalize (A + B) X) = X) ∧
    (∀ Y ∈ positiveOverlaps (normalize (A + B) A) (t • normalize (A + B) B),
      reconstruct (A + B) Y ∈ positiveOverlaps A (t • B) ∧
        normalize (A + B) (reconstruct (A + B) Y) = Y) := by
  have hS := hA.add hB
  obtain ⟨hR, hK, hP, -, -, -, hPS, -⟩ := spectral_sqrt_normalization (A + B) hS
  obtain ⟨hPA, hAP, hPB, hBP⟩ := pair_supported A B hA hB
  have hRA := reconstruct_normalize (A + B) A hS hPA hAP
  have hRB := reconstruct_normalize (A + B) B hS hPB hBP
  have hrsmul (r : ℝ) (Z : Matrix n n ℂ) :
      reconstruct (A + B) (r • Z) = r • reconstruct (A + B) Z := by
    simp only [reconstruct, Matrix.mul_smul, Matrix.smul_mul]
  constructor
  · intro X hX
    have hXS : X ≤ A + B := hX.2.1.trans (le_add_of_nonneg_right hB.nonneg)
    obtain ⟨hPX, hXP⟩ := support_of_nonneg_le_smul (A + B) X
      (spectralSupport (A + B)) hP hPS hX.1.posSemidef 1 (by simpa using hXS)
    refine ⟨⟨(congruence_pos _ _ hK hX.1.posSemidef).nonneg,
      congruence_le _ hK hX.2.1, ?_⟩, reconstruct_normalize _ _ hS hPX hXP⟩
    simpa only [normalize, Matrix.mul_smul, Matrix.smul_mul] using
      congruence_le _ hK hX.2.2
  · intro Y hY
    obtain ⟨-, -, hPK, -⟩ := spectral_sqrt_inverse_products (A + B) hS
    have hPC : spectralSupport (A + B) * normalize (A + B) A = normalize (A + B) A := by
      simp only [normalize, ← Matrix.mul_assoc, hPK]
    obtain ⟨hPY, hYP⟩ := support_of_nonneg_le_smul (normalize (A + B) A) Y
      (spectralSupport (A + B)) hP hPC hY.1.posSemidef 1 (by simpa using hY.2.1)
    refine ⟨⟨(congruence_pos _ _ hR hY.1.posSemidef).nonneg, ?_, ?_⟩,
      normalize_reconstruct _ _ hS hPY hYP⟩
    · have h := congruence_le _ hR hY.2.1
      change reconstruct (A + B) Y ≤ reconstruct (A + B) (normalize (A + B) A) at h
      simpa only [hRA] using h
    · have h := congruence_le _ hR hY.2.2
      change reconstruct (A + B) Y ≤ reconstruct (A + B) (t • normalize (A + B) B) at h
      simpa only [hrsmul, hRB] using h

/-- The original trace objective becomes the actual total-mass trace weight. -/
theorem reconstruction_trace (S Y : Matrix n n ℂ) (hS : S.PosSemidef) :
    (reconstruct S Y).trace = (S * Y).trace := by
  rw [reconstruct, Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self S hS.nonneg]

end D5.S3.Quantum.Divergence.MaximalHockeyStickSupport
