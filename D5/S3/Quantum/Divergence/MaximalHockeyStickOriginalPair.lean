/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickOriginalPair
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickOriginalPair
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: Original singular-pair hockey overlap classification on the actual common corner. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickSingularCriterion
import D5.S3.Quantum.Divergence.MaximalHockeyStickProfile

/-! The trace optimizer criterion is transported back to the original PSD pair. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport
open D5.S3.Quantum.Lieb.SupportPerspectiveTransformer
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
open D5.S3.Quantum.Divergence.MaximalHockeyStickProfile
open D5.S3.Quantum.Divergence.MaximalHockeyStickSupport
open D5.S3.Quantum.Divergence.MaximalHockeyStickCorner
open D5.S3.Quantum.Divergence.MaximalHockeyStickCornerWeight
open D5.S3.Quantum.Divergence.MaximalHockeyStickSingularCriterion
open D5.S3.Quantum.Divergence.MaximalHockeyStickThreshold
open D5.S3.Quantum.Divergence.MaximalHockeyStickSpectral

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickOriginalPair

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem normalized_contraction (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : normalize (A + B) A ≤ 1 := by
  obtain ⟨hC, hD, hsum⟩ := normalized_pair A B hA hB
  have hQ : spectralSupport (A + B) ≤ 1 := by
    rw [spectralSupport, ← cfc_const 1 (A + B) (hA.add hB).isHermitian.isSelfAdjoint]
    exact cfc_mono (fun x _ => by split_ifs <;> norm_num)
      ((A + B).finite_real_spectrum.continuousOn _)
      ((A + B).finite_real_spectrum.continuousOn _)
  calc
    normalize (A + B) A ≤ normalize (A + B) A + normalize (A + B) B :=
      le_add_of_nonneg_right hD.nonneg
    _ = spectralSupport (A + B) := hsum
    _ ≤ 1 := hQ

private theorem reconstruction_pair (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    reconstruct (A + B) (normalize (A + B) A) = A ∧
      reconstruct (A + B) (1 - normalize (A + B) A) = B := by
  obtain ⟨hPA, hAP, -, -⟩ := pair_supported A B hA hB
  have hrecA := reconstruct_normalize (A + B) A (hA.add hB) hPA hAP
  refine ⟨hrecA, ?_⟩
  simp only [reconstruct, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    CFC.sqrt_mul_sqrt_self (A + B) (hA.add hB).nonneg]
  change A + B - reconstruct (A + B) (normalize (A + B) A) = B
  rw [hrecA]
  abel

private theorem reconstruct_feasible (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (t : ℝ) (Y : Matrix n n ℂ)
    (hY : Y ∈ positiveOverlaps (normalize (A + B) A)
      (t • (1 - normalize (A + B) A))) :
    reconstruct (A + B) Y ∈ positiveOverlaps A (t • B) := by
  obtain ⟨hrecA, hrecB⟩ := reconstruction_pair A B hA hB
  have hroot : (CFC.sqrt (A + B)).IsHermitian :=
    (CFC.sqrt_nonneg (A + B)).posSemidef.isHermitian
  have hmono {U V : Matrix n n ℂ} (h : U ≤ V) :
      reconstruct (A + B) U ≤ reconstruct (A + B) V := by
    apply Matrix.le_iff.mpr
    simpa only [reconstruct, Matrix.mul_sub, Matrix.sub_mul, hroot.eq] using
      (Matrix.le_iff.mp h).conjTranspose_mul_mul_same (CFC.sqrt (A + B))
  refine ⟨?_, (hmono hY.2.1).trans_eq hrecA, ?_⟩
  · simpa only [reconstruct, hroot.eq] using
      (hY.1.posSemidef.conjTranspose_mul_mul_same (CFC.sqrt (A + B))).nonneg
  · have hh := hmono hY.2.2
    have hs (Z : Matrix n n ℂ) : reconstruct (A + B) (t • Z) =
        t • reconstruct (A + B) Z := by
      simp only [reconstruct, Matrix.mul_smul, Matrix.smul_mul]
    simpa only [hs, hrecB] using hh

private theorem normalize_feasible (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (t : ℝ) (ht : 0 ≤ t)
    (X : Matrix n n ℂ) (hX : X ∈ positiveOverlaps A (t • B)) :
    normalize (A + B) X ∈ positiveOverlaps (normalize (A + B) A)
      (t • (1 - normalize (A + B) A)) := by
  have hx := ((overlap_bijection A B hA hB t).1 X hX).1
  obtain ⟨-, -, hsum⟩ := normalized_pair A B hA hB
  have hQ : spectralSupport (A + B) ≤ 1 := by
    rw [spectralSupport, ← cfc_const 1 (A + B) (hA.add hB).isHermitian.isSelfAdjoint]
    exact cfc_mono (fun x _ => by split_ifs <;> norm_num)
      ((A + B).finite_real_spectrum.continuousOn _)
      ((A + B).finite_real_spectrum.continuousOn _)
  have hb : normalize (A + B) B ≤ 1 - normalize (A + B) A := by
    have hh : normalize (A + B) A + normalize (A + B) B ≤ 1 := hsum.trans_le hQ
    exact (le_sub_iff_add_le').mpr hh
  exact ⟨hx.1, hx.2.1, hx.2.2.trans (smul_le_smul_of_nonneg_left hb ht)⟩

/-- Equality of the original overlap objective with the normalized canonical
one is equivalent to actual weighted optimality after normalization. -/
theorem original_optimal_iff_normalized (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (t : ℝ) (ht : 0 ≤ t) :
    let S := A + B
    let C := normalize S A
    (∀ X ∈ positiveOverlaps A (t • B),
      X.trace.re ≤ (S * canonicalOverlap C t).trace.re) ↔
      (∀ Y ∈ positiveOverlaps C (t • (1 - C)),
        (S * Y).trace.re ≤ (S * canonicalOverlap C t).trace.re) := by
  dsimp only
  constructor
  · intro h Y hY
    have hh := h _ (reconstruct_feasible A B hA hB t Y hY)
    simpa only [reconstruction_trace (A + B) Y (hA.add hB)] using hh
  · intro h X hX
    have hh := h _ (normalize_feasible A B hA hB t ht X hX)
    have hrec := ((overlap_bijection A B hA hB t).1 X hX).2
    have htrace := reconstruction_trace (A + B) (normalize (A + B) X) (hA.add hB)
    rw [hrec] at htrace
    simpa only [← htrace] using hh

/-- The canonical scalar minimum gives an actual feasible overlap after
reconstruction to the original singular pair. -/
theorem original_canonical_feasible (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (t : ℝ) (ht : 0 ≤ t) :
    reconstruct (A + B) (canonicalOverlap (normalize (A + B) A) t) ∈
      positiveOverlaps A (t • B) := by
  apply reconstruct_feasible A B hA hB t
  exact canonical_feasible _ (normalized_pair A B hA hB).1
    (normalized_contraction A B hA hB) t ht

/-- Every positive threshold of the original singular PSD pair has its actual
overlap supremum at the canonical point exactly when the original total mass
commutes with the normalized pair inside their common interior corner.
No optimizer, commutation, or faithfulness premise is assumed. -/
theorem original_all_thresholds_iff_commute (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    let S := A + B
    let C := normalize S A
    let P := interiorProjection C
    (∀ t : ℝ, 0 < t → maximalHockey A B t =
      A.trace.re - (S * canonicalOverlap C t).trace.re) ↔
      (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P) := by
  dsimp only
  let C := normalize (A + B) A
  have hC : C.PosSemidef := (normalized_pair A B hA hB).1
  have hC1 : C ≤ 1 := normalized_contraction A B hA hB
  have hweight := original_pair_weight_posDef A B hA hB
  have hcrit := common_all_thresholds_iff_commute C (A + B) hC hC1
    (hA.add hB).isHermitian hweight
  dsimp only at hcrit
  rw [← hcrit]
  apply forall_congr'
  intro t
  apply imp_congr_right
  intro ht
  have hnorm := original_optimal_iff_normalized A B hA hB t ht.le
  dsimp only at hnorm
  rw [← hnorm]
  have hfeas := original_canonical_feasible A B hA hB t ht.le
  have hlow := feasible_le_value hfeas
  rw [reconstruction_trace (A + B) (canonicalOverlap C t) (hA.add hB)] at hlow
  constructor
  · intro he X hX
    have hh := feasible_le_value hX
    dsimp only [maximalHockey] at he
    dsimp only [C] at hh ⊢
    linarith
  · intro h
    obtain ⟨X, hX, hx⟩ := overlap_attained A (t • B) hA (hB.smul ht.le)
    have hh := h X hX
    rw [hx] at hh
    have he := le_antisymm hh hlow
    dsimp only [maximalHockey]
    rw [he]

end D5.S3.Quantum.Divergence.MaximalHockeyStickOriginalPair
