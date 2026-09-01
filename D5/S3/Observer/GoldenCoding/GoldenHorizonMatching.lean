/- GID: D5/S3/Observer/GoldenCoding/GoldenHorizonMatching
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/GoldenHorizonMatching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Rank-one horizon channel laws make seven golden matching conditions equivalent. -/

import Mathlib

/- Library-search audit trail (2026-09-01):
   * The target atom has no absorbed-ledger coverage or formalization receipt.
     Repository searches for golden horizon matching, sampling ratios,
     observer events, and the seven displayed quantities found no equivalent
     theorem. The neighboring effective-index and Bogoliubov modules establish
     different statements and do not imply this equivalence.
   * All seven existing modules in `Observer/GoldenCoding` and the bound
     same-section neighbor `Weil/Pick/HorizonEffectiveIndex` were inspected.
     No content-level generalization of the target statement was found.
   * Pinned Mathlib supplies `Real.goldenRatio_sq`, positivity of the golden
     ratio, `Real.sq_sqrt`, `Real.log_pow`, `Real.log_injOn_pos`, and
     `List.TFAE`; these are reused directly. Three full-shape searches and a
     search of installed non-Mathlib packages found no packaged seven-way
     equivalence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.GoldenCoding.GoldenHorizonMatching

/-- The positive sampling ratio singled out by golden horizon matching. -/
noncomputable def goldenHorizonRatio : ℝ :=
  Real.sqrt (Real.goldenRatio⁻¹)

private theorem golden_inverse_split :
    (Real.goldenRatio ^ 2)⁻¹ + Real.goldenRatio⁻¹ = 1 := by
  have hInv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
    rw [Real.inv_goldenRatio]
    linarith [Real.one_sub_goldenRatio]
  rw [← inv_pow, hInv]
  nlinarith only [Real.goldenRatio_sq]

private theorem golden_horizon_ratio_sq :
    goldenHorizonRatio ^ 2 = Real.goldenRatio⁻¹ := by
  exact Real.sq_sqrt (inv_nonneg.mpr Real.goldenRatio_pos.le)

private theorem golden_horizon_ratio_pos : 0 < goldenHorizonRatio := by
  exact Real.sqrt_pos.2 (inv_pos.mpr Real.goldenRatio_pos)

private theorem golden_horizon_index_identity :
    Real.goldenRatio ^ 2 = (1 - goldenHorizonRatio ^ 2)⁻¹ := by
  rw [golden_horizon_ratio_sq]
  have hden : 1 - Real.goldenRatio⁻¹ = (Real.goldenRatio ^ 2)⁻¹ := by
    linarith [golden_inverse_split]
  rw [hden, inv_inv]

/-- For a strictly contractive rank-one observer channel, the golden value of
the horizon index is equivalent to its complementary transmission law, the
sampling square, the two Bogoliubov squared amplitudes, the relative-entropy
cost, and the positive square-root sampling ratio.

The hypotheses state the source's external channel laws explicitly. In
particular, `0 < delta`, `0 <= omega`, and `omega < delta` rule out division by
zero, the negative square-root branch, and the singular horizon boundary. -/
theorem golden_horizon_matching
    (horizonIndex sigma alphaSq betaSq kl omega delta : ℝ)
    (hDelta : 0 < delta) (hOmega : 0 ≤ omega) (hContractive : omega < delta)
    (hHorizon : horizonIndex = (1 - sigma ^ 2)⁻¹)
    (hSampling : sigma = omega / delta)
    (hAlpha : alphaSq = horizonIndex)
    (hBeta : betaSq = alphaSq - 1)
    (hKL : kl = Real.log horizonIndex) :
    List.TFAE [
      horizonIndex = Real.goldenRatio ^ 2,
      1 - sigma ^ 2 = (Real.goldenRatio ^ 2)⁻¹,
      sigma ^ 2 = Real.goldenRatio⁻¹,
      alphaSq = Real.goldenRatio ^ 2,
      betaSq = Real.goldenRatio,
      kl = 2 * Real.log Real.goldenRatio,
      omega / delta = goldenHorizonRatio] := by
  have hSigmaNonneg : 0 ≤ sigma := by
    rw [hSampling]
    exact div_nonneg hOmega hDelta.le
  have hSigmaLt : sigma < 1 := by
    rw [hSampling]
    exact (div_lt_one hDelta).2 hContractive
  have hDenPos : 0 < 1 - sigma ^ 2 := by
    have hMinus : 0 < 1 - sigma := sub_pos.mpr hSigmaLt
    have hPlus : 0 < 1 + sigma := by linarith
    nlinarith [mul_pos hMinus hPlus]
  have hIndexPos : 0 < horizonIndex := by
    rw [hHorizon]
    exact inv_pos.mpr hDenPos
  have hPhiSqPos : 0 < Real.goldenRatio ^ 2 :=
    sq_pos_of_pos Real.goldenRatio_pos
  have hRatioSq := golden_horizon_ratio_sq
  have hRatioPos := golden_horizon_ratio_pos
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hIndex
      calc
        1 - sigma ^ 2 = horizonIndex⁻¹ := by rw [hHorizon, inv_inv]
        _ = (Real.goldenRatio ^ 2)⁻¹ := congrArg Inv.inv hIndex
    · intro hComplement
      calc
        horizonIndex = (1 - sigma ^ 2)⁻¹ := hHorizon
        _ = ((Real.goldenRatio ^ 2)⁻¹)⁻¹ := congrArg Inv.inv hComplement
        _ = Real.goldenRatio ^ 2 := inv_inv _
  tfae_have 2 ↔ 3 := by
    constructor <;> intro h <;> nlinarith [golden_inverse_split]
  tfae_have 1 ↔ 4 := by
    constructor
    · intro hIndex
      exact hAlpha.trans hIndex
    · intro hAlphaGolden
      exact hAlpha.symm.trans hAlphaGolden
  tfae_have 4 ↔ 5 := by
    constructor
    · intro hAlphaGolden
      rw [hBeta, hAlphaGolden, Real.goldenRatio_sq]
      ring
    · intro hBetaGolden
      rw [hBeta] at hBetaGolden
      nlinarith [Real.goldenRatio_sq]
  tfae_have 1 ↔ 6 := by
    constructor
    · intro hIndex
      rw [hKL, hIndex, Real.log_pow]
      norm_num
    · intro hEntropy
      apply Real.log_injOn_pos hIndexPos hPhiSqPos
      rw [← hKL, hEntropy, Real.log_pow]
      norm_num
  tfae_have 3 ↔ 7 := by
    constructor
    · intro hSigmaSq
      have hSquares : sigma ^ 2 = goldenHorizonRatio ^ 2 :=
        hSigmaSq.trans hRatioSq.symm
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hSquares with hSigma | hSigma
      · rw [← hSampling, hSigma]
      · exfalso
        nlinarith
    · intro hRatio
      calc
        sigma ^ 2 = goldenHorizonRatio ^ 2 := by rw [hSampling, hRatio]
        _ = Real.goldenRatio⁻¹ := hRatioSq
  tfae_finish

-- Non-vacuity probe: the canonical positive sampling channel satisfies all
-- structural hypotheses, hence all seven golden conditions are equivalent.
example :
    List.TFAE [
      Real.goldenRatio ^ 2 = Real.goldenRatio ^ 2,
      1 - goldenHorizonRatio ^ 2 = (Real.goldenRatio ^ 2)⁻¹,
      goldenHorizonRatio ^ 2 = Real.goldenRatio⁻¹,
      Real.goldenRatio ^ 2 = Real.goldenRatio ^ 2,
      Real.goldenRatio = Real.goldenRatio,
      2 * Real.log Real.goldenRatio = 2 * Real.log Real.goldenRatio,
      goldenHorizonRatio / 1 = goldenHorizonRatio] := by
  apply golden_horizon_matching
  · norm_num
  · exact golden_horizon_ratio_pos.le
  · rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
    exact Real.sqrt_lt_sqrt (inv_nonneg.mpr Real.goldenRatio_pos.le)
      (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
  · exact golden_horizon_index_identity
  · norm_num
  · rfl
  · nlinarith [Real.goldenRatio_sq]
  · simpa using (Real.log_pow Real.goldenRatio 2).symm

-- Broken-law probe: setting the sampling ratio to zero while retaining the
-- golden horizon index violates the index law and makes the equivalence false.
example :
    ¬(Real.goldenRatio ^ 2 = (1 - (0 : ℝ) ^ 2)⁻¹) ∧
      ¬List.TFAE [
        Real.goldenRatio ^ 2 = Real.goldenRatio ^ 2,
        1 - (0 : ℝ) ^ 2 = (Real.goldenRatio ^ 2)⁻¹,
        (0 : ℝ) ^ 2 = Real.goldenRatio⁻¹,
        Real.goldenRatio ^ 2 = Real.goldenRatio ^ 2,
        Real.goldenRatio = Real.goldenRatio,
        2 * Real.log Real.goldenRatio = 2 * Real.log Real.goldenRatio,
        (0 : ℝ) / 1 = goldenHorizonRatio] := by
  constructor
  · norm_num only [zero_pow, sub_zero, inv_one]
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  · intro hAll
    have hSamplingSquare := (hAll.out 0 2).mp rfl
    have hInvPos : 0 < Real.goldenRatio⁻¹ := inv_pos.mpr Real.goldenRatio_pos
    have hZero : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [hZero] at hSamplingSquare
    exact hInvPos.ne' hSamplingSquare.symm

#print axioms golden_horizon_matching

end D5.S3.Observer.GoldenCoding.GoldenHorizonMatching
