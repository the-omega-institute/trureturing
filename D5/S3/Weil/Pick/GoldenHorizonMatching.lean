/- GID: D5/S3/Weil/Pick/GoldenHorizonMatching
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/GoldenHorizonMatching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden effective index characterizes six equivalent rank-one channel conditions. -/

import D5.S3.Weil.Pick.HorizonEffectiveIndex
import D5.S3.Quantum.Bogoliubov.BogoliubovNormConservation
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * Repository searches for golden horizon matching, the golden effective
     index, and rank-one Bogoliubov equivalences found no exact D5 owner.
     `HorizonEffectiveIndex` supplies the canonical determinant index, while
     `BogoliubovNormConservation` supplies the standard real coefficient law.
   * Pinned Mathlib supplies `Real.cosh_artanh`, `Real.log_pow`,
     `Real.log_injOn_pos`, and the golden-ratio identities used below, but no
     theorem combining the seven channel conditions.
   * A Lean ecosystem search for golden-ratio Bogoliubov/artanh matching found
     no result. -/

noncomputable section

open scoped Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Pick.GoldenHorizonMatching

open D5.S3.Weil.Pick.HorizonEffectiveIndex
open D5.S3.Quantum.Bogoliubov.BogoliubovNormConservation

/-- For a positive strictly contractive rank-one channel, construct the
single-entry Hankel matrix, its effective index, and its standard real
Bogoliubov coefficients. The golden value of the index is equivalent to each
of the six displayed defect, singular-value, coefficient, logarithmic, and
frequency-ratio conditions. -/
theorem golden_horizon_matching
    (delta omega : ℝ) (hdelta : 0 < delta)
    (homega : 0 < omega) (hlt : omega < delta) :
    let sigma := omega / delta
    let hankel : Matrix (Fin 1) (Fin 1) ℝ := !![sigma]
    let index := horizonEffectiveIndex hankel
    let rapidity := Real.artanh sigma
    let alpha := Real.cosh rapidity
    let beta := Real.sinh rapidity
    let divergence := Real.log index
    (index = Real.goldenRatio ^ 2 ↔
        1 - sigma ^ 2 = (Real.goldenRatio ^ 2)⁻¹) ∧
      (index = Real.goldenRatio ^ 2 ↔
        sigma ^ 2 = Real.goldenRatio⁻¹) ∧
      (index = Real.goldenRatio ^ 2 ↔
        |alpha| ^ 2 = Real.goldenRatio ^ 2) ∧
      (index = Real.goldenRatio ^ 2 ↔
        |beta| ^ 2 = Real.goldenRatio) ∧
      (index = Real.goldenRatio ^ 2 ↔
        divergence = 2 * Real.log Real.goldenRatio) ∧
      (index = Real.goldenRatio ^ 2 ↔
        omega / delta = Real.sqrt Real.goldenRatio⁻¹) := by
  dsimp only
  let sigma := omega / delta
  have hsigma_pos : 0 < sigma := div_pos homega hdelta
  have hsigma_lt : sigma < 1 := (div_lt_one hdelta).mpr hlt
  have hsigma_mem : sigma ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hsigma_lt⟩
  have hdefect_pos : 0 < 1 - sigma ^ 2 := by
    nlinarith
  have hindex :
      horizonEffectiveIndex (!![sigma] : Matrix (Fin 1) (Fin 1) ℝ) =
        (1 - sigma ^ 2)⁻¹ := by
    simp [horizonEffectiveIndex, horizonDefect, Matrix.mul_apply]
    ring
  have hindex_pos :
      0 < horizonEffectiveIndex (!![sigma] : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [hindex]
    exact inv_pos.mpr hdefect_pos
  have hphi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hphi_sq_pos : 0 < Real.goldenRatio ^ 2 := sq_pos_of_pos hphi_pos
  have hphi_inv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hphi_inv_sq :
      (Real.goldenRatio ^ 2)⁻¹ = 2 - Real.goldenRatio := by
    rw [← inv_pow, hphi_inv]
    nlinarith [Real.goldenRatio_sq]
  have hgolden_inv :
      1 - (Real.goldenRatio ^ 2)⁻¹ = Real.goldenRatio⁻¹ := by
    rw [hphi_inv_sq, hphi_inv]
    ring
  have halpha :
      |Real.cosh (Real.artanh sigma)| ^ 2 =
        horizonEffectiveIndex (!![sigma] : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [Real.cosh_artanh hsigma_mem, one_div]
    rw [hindex, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.2 hdefect_pos))]
    rw [inv_pow, Real.sq_sqrt hdefect_pos.le]
  have hbeta :
      |Real.sinh (Real.artanh sigma)| ^ 2 =
        horizonEffectiveIndex (!![sigma] : Matrix (Fin 1) (Fin 1) ℝ) - 1 := by
    have hnorm := bogoliubov_norm_conservation (Real.artanh sigma)
    rw [halpha] at hnorm
    linarith
  have hfirst :
      horizonEffectiveIndex (!![sigma] : Matrix (Fin 1) (Fin 1) ℝ) =
          Real.goldenRatio ^ 2 ↔
        1 - sigma ^ 2 = (Real.goldenRatio ^ 2)⁻¹ := by
    rw [hindex]
    constructor
    · intro h
      calc
        1 - sigma ^ 2 = ((1 - sigma ^ 2)⁻¹)⁻¹ := (inv_inv _).symm
        _ = (Real.goldenRatio ^ 2)⁻¹ := congrArg Inv.inv h
    · intro h
      calc
        (1 - sigma ^ 2)⁻¹ = ((Real.goldenRatio ^ 2)⁻¹)⁻¹ := congrArg Inv.inv h
        _ = Real.goldenRatio ^ 2 := inv_inv _
  have hsecond :
      1 - sigma ^ 2 = (Real.goldenRatio ^ 2)⁻¹ ↔
        sigma ^ 2 = Real.goldenRatio⁻¹ := by
    constructor <;> intro h <;> nlinarith [hgolden_inv]
  have hthird :
      horizonEffectiveIndex (!![sigma] : Matrix (Fin 1) (Fin 1) ℝ) =
          Real.goldenRatio ^ 2 ↔
        |Real.cosh (Real.artanh sigma)| ^ 2 = Real.goldenRatio ^ 2 := by
    rw [halpha]
  have hfourth :
      horizonEffectiveIndex (!![sigma] : Matrix (Fin 1) (Fin 1) ℝ) =
          Real.goldenRatio ^ 2 ↔
        |Real.sinh (Real.artanh sigma)| ^ 2 = Real.goldenRatio := by
    rw [hbeta]
    constructor <;> intro h <;> nlinarith [Real.goldenRatio_sq]
  have hlog_phi_sq :
      Real.log (Real.goldenRatio ^ 2) =
        2 * Real.log Real.goldenRatio := by
    simpa only [Nat.cast_ofNat] using Real.log_pow Real.goldenRatio 2
  have hfifth :
      horizonEffectiveIndex (!![sigma] : Matrix (Fin 1) (Fin 1) ℝ) =
          Real.goldenRatio ^ 2 ↔
        Real.log (horizonEffectiveIndex
          (!![sigma] : Matrix (Fin 1) (Fin 1) ℝ)) =
          2 * Real.log Real.goldenRatio := by
    constructor
    · intro h
      calc
        Real.log (horizonEffectiveIndex
            (!![sigma] : Matrix (Fin 1) (Fin 1) ℝ)) =
            Real.log (Real.goldenRatio ^ 2) := congrArg Real.log h
        _ = 2 * Real.log Real.goldenRatio := hlog_phi_sq
    · intro h
      have hlog :
          Real.log (horizonEffectiveIndex
            (!![sigma] : Matrix (Fin 1) (Fin 1) ℝ)) =
            Real.log (Real.goldenRatio ^ 2) := by
        exact h.trans hlog_phi_sq.symm
      exact Real.log_injOn_pos hindex_pos hphi_sq_pos hlog
  have hsixth :
      horizonEffectiveIndex (!![sigma] : Matrix (Fin 1) (Fin 1) ℝ) =
          Real.goldenRatio ^ 2 ↔
        omega / delta = Real.sqrt Real.goldenRatio⁻¹ := by
    rw [hfirst, hsecond]
    constructor
    · intro h
      calc
        sigma = |sigma| := (abs_of_pos hsigma_pos).symm
        _ = Real.sqrt (sigma ^ 2) := (Real.sqrt_sq_eq_abs sigma).symm
        _ = Real.sqrt Real.goldenRatio⁻¹ := congrArg Real.sqrt h
    · intro h
      change sigma = _ at h
      rw [h, Real.sq_sqrt (inv_pos.mpr hphi_pos).le]
  exact ⟨hfirst, hfirst.trans hsecond, hthird, hfourth, hfifth, hsixth⟩

#print axioms golden_horizon_matching

end D5.S3.Weil.Pick.GoldenHorizonMatching
