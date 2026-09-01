/- GID: D5/S3/Weil/ZetaLinear/HorizonFreeEnergyDivergence
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaLinear/HorizonFreeEnergyDivergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The single-defect horizon determinant has a logarithmically divergent free energy. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * The atom is residual-open with empty `coverage_gids`, and its atom id
     occurs in no formalization receipt. Repository searches for horizon
     determinants, free energy, boundary logarithmic divergence, and artanh
     found no equivalent declaration.
   * `Weil.Pick.HorizonEffectiveIndex.singularFactor_tendsto_atTop` proves
     divergence of `(1 - sigma^2)⁻¹`, while
     `Analytic.Zeta.ZetaEntropyDivergence.log_tendsto_atTop_of_pos_simple_pole`
     treats logarithms of positive simple poles. Neither supplies the
     determinant identities or the negative-log boundary theorem below.
   * Pinned Mathlib supplies `sq_lt_sq`, `sq_eq_sq_iff_abs_eq_abs`,
     `Real.tendsto_log_nhdsGT_zero`, and
     `tendsto_one_div_add_atTop_nhds_zero_nat`. The last two are reused for
     the substantive filter limit and its explicit sequential witness.
   * Searches of the installed admissible third-party Lean packages for
     horizon determinants, free energy, and artanh returned no hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaLinear.HorizonFreeEnergyDivergence

open Filter Set Topology

/-- The scalar horizon determinant of a single normalized defect mode. -/
def horizonDeterminant (delta omega : ℝ) : ℝ :=
  1 - (omega / delta) ^ 2

/-- The free-energy defect is the negative logarithm of the horizon
determinant. Its analytic interpretation is restricted to the positive
determinant region characterized below. -/
def horizonFreeEnergy (delta omega : ℝ) : ℝ :=
  -Real.log (horizonDeterminant delta omega)

/-- Away from zero depth, the normalized and quotient forms of the horizon
determinant agree. -/
theorem horizon_determinant_eq_div (delta omega : ℝ) (hdelta : delta ≠ 0) :
    horizonDeterminant delta omega =
      (delta ^ 2 - omega ^ 2) / delta ^ 2 := by
  unfold horizonDeterminant
  field_simp

/-- The determinant is positive precisely in the open horizon interior. -/
theorem horizon_determinant_pos_iff_abs_lt (delta omega : ℝ)
    (hdelta : delta ≠ 0) :
    0 < horizonDeterminant delta omega ↔ |omega| < |delta| := by
  rw [horizon_determinant_eq_div delta omega hdelta, div_pos_iff]
  have hdeltaSq : 0 < delta ^ 2 := sq_pos_of_ne_zero hdelta
  simp only [hdeltaSq, and_true, not_lt_of_ge hdeltaSq.le, and_false, or_false]
  rw [sub_pos, sq_lt_sq]

/-- The two signed horizon points are exactly the determinant-zero locus. -/
theorem horizon_determinant_eq_zero_iff_abs_eq (delta omega : ℝ)
    (hdelta : delta ≠ 0) :
    horizonDeterminant delta omega = 0 ↔ |omega| = |delta| := by
  rw [horizon_determinant_eq_div delta omega hdelta, div_eq_zero_iff]
  have hdeltaSq : delta ^ 2 ≠ 0 := pow_ne_zero 2 hdelta
  simp only [hdeltaSq, or_false, sub_eq_zero]
  exact sq_eq_sq_iff_abs_eq_abs delta omega |>.trans eq_comm

/-- At a positive defect depth, the free energy diverges as the observation
frequency approaches the horizon from its positive-determinant side. -/
theorem horizon_free_energy_tendsto_atTop (delta : ℝ) (hdelta : 0 < delta) :
    Tendsto (fun omega : ℝ => horizonFreeEnergy delta omega)
      (nhdsWithin delta (Iio delta)) atTop := by
  have hdeltaNe : delta ≠ 0 := ne_of_gt hdelta
  have hDetNhds :
      Tendsto (fun omega : ℝ => horizonDeterminant delta omega)
        (nhdsWithin delta (Iio delta)) (nhds 0) := by
    have hContinuous : Continuous (fun omega : ℝ => horizonDeterminant delta omega) := by
      unfold horizonDeterminant
      fun_prop
    have hAtDelta :
        Tendsto (fun omega : ℝ => horizonDeterminant delta omega)
          (nhds delta) (nhds (horizonDeterminant delta delta)) :=
      hContinuous.continuousAt
    have hValue : horizonDeterminant delta delta = 0 :=
      (horizon_determinant_eq_zero_iff_abs_eq delta delta hdeltaNe).2 rfl
    simpa only [hValue] using hAtDelta.mono_left nhdsWithin_le_nhds
  have hDetRight :
      Tendsto (fun omega : ℝ => horizonDeterminant delta omega)
        (nhdsWithin delta (Iio delta)) (nhdsWithin 0 (Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hDetNhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT (show -delta < delta by linarith)] with omega homega
    exact (horizon_determinant_pos_iff_abs_lt delta omega hdeltaNe).2
      (by rw [abs_of_pos hdelta, abs_lt]; exact homega)
  unfold horizonFreeEnergy
  exact tendsto_neg_atTop_iff.mpr
    (Real.tendsto_log_nhdsGT_zero.comp hDetRight)

/-- A concrete sequence approaching the depth-two horizon from below. -/
def horizonApproach (n : ℕ) : ℝ :=
  2 - 1 / ((n : ℝ) + 1)

theorem horizonApproach_tendsto :
    Tendsto horizonApproach atTop (nhdsWithin 2 (Iio 2)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · change Tendsto (fun n : ℕ => 2 - 1 / ((n : ℝ) + 1)) atTop (nhds 2)
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · exact Eventually.of_forall fun n => by
      change horizonApproach n < 2
      unfold horizonApproach
      have hPositive : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      linarith

/-- The explicit horizon-approach sequence witnesses the same unbounded free
energy as the neighborhood theorem. -/
theorem horizonApproach_free_energy_tendsto_atTop :
    Tendsto (fun n : ℕ => horizonFreeEnergy 2 (horizonApproach n))
      atTop atTop := by
  exact (horizon_free_energy_tendsto_atTop 2 (by norm_num)).comp
    horizonApproach_tendsto

/-- Both finite and horizon sides are inhabited by exact numerical values. -/
theorem horizon_free_energy_numeric_witnesses :
    horizonDeterminant 2 1 = 3 / 4 ∧
      0 < horizonDeterminant 2 1 ∧
      horizonFreeEnergy 2 1 = Real.log (4 / 3) ∧
      0 < horizonFreeEnergy 2 1 ∧
      horizonDeterminant 2 2 = 0 := by
  have hLog : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  norm_num [horizonDeterminant, horizonFreeEnergy, ← Real.log_inv, hLog]

/-- Universal single-defect horizon law. The source's depth is nonnegative;
nonzero depth is therefore exactly the positivity needed by the one-sided
limit, with no additional proposition assumed. -/
theorem single_defect_horizon_free_energy_universal_divergence
    (delta : NNReal) (hdelta : delta ≠ 0) :
    (∀ omega : ℝ,
        horizonDeterminant delta omega =
          ((delta : ℝ) ^ 2 - omega ^ 2) / (delta : ℝ) ^ 2) ∧
      (∀ omega : ℝ,
        0 < horizonDeterminant delta omega ↔ |omega| < |(delta : ℝ)|) ∧
      (∀ omega : ℝ,
        horizonDeterminant delta omega = 0 ↔ |omega| = |(delta : ℝ)|) ∧
      Tendsto (fun omega : ℝ => horizonFreeEnergy delta omega)
        (nhdsWithin (delta : ℝ) (Iio (delta : ℝ))) atTop := by
  have hdeltaReal : (delta : ℝ) ≠ 0 := by exact_mod_cast hdelta
  have hdeltaPos : (0 : ℝ) < delta :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hdelta)
  exact ⟨fun omega => horizon_determinant_eq_div delta omega hdeltaReal,
    fun omega => horizon_determinant_pos_iff_abs_lt delta omega hdeltaReal,
    fun omega => horizon_determinant_eq_zero_iff_abs_eq delta omega hdeltaReal,
    horizon_free_energy_tendsto_atTop delta hdeltaPos⟩

#print axioms single_defect_horizon_free_energy_universal_divergence
#print axioms horizon_free_energy_numeric_witnesses
#print axioms horizonApproach_free_energy_tendsto_atTop

end D5.S3.Weil.ZetaLinear.HorizonFreeEnergyDivergence
