/- GID: D5/S3/Constants/Moments/LeadingSpectralMomentRecovery
   generality: G
   mirror-B: D5/B/S3/Constants/Moments/LeadingSpectralMomentRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The leading positive spectral scale is recovered from its power moments. -/

/- Library-search audit trail (2026-08-31):
   * D5 name and body-shape searches for leading spectral moment recovery,
     moment ratios and roots, dominant atoms, and multiplicity-weighted power
     sums found no exact theorem or canonical duplicate.
   * Pinned Mathlib has no packaged leading-atom moment theorem. The proof uses
     `tendsto_tsum_of_dominated_convergence`,
     `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Filter.Tendsto.rpow`, and
     continuity of division and square root.
   * GitHub Lean searches for moment-ratio, dominant-term, and spectral-radius
     power limits returned no exact result. -/

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

open Filter Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.Moments.LeadingSpectralMomentRecovery

/-- A summable positive spectrum with a strictly largest atom recovers that
atom from consecutive moment ratios and moment roots. If the atom is the
inverse square of a positive ordinate, inverse ratios recover the ordinate. -/
theorem leading_spectral_moment_recovery
    (alpha : Nat -> Real)
    (multiplicity : Nat -> Nat)
    (gamma : Real)
    (alphaPositive : forall j, 0 < alpha j)
    (alphaStrict : StrictAnti alpha)
    (leadingMultiplicityPositive : 0 < multiplicity 0)
    (spectralSummable : Summable fun j => (multiplicity j : Real) * alpha j)
    (gammaPositive : 0 < gamma)
    (alphaGamma : alpha 0 = gamma⁻¹ ^ 2) :
    let moment := fun n : Nat =>
      ∑' j : Nat, (multiplicity j : Real) * alpha j ^ (n + 1)
    Tendsto (fun n => moment (n + 1) / moment n) atTop (nhds (alpha 0)) /\
      Tendsto (fun n => moment n ^ ((1 : Real) / ((n + 1 : Nat) : Real)))
        atTop (nhds (alpha 0)) /\
      Tendsto (fun n => Real.sqrt (moment n / moment (n + 1)))
        atTop (nhds gamma) := by
  let moment := fun n : Nat =>
    ∑' j : Nat, (multiplicity j : Real) * alpha j ^ (n + 1)
  let normalized := fun n : Nat =>
    ∑' j : Nat,
      (multiplicity j : Real) * (alpha j / alpha 0) ^ (n + 1)
  have alphaZeroPositive : 0 < alpha 0 := alphaPositive 0
  have alphaZeroNe : alpha 0 ≠ 0 := alphaZeroPositive.ne'
  have normalizedLimit : Tendsto normalized atTop (nhds (multiplicity 0 : Real)) := by
    have boundSummable : Summable fun j : Nat =>
        (multiplicity j : Real) * (alpha j / alpha 0) := by
      apply (spectralSummable.mul_right (alpha 0)⁻¹).congr
      intro j
      field_simp
    have pointwise : forall j : Nat, Tendsto
        (fun n : Nat =>
          (multiplicity j : Real) * (alpha j / alpha 0) ^ (n + 1))
        atTop (nhds (if j = 0 then (multiplicity 0 : Real) else 0)) := by
      intro j
      by_cases hj : j = 0
      · subst j
        convert (tendsto_const_nhds : Tendsto
          (fun _ : Nat => (multiplicity 0 : Real)) atTop
          (nhds (multiplicity 0 : Real))) using 1 <;> simp [alphaZeroNe]
      · have ratioNonnegative : 0 <= alpha j / alpha 0 :=
          div_nonneg (alphaPositive j).le alphaZeroPositive.le
        have ratioLtOne : alpha j / alpha 0 < 1 := by
          rw [div_lt_one alphaZeroPositive]
          exact alphaStrict (Nat.pos_of_ne_zero hj)
        have ratioPowerLimit : Tendsto
            (fun n : Nat => (alpha j / alpha 0) ^ (n + 1))
            atTop (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one ratioNonnegative ratioLtOne).comp
            (tendsto_add_atTop_nat 1)
        simpa [hj] using tendsto_const_nhds.mul ratioPowerLimit
    have dominated : forall n j : Nat,
        ‖(multiplicity j : Real) * (alpha j / alpha 0) ^ (n + 1)‖ <=
          (multiplicity j : Real) * (alpha j / alpha 0) := by
      intro n j
      have ratioNonnegative : 0 <= alpha j / alpha 0 :=
        div_nonneg (alphaPositive j).le alphaZeroPositive.le
      have ratioLeOne : alpha j / alpha 0 <= 1 := by
        rw [div_le_one alphaZeroPositive]
        exact alphaStrict.antitone (Nat.zero_le j)
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ratioNonnegative _))]
      exact mul_le_mul_of_nonneg_left
        (pow_le_of_le_one ratioNonnegative ratioLeOne (by omega))
        (Nat.cast_nonneg _)
    have limit := tendsto_tsum_of_dominated_convergence
      boundSummable pointwise (Filter.Eventually.of_forall dominated)
    simpa [normalized] using limit
  have momentFactor (n : Nat) :
      moment n = alpha 0 ^ (n + 1) * normalized n := by
    unfold moment normalized
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    rw [div_pow]
    field_simp
  have leadingMultiplicityRealPositive : 0 < (multiplicity 0 : Real) := by
    exact_mod_cast leadingMultiplicityPositive
  have normalizedEventuallyPositive : ∀ᶠ n in atTop, 0 < normalized n :=
    normalizedLimit.eventually (Ioi_mem_nhds leadingMultiplicityRealPositive)
  have normalizedShiftLimit :
      Tendsto (fun n => normalized (n + 1)) atTop
        (nhds (multiplicity 0 : Real)) :=
    normalizedLimit.comp (tendsto_add_atTop_nat 1)
  have normalizedRatioLimit :
      Tendsto (fun n => normalized (n + 1) / normalized n) atTop (nhds 1) := by
    have h := normalizedShiftLimit.div normalizedLimit
      leadingMultiplicityRealPositive.ne'
    rw [div_self leadingMultiplicityRealPositive.ne'] at h
    exact h.congr' (Filter.Eventually.of_forall fun _ => rfl)
  have momentRatioLimit :
      Tendsto (fun n => moment (n + 1) / moment n) atTop
        (nhds (alpha 0)) := by
    have scaled : Tendsto
        (fun n : Nat => alpha 0 * (normalized (n + 1) / normalized n))
        atTop (nhds (alpha 0 * 1)) :=
      tendsto_const_nhds.mul normalizedRatioLimit
    have h : Tendsto (fun n => moment (n + 1) / moment n) atTop
        (nhds (alpha 0 * 1)) := scaled.congr' (by
      filter_upwards [normalizedEventuallyPositive] with n hn
      symm
      rw [momentFactor, momentFactor]
      field_simp [alphaZeroNe, hn.ne']
      ring)
    simpa using h
  refine ⟨momentRatioLimit, ?_, ?_⟩
  · have exponentLimit : Tendsto
        (fun n : Nat => (1 : Real) / ((n + 1 : Nat) : Real))
        atTop (nhds 0) := by
      simpa [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    have normalizedRootLimit : Tendsto
        (fun n : Nat => normalized n ^ ((1 : Real) / ((n + 1 : Nat) : Real)))
        atTop (nhds 1) := by
      simpa using normalizedLimit.rpow exponentLimit
        (Or.inl leadingMultiplicityRealPositive.ne')
    have alphaPowerRoot (n : Nat) :
        (alpha 0 ^ (n + 1)) ^ ((1 : Real) / ((n + 1 : Nat) : Real)) =
          alpha 0 := by
      calc
        (alpha 0 ^ (n + 1)) ^ ((1 : Real) / ((n + 1 : Nat) : Real)) =
            (alpha 0 ^ (((n + 1 : Nat) : Real))) ^
              ((1 : Real) / ((n + 1 : Nat) : Real)) := by
                rw [Real.rpow_natCast]
        _ = alpha 0 ^ ((((n + 1 : Nat) : Real)) *
              ((1 : Real) / ((n + 1 : Nat) : Real))) := by
                rw [Real.rpow_mul alphaZeroPositive.le]
        _ = alpha 0 := by
              rw [mul_one_div_cancel]
              · exact Real.rpow_one (alpha 0)
              · positivity
    have scaled : Tendsto
        (fun n : Nat => alpha 0 *
          normalized n ^ ((1 : Real) / ((n + 1 : Nat) : Real)))
        atTop (nhds (alpha 0 * 1)) :=
      tendsto_const_nhds.mul normalizedRootLimit
    have h : Tendsto
        (fun n : Nat => moment n ^ ((1 : Real) / ((n + 1 : Nat) : Real)))
        atTop (nhds (alpha 0 * 1)) := scaled.congr' (by
      filter_upwards [normalizedEventuallyPositive] with n hn
      symm
      rw [momentFactor, Real.mul_rpow (pow_nonneg alphaZeroPositive.le _)
        hn.le, alphaPowerRoot])
    simpa using h
  · have inverseRatioLimit : Tendsto
        (fun n : Nat => moment n / moment (n + 1)) atTop
        (nhds (alpha 0)⁻¹) := by
      simpa only [inv_div] using momentRatioLimit.inv₀ alphaZeroNe
    have sqrtAlphaInv : Real.sqrt (alpha 0)⁻¹ = gamma := by
      rw [alphaGamma]
      simp only [inv_pow, inv_inv]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos gammaPositive]
    simpa only [sqrtAlphaInv] using inverseRatioLimit.sqrt

#print axioms leading_spectral_moment_recovery

end D5.S3.Constants.Moments.LeadingSpectralMomentRecovery
