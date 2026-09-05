/- GID: D5/S0/Tower/DBonacci/PerronDeficitAsymptotic
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacci/PerronDeficitAsymptotic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The d-bonacci Perron deficit is asymptotic to two to the negative d. -/

import D5.S0.Tower.DBonacci.PerronRoot
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace D5.S0.Tower.DBonacci.PerronDeficitAsymptotic

open Filter
open D5.S0.Tower.DBonacci.PerronRoot

/- Library-search and duplication audit (2026-09-05): repository keyword, symbol-variant,
   digestion-state, generalized-consequence, module-name, and in-flight branch searches found
   the exact deficit identity and convergence of the roots, but not this ratio limit. Mathlib's
   `tendsto_self_mul_const_pow_of_lt_one` supplies the polynomial-times-geometric decay and
   `Real.log_le_sub_one_of_pos` supplies the exponential comparison. The live proof rewrites the
   normalized deficit as `(2 / lambda_d)^d`, bounds its scaled logarithm by
   `goldenRatio^(-1) * d * goldenRatio^(-d)`, and exponentiates the squeezed limit. -/

/-- The upper-endpoint deficit of the d-bonacci Perron root is sharply asymptotic to `2⁻ᵈ`.
The denominator is nonzero for every `d`, and orders below two are irrelevant to the limit. -/
theorem dbonacci_perron_deficit_asymptotic :
    Tendsto
      (fun d : Nat =>
        (2 - dbonacciPerronRoot d) / ((2 : Real)⁻¹ ^ d))
      atTop (nhds 1) := by
  have hphi_inv_nonneg : 0 ≤ Real.goldenRatio⁻¹ :=
    (inv_pos.mpr Real.goldenRatio_pos).le
  have hphi_inv_lt_one : Real.goldenRatio⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hgeometric :
      Tendsto
        (fun d : Nat => (d : Real) * Real.goldenRatio⁻¹ ^ d)
        atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one hphi_inv_nonneg hphi_inv_lt_one
  have hmajorant :
      Tendsto
        (fun d : Nat =>
          Real.goldenRatio⁻¹ * ((d : Real) * Real.goldenRatio⁻¹ ^ d))
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hgeometric
  have hscaledLog :
      Tendsto
        (fun d : Nat =>
          (d : Real) * Real.log (2 / dbonacciPerronRoot d))
        atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop 2] with d hd
      have hroot_pos : 0 < dbonacciPerronRoot d :=
        lt_trans zero_lt_one (one_lt_dbonacciPerronRoot d hd)
      have hbase_one : 1 ≤ 2 / dbonacciPerronRoot d := by
        apply (le_div_iff₀ hroot_pos).2
        simpa using (dbonacciPerronRoot_lt_two d hd).le
      exact mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg hbase_one)
    · filter_upwards [eventually_ge_atTop 2] with d hd
      have hroot_pos : 0 < dbonacciPerronRoot d :=
        lt_trans zero_lt_one (one_lt_dbonacciPerronRoot d hd)
      have hbase_pos : 0 < 2 / dbonacciPerronRoot d :=
        div_pos (by norm_num) hroot_pos
      have hphi_le_root : Real.goldenRatio ≤ dbonacciPerronRoot d := by
        rw [← dbonacciPerronRoot_two_eq_goldenRatio]
        exact dbonacciPerronRoot_strictMonoOn.monotoneOn (by simp) hd hd
      have hinv_le :
          (dbonacciPerronRoot d)⁻¹ ≤ Real.goldenRatio⁻¹ :=
        (inv_le_inv₀ hroot_pos Real.goldenRatio_pos).2 hphi_le_root
      have hratio_sub :
          2 / dbonacciPerronRoot d - 1 =
            (dbonacciPerronRoot d)⁻¹ ^ (d + 1) := by
        calc
          2 / dbonacciPerronRoot d - 1 =
              (2 - dbonacciPerronRoot d) / dbonacciPerronRoot d := by
                field_simp
          _ = (dbonacciPerronRoot d)⁻¹ ^ d /
              dbonacciPerronRoot d := by
                rw [two_sub_dbonacciPerronRoot_eq_inv_pow d hd]
          _ = (dbonacciPerronRoot d)⁻¹ ^ (d + 1) := by
                rw [pow_succ]
                simp only [div_eq_mul_inv]
      calc
        (d : Real) * Real.log (2 / dbonacciPerronRoot d) ≤
            (d : Real) * (2 / dbonacciPerronRoot d - 1) :=
          mul_le_mul_of_nonneg_left
            (Real.log_le_sub_one_of_pos hbase_pos) (Nat.cast_nonneg d)
        _ = (d : Real) * (dbonacciPerronRoot d)⁻¹ ^ (d + 1) := by
          rw [hratio_sub]
        _ ≤ (d : Real) * Real.goldenRatio⁻¹ ^ (d + 1) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (inv_nonneg.mpr hroot_pos.le) hinv_le (d + 1))
            (Nat.cast_nonneg d)
        _ = Real.goldenRatio⁻¹ *
            ((d : Real) * Real.goldenRatio⁻¹ ^ d) := by
          rw [pow_succ]
          ring
    · exact hmajorant
  have hexponential :
      Tendsto
        (fun d : Nat =>
          Real.exp ((d : Real) * Real.log (2 / dbonacciPerronRoot d)))
        atTop (nhds 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp hscaledLog
  apply hexponential.congr'
  filter_upwards [eventually_ge_atTop 2] with d hd
  have hroot_pos : 0 < dbonacciPerronRoot d :=
    lt_trans zero_lt_one (one_lt_dbonacciPerronRoot d hd)
  symm
  rw [two_sub_dbonacciPerronRoot_eq_inv_pow d hd]
  calc
    (dbonacciPerronRoot d)⁻¹ ^ d / (2 : Real)⁻¹ ^ d =
        (2 / dbonacciPerronRoot d) ^ d := by
      rw [← div_pow]
      congr 1
      field_simp
    _ = Real.exp ((d : Real) * Real.log (2 / dbonacciPerronRoot d)) := by
      rw [Real.exp_nat_mul, Real.exp_log (div_pos (by norm_num) hroot_pos)]

#print axioms dbonacci_perron_deficit_asymptotic

end D5.S0.Tower.DBonacci.PerronDeficitAsymptotic
