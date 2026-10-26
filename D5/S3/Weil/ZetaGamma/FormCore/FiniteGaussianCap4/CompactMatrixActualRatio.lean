/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CompactMatrixActualRatio
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual cap multiplier integrals and the conditional original ratio consumer. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianGraph
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4CompactMultiplier
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianStrictEnergy

set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace FiniteGaussianCap475
open FiniteGaussianCap4

private theorem capWeight_density_above_pi (x : ℝ) (hx : Real.pi < x) :
    x ^ (7 / 2 : ℝ) * capWeight x =
      Real.pi ^ (-5 / 2 : ℝ) * x ^ 6 - 4 * Real.pi ^ (7 / 2 : ℝ) := by
  have hx0 : 0 < x := lt_trans Real.pi_pos hx
  have hprod : x ^ (7 / 2 : ℝ) * x ^ (5 / 2 : ℝ) = x ^ 6 := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hcancel : x ^ (7 / 2 : ℝ) * x ^ (-7 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hp5 : Real.pi ^ (-5 / 2 : ℝ) = (Real.pi ^ (5 / 2 : ℝ))⁻¹ := by
    rw [show (-5 / 2 : ℝ) = -(5 / 2 : ℝ) by ring, Real.rpow_neg Real.pi_pos.le]
  have hp7 : Real.pi ^ (-7 / 2 : ℝ) = (Real.pi ^ (7 / 2 : ℝ))⁻¹ := by
    rw [show (-7 / 2 : ℝ) = -(7 / 2 : ℝ) by ring, Real.rpow_neg Real.pi_pos.le]
  calc
    x ^ (7 / 2 : ℝ) * capWeight x =
        (x ^ (7 / 2 : ℝ) * x ^ (5 / 2 : ℝ)) / Real.pi ^ (5 / 2 : ℝ) -
          4 * (x ^ (7 / 2 : ℝ) * x ^ (-7 / 2 : ℝ)) / Real.pi ^ (-7 / 2 : ℝ) := by
      rw [capWeight, if_pos hx, Real.div_rpow hx0.le Real.pi_pos.le,
        Real.div_rpow hx0.le Real.pi_pos.le]
      ring
    _ = x ^ 6 / Real.pi ^ (5 / 2 : ℝ) - 4 / Real.pi ^ (-7 / 2 : ℝ) := by
      rw [hprod, hcancel]
      ring
    _ = Real.pi ^ (-5 / 2 : ℝ) * x ^ 6 - 4 * Real.pi ^ (7 / 2 : ℝ) := by
      rw [hp5, hp7]
      simp only [div_inv_eq_mul]
      ring

private theorem capWeight_density_indicator (F : ℝ → ℝ) :
    (fun x : ℝ => x ^ (7 / 2 : ℝ) * capWeight x * F x ^ 2) =
      (Ioi Real.pi).indicator (fun x : ℝ =>
        Real.pi ^ (-5 / 2 : ℝ) * (x ^ 6 * F x ^ 2) -
          (4 * Real.pi ^ (7 / 2 : ℝ)) * F x ^ 2) := by
  funext x
  by_cases hx : Real.pi < x
  · rw [indicator_of_mem (s := Ioi Real.pi) hx, capWeight_density_above_pi x hx]
    ring
  · simp [capWeight, hx]

/-- Actual, integrable cap energy with the original endpoint and exact
scaling. No integrability, parity, or coefficient-domain premise is assumed. -/
theorem finiteGaussian_capWeight_integral {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (7 / 2 : ℝ) * capWeight x *
      gaussianFeature c site x ^ 2) (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * capWeight x * gaussianFeature c site x ^ 2) =
      Real.pi ^ (-5 / 2 : ℝ) *
        (∫ x in Ioi Real.pi, x ^ 6 * gaussianFeature c site x ^ 2) -
      4 * Real.pi ^ (7 / 2 : ℝ) *
        (∫ x in Ioi Real.pi, gaussianFeature c site x ^ 2) := by
  have h6 : IntegrableOn (fun x : ℝ => x ^ 6 * gaussianFeature c site x ^ 2) (Ioi 0) := by
    simpa only [Real.rpow_natCast] using
      (finiteGaussian_weighted_energy_convergence c site (6 : ℕ) (by norm_num)).2.1
  have h0 : IntegrableOn (fun x : ℝ => gaussianFeature c site x ^ 2) (Ioi 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      (finiteGaussian_weighted_energy_convergence c site 0 (by norm_num)).2.1
  have hsub := (h6.const_mul (Real.pi ^ (-5 / 2 : ℝ))).sub
    (h0.const_mul (4 * Real.pi ^ (7 / 2 : ℝ)))
  constructor
  · rw [capWeight_density_indicator]
    exact hsub.indicator measurableSet_Ioi
  · rw [capWeight_density_indicator, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi Real.pi_pos.le)]
    rw [integral_sub
      ((h6.mono_set (Ioi_subset_Ioi Real.pi_pos.le)).const_mul (Real.pi ^ (-5 / 2 : ℝ)))
      ((h0.mono_set (Ioi_subset_Ioi Real.pi_pos.le)).const_mul (4 * Real.pi ^ (7 / 2 : ℝ))),
      integral_const_mul, integral_const_mul]

private theorem positive_weight_two (x : ℝ) (hx : 0 < x) :
    x ^ (7 / 2 : ℝ) * x ^ 2 = x ^ (11 / 2 : ℝ) := by
  rw [← Real.rpow_two, ← Real.rpow_add hx]
  norm_num

/-- Integrability of the same compact correction, and the integrated global
quadratic-minus-compact lower estimate, both derived on the actual source. -/
theorem finiteGaussian_capWeight_quadratic_lower {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (7 / 2 : ℝ) * compactDebit x *
      gaussianFeature c site x ^ 2) (Ioi 0) ∧
    (1 / 10 : ℝ) * (∫ x in Ioi (0 : ℝ), x ^ (11 / 2 : ℝ) * gaussianFeature c site x ^ 2) -
      (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * compactDebit x * gaussianFeature c site x ^ 2) ≤
      ∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * capWeight x * gaussianFeature c site x ^ 2 := by
  have hK := (finiteGaussian_weighted_energy_convergence c site (11 / 2 : ℝ) (by norm_num)).2.1
  have hQ := (finiteGaussian_capWeight_integral c site).1
  have hsplit : (fun x : ℝ => x ^ (7 / 2 : ℝ) * compactDebit x *
      gaussianFeature c site x ^ 2) =
      (Ioo (0 : ℝ) 6).indicator (fun x : ℝ =>
        (1 / 10 : ℝ) * (x ^ (11 / 2 : ℝ) * gaussianFeature c site x ^ 2) -
          x ^ (7 / 2 : ℝ) * capWeight x * gaussianFeature c site x ^ 2) := by
    funext x
    by_cases hx : 0 < x ∧ x < 6
    · rw [indicator_of_mem (s := Ioo (0 : ℝ) 6) hx, compactDebit, if_pos hx,
        ← positive_weight_two x hx.1]
      ring
    · simp [compactDebit, hx]
  have hD : IntegrableOn (fun x : ℝ => x ^ (7 / 2 : ℝ) * compactDebit x *
      gaussianFeature c site x ^ 2) (Ioi 0) := by
    rw [hsplit]
    exact ((hK.const_mul (1 / 10 : ℝ)).sub hQ).indicator measurableSet_Ioo
  refine ⟨hD, ?_⟩
  have hle := integral_mono_ae ((hK.const_mul (1 / 10 : ℝ)).sub hD) hQ
    (show ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      (1 / 10 : ℝ) * (x ^ (11 / 2 : ℝ) * gaussianFeature c site x ^ 2) -
        x ^ (7 / 2 : ℝ) * compactDebit x * gaussianFeature c site x ^ 2 ≤
      x ^ (7 / 2 : ℝ) * capWeight x * gaussianFeature c site x ^ 2 from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hm := mul_le_mul_of_nonneg_right
        (capWeight_ge_quadratic_minus_compact x hx.le)
        (mul_nonneg (Real.rpow_nonneg hx.le (7 / 2 : ℝ)) (sq_nonneg (gaussianFeature c site x)))
      calc
        (1 / 10 : ℝ) * (x ^ (11 / 2 : ℝ) * gaussianFeature c site x ^ 2) -
            x ^ (7 / 2 : ℝ) * compactDebit x * gaussianFeature c site x ^ 2 =
            (x ^ 2 / 10 - compactDebit x) *
              (x ^ (7 / 2 : ℝ) * gaussianFeature c site x ^ 2) := by
          rw [← positive_weight_two x hx]
          ring
        _ ≤ capWeight x * (x ^ (7 / 2 : ℝ) * gaussianFeature c site x ^ 2) := hm
        _ = x ^ (7 / 2 : ℝ) * capWeight x * gaussianFeature c site x ^ 2 := by ring)
  rw [integral_sub' (hK.const_mul (1 / 10 : ℝ)) hD, integral_const_mul] at hle
  exact hle

/-- Conditional consumer of the still-required physical coercivity theorem.
Strictness and denominator positivity are supplied by the actual globally
nonzero Gaussian source. The coercivity premise is explicit. -/
theorem finiteGaussian_ratio_gt_nineteen_four_of_coercive {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (hF : gaussianFeature c site ≠ 0)
    (hQ : (3 / 4 : ℝ) * (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
      gaussianFeature c site x ^ 2) ≤
      ∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * capWeight x * gaussianFeature c site x ^ 2) :
    (19 / 4 : ℝ) <
      (∫ x in Ioi Real.pi, x ^ 6 * gaussianFeature c site x ^ 2) /
        (Real.pi ^ 6 * (∫ x in Ioi Real.pi, gaussianFeature c site x ^ 2)) := by
  let D := ∫ x in Ioi Real.pi, gaussianFeature c site x ^ 2
  let N := ∫ x in Ioi Real.pi, x ^ 6 * gaussianFeature c site x ^ 2
  let H := ∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * gaussianFeature c site x ^ 2
  have hs := finite_gaussian_strict_weighted_mass c site hF Real.pi (7 / 2 : ℝ)
    Real.pi_pos (by norm_num)
  change 0 < D ∧ Real.pi ^ (7 / 2 : ℝ) * D < H at hs
  rw [(finiteGaussian_capWeight_integral c site).2] at hQ
  change (3 / 4 : ℝ) * H ≤
    Real.pi ^ (-5 / 2 : ℝ) * N - 4 * Real.pi ^ (7 / 2 : ℝ) * D at hQ
  have hraw : (19 / 4 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * D <
      Real.pi ^ (-5 / 2 : ℝ) * N := by nlinarith [hs.2]
  have hsum : Real.pi ^ (5 / 2 : ℝ) * Real.pi ^ (7 / 2 : ℝ) = Real.pi ^ 6 := by
    rw [← Real.rpow_add Real.pi_pos]
    norm_num
  have hcancel : Real.pi ^ (5 / 2 : ℝ) * Real.pi ^ (-5 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add Real.pi_pos]
    norm_num
  have hnum : (19 / 4 : ℝ) * (Real.pi ^ 6 * D) < N := by
    calc
      (19 / 4 : ℝ) * (Real.pi ^ 6 * D) =
          Real.pi ^ (5 / 2 : ℝ) * ((19 / 4 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * D) := by
        rw [← hsum]
        ring
      _ < Real.pi ^ (5 / 2 : ℝ) * (Real.pi ^ (-5 / 2 : ℝ) * N) :=
        mul_lt_mul_of_pos_left hraw (Real.rpow_pos_of_pos Real.pi_pos _)
      _ = N := by rw [← mul_assoc, hcancel, one_mul]
  change (19 / 4 : ℝ) < N / (Real.pi ^ 6 * D)
  exact (lt_div_iff₀ (mul_pos (pow_pos Real.pi_pos 6) hs.1)).2 hnum

end FiniteGaussianCap475
