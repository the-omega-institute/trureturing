/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianCap475Uniform
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianCap475Uniform
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Uniform explicit physical comparison surplus for reflected mass-zero finite Gaussians. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianCap475
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4FiniteChargeBudget

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace FiniteGaussianCap475
open FiniteGaussianCap4
open FiniteGaussianCap4.LaguerreSevenHalf

/-- The original matrix margin controls the actual head norm, even when
the head is zero. The weights are the original literal certificate weights. -/
theorem finiteGaussian_actual_head_certificate_margin {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) :
    (123 / 125000000 : ℝ) *
      (∑ k ∈ Finset.range 16, finiteGaussianNormalizedCoefficient c site (2 * k) ^ 2) ≤
      rho * (∑ k ∈ Finset.range 16,
        (normalizedCentralMellin (2 * k) / normalizedCentralMellin 0) *
          finiteGaussianNormalizedCoefficient c site (2 * k)) ^ 2 -
      (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * compactDebit x *
        finiteGaussianPartialSum c site 32 x ^ 2) +
      (1 / 10 : ℝ) * jacobiPaidHead
        (fun k => finiteGaussianNormalizedCoefficient c site (2 * k)) -
      (23 / 20 : ℝ) *
        ∑ k ∈ Finset.range 16, finiteGaussianNormalizedCoefficient c site (2 * k) ^ 2 := by
  have hsym : Matrix.IsSymm (compactMomentMatrix : Matrix (Fin 16) (Fin 16) ℝ) :=
    Matrix.IsSymm.ext (fun i j => compactMomentMatrix_symm j i)
  have hentry (i j : Fin 16) :
      |compactMomentMatrix i j - Cap4FiniteCertificate.center i j| ≤
        Cap4FinitePerturbation.delta := by
    simpa only [Cap4FinitePerturbation.delta] using (compactMomentMatrix_bounds i j).le
  have h := Cap4FinitePerturbation.perturbed_energy_lower
    compactMomentMatrix hsym hentry (actualCentralHeadCoordinates c site)
  rw [Cap4FinitePerturbation.exact_margin] at h
  have hnorm :
      (∑ k ∈ Finset.range 16, finiteGaussianNormalizedCoefficient c site (2 * k) ^ 2) ≤
      ∑ i : Fin 16, actualCentralHeadCoordinates c site i ^ 2 := by
    simpa only [actualCentralHeadCoordinates, actualMellinScale] using
      actual_head_norm_le_coordinates
        (fun k => finiteGaussianNormalizedCoefficient c site (2 * k))
  have hmargin := (mul_le_mul_of_nonneg_left hnorm
    (by norm_num : (0 : ℝ) ≤ 123 / 125000000)).trans h
  have hrho : Cap4FinitePerturbation.rho = rho := by
    norm_num [Cap4FinitePerturbation.rho, Cap4FiniteCertificate.rhoQ, rho]
  dsimp only [Cap4FinitePerturbation.energy] at hmargin
  rw [hrho,
    ← actual_head_charge_coordinates c site,
    ← finiteGaussianPrefix_compact_quadratic c site reflection hc hs,
    ← actual_jacobiPaidHead_coordinates c site,
    ← actual_head_norm_coordinates c site] at hmargin
  exact hmargin

/-- A fixed part of the complete-tail slack converts the original head
margin into a uniform physical surplus. Every source has the same 10^-9. -/
theorem finiteGaussian_cap475_uniform_coercivity {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i)
    (hmass : ∑ i, c i = 0) :
    ((3 / 4 : ℝ) + 1 / 1000000000) *
      (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * gaussianFeature c site x ^ 2) ≤
      ∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * capWeight x * gaussianFeature c site x ^ 2 := by
  let d (k : ℕ) := finiteGaussianNormalizedCoefficient c site (2 * k)
  let HH := ∑ k ∈ Finset.range 16, d k ^ 2
  let HT := ∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
    (gaussianFeature c site x - finiteGaussianPartialSum c site 32 x) ^ 2
  let q := ∑ k ∈ Finset.range 16, actualMellinScale k * d k
  let E := ∑' n : ℕ, tailH (16 + n : ℕ) * d (16 + n) ^ 2
  let S := ∑' n : ℕ, (2 * (16 + n : ℕ) + 9 / 4 : ℝ) ^ 2 * d (16 + n) ^ 2
  let B := jacobiPaidHead d
  let VH := ∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * compactDebit x *
    finiteGaussianPartialSum c site 32 x ^ 2
  let VF := ∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * compactDebit x * gaussianFeature c site x ^ 2
  let K := ∫ x in Ioi (0 : ℝ), x ^ (11 / 2 : ℝ) * gaussianFeature c site x ^ 2
  let Q := ∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * capWeight x * gaussianFeature c site x ^ 2
  have hquad : (1 / 10 : ℝ) * K - VF ≤ Q :=
    (finiteGaussian_capWeight_quadratic_lower c site).2
  have hpayment : -VH - (2 / 5 : ℝ) * HH - 44 * HT ≤ -VF := by
    have h := finiteGaussian_compact_head_tail_payment c site
    rw [finiteGaussian_actual_head_norm c site reflection hc hs] at h
    exact h
  have hboundary : B + S ≤ K :=
    finiteGaussian_actual_boundary_payment c site reflection hc hs
  have hcharge : rho * q ^ 2 ≤ E := by
    have h := finiteGaussian_actual_complete_tail_charge c site
    rw [finiteGaussian_actual_zero_tail_charge c site hmass, neg_sq] at h
    exact h
  have hlarge : 70 * HT ≤ E :=
    finiteGaussian_actual_tailH_seventy_norm c site reflection hc hs
  have hheadcharge : rho * q ^ 2 ≤ 3200 * HH := actual_head_charge_budget d
  have hmargin : (123 / 125000000 : ℝ) * HH ≤
      rho * q ^ 2 - VH + (1 / 10 : ℝ) * B - (23 / 20 : ℝ) * HH :=
    finiteGaussian_actual_head_certificate_margin c site reflection hc hs
  have hbudget : E = (1 / 10 : ℝ) * S - (179 / 4 : ℝ) * HT :=
    finiteGaussian_actual_tailH_budget c site reflection hc hs
  have hHH : 0 ≤ HH := Finset.sum_nonneg (fun k _ => sq_nonneg (d k))
  have hHT : 0 ≤ HT := by
    have h := (finiteGaussian_actual_remainder_norm c site reflection hc hs 16).2
    have hn : 0 ≤ ∑' n : ℕ,
        finiteGaussianNormalizedCoefficient c site (2 * (16 + n)) ^ 2 :=
      tsum_nonneg (fun n => sq_nonneg _)
    rw [h.tsum_eq] at hn
    exact hn
  have hmixed : (1 / 10000000000 : ℝ) * (70 * HT - 3200 * HH) ≤ E - rho * q ^ 2 := by
    linarith only [hcharge, hlarge, hheadcharge]
  have hgap : (123 / 125000000 : ℝ) * HH +
      (1 / 10000000000 : ℝ) * (70 * HT - 3200 * HH) ≤
      Q - (3 / 4 : ℝ) * (HH + HT) := by
    linarith only [hquad, hpayment, hboundary, hmargin, hmixed, hbudget]
  have hsurplus : (1 / 1000000000 : ℝ) * (HH + HT) ≤
      (123 / 125000000 : ℝ) * HH +
        (1 / 10000000000 : ℝ) * (70 * HT - 3200 * HH) := by
    linarith only [hHH, hHT]
  rw [finiteGaussian_actual_head_tail_norm c site reflection hc hs]
  change ((3 / 4 : ℝ) + 1 / 1000000000) * (HH + HT) ≤ Q
  linarith only [hgap, hsurplus]

/-- The original physical quotient has the same explicit surplus for all
globally nonzero reflected zero-mass finite real Gaussian sources. -/
theorem finiteGaussian_cap475_uniform_ratio {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i)
    (hmass : ∑ i, c i = 0) (hF : gaussianFeature c site ≠ 0) :
    ((19 / 4 : ℝ) + 1 / 1000000000) <
      (∫ x in Ioi Real.pi, x ^ 6 * gaussianFeature c site x ^ 2) /
        (Real.pi ^ 6 * (∫ x in Ioi Real.pi, gaussianFeature c site x ^ 2)) := by
  let D := ∫ x in Ioi Real.pi, gaussianFeature c site x ^ 2
  let N := ∫ x in Ioi Real.pi, x ^ 6 * gaussianFeature c site x ^ 2
  let H := ∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * gaussianFeature c site x ^ 2
  have hstrict := finite_gaussian_strict_weighted_mass c site hF Real.pi (7 / 2 : ℝ)
    Real.pi_pos (by norm_num)
  change 0 < D ∧ Real.pi ^ (7 / 2 : ℝ) * D < H at hstrict
  have hQ := finiteGaussian_cap475_uniform_coercivity c site reflection hc hs hmass
  rw [(finiteGaussian_capWeight_integral c site).2] at hQ
  change ((3 / 4 : ℝ) + 1 / 1000000000) * H ≤
    Real.pi ^ (-5 / 2 : ℝ) * N - 4 * Real.pi ^ (7 / 2 : ℝ) * D at hQ
  have hraw : ((19 / 4 : ℝ) + 1 / 1000000000) * Real.pi ^ (7 / 2 : ℝ) * D <
      Real.pi ^ (-5 / 2 : ℝ) * N := by linarith only [hstrict.2, hQ]
  have hsum : Real.pi ^ (5 / 2 : ℝ) * Real.pi ^ (7 / 2 : ℝ) = Real.pi ^ 6 := by
    rw [← Real.rpow_add Real.pi_pos]
    norm_num
  have hcancel : Real.pi ^ (5 / 2 : ℝ) * Real.pi ^ (-5 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add Real.pi_pos]
    norm_num
  have hnum : ((19 / 4 : ℝ) + 1 / 1000000000) * (Real.pi ^ 6 * D) < N := by
    calc
      ((19 / 4 : ℝ) + 1 / 1000000000) * (Real.pi ^ 6 * D) =
          Real.pi ^ (5 / 2 : ℝ) *
            (((19 / 4 : ℝ) + 1 / 1000000000) * Real.pi ^ (7 / 2 : ℝ) * D) := by
        rw [← hsum]
        ring
      _ < Real.pi ^ (5 / 2 : ℝ) * (Real.pi ^ (-5 / 2 : ℝ) * N) :=
        mul_lt_mul_of_pos_left hraw (Real.rpow_pos_of_pos Real.pi_pos _)
      _ = N := by rw [← mul_assoc, hcancel, one_mul]
  change ((19 / 4 : ℝ) + 1 / 1000000000) < N / (Real.pi ^ 6 * D)
  exact (lt_div_iff₀ (mul_pos (pow_pos Real.pi_pos 6) hstrict.1)).2 hnum

end FiniteGaussianCap475
