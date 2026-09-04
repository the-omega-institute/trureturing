/- GID: D5/S3/Analytic/Isolation/GoldenGermSecondOrderStructuralResidue
   generality: I
   mirror-B: D5/B/S3/Analytic/Isolation/GoldenGermSecondOrderStructuralResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The second-order golden germ has its explicit structural residue. -/

/- Library-search audit trail (2026-09-03):
   * Exact `#check` probes confirmed the frozen public declarations
     `golden_germ_second_order_factorization`,
     `golden_germ_second_normalized_factor_regularity`,
     `riemannZeta_golden_auxiliary_ne_zero`, and
     `golden_germ_structural_simple_pole` on the pinned toolchain.
   * The factorization exposes its continuation only under `ExistsUnique`.
     Accordingly this module reuses its displayed factor formula at the
     definition level, as does the frozen structural-pole module; it does not
     introduce a dead wrapper pretending that the continuation is named.
   * Repository search found the first-boundary residue proof in
     `GoldenGermZetaResidue`, but no residue formula at `1 / phi^3`. Pinned
     Mathlib supplies `riemannZeta_residue_one`, `analyticOn_riemannZeta`,
     `riemannZeta_ne_zero_of_one_le_re`, and the `Tendsto` product rules.

   STOPPING JUSTIFICATION: this theorem computes only the local residue of the
   second-order continued germ at `1 / phi^3`, and records that this displayed
   residue is nonzero. It makes no assertion about other points or zeros and
   implies neither O-5 nor the Riemann hypothesis. -/

import D5.S3.Analytic.EulerGerm.GoldenGermSecondOrderFactorization
import D5.S3.Analytic.Regularity.GoldenGermSecondNormalizedFactorRegularity
import D5.S3.Analytic.Isolation.GoldenAuxiliaryZetaNonzero
import D5.S3.Analytic.Isolation.GoldenGermStructuralSimplePole

namespace D5.S3.Analytic.Isolation.GoldenGermSecondOrderStructuralResidue

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Complex
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.Regularity.GoldenGermSecondNormalizedFactorRegularity
open D5.S3.Analytic.Isolation.GoldenAuxiliaryZetaNonzero
open D5.S3.Analytic.Isolation.GoldenGermStructuralSimplePole
open scoped Topology

noncomputable section

private noncomputable def aPt : ℂ :=
  ((1 / Real.goldenRatio ^ 3 : ℝ) : ℂ)

private noncomputable def phiSq : ℂ :=
  ((Real.goldenRatio ^ 2 : ℝ) : ℂ)

private noncomputable def phiCub : ℂ :=
  ((Real.goldenRatio ^ 3 : ℝ) : ℂ)

private noncomputable def doublePhiSq : ℂ :=
  ((2 * Real.goldenRatio ^ 2 : ℝ) : ℂ)

private noncomputable def secondG : ℂ → ℂ := fun s =>
  ∏' p : Nat.Primes,
    (1 - (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))) *
      (1 + (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)))⁻¹ *
      germLocalFactor s p

private noncomputable def regularMultiplier : ℂ → ℂ := fun s =>
  riemannZeta (phiSq * s) * (riemannZeta (doublePhiSq * s))⁻¹ * secondG s

private noncomputable def structuralGerm : ℂ → ℂ := fun s =>
  riemannZeta (phiSq * s) * riemannZeta (phiCub * s) *
    (riemannZeta (doublePhiSq * s))⁻¹ * secondG s

private noncomputable def explicitResidue : ℂ :=
  riemannZeta (((1 / Real.goldenRatio : ℝ) : ℂ)) *
    (riemannZeta (((2 / Real.goldenRatio : ℝ) : ℂ)))⁻¹ *
    secondG aPt / phiCub

private theorem phiCub_ne_zero : phiCub ≠ 0 := by
  rw [phiCub]
  exact_mod_cast (pow_ne_zero 3 Real.goldenRatio_ne_zero)

private theorem pole_transport : phiCub * aPt = 1 := by
  have hne : (Real.goldenRatio ^ 3 : ℝ) ≠ 0 := by positivity
  rw [phiCub, aPt, ← Complex.ofReal_mul, mul_one_div, div_self hne,
    Complex.ofReal_one]

private theorem auxiliary_transport :
    phiSq * aPt = ((1 / Real.goldenRatio : ℝ) : ℂ) := by
  rw [phiSq, aPt, ← Complex.ofReal_mul]
  congr 1
  field_simp [Real.goldenRatio_ne_zero]

private theorem double_auxiliary_transport :
    doublePhiSq * aPt = ((2 / Real.goldenRatio : ℝ) : ℂ) := by
  rw [doublePhiSq, aPt, ← Complex.ofReal_mul]
  congr 1
  field_simp [Real.goldenRatio_ne_zero]

private theorem structural_numeric_check :
    (0 : ℝ) < 1 / Real.goldenRatio ^ 3 ∧
      (1 : ℝ) < 2 / Real.goldenRatio := by
  constructor
  · positivity
  · exact (lt_div_iff₀ Real.goldenRatio_pos).2 (by
      simpa using Real.goldenRatio_lt_two)

private theorem auxiliary_ne_one :
    ((1 / Real.goldenRatio : ℝ) : ℂ) ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.ofReal_re, one_re] at hre
  have hlt : (1 / Real.goldenRatio : ℝ) < 1 := by
    simpa only [one_div] using
      (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
  linarith

private theorem double_auxiliary_ne_one :
    ((2 / Real.goldenRatio : ℝ) : ℂ) ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.ofReal_re, one_re] at hre
  linarith [structural_numeric_check.2]

private theorem fourth_threshold_lt_structural :
    1 / Real.goldenRatio ^ 4 < 1 / Real.goldenRatio ^ 3 := by
  have hphi3 : 0 < Real.goldenRatio ^ 3 := by positivity
  have hphi3_lt_phi4 :
      Real.goldenRatio ^ 3 < Real.goldenRatio ^ 4 := by
    calc
      Real.goldenRatio ^ 3 <
          Real.goldenRatio ^ 3 * Real.goldenRatio :=
        (lt_mul_iff_one_lt_right hphi3).mpr Real.one_lt_goldenRatio
      _ = Real.goldenRatio ^ 4 := by ring
  exact one_div_lt_one_div_of_lt hphi3 hphi3_lt_phi4

private theorem auxiliary_zeta_ne_zero :
    riemannZeta (phiSq * aPt) ≠ 0 := by
  rw [auxiliary_transport]
  exact riemannZeta_golden_auxiliary_ne_zero

private theorem double_auxiliary_zeta_ne_zero :
    riemannZeta (doublePhiSq * aPt) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_le_re
  rw [double_auxiliary_transport]
  change (1 : ℝ) ≤ 2 / Real.goldenRatio
  exact structural_numeric_check.2.le

private theorem secondG_analytic : AnalyticAt ℂ secondG aPt := by
  have hregularity := golden_germ_second_normalized_factor_regularity
  dsimp only at hregularity
  have h := hregularity.1 aPt (by
    change 1 / Real.goldenRatio ^ 4 < 1 / Real.goldenRatio ^ 3
    exact fourth_threshold_lt_structural)
  change AnalyticAt ℂ secondG aPt at h
  exact h

private theorem secondG_ne_zero : secondG aPt ≠ 0 := by
  have hregularity := golden_germ_second_normalized_factor_regularity
  dsimp only at hregularity
  change secondG aPt ≠ 0
  exact hregularity.2.2

private theorem regular_multiplier_continuous :
    ContinuousAt regularMultiplier aPt := by
  have hSqOuter : AnalyticAt ℂ riemannZeta (phiSq * aPt) :=
    analyticOn_riemannZeta _ (by
      rw [auxiliary_transport]
      exact auxiliary_ne_one)
  have hSqInner : AnalyticAt ℂ (fun s : ℂ => phiSq * s) aPt :=
    analyticAt_const.mul analyticAt_id
  have hDoubleOuter : AnalyticAt ℂ riemannZeta (doublePhiSq * aPt) :=
    analyticOn_riemannZeta _ (by
      rw [double_auxiliary_transport]
      exact double_auxiliary_ne_one)
  have hDoubleInner : AnalyticAt ℂ (fun s : ℂ => doublePhiSq * s) aPt :=
    analyticAt_const.mul analyticAt_id
  have hSq := hSqOuter.comp hSqInner
  have hDouble := (hDoubleOuter.comp hDoubleInner).inv
    double_auxiliary_zeta_ne_zero
  exact ((hSq.mul hDouble).mul secondG_analytic).continuousAt

private theorem transported_zeta_residue :
    Tendsto (fun s : ℂ =>
      (phiCub * s - 1) * riemannZeta (phiCub * s))
      (𝓝[≠] aPt) (𝓝 1) := by
  have hscale : Tendsto (fun s : ℂ => phiCub * s)
      (𝓝[≠] aPt) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun s : ℂ => phiCub * s) :=
        continuous_const.mul continuous_id
      have hcAt : Tendsto (fun s : ℂ => phiCub * s)
          (𝓝 aPt) (𝓝 1) := by
        have hcT := hc.tendsto aPt
        rw [pole_transport] at hcT
        exact hcT
      exact hcAt.mono_left inf_le_left
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro h
      apply hs
      apply mul_left_cancel₀ phiCub_ne_zero
      rw [h, pole_transport]
  exact riemannZeta_residue_one.comp hscale

private theorem explicit_residue_limit :
    Tendsto (fun s : ℂ => (s - aPt) * structuralGerm s)
      (𝓝[≠] aPt) (𝓝 explicitResidue) := by
  have hregular : Tendsto (fun s : ℂ => regularMultiplier s / phiCub)
      (𝓝[≠] aPt) (𝓝 (regularMultiplier aPt / phiCub)) := by
    exact (regular_multiplier_continuous.tendsto.div_const phiCub).mono_left
      inf_le_left
  have hproduct := transported_zeta_residue.mul hregular
  have hrewritten :
      Tendsto (fun s : ℂ => (s - aPt) * structuralGerm s)
        (𝓝[≠] aPt) (𝓝 (1 * (regularMultiplier aPt / phiCub))) := by
    refine hproduct.congr' ?_
    filter_upwards with s
    have hlinear : phiCub * s - 1 = phiCub * (s - aPt) := by
      rw [mul_sub, pole_transport]
    rw [structuralGerm, regularMultiplier, hlinear]
    field_simp [phiCub_ne_zero]
  have hvalue : regularMultiplier aPt / phiCub = explicitResidue := by
    rw [regularMultiplier, explicitResidue, auxiliary_transport,
      double_auxiliary_transport]
  simpa only [one_mul, hvalue] using hrewritten

private theorem explicit_residue_ne_zero : explicitResidue ≠ 0 := by
  rw [explicitResidue]
  exact div_ne_zero
    (mul_ne_zero
      (mul_ne_zero riemannZeta_golden_auxiliary_ne_zero
        (inv_ne_zero (by
          simpa only [double_auxiliary_transport] using
            double_auxiliary_zeta_ne_zero)))
      secondG_ne_zero)
    phiCub_ne_zero

/-- At `a = 1 / phi^3`, the explicit second-order continued golden germ has
meromorphic order minus one and residue
`zeta(1 / phi) * zeta(2 / phi)⁻¹ * H(a) / phi^3`. The residue is nonzero. -/
theorem golden_germ_second_order_structural_residue :
    let H : ℂ → ℂ := fun s =>
      ∏' p : Nat.Primes,
        (1 - (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))) *
          (1 + (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)))⁻¹ *
          germLocalFactor s p
    let F2 : ℂ → ℂ := fun s =>
      riemannZeta (((Real.goldenRatio ^ 2 : ℝ) : ℂ) * s) *
        riemannZeta (((Real.goldenRatio ^ 3 : ℝ) : ℂ) * s) *
        (riemannZeta (((2 * Real.goldenRatio ^ 2 : ℝ) : ℂ) * s))⁻¹ * H s
    let a : ℂ := ((1 / Real.goldenRatio ^ 3 : ℝ) : ℂ)
    MeromorphicAt F2 a ∧
      meromorphicOrderAt F2 a = (-1 : ℤ) ∧
      Tendsto (fun s : ℂ => (s - a) * F2 s)
        (𝓝[≠] a)
        (𝓝 (riemannZeta (((1 / Real.goldenRatio : ℝ) : ℂ)) *
          (riemannZeta (((2 / Real.goldenRatio : ℝ) : ℂ)))⁻¹ * H a /
          ((Real.goldenRatio ^ 3 : ℝ) : ℂ))) ∧
      riemannZeta (((1 / Real.goldenRatio : ℝ) : ℂ)) *
          (riemannZeta (((2 / Real.goldenRatio : ℝ) : ℂ)))⁻¹ * H a /
          ((Real.goldenRatio ^ 3 : ℝ) : ℂ) ≠ 0 := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  dsimp only
  have hpole := golden_germ_structural_simple_pole
  dsimp only at hpole
  change MeromorphicAt structuralGerm aPt ∧
    meromorphicOrderAt structuralGerm aPt = (-1 : ℤ) ∧
    Tendsto (fun s : ℂ => (s - aPt) * structuralGerm s)
      (𝓝[≠] aPt) (𝓝 explicitResidue) ∧
    explicitResidue ≠ 0
  change MeromorphicAt structuralGerm aPt ∧
    meromorphicOrderAt structuralGerm aPt = (-1 : ℤ) ∧
    Tendsto structuralGerm (𝓝[≠] aPt) (Bornology.cobounded ℂ) at hpole
  exact ⟨hpole.1, hpole.2.1, explicit_residue_limit,
    explicit_residue_ne_zero⟩

#print axioms golden_germ_second_order_structural_residue

end

end D5.S3.Analytic.Isolation.GoldenGermSecondOrderStructuralResidue
