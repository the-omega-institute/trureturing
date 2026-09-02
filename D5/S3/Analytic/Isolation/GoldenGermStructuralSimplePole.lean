/- GID: D5/S3/Analytic/Isolation/GoldenGermStructuralSimplePole
   generality: I
   mirror-B: D5/B/S3/Analytic/Isolation/GoldenGermStructuralSimplePole
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The second-order golden germ has a genuine simple structural pole. -/

/- Library-search audit trail (2026-09-03):
   * Repository search found the exact signed factor formula in
     `golden_germ_second_order_factorization`, the removable zeta-pole normal
     form in `golden_germ_zeta_simple_pole`, the regular and nonzero second
     normalized factor in `golden_germ_second_normalized_factor_regularity`,
     and the needed exceptional-strip value in
     `riemannZeta_golden_auxiliary_ne_zero`.
   * The factorization theorem exposes its continuation only under `ExistsUnique`.
     Consequently the total function below uses that frozen theorem's displayed
     factor formula at the definition level; no dead wrapper pretends that the
     existential theorem exposes a reusable named continuation. The first-order
     theorem similarly supplies the already-kernel-checked proof architecture,
     while its removable extension lemmas are private, so the same Mathlib
     residue construction is instantiated here for the `phi^3` transport.
   * Pinned Mathlib supplies `riemannZeta_residue_one`,
     `riemannZeta_ne_zero_of_one_le_re`,
     `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`,
     `meromorphicOrderAt_eq_int_iff`, and
     `tendsto_cobounded_iff_meromorphicOrderAt_neg`.

   STOPPING JUSTIFICATION: this node identifies the second extracted zeta
   factor as a genuine simple pole at `1 / phi^3`. It proves only the stated
   local meromorphy, exact order, and punctured-neighborhood blow-up. It says
   nothing about other points or zeros, and it implies neither O-5 nor RH. -/

import D5.S3.Analytic.EulerGerm.GoldenGermSecondOrderFactorization
import D5.S3.Analytic.Isolation.GoldenGermZetaSimplePole
import D5.S3.Analytic.Regularity.GoldenGermSecondNormalizedFactorRegularity
import D5.S3.Analytic.Isolation.GoldenAuxiliaryZetaNonzero

namespace D5.S3.Analytic.Isolation.GoldenGermStructuralSimplePole

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Complex Function
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GoldenGermSecondOrderFactorization
open D5.S3.Analytic.Isolation.GoldenGermZetaSimplePole
open D5.S3.Analytic.Regularity.GoldenGermSecondNormalizedFactorRegularity
open D5.S3.Analytic.Isolation.GoldenAuxiliaryZetaNonzero
open scoped Topology

private noncomputable def zk : ℂ → ℂ := fun s => (s - 1) * riemannZeta s

private noncomputable def zkA : ℂ → ℂ :=
  update zk 1 (limUnder (𝓝[≠] (1 : ℂ)) zk)

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

private noncomputable def resid : ℂ → ℂ := fun s =>
  zkA (phiCub * s) * (regularMultiplier s / phiCub)

private noncomputable def structuralGerm : ℂ → ℂ := fun s =>
  riemannZeta (phiSq * s) * riemannZeta (phiCub * s) *
    (riemannZeta (doublePhiSq * s))⁻¹ * secondG s

private theorem u0_phiCub_ne : phiCub ≠ 0 := by
  rw [phiCub]
  exact_mod_cast (by positivity : (Real.goldenRatio ^ 3 : ℝ) ≠ 0)

private theorem u1_pole_transport : phiCub * aPt = 1 := by
  have hne : (Real.goldenRatio ^ 3 : ℝ) ≠ 0 := by positivity
  rw [phiCub, aPt, ← Complex.ofReal_mul, mul_one_div, div_self hne,
    Complex.ofReal_one]

private theorem u2_aux_transport :
    phiSq * aPt = ((1 / Real.goldenRatio : ℝ) : ℂ) := by
  rw [phiSq, aPt, ← Complex.ofReal_mul]
  congr 1
  field_simp [Real.goldenRatio_ne_zero]

private theorem u3_double_transport :
    doublePhiSq * aPt = ((2 / Real.goldenRatio : ℝ) : ℂ) := by
  rw [doublePhiSq, aPt, ← Complex.ofReal_mul]
  congr 1
  field_simp [Real.goldenRatio_ne_zero]

private theorem u4_one_lt_double_aux :
    (1 : ℝ) < 2 / Real.goldenRatio := by
  exact (lt_div_iff₀ Real.goldenRatio_pos).2 (by
    simpa using Real.goldenRatio_lt_two)

private theorem u5_aux_ne_one :
    ((1 / Real.goldenRatio : ℝ) : ℂ) ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.ofReal_re, one_re] at hre
  have hlt : (1 / Real.goldenRatio : ℝ) < 1 := by
    simpa only [one_div] using
      (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
  linarith

private theorem u6_double_aux_ne_one :
    ((2 / Real.goldenRatio : ℝ) : ℂ) ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.ofReal_re, one_re] at hre
  linarith [u4_one_lt_double_aux]

private theorem u7_fourth_threshold :
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

private theorem u8_zkA_at_one : zkA 1 = 1 := by
  rw [zkA, update_self]
  exact riemannZeta_residue_one.limUnder_eq

private theorem t1_zkA_analytic : AnalyticAt ℂ zkA 1 := by
  have hd : DifferentiableOn ℂ zkA (Metric.ball (1 : ℂ) 1) := by
    refine differentiableOn_update_limUnder_of_isLittleO
      (Metric.ball_mem_nhds (1 : ℂ) one_pos) ?_ ?_
    · intro z hz
      exact (((differentiable_id.sub_const 1).differentiableAt).mul
        (differentiableAt_riemannZeta (by simpa using hz.2))).differentiableWithinAt
    · exact (((riemannZeta_residue_one.sub_const (zk 1)).norm).isBoundedUnder_le
        ).isLittleO_sub_self_inv
  exact hd.analyticAt (Metric.ball_mem_nhds (1 : ℂ) one_pos)

private theorem t2_secondG_analytic : AnalyticAt ℂ secondG aPt := by
  have hregularity := golden_germ_second_normalized_factor_regularity
  dsimp only at hregularity
  have h := hregularity.1 aPt (by
    change 1 / Real.goldenRatio ^ 4 < 1 / Real.goldenRatio ^ 3
    exact u7_fourth_threshold)
  change AnalyticAt ℂ (fun s : ℂ =>
    ∏' p : Nat.Primes,
      (1 - (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))) *
        (1 + (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)))⁻¹ *
        germLocalFactor s p) aPt
  exact h

private theorem u9_aux_zeta_ne_zero :
    riemannZeta (phiSq * aPt) ≠ 0 := by
  rw [u2_aux_transport]
  exact riemannZeta_golden_auxiliary_ne_zero

private theorem u10_double_zeta_ne_zero :
    riemannZeta (doublePhiSq * aPt) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_le_re
  rw [u3_double_transport]
  change (1 : ℝ) ≤ 2 / Real.goldenRatio
  exact u4_one_lt_double_aux.le

private theorem u11_secondG_ne_zero : secondG aPt ≠ 0 := by
  have hregularity := golden_germ_second_normalized_factor_regularity
  dsimp only at hregularity
  change (∏' p : Nat.Primes,
    (1 - (p : ℂ) ^
        (-((1 / Real.goldenRatio ^ 3 : ℝ) : ℂ) *
          ((Real.goldenRatio ^ 3 : ℝ) : ℂ))) *
      (1 + (p : ℂ) ^
        (-((1 / Real.goldenRatio ^ 3 : ℝ) : ℂ) *
          ((Real.goldenRatio ^ 2 : ℝ) : ℂ)))⁻¹ *
      germLocalFactor ((1 / Real.goldenRatio ^ 3 : ℝ) : ℂ) p) ≠ 0
  exact hregularity.2.2

private theorem t3_regular_analytic : AnalyticAt ℂ regularMultiplier aPt := by
  have hSqOuter : AnalyticAt ℂ riemannZeta (phiSq * aPt) :=
    analyticOn_riemannZeta _ (by
      rw [u2_aux_transport]
      exact u5_aux_ne_one)
  have hSqInner : AnalyticAt ℂ (fun s : ℂ => phiSq * s) aPt :=
    analyticAt_const.mul analyticAt_id
  have hDoubleOuter : AnalyticAt ℂ riemannZeta (doublePhiSq * aPt) :=
    analyticOn_riemannZeta _ (by
      rw [u3_double_transport]
      exact u6_double_aux_ne_one)
  have hDoubleInner : AnalyticAt ℂ (fun s : ℂ => doublePhiSq * s) aPt :=
    analyticAt_const.mul analyticAt_id
  have hSq := hSqOuter.comp hSqInner
  have hDouble := (hDoubleOuter.comp hDoubleInner).inv u10_double_zeta_ne_zero
  exact (hSq.mul hDouble).mul t2_secondG_analytic

private theorem u12_regular_ne_zero : regularMultiplier aPt ≠ 0 := by
  rw [regularMultiplier]
  exact mul_ne_zero (mul_ne_zero u9_aux_zeta_ne_zero
    (inv_ne_zero u10_double_zeta_ne_zero)) u11_secondG_ne_zero

private theorem t4_resid_analytic : AnalyticAt ℂ resid aPt := by
  have hOuter : AnalyticAt ℂ zkA (phiCub * aPt) := by
    rw [u1_pole_transport]
    exact t1_zkA_analytic
  have hInner : AnalyticAt ℂ (fun s : ℂ => phiCub * s) aPt :=
    analyticAt_const.mul analyticAt_id
  exact (hOuter.comp hInner).mul
    (t3_regular_analytic.div analyticAt_const u0_phiCub_ne)

private theorem u13_resid_ne_zero : resid aPt ≠ 0 := by
  have h : resid aPt = regularMultiplier aPt / phiCub := by
    rw [resid, u1_pole_transport, u8_zkA_at_one, one_mul]
  rw [h]
  exact div_ne_zero u12_regular_ne_zero u0_phiCub_ne

private theorem t5_punctured :
    ∀ᶠ s in 𝓝[≠] aPt,
      structuralGerm s = (s - aPt) ^ (-1 : ℤ) • resid s := by
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsa : s - aPt ≠ 0 := sub_ne_zero.mpr hs
  have hne1 : phiCub * s ≠ 1 := by
    rw [← u1_pole_transport]
    intro hc
    exact hsa (sub_eq_zero.mpr (mul_left_cancel₀ u0_phiCub_ne hc))
  have hzk : zkA (phiCub * s) =
      (phiCub * s - 1) * riemannZeta (phiCub * s) := by
    rw [zkA, update_of_ne hne1, zk]
  have hfac : phiCub * s - 1 = phiCub * (s - aPt) := by
    rw [mul_sub, u1_pole_transport]
  rw [structuralGerm, resid, regularMultiplier, hzk, hfac, zpow_neg,
    zpow_one, smul_eq_mul]
  field_simp [u0_phiCub_ne]

private theorem v1_meromorphic : MeromorphicAt structuralGerm aPt :=
  MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr
    ⟨(-1 : ℤ), resid, t4_resid_analytic, t5_punctured⟩

private theorem v2_simple_pole :
    meromorphicOrderAt structuralGerm aPt = (-1 : ℤ) :=
  (meromorphicOrderAt_eq_int_iff v1_meromorphic).mpr
    ⟨resid, t4_resid_analytic, u13_resid_ne_zero, t5_punctured⟩

private theorem v3_blows_up :
    Tendsto structuralGerm (𝓝[≠] aPt) (Bornology.cobounded ℂ) := by
  rw [tendsto_cobounded_iff_meromorphicOrderAt_neg v1_meromorphic,
    v2_simple_pole]
  decide

/-- The second-order continued golden germ has a genuine simple pole at
`1 / phi^3` and tends to the cobounded filter on its punctured neighborhood. -/
theorem golden_germ_structural_simple_pole :
    let H : ℂ → ℂ := fun s =>
      ∏' p : Nat.Primes,
        (1 - (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))) *
          (1 + (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)))⁻¹ *
          germLocalFactor s p
    let F : ℂ → ℂ := fun s =>
      riemannZeta (((Real.goldenRatio ^ 2 : ℝ) : ℂ) * s) *
        riemannZeta (((Real.goldenRatio ^ 3 : ℝ) : ℂ) * s) *
        (riemannZeta (((2 * Real.goldenRatio ^ 2 : ℝ) : ℂ) * s))⁻¹ * H s
    MeromorphicAt F ((1 / Real.goldenRatio ^ 3 : ℝ) : ℂ) ∧
      meromorphicOrderAt F
          ((1 / Real.goldenRatio ^ 3 : ℝ) : ℂ) = (-1 : ℤ) ∧
        Tendsto F
          (𝓝[≠] ((1 / Real.goldenRatio ^ 3 : ℝ) : ℂ))
          (Bornology.cobounded ℂ) := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  dsimp only
  exact ⟨v1_meromorphic, v2_simple_pole, v3_blows_up⟩

#print axioms golden_germ_structural_simple_pole

end D5.S3.Analytic.Isolation.GoldenGermStructuralSimplePole
