/- GID: D5/S3/Weil/ZetaPntBounds/MobiusBoundaryMixedScaleExclusion
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/MobiusBoundaryMixedScaleExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite critical Möbius energy excludes pairs of high zeta zeros with separate distance bounds. -/

import D5.S3.Weil.ZetaPntBounds.MobiusBoundaryClusterExclusion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Finite critical Möbius energy excludes mixed-scale pairs of high zeta zeros. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex Filter Function MeasureTheory Metric Set
open scoped Topology BigOperators
open D5.S3.Weil.Mertens.MobiusDyadicEnergy (mobiusDyadicDifference)
open D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundary
  (weighted_reciprocal_zeta_sq_bound_of_mobiusDyadicEnergy)
open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa zero_re_le_abscissa)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
  (exists_nontrivial_zero_re_ge_half)
open D5.S3.Weil.ZetaPntBounds.MobiusBoundaryClusterExclusion
  (analyticOnNhd_selectedZeroQuotient boundaryPoint boundaryDensity
    norm_riemannZeta_le_rpow_on_boundary_disks)
open Zeta23 (riemannZeta_analyticOnNhd_compl_one analyticOrderAt_riemannZeta_ne_top)

namespace D5.S3.Weil.ZetaPntBounds.MobiusBoundaryMixedScaleExclusion

private theorem prod_const_pow_selectedMultiplicity {U : Set ℂ}
    {D : Function.locallyFinsuppWithin U ℤ} (hFinite : D.support.Finite) (a : ℝ) :
    (∏ u ∈ hFinite.toFinset, a ^ (D u).toNat) = a ^ (∑ᶠ u, (D u).toNat) := by
  classical
  have hq : (∑ᶠ u, (D u).toNat) = ∑ u ∈ hFinite.toFinset, (D u).toNat := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    apply hFinite.mem_toFinset.mpr
    change D u ≠ 0
    change (D u).toNat ≠ 0 at hu
    exact fun hZero ↦ hu (by simp [hZero])
  rw [Finset.prod_pow_eq_pow_sum, hq]

/-- The local disk bound with one distance factor for each selected zero,
raised to its selected multiplicity. -/
private theorem norm_le_mul_prod_of_selectedZeroCluster {f : ℂ → ℂ} {c z : ℂ} {r R M : ℝ}
    {D : Function.locallyFinsuppWithin (Metric.closedBall c R) ℤ}
    (hr : r < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hNonneg : 0 ≤ D) (hLe : D ≤ MeromorphicOn.divisor f (Metric.closedBall c R))
    (hOrder : ∀ w ∈ Metric.closedBall c R, meromorphicOrderAt f w ≠ ⊤)
    (hCluster : D.support ⊆ Metric.closedBall c r)
    (hM : ∀ w ∈ Metric.sphere c R, ‖f w‖ ≤ M)
    (hz : z ∈ Metric.closedBall c R) :
    let s : Finset ℂ := (D.finiteSupport (isCompact_closedBall c R)).toFinset
    let q : ℕ := ∑ᶠ u, (D u).toNat
    ‖f z‖ ≤ (M / (R - r) ^ q) * (∏ u ∈ s, ‖z - u‖ ^ (D u).toNat) := by
  classical
  let q : ℕ := ∑ᶠ u, (D u).toNat
  have hFinite := D.finiteSupport (isCompact_closedBall c R)
  let s : Finset ℂ := hFinite.toFinset
  change ‖f z‖ ≤ (M / (R - r) ^ q) * (∏ u ∈ s, ‖z - u‖ ^ (D u).toNat)
  let P : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
  let Q := toMeromorphicNFOn (P⁻¹ • f) (Metric.closedBall c R)
  have hQuot :
      AnalyticOnNhd ℂ Q (Metric.closedBall c R) ∧
      ∀ w ∈ Metric.closedBall c R, w ∉ D.support → Q w = f w / P w :=
    analyticOnNhd_selectedZeroQuotient (D := D) hf hFinite hNonneg hLe hOrder
  obtain ⟨hQ, hQEq⟩ := hQuot
  have hRadius : 0 < R - r := sub_pos.mpr hr
  have hCenterDist {u : ℂ} (hu : u ∈ s) : dist u c ≤ r :=
    Metric.mem_closedBall.mp (hCluster (hFinite.mem_toFinset.mp hu))
  have hConstProd (a : ℝ) : (∏ u ∈ s, a ^ (D u).toNat) = a ^ q := by
    exact prod_const_pow_selectedMultiplicity hFinite a
  have hFactorSupport : (fun u : ℂ ↦ (· - u) ^ D u).mulSupport ⊆ (s : Set ℂ) := by
    rw [FactorizedRational.mulSupport (D : ℂ → ℤ)]
    exact fun _ hu ↦ hFinite.mem_toFinset.mpr hu
  have hNormProd (w : ℂ) : ‖P w‖ = ∏ u ∈ s, ‖w - u‖ ^ (D u).toNat := by
    unfold P
    rw [finprod_eq_prod_of_mulSupport_subset _ hFactorSupport, Finset.prod_apply, Complex.norm_prod]
    apply Finset.prod_congr rfl
    intro u _
    have hCast : ((D u).toNat : ℤ) = D u := Int.toNat_of_nonneg (hNonneg u)
    rw [Pi.pow_apply, Complex.norm_zpow, ← zpow_natCast, hCast]
  have hPLower (w : ℂ) (hw : w ∈ Metric.sphere c R) : (R - r) ^ q ≤ ‖P w‖ := by
    rw [hNormProd w, ← hConstProd (R - r)]
    refine Finset.prod_le_prod₀ (fun _ _ ↦ pow_nonneg hRadius.le _) ?_
    intro u hu
    apply pow_le_pow_left₀ hRadius.le
    have hTriangle := dist_triangle w u c
    rw [Metric.mem_sphere.mp hw, dist_eq_norm w u] at hTriangle
    exact sub_le_iff_le_add.mpr (hTriangle.trans (add_le_add le_rfl (hCenterDist hu)))
  have hQSphere (w : ℂ) (hw : w ∈ Metric.sphere c R) :
      ‖Q w‖ ≤ M / (R - r) ^ q := by
    have hwD : w ∉ D.support := by
      intro hwD
      have hDist := Metric.mem_closedBall.mp (hCluster hwD)
      rw [Metric.mem_sphere.mp hw] at hDist
      exact (not_le_of_gt (sub_pos.mp hRadius)) hDist
    have hMNonneg : 0 ≤ M := (norm_nonneg (f w)).trans (hM w hw)
    rw [hQEq w (Metric.sphere_subset_closedBall hw) hwD, Complex.norm_div]
    calc
      ‖f w‖ / ‖P w‖ ≤ M / ‖P w‖ := div_le_div_of_nonneg_right (hM w hw) (norm_nonneg _)
      _ ≤ M / (R - r) ^ q := div_le_div_of_nonneg_left hMNonneg (pow_pos hRadius _) (hPLower w hw)
  have hQz : ‖Q z‖ ≤ M / (R - r) ^ q := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le
      (U := Metric.closedBall c R) Metric.isBounded_closedBall ?_ ?_ (subset_closure hz)
    · apply DifferentiableOn.diffContOnCl
      rw [Metric.closure_closedBall]
      exact hQ.differentiableOn
    · intro w hw
      exact hQSphere w (Metric.frontier_closedBall_subset_sphere hw)
  by_cases hzD : z ∈ D.support
  · have hfz : f z = 0 := by
      by_contra hne
      have hord : meromorphicOrderAt f z = 0 :=
        (hf z hz).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hne
      have hDz : D z ≤ 0 := by
        have hDz := hLe z
        change D z ≤ MeromorphicOn.divisor f (Metric.closedBall c R) z at hDz
        rw [hf.meromorphicOn.divisor_apply hz, hord, WithTop.untop₀_zero] at hDz
        exact hDz
      exact (show D z ≠ 0 from hzD) (le_antisymm hDz (hNonneg z))
    rw [hfz, norm_zero]
    exact mul_nonneg ((norm_nonneg (Q z)).trans hQz)
      (Finset.prod_nonneg fun u _ ↦ pow_nonneg (norm_nonneg (z - u)) _)
  · have hPz : P z ≠ 0 :=
      FactorizedRational.ne_zero (d := (D : ℂ → ℤ)) (notMem_support.mp hzD)
    calc
      ‖f z‖ = ‖Q z‖ * ‖P z‖ := by
        rw [← Complex.norm_mul, hQEq z hz hzD, div_mul_cancel₀ _ hPz]
      _ ≤ (M / (R - r) ^ q) * ‖P z‖ :=
        mul_le_mul_of_nonneg_right hQz (norm_nonneg _)
      _ = _ := by rw [hNormProd z]

open scoped Classical in
/-- The open window around a selected zero's ordinate has radius equal to its
distance from the boundary line. Every other selected zero contributes its own
distance factor and multiplicity. -/
private theorem reciprocal_mass_lower_of_selectedZeroCluster_anchor {θ r R M : ℝ} {ρ : ℂ}
    {D : Function.locallyFinsuppWithin
      (Metric.closedBall ((θ : ℂ) + (ρ.im : ℂ) * I) R) ℤ}
    (hr : r < R) (ha₁ : θ - ρ.re ≤ 1) (hM : 0 < M)
    (havoid : (1 : ℂ) ∉ Metric.closedBall ((θ : ℂ) + (ρ.im : ℂ) * I) R)
    (hD : 0 ≤ D)
    (hLe : D ≤ MeromorphicOn.divisor riemannZeta
      (Metric.closedBall ((θ : ℂ) + (ρ.im : ℂ) * I) R))
    (hcluster : D.support ⊆ Metric.closedBall ((θ : ℂ) + (ρ.im : ℂ) * I) r)
    (hρ : ρ ∈ D.support) (hleft : ρ.re < θ)
    (hsphere : ∀ w ∈ Metric.sphere ((θ : ℂ) + (ρ.im : ℂ) * I) R, ‖riemannZeta w‖ ≤ M)
    (hzero : ∀ y ∈ Ioo (ρ.im - (θ - ρ.re)) (ρ.im + (θ - ρ.re)),
      riemannZeta ((θ : ℂ) + (y : ℂ) * I) ≠ 0)
    (hint : IntegrableOn (fun y : ℝ =>
      1 / ((1 + |y|) ^ 2 * ‖riemannZeta ((θ : ℂ) + (y : ℂ) * I)‖ ^ 2))
      (Ioo (ρ.im - (θ - ρ.re)) (ρ.im + (θ - ρ.re)))) :
    let c : ℂ := (θ : ℂ) + (ρ.im : ℂ) * I
    let a : ℝ := θ - ρ.re
    let s : Finset ℂ := (D.finiteSupport (isCompact_closedBall c R)).toFinset
    let q : ℕ := ∑ᶠ u, (D u).toNat
    let m : ℕ := (D ρ).toNat
    let A : ℝ := M / (R - r) ^ q
    let B : ℝ := ∏ u ∈ s.erase ρ, (a + dist c u) ^ (D u).toNat
    1 / ((2 * (1 + |ρ.im|)) ^ 2 * (A ^ 2 * (a * (2 * a ^ 2) ^ (m - 1) * B ^ 2))) ≤
      ∫ y in Ioo (ρ.im - a) (ρ.im + a),
        1 / ((1 + |y|) ^ 2 * ‖riemannZeta ((θ : ℂ) + (y : ℂ) * I)‖ ^ 2) := by
  let c := boundaryPoint θ ρ.im
  let a := θ - ρ.re
  have hFinite : D.support.Finite := D.finiteSupport (isCompact_closedBall c R)
  let s : Finset ℂ := hFinite.toFinset
  let q : ℕ := ∑ᶠ u, (D u).toNat
  let m : ℕ := (D ρ).toNat
  let A : ℝ := M / (R - r) ^ q
  let B : ℝ := ∏ u ∈ s.erase ρ, (a + dist c u) ^ (D u).toNat
  let K : ℝ := (2 * (1 + |ρ.im|)) ^ 2 * (A ^ 2 * (a * (2 * a ^ 2) ^ (m - 1) * B ^ 2))
  let C : ℝ := (2 * (1 + |ρ.im|)) ^ 2 * (A ^ 2 * ((2 * a ^ 2) ^ m * B ^ 2))
  let W := Ioo (ρ.im - a) (ρ.im + a)
  change 1 / K ≤ ∫ y in W, boundaryDensity θ y
  change IntegrableOn (boundaryDensity θ) W at hint
  have ha : 0 < a := sub_pos.mpr hleft
  have hA : 0 ≤ A := div_nonneg hM.le (pow_nonneg (sub_pos.mpr hr).le _)
  have hρs : ρ ∈ s := hFinite.mem_toFinset.mpr hρ
  have hm : 1 ≤ m := by
    have hne : D ρ ≠ 0 := hρ
    have hnonneg : 0 ≤ D ρ := hD ρ
    change 1 ≤ (D ρ).toNat
    omega
  have hreal (y : ℝ) : (boundaryPoint θ y - ρ).re = a := by
    simp [boundaryPoint, Complex.mul_re, a]
  have har : a ≤ r := by
    calc
      a = |(c - ρ).re| := by
        change a = |(boundaryPoint θ ρ.im - ρ).re|
        rw [hreal ρ.im, abs_of_pos ha]
      _ ≤ ‖c - ρ‖ := Complex.abs_re_le_norm _
      _ = dist ρ c := by rw [dist_comm ρ c, dist_eq_norm]
      _ ≤ r := Metric.mem_closedBall.mp (hcluster hρ)
  have hne (w : ℂ) (hw : w ∈ Metric.closedBall c R) : w ≠ 1 := by
    rintro rfl
    exact havoid hw
  have hf : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c R) :=
    fun w hw ↦ riemannZeta_analyticOnNhd_compl_one w (hne w hw)
  have hOrder (w : ℂ) (hw : w ∈ Metric.closedBall c R) :
      meromorphicOrderAt riemannZeta w ≠ ⊤ := by
    rw [(hf w hw).meromorphicOrderAt_eq, ne_eq, ENat.map_eq_top_iff]
    exact analyticOrderAt_riemannZeta_ne_top (hne w hw)
  have hpoint (y : ℝ) (hy : y ∈ W) : 1 / C ≤ boundaryDensity θ y := by
    let z := boundaryPoint θ y
    have hy₁ : ρ.im - a < y := hy.1
    have hy₂ : y < ρ.im + a := hy.2
    have hyT : |y - ρ.im| ≤ a := abs_le.mpr
      ⟨by linarith only [hy₁], by linarith only [hy₂]⟩
    have hzdist : dist z c = |y - ρ.im| := by
      have heq : z - c = ((y - ρ.im : ℝ) : ℂ) * I := by
        push_cast
        dsimp [z, c, boundaryPoint]
        ring
      rw [dist_eq_norm, heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hzclose : dist z c ≤ a := hzdist.le.trans hyT
    have hzmem : z ∈ Metric.closedBall c R :=
      Metric.mem_closedBall.mpr (hzclose.trans (har.trans hr.le))
    have hanchor : ‖z - ρ‖ ^ 2 ≤ 2 * a ^ 2 := by
      have hre : (z - ρ).re = a := hreal y
      have him : (z - ρ).im = y - ρ.im := by simp [z, boundaryPoint, Complex.mul_im]
      have hysq : (y - ρ.im) ^ 2 ≤ a ^ 2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (y - ρ.im)) hyT 2
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
      nlinarith only [hysq]
    have hOther : (∏ u ∈ s.erase ρ, ‖z - u‖ ^ (D u).toNat) ≤ B := by
      change _ ≤ ∏ u ∈ s.erase ρ, (a + dist c u) ^ (D u).toNat
      refine Finset.prod_le_prod₀ (fun u _ ↦ pow_nonneg (norm_nonneg (z - u)) _) ?_
      intro u _
      apply pow_le_pow_left₀ (norm_nonneg (z - u))
      calc
        ‖z - u‖ = dist z u := (dist_eq_norm _ _).symm
        _ ≤ dist z c + dist c u := dist_triangle _ _ _
        _ ≤ a + dist c u := add_le_add hzclose le_rfl
    have hprod := norm_le_mul_prod_of_selectedZeroCluster (D := D)
      hr hf hD hLe hOrder hcluster hsphere hzmem
    change ‖riemannZeta z‖ ≤ A * (∏ u ∈ s, ‖z - u‖ ^ (D u).toNat) at hprod
    rw [← Finset.mul_prod_erase s (fun u ↦ ‖z - u‖ ^ (D u).toNat) hρs] at hprod
    have hnorm : ‖riemannZeta z‖ ≤ A * (‖z - ρ‖ ^ m * B) :=
      hprod.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hOther (pow_nonneg (norm_nonneg _) _)) hA)
    have hanchorPow : (‖z - ρ‖ ^ m) ^ 2 ≤ (2 * a ^ 2) ^ m := by
      rw [pow_right_comm ‖z - ρ‖ m 2]
      exact pow_le_pow_left₀ (sq_nonneg _) hanchor m
    have hfsq : ‖riemannZeta z‖ ^ 2 ≤ A ^ 2 * ((2 * a ^ 2) ^ m * B ^ 2) := by
      calc
        _ ≤ (A * (‖z - ρ‖ ^ m * B)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ = A ^ 2 * ((‖z - ρ‖ ^ m) ^ 2 * B ^ 2) := by simp only [mul_pow]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hanchorPow (sq_nonneg B)) (sq_nonneg A)
    have hyabs : |y| ≤ |ρ.im| + a := by
      calc
        |y| = |ρ.im + (y - ρ.im)| := by rw [show ρ.im + (y - ρ.im) = y by ring]
        _ ≤ |ρ.im| + |y - ρ.im| := abs_add_le _ _
        _ ≤ _ := add_le_add le_rfl hyT
    have hweight : 1 + |y| ≤ 2 * (1 + |ρ.im|) := by
      have haBound : a ≤ 1 := ha₁
      linarith only [hyabs, haBound, abs_nonneg ρ.im]
    have hden : (1 + |y|) ^ 2 * ‖riemannZeta z‖ ^ 2 ≤ C :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hweight 2) hfsq
        (sq_nonneg _) (by positivity)
    have hpos : 0 < (1 + |y|) ^ 2 * ‖riemannZeta z‖ ^ 2 :=
      mul_pos (by positivity) (pow_pos (norm_pos_iff.mpr (hzero y hy)) _)
    exact one_div_le_one_div_of_le hpos hden
  have hC : C = 2 * a * K := by
    have hmEq : m - 1 + 1 = m := Nat.sub_add_cancel hm
    have hpow : (2 * a ^ 2) ^ m = (2 * a ^ 2) ^ (m - 1) * (2 * a ^ 2) := by
      calc
        _ = (2 * a ^ 2) ^ (m - 1 + 1) := congrArg (fun n : ℕ ↦ (2 * a ^ 2) ^ n) hmEq.symm
        _ = _ := pow_succ _ _
    dsimp only [C, K]
    rw [hpow]
    ring
  have hmeas : MeasurableSet W := measurableSet_Ioo
  have hconst : IntegrableOn (fun _ : ℝ => 1 / C) W :=
    integrableOn_const (measure_Ioo_lt_top (μ := (volume : Measure ℝ))).ne
  calc
    1 / K = (2 * a) / C := by
      rw [hC]
      have ha_ne : 2 * a ≠ 0 := (mul_pos (by norm_num) ha).ne'
      simpa only [mul_one] using (mul_div_mul_left (1 : ℝ) K ha_ne).symm
    _ = ∫ _ in W, 1 / C := by
      unfold W
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le (by linarith only [ha])]
      rw [show ρ.im + a - (ρ.im - a) = 2 * a by ring, div_eq_mul_one_div]
    _ ≤ _ := setIntegral_mono_on hconst hint hmeas hpoint

private theorem exists_twoPoint_zeta_subdivisor
    {U : Set ℂ} {ρ σ : ℂ} (havoid : (1 : ℂ) ∉ U)
    (hρU : ρ ∈ U) (hσU : σ ∈ U) (hne : ρ ≠ σ)
    (hρ : riemannZeta ρ = 0) (hσ : riemannZeta σ = 0) :
    ∃ D : Function.locallyFinsuppWithin U ℤ,
      D.support = ({ρ, σ} : Set ℂ) ∧ D ρ = 1 ∧ D σ = 1 ∧
        0 ≤ D ∧ D ≤ MeromorphicOn.divisor riemannZeta U := by
  classical
  have hneOne (w : ℂ) (hw : w ∈ U) : w ≠ 1 := by
    rintro rfl
    exact havoid hw
  have hf : AnalyticOnNhd ℂ riemannZeta U :=
    fun w hw ↦ riemannZeta_analyticOnNhd_compl_one w (hneOne w hw)
  have hdiv : 0 ≤ MeromorphicOn.divisor riemannZeta U :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf
  have hdivOne (w : ℂ) (hw : w ∈ U) (hz : riemannZeta w = 0) :
      1 ≤ MeromorphicOn.divisor riemannZeta U w := by
    have hord : analyticOrderAt riemannZeta w ≠ 0 := (hf w hw).analyticOrderAt_ne_zero.mpr hz
    obtain ⟨n, hn⟩ :=
      ENat.ne_top_iff_exists.mp (analyticOrderAt_riemannZeta_ne_top (hneOne w hw))
    rw [← hn] at hord
    have hnOne : 1 ≤ n := by
      simp only [ne_eq, Nat.cast_eq_zero] at hord
      omega
    rw [MeromorphicOn.divisor_apply hf.meromorphicOn hw, (hf w hw).meromorphicOrderAt_eq, ← hn]
    change (1 : ℤ) ≤ (n : ℤ)
    exact_mod_cast hnOne
  let D : Function.locallyFinsuppWithin U ℤ :=
    (Function.locallyFinsuppWithin.single ρ (1 : ℤ) +
      Function.locallyFinsuppWithin.single σ (1 : ℤ)).restrict (subset_univ U)
  have hDapply (w : ℂ) :
      D w = if w ∈ U then (if w = ρ then 1 else 0) + (if w = σ then 1 else 0) else 0 := by
    simp only [D, Function.locallyFinsuppWithin.restrict_apply,
      Function.locallyFinsuppWithin.coe_add, Pi.add_apply, Function.locallyFinsuppWithin.single_apply]
  have hDρ : D ρ = 1 := by simp [hDapply, hρU, hne]
  have hDσ : D σ = 1 := by simp [hDapply, hσU, hne.symm]
  have hsupport : D.support = ({ρ, σ} : Set ℂ) := by
    ext w
    change (D w ≠ 0) ↔ w ∈ ({ρ, σ} : Set ℂ)
    by_cases hwr : w = ρ
    · subst w
      simp [hDρ]
    by_cases hws : w = σ
    · subst w
      simp [hDσ]
    simp [hDapply, hwr, hws]
  refine ⟨D, hsupport, hDρ, hDσ, ?_, ?_⟩
  · intro w
    change 0 ≤ D w
    rw [hDapply]
    split_ifs <;> norm_num
  · intro w
    change D w ≤ MeromorphicOn.divisor riemannZeta U w
    by_cases hwr : w = ρ
    · subst w
      rw [hDρ]
      exact hdivOne ρ hρU hρ
    by_cases hws : w = σ
    · subst w
      rw [hDσ]
      exact hdivOne σ hσU hσ
    have hDw : D w = 0 := by simp [hDapply, hwr, hws]
    rw [hDw]
    exact hdiv w

/-- A zero anchored at horizontal gap at most `|t| ^ (-u)` and a distinct zero
within distance `|t| ^ (-v)` of the boundary point at ordinate `t` cannot occur
at sufficiently high absolute ordinate if `0 < v ≤ u` and `2 < u + 2 * v`. -/
private theorem no_mixedScaleZeroPair_atHighOrdinate
    {θ u v : ℝ} (hθhalf : 1 / 2 < θ) (hθone : θ < 1)
    (hv : 0 < v) (hvu : v ≤ u) (hexponent : 2 < u + 2 * v)
    (hRight : ∀ z : ℂ, θ < z.re → z ≠ 1 → riemannZeta z ≠ 0)
    (hLine : ∀ y : ℝ, riemannZeta ((θ : ℂ) + (y : ℂ) * I) ≠ 0)
    (hE : IntegrableOn
      (fun x : ℝ => mobiusDyadicDifference x ^ 2 * x ^ (-(2 * θ - 1))) (Ioi 1)) :
    ∃ T : ℝ, 0 < T ∧
      ∀ ρ σ : ℂ, T ≤ |ρ.im| →
        ρ ≠ σ → riemannZeta ρ = 0 → riemannZeta σ = 0 →
        ρ.re < θ → θ - ρ.re ≤ |ρ.im| ^ (-u) →
        dist ((θ : ℂ) + (ρ.im : ℂ) * I) σ ≤ |ρ.im| ^ (-v) → False := by
  classical
  let eps : ℝ := (u + 2 * v - 2) / 4
  let γ : ℝ := u + 2 * v - (2 + 2 * eps)
  have heps : 0 < eps := by dsimp [eps]; linarith only [hexponent]
  have hγ : 0 < γ := by dsimp [γ, eps]; linarith only [hexponent]
  obtain ⟨R, C₀, T₀, hR, hC₀, _hT₀, hζ⟩ :=
    norm_riemannZeta_le_rpow_on_boundary_disks hθhalf hθone heps hRight
  let f (y : ℝ) : ℝ :=
    1 / ((1 + |y|) ^ 2 * ‖riemannZeta ((θ : ℂ) + (y : ℂ) * I)‖ ^ 2)
  let K : ℝ := 4 + 4 * Real.pi *
    (∫ x in Ioi (1 : ℝ), mobiusDyadicDifference x ^ 2 * x ^ (-(2 * θ - 1))) /
    (1 - (2 : ℝ) ^ (θ - 1)) ^ 2
  obtain ⟨hInt, hEnergy⟩ :=
    weighted_reciprocal_zeta_sq_bound_of_mobiusDyadicEnergy
      (by linarith only [hθhalf]) (by linarith only [hθone]) hθone.ne hLine hE
  change Integrable f at hInt
  change (∫ y, f y) ≤ K at hEnergy
  have hf₀ (y : ℝ) : 0 ≤ f y := by dsimp [f]; positivity
  have hK : 0 ≤ K := (integral_nonneg hf₀).trans hEnergy
  let C : ℝ := C₀ / (R / 2) ^ 2
  let L : ℝ := K * (64 * C ^ 2)
  have hsmall : ∀ᶠ x : ℝ in atTop, x ^ (-v) < min 1 (R / 2) :=
    (tendsto_rpow_neg_atTop hv).eventually
      (eventually_lt_nhds (lt_min zero_lt_one (half_pos hR)))
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hsmall
  have hlarge : ∀ᶠ x : ℝ in atTop, L < x ^ γ :=
    (tendsto_rpow_atTop hγ).eventually (eventually_gt_atTop L)
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp hlarge
  let T : ℝ := max (R + 1) (max T₀ (max T₁ T₂))
  refine ⟨T, (by dsimp [T]; positivity), ?_⟩
  intro ρ σ ht hne hρ hσ hleft haSmall hσSmall
  let x : ℝ := |ρ.im|
  let c : ℂ := (θ : ℂ) + (ρ.im : ℂ) * I
  let a : ℝ := θ - ρ.re
  let r : ℝ := x ^ (-v)
  have hxR : R + 1 ≤ x := (le_max_left _ _).trans ht
  have hx₁ : 1 ≤ x := by linarith only [hxR, hR]
  have hx : 0 < x := by linarith only [hx₁]
  have hxT₀ : T₀ ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hxT₁ : T₁ ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  have hxT₂ : T₂ ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  have hrmin : r ≤ min 1 (R / 2) := (hT₁ x hxT₁).le
  have hrR : r ≤ R / 2 := hrmin.trans (min_le_right _ _)
  have hRhalf : R / 2 ≤ R - r := by linarith only [hrR]
  have hRr : 0 < R - r := (half_pos hR).trans_le hRhalf
  have ha : 0 < a := sub_pos.mpr hleft
  change a ≤ x ^ (-u) at haSmall
  change dist c σ ≤ r at hσSmall
  have har : a ≤ r := haSmall.trans (Real.rpow_le_rpow_of_exponent_le hx₁ (neg_le_neg hvu))
  have ha₁ : a ≤ 1 := har.trans (hrmin.trans (min_le_left _ _))
  have havoid : (1 : ℂ) ∉ closedBall c R := by
    intro h
    have hnorm := (Complex.abs_im_le_norm ((1 : ℂ) - c)).trans
      (show ‖(1 : ℂ) - c‖ ≤ R by simpa only [mem_closedBall, dist_eq_norm] using h)
    have hc : c.im = ρ.im := by simp [c, Complex.mul_im]
    simp only [Complex.sub_im, Complex.one_im, hc, zero_sub, abs_neg] at hnorm
    change x ≤ R at hnorm
    linarith only [hnorm, hxR]
  have hρdist : dist ρ c = a := by
    have hsub : ρ - c = ((ρ.re - θ : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [c, Complex.mul_re, Complex.mul_im]
    rw [dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hleft.le)]
    dsimp [a]
    ring
  have hρr : ρ ∈ closedBall c r := mem_closedBall.mpr (hρdist.trans_le har)
  have hσr : σ ∈ closedBall c r := mem_closedBall.mpr (by simpa only [dist_comm σ c] using hσSmall)
  have hsubset : closedBall c r ⊆ closedBall c R := closedBall_subset_closedBall (sub_pos.mp hRr).le
  obtain ⟨D, hsupport, hDρ, hDσ, hD, hLe⟩ :=
    exists_twoPoint_zeta_subdivisor havoid (hsubset hρr) (hsubset hσr) hne hρ hσ
  have hcluster : D.support ⊆ closedBall c r := by
    rw [hsupport]
    intro w hw
    rcases (show w = ρ ∨ w = σ by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hw)
      with rfl | rfl
    · exact hρr
    · exact hσr
  have hρD : ρ ∈ D.support := by rw [hsupport]; simp
  let s : Finset ℂ := (D.finiteSupport (isCompact_closedBall c R)).toFinset
  have hs : s = {ρ, σ} := by
    ext w
    simp only [s, Set.Finite.mem_toFinset, hsupport, Set.mem_insert_iff, Set.mem_singleton_iff,
      Finset.mem_insert, Finset.mem_singleton]
  have hq : (∑ᶠ w, (D w).toNat) = 2 := by
    calc
      _ = ∑ w ∈ s, (D w).toNat := by
        apply finsum_eq_sum_of_support_subset
        intro w hw
        apply (Set.Finite.mem_toFinset _).mpr
        change D w ≠ 0
        change (D w).toNat ≠ 0 at hw
        exact fun hz ↦ hw (by simp [hz])
      _ = _ := by simp [hs, Finset.sum_insert, hne, hDρ, hDσ]
  have hm : (D ρ).toNat - 1 = 0 := by rw [hDρ] <;> decide
  have hσNat : (D σ).toNat = 1 := by rw [hDσ] <;> decide
  have hErase : s.erase ρ = {σ} := by
    rw [hs]
    ext w
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hwr, hw | hw⟩
      · exact (hwr hw).elim
      · exact hw
    · rintro rfl
      exact ⟨hne.symm, Or.inr rfl⟩
  let b : ℝ := a + dist c σ
  have hB : (∏ w ∈ s.erase ρ, (a + dist c w) ^ (D w).toNat) = b := by
    rw [hErase, Finset.prod_singleton, hσNat, pow_one]
  let M : ℝ := C₀ * x ^ eps
  have hM : 0 < M := mul_pos hC₀ (Real.rpow_pos_of_pos hx eps)
  let A : ℝ := M / (R - r) ^ 2
  let denominator : ℝ := (2 * (1 + x)) ^ 2 * (A ^ 2 * (a * b ^ 2))
  let W : Set ℝ := Ioo (ρ.im - a) (ρ.im + a)
  have hLower := reciprocal_mass_lower_of_selectedZeroCluster_anchor
    (θ := θ) (ρ := ρ) (r := r) (R := R) (M := M) (D := D)
    (sub_pos.mp hRr) ha₁ hM havoid hD hLe hcluster hρD hleft
    (fun z hz ↦ hζ ρ.im hxT₀ z (sphere_subset_closedBall hz))
    (fun y _ ↦ hLine y) hInt.integrableOn
  change 1 / ((2 * (1 + x)) ^ 2 *
    ((M / (R - r) ^ (∑ᶠ w, (D w).toNat)) ^ 2 *
      (a * (2 * a ^ 2) ^ ((D ρ).toNat - 1) *
        (∏ w ∈ s.erase ρ, (a + dist c w) ^ (D w).toNat) ^ 2))) ≤
      ∫ y in W, f y at hLower
  simp only [hq, hm, pow_zero, mul_one, hB] at hLower
  have hLocal : 1 / denominator ≤ ∫ y in W, f y := hLower
  have hMass : 1 / denominator ≤ K :=
    hLocal.trans ((setIntegral_le_integral hInt (ae_of_all _ hf₀)).trans hEnergy)
  have hA : 0 < A := div_pos hM (pow_pos hRr 2)
  have hb : 0 < b := add_pos_of_pos_of_nonneg ha dist_nonneg
  have hDenPos : 0 < denominator :=
    mul_pos (pow_pos (by linarith only [hx]) 2)
      (mul_pos (pow_pos hA 2) (mul_pos ha (pow_pos hb 2)))
  have hAupper : A ≤ C * x ^ eps := by
    dsimp only [A, M, C]
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left hM.le (pow_pos (half_pos hR) 2)
      (pow_le_pow_left₀ (half_pos hR).le hRhalf 2)
  have hbUpper : b ≤ 2 * r := by dsimp only [b]; linarith only [har, hσSmall]
  have hPair : a * b ^ 2 ≤ x ^ (-u) * (2 * r) ^ 2 :=
    mul_le_mul haSmall (pow_le_pow_left₀ hb.le hbUpper 2) (sq_nonneg b)
      (Real.rpow_pos_of_pos hx (-u)).le
  have hFactors : A ^ 2 * (a * b ^ 2) ≤ (C * x ^ eps) ^ 2 * (x ^ (-u) * (2 * r) ^ 2) :=
    mul_le_mul (pow_le_pow_left₀ hA.le hAupper 2) hPair (by positivity) (sq_nonneg _)
  have hWeight : 2 * (1 + x) ≤ 4 * x := by linarith only [hx₁]
  have hDenUpper : denominator ≤ (4 * x) ^ 2 * ((C * x ^ eps) ^ 2 * (x ^ (-u) * (2 * r) ^ 2)) :=
    mul_le_mul (pow_le_pow_left₀ (by positivity) hWeight 2) hFactors
      (by positivity) (sq_nonneg _)
  have hBound : 1 ≤ K * ((4 * x) ^ 2 * ((C * x ^ eps) ^ 2 * (x ^ (-u) * (2 * r) ^ 2))) :=
    ((div_le_iff₀ hDenPos).mp hMass).trans (mul_le_mul_of_nonneg_left hDenUpper hK)
  have hXPow : x ^ (2 : ℕ) = x ^ (2 : ℝ) := (Real.rpow_natCast x 2).symm
  have hEpsPow : (x ^ eps) ^ (2 : ℕ) = x ^ (eps * 2) := by
    simpa only [Nat.cast_ofNat] using (Real.rpow_mul_natCast hx.le eps 2).symm
  have hRPow : r ^ (2 : ℕ) = x ^ ((-v) * 2) := by
    simpa only [r, Nat.cast_ofNat] using (Real.rpow_mul_natCast hx.le (-v) 2).symm
  have hNormalize :
      K * ((4 * x) ^ 2 * ((C * x ^ eps) ^ 2 * (x ^ (-u) * (2 * r) ^ 2))) =
        L * x ^ (-γ) := by
    calc
      _ = L * (x ^ (2 : ℕ) * ((x ^ eps) ^ 2 * (x ^ (-u) * r ^ 2))) := by
        dsimp only [L]
        ring
      _ = _ := by
        have hExp : (2 : ℝ) + (eps * 2 + (-u + (-v) * 2)) = -γ := by
          dsimp only [γ]
          ring
        rw [hXPow, hEpsPow, hRPow, ← Real.rpow_add hx (-u) ((-v) * 2),
          ← Real.rpow_add hx (eps * 2) (-u + (-v) * 2),
          ← Real.rpow_add hx 2 (eps * 2 + (-u + (-v) * 2)), hExp]
  rw [hNormalize] at hBound
  have hStrict : L * x ^ (-γ) < 1 := by
    rw [Real.rpow_neg hx.le, ← div_eq_mul_inv]
    exact (div_lt_one (Real.rpow_pos_of_pos hx γ)).2 (hT₂ x hxT₂)
  exact (not_lt_of_ge hBound) hStrict

/-- Finite critical signed dyadic Möbius energy rules out high pairs in
which a zero approaches the unattained abscissa at scale `|t|^(-u)` and a
distinct zero lies within distance `|t|^(-v)` of the same point of the boundary
line, provided `0 < v ≤ u` and `u + 2*v > 2`. -/
theorem no_mixedScaleZeroPair_atHighOrdinate_of_unattainedZeroAbscissa
    {u v : ℝ} (hΘ : zeroAbscissa < 1)
    (hunattained : ∀ z : ℂ, IsNontrivialZero z → z.re ≠ zeroAbscissa)
    (hv : 0 < v) (hvu : v ≤ u) (hexponent : 2 < u + 2 * v)
    (hE : IntegrableOn
      (fun x : ℝ => mobiusDyadicDifference x ^ 2 * x ^ (-(2 * zeroAbscissa - 1))) (Ioi 1)) :
    ∃ T : ℝ, 0 < T ∧
      ∀ ρ σ : ℂ, T ≤ |ρ.im| →
        ρ ≠ σ → riemannZeta ρ = 0 → riemannZeta σ = 0 →
        ρ.re < zeroAbscissa → zeroAbscissa - ρ.re ≤ |ρ.im| ^ (-u) →
        dist ((zeroAbscissa : ℂ) + (ρ.im : ℂ) * I) σ ≤ |ρ.im| ^ (-v) → False := by
  have hFacts :
      1 / 2 < zeroAbscissa ∧
      (∀ z : ℂ, zeroAbscissa < z.re → z ≠ 1 → riemannZeta z ≠ 0) ∧
      (∀ y : ℝ, riemannZeta ((zeroAbscissa : ℂ) + (y : ℂ) * I) ≠ 0) := by
    obtain ⟨ρ, hρ, hhalf⟩ := exists_nontrivial_zero_re_ge_half
    have hΘhalf := hhalf.trans_lt
      (lt_of_le_of_ne (zero_re_le_abscissa hρ) (hunattained ρ hρ))
    refine ⟨hΘhalf, ?_, ?_⟩
    · intro z hz _ hζ
      by_cases h : 1 ≤ z.re
      · exact riemannZeta_ne_zero_of_one_le_re h hζ
      · exact hz.not_ge (zero_re_le_abscissa
          (show IsNontrivialZero z from ⟨hζ, by linarith only [hΘhalf, hz], lt_of_not_ge h⟩))
    · intro y hζ
      let z : ℂ := (zeroAbscissa : ℂ) + (y : ℂ) * I
      have hz : z.re = zeroAbscissa := by simp [z, Complex.mul_re]
      exact hunattained z ⟨hζ, by linarith only [hΘhalf, hz], by simpa only [hz] using hΘ⟩ hz
  exact no_mixedScaleZeroPair_atHighOrdinate hFacts.1 hΘ hv hvu hexponent
    hFacts.2.1 hFacts.2.2 hE

end D5.S3.Weil.ZetaPntBounds.MobiusBoundaryMixedScaleExclusion
