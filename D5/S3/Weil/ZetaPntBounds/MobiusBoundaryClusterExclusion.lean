/- GID: D5/S3/Weil/ZetaPntBounds/MobiusBoundaryClusterExclusion
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/MobiusBoundaryClusterExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite critical Möbius energy excludes narrow selected clusters at the unattained zeta zero abscissa. -/

import D5.S3.Arith.Robin.ForwardKernel.KappaGap
import D5.S3.Weil.Mertens.LittlewoodUpstream.ZetaReciprocalSubpolynomial
import D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundary
import D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
import D5.S3.Weil.ZetaSeam.StatementSeam
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Zero clusters at the unattained zeta zero abscissa

Factoring a selected local divisor bounds zeta on a short ordinate window.
Disk growth and the critical Möbius energy bound then exclude sufficiently
small windows with fixed selected multiplicity at large absolute ordinate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaPntBounds.MobiusBoundaryClusterExclusion

section ClusterMass

open Function Set
open scoped BigOperators

/-- The normal form of the quotient by the selected zero factor is analytic on
the whole domain and agrees with the quotient away from the selected zeros. -/
private theorem analyticOnNhd_selectedZeroQuotient {U : Set ℂ} {f : ℂ → ℂ}
    {D : Function.locallyFinsuppWithin U ℤ}
    (hf : AnalyticOnNhd ℂ f U) (hFinite : D.support.Finite)
    (hNonneg : 0 ≤ D) (hLe : D ≤ MeromorphicOn.divisor f U)
    (hOrder : ∀ w ∈ U, meromorphicOrderAt f w ≠ ⊤) :
    let P : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
    let Q := toMeromorphicNFOn (P⁻¹ • f) U
    AnalyticOnNhd ℂ Q U ∧ ∀ w ∈ U, w ∉ D.support → Q w = f w / P w := by
  let P : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
  change AnalyticOnNhd ℂ (toMeromorphicNFOn (P⁻¹ • f) U) U ∧
    ∀ w ∈ U, w ∉ D.support → toMeromorphicNFOn (P⁻¹ • f) U w = f w / P w
  have hP : MeromorphicOn P U := (FactorizedRational.meromorphicNFOn D U).meromorphicOn
  have hPDiv : MeromorphicOn.divisor P U = D := FactorizedRational.divisor (D := D) hFinite
  have hPInvOrder : ∀ w ∈ U, meromorphicOrderAt P⁻¹ w ≠ ⊤ := by
    intro w _
    have hPOrder : meromorphicOrderAt P w ≠ ⊤ :=
      FactorizedRational.meromorphicOrderAt_ne_top D
    simpa [meromorphicOrderAt_inv] using hPOrder
  have hQuot : MeromorphicOn (P⁻¹ • f) U := hP.inv.smul hf.meromorphicOn
  have hNF := meromorphicNFOn_toMeromorphicNFOn (P⁻¹ • f) U
  constructor
  · apply hNF.divisor_nonneg_iff_analyticOnNhd.mp
    rw [hQuot.divisor_of_toMeromorphicNFOn,
      MeromorphicOn.divisor_smul hP.inv hf.meromorphicOn hPInvOrder hOrder,
      MeromorphicOn.divisor_inv, hPDiv, neg_add_eq_sub]
    exact sub_nonneg.mpr hLe
  · intro w hw hwD
    have hPAt : AnalyticAt ℂ P w :=
      FactorizedRational.analyticAt (d := (D : ℂ → ℤ)) (hNonneg w)
    have hPNe : P w ≠ 0 :=
      FactorizedRational.ne_zero (d := (D : ℂ → ℤ)) (notMem_support.mp hwD)
    have hQuotAt : AnalyticAt ℂ (P⁻¹ • f) w := (hPAt.inv hPNe).smul (hf w hw)
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hQuot hw,
      toMeromorphicNFAt_eq_self.mpr hQuotAt.meromorphicNFAt]
    simp only [Pi.smul_apply', Pi.inv_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- A cluster within radius `r` of the center gives a disk bound with exponent
equal to the sum of the selected multiplicities. -/
private theorem norm_le_of_selectedZeroCluster {f : ℂ → ℂ} {c z : ℂ} {r R M : ℝ}
    {D : Function.locallyFinsuppWithin (Metric.closedBall c R) ℤ}
    (hR : 0 < R) (hr : r ≤ R / 2)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hNonneg : 0 ≤ D) (hLe : D ≤ MeromorphicOn.divisor f (Metric.closedBall c R))
    (hOrder : ∀ w ∈ Metric.closedBall c R, meromorphicOrderAt f w ≠ ⊤)
    (hCluster : D.support ⊆ Metric.closedBall c r)
    (hM : ∀ w ∈ Metric.sphere c R, ‖f w‖ ≤ M)
    (hz : z ∈ Metric.closedBall c R) (hzD : z ∉ D.support) :
    let q : ℕ := ∑ᶠ u, (D u).toNat
    ‖f z‖ ≤ M * ((‖z - c‖ + r) / (R - r)) ^ q := by
  classical
  let q : ℕ := ∑ᶠ u, (D u).toNat
  change ‖f z‖ ≤ M * ((‖z - c‖ + r) / (R - r)) ^ q
  have hFinite := D.finiteSupport (isCompact_closedBall c R)
  let s : Finset ℂ := hFinite.toFinset
  let P : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
  let Q := toMeromorphicNFOn (P⁻¹ • f) (Metric.closedBall c R)
  have hQuot :
      AnalyticOnNhd ℂ Q (Metric.closedBall c R) ∧
      ∀ w ∈ Metric.closedBall c R, w ∉ D.support → Q w = f w / P w :=
    analyticOnNhd_selectedZeroQuotient (D := D) hf hFinite hNonneg hLe hOrder
  obtain ⟨hQ, hQEq⟩ := hQuot
  have hRadius : 0 < R - r := sub_pos.mpr (hr.trans_lt (half_lt_self hR))
  have hCenterDist {u : ℂ} (hu : u ∈ s) : dist u c ≤ r :=
    Metric.mem_closedBall.mp (hCluster (hFinite.mem_toFinset.mp hu))
  have hq : q = ∑ u ∈ s, (D u).toNat := by
    change (∑ᶠ u, (D u).toNat) = _
    apply finsum_eq_sum_of_support_subset
    intro u hu
    apply hFinite.mem_toFinset.mpr
    change D u ≠ 0
    change (D u).toNat ≠ 0 at hu
    exact fun hZero ↦ hu (by simp [hZero])
  have hConstProd (a : ℝ) : (∏ u ∈ s, a ^ (D u).toNat) = a ^ q := by
    rw [Finset.prod_pow_eq_pow_sum, hq]
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
  have hPUpper (w : ℂ) : ‖P w‖ ≤ (‖w - c‖ + r) ^ q := by
    rw [hNormProd w, ← hConstProd (‖w - c‖ + r)]
    refine Finset.prod_le_prod₀ (fun u _ ↦ pow_nonneg (norm_nonneg (w - u)) _) ?_
    intro u hu
    apply pow_le_pow_left₀ (norm_nonneg (w - u))
    calc
      ‖w - u‖ = dist w u := (dist_eq_norm _ _).symm
      _ ≤ dist w c + dist c u := dist_triangle _ _ _
      _ ≤ ‖w - c‖ + r := by
        rw [dist_eq_norm w c, dist_comm c u]
        exact add_le_add le_rfl (hCenterDist hu)
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
  have hPz : P z ≠ 0 :=
    FactorizedRational.ne_zero (d := (D : ℂ → ℤ)) (notMem_support.mp hzD)
  calc
    ‖f z‖ = ‖Q z‖ * ‖P z‖ := by
      rw [← Complex.norm_mul, hQEq z hz hzD, div_mul_cancel₀ _ hPz]
    _ ≤ (M / (R - r) ^ q) * (‖z - c‖ + r) ^ q :=
      mul_le_mul hQz (hPUpper z) (norm_nonneg _) ((norm_nonneg _).trans hQz)
    _ = M * ((‖z - c‖ + r) / (R - r)) ^ q := by
      rw [div_pow, div_mul_eq_mul_div, mul_div_assoc]


open Complex MeasureTheory Set
open D5.S3.Weil.Mertens.MobiusDyadicEnergy (mobiusDyadicDifference)
open D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundary
  (weighted_reciprocal_zeta_sq_bound_of_mobiusDyadicEnergy)
open Zeta23 (riemannZeta_analyticOnNhd_compl_one analyticOrderAt_riemannZeta_ne_top)

private def boundaryPoint (θ y : ℝ) : ℂ := (θ : ℂ) + (y : ℂ) * I

private noncomputable def boundaryDensity (θ y : ℝ) : ℝ :=
  1 / ((1 + |y|) ^ 2 * ‖riemannZeta (boundaryPoint θ y)‖ ^ 2)

/-- A cluster of selected zeta zeros gives a lower bound for the reciprocal mass
of an ordinate interval, with the total selected multiplicity in the exponent. -/
private theorem reciprocal_mass_lower_of_selectedZeroCluster
    {θ T r R M : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hrR : r ≤ R / 2) (hM : 0 < M)
    {D : Function.locallyFinsuppWithin (Metric.closedBall (boundaryPoint θ T) R) ℤ}
    (havoid : (1 : ℂ) ∉ Metric.closedBall (boundaryPoint θ T) R)
    (hD : 0 ≤ D)
    (hLe : D ≤ MeromorphicOn.divisor riemannZeta (Metric.closedBall (boundaryPoint θ T) R))
    (hcluster : D.support ⊆ Metric.closedBall (boundaryPoint θ T) r)
    (hleft : ∀ w ∈ D.support, w.re < θ)
    (hsphere : ∀ w ∈ Metric.sphere (boundaryPoint θ T) R, ‖riemannZeta w‖ ≤ M)
    (hzero : ∀ y : ℝ, riemannZeta (boundaryPoint θ y) ≠ 0)
    (hint : Integrable (boundaryDensity θ)) :
    let q : ℕ := ∑ᶠ u, (D u).toNat
    2 * r /
        ((2 * (1 + |T|)) ^ 2 * (M * (2 * r / (R - r)) ^ q) ^ 2) ≤
      ∫ y in Ioo (T - r) (T + r), boundaryDensity θ y := by
  let q : ℕ := ∑ᶠ u, (D u).toNat
  let C : ℝ := (2 * (1 + |T|)) ^ 2 * (M * (2 * r / (R - r)) ^ q) ^ 2
  have hR : 0 < R := by linarith only [hr, hrR]
  have hRr : 0 < R - r := by linarith only [hr, hrR]
  have hne (w : ℂ) (hw : w ∈ Metric.closedBall (boundaryPoint θ T) R) : w ≠ 1 := by
    rintro rfl
    exact havoid hw
  have hf : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall (boundaryPoint θ T) R) :=
    fun w hw => riemannZeta_analyticOnNhd_compl_one w (hne w hw)
  have hOrder (w : ℂ) (hw : w ∈ Metric.closedBall (boundaryPoint θ T) R) :
      meromorphicOrderAt riemannZeta w ≠ ⊤ := by
    rw [(hf w hw).meromorphicOrderAt_eq, ne_eq, ENat.map_eq_top_iff]
    exact analyticOrderAt_riemannZeta_ne_top (hne w hw)
  have hpoint (y : ℝ) (hy : y ∈ Ioo (T - r) (T + r)) : 1 / C ≤ boundaryDensity θ y := by
    let z := boundaryPoint θ y
    have hyT : |y - T| ≤ r := abs_le.mpr
      ⟨by linarith only [hy.1], by linarith only [hy.2]⟩
    have hzdist : ‖z - boundaryPoint θ T‖ = |y - T| := by
      have heq : z - boundaryPoint θ T = ((y - T : ℝ) : ℂ) * I := by
        push_cast
        dsimp [z, boundaryPoint]
        ring
      rw [heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hzmem : z ∈ Metric.closedBall (boundaryPoint θ T) R := by
      rw [Metric.mem_closedBall, dist_eq_norm, hzdist]
      linarith only [hyT, hrR, hR]
    have hzD : z ∉ D.support := by
      intro hzD
      have hzlt := hleft z hzD
      simp [z, boundaryPoint, Complex.mul_re] at hzlt
    have hzbound := norm_le_of_selectedZeroCluster hR hrR hf hD hLe hOrder
      hcluster hsphere hzmem hzD
    change ‖riemannZeta z‖ ≤ M * ((‖z - boundaryPoint θ T‖ + r) / (R - r)) ^ q at hzbound
    rw [hzdist] at hzbound
    have hquot : (|y - T| + r) / (R - r) ≤ 2 * r / (R - r) :=
      div_le_div_of_nonneg_right (by linarith only [hyT]) hRr.le
    have hζ : ‖riemannZeta z‖ ≤ M * (2 * r / (R - r)) ^ q :=
      hzbound.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hquot q) hM.le)
    have hyabs : |y| ≤ |T| + r := by
      calc
        |y| = |T + (y - T)| := by rw [show T + (y - T) = y by ring]
        _ ≤ |T| + |y - T| := abs_add_le _ _
        _ ≤ _ := add_le_add le_rfl hyT
    have hweight : 1 + |y| ≤ 2 * (1 + |T|) := by
      linarith only [hyabs, hr₁, abs_nonneg T]
    have hden : (1 + |y|) ^ 2 * ‖riemannZeta z‖ ^ 2 ≤ C :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hweight 2)
        (pow_le_pow_left₀ (norm_nonneg _) hζ 2) (by positivity) (by positivity)
    have hpos : 0 < (1 + |y|) ^ 2 * ‖riemannZeta z‖ ^ 2 :=
      mul_pos (by positivity) (pow_pos (norm_pos_iff.mpr (hzero y)) _)
    exact one_div_le_one_div_of_le hpos hden
  have hmeas : MeasurableSet (Ioo (T - r) (T + r)) := measurableSet_Ioo
  have hconst : IntegrableOn (fun _ : ℝ => 1 / C) (Ioo (T - r) (T + r)) :=
    integrableOn_const (measure_Ioo_lt_top (μ := (volume : Measure ℝ))).ne
  change 2 * r / C ≤ _
  calc
    _ = ∫ _ in Ioo (T - r) (T + r), 1 / C := by
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le (by linarith only [hr])]
      rw [show T + r - (T - r) = 2 * r by ring, div_eq_mul_one_div]
    _ ≤ _ := setIntegral_mono_on hconst hint.integrableOn hmeas hpoint


/-- Finite weighted dyadic Möbius energy on a zero-free line bounds the
reciprocal mass forced by a nearby cluster, including multiplicities. -/
private theorem cluster_mass_le_of_mobiusDyadicEnergy {θ T r R M : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₂ : θ < 2) (hθne : θ ≠ 1)
    (hr : 0 < r) (hr₁ : r ≤ 1) (hrR : r ≤ R / 2) (hM : 0 < M)
    {D : Function.locallyFinsuppWithin (Metric.closedBall ((θ : ℂ) + (T : ℂ) * I) R) ℤ}
    (havoid : (1 : ℂ) ∉ Metric.closedBall ((θ : ℂ) + (T : ℂ) * I) R)
    (hD : 0 ≤ D)
    (hLe : D ≤ MeromorphicOn.divisor riemannZeta (Metric.closedBall ((θ : ℂ) + (T : ℂ) * I) R))
    (hcluster : D.support ⊆ Metric.closedBall ((θ : ℂ) + (T : ℂ) * I) r)
    (hleft : ∀ w ∈ D.support, w.re < θ)
    (hsphere : ∀ w ∈ Metric.sphere ((θ : ℂ) + (T : ℂ) * I) R, ‖riemannZeta w‖ ≤ M)
    (hzero : ∀ y : ℝ, riemannZeta ((θ : ℂ) + (y : ℂ) * I) ≠ 0)
    (hE : IntegrableOn (fun x : ℝ => mobiusDyadicDifference x ^ 2 * x ^ (-(2 * θ - 1))) (Ioi 1)) :
    let q : ℕ := ∑ᶠ u, (D u).toNat
    2 * r / ((2 * (1 + |T|)) ^ 2 * (M * (2 * r / (R - r)) ^ q) ^ 2) ≤
      4 + 4 * Real.pi *
        (∫ x in Ioi (1 : ℝ), mobiusDyadicDifference x ^ 2 * x ^ (-(2 * θ - 1))) /
        (1 - (2 : ℝ) ^ (θ - 1)) ^ 2 := by
  obtain ⟨hInt, hbound⟩ :=
    weighted_reciprocal_zeta_sq_bound_of_mobiusDyadicEnergy hθ₀ hθ₂ hθne hzero hE
  change Integrable (boundaryDensity θ) at hInt
  change (∫ y, boundaryDensity θ y) ≤ _ at hbound
  have hlower := reciprocal_mass_lower_of_selectedZeroCluster
    hr hr₁ hrR hM havoid hD hLe hcluster hleft hsphere hzero hInt
  have hsub :
      (∫ y in Ioo (T - r) (T + r), boundaryDensity θ y) ≤ ∫ y, boundaryDensity θ y :=
    setIntegral_le_integral hInt (ae_of_all _ fun _ => by
      unfold boundaryDensity
      positivity)
  exact hlower.trans (hsub.trans hbound)

end ClusterMass

section DiskGrowth

open Complex Filter Metric Set
open Complex.HadamardThreeLines
open scoped Topology

/-- Bounds on two concentric circles interpolate throughout the annulus when
the function is holomorphic on a neighborhood of the larger disk. -/
private theorem norm_le_interp_of_mem_annulus {f : ℂ → ℂ} {c z : ℂ} {r R A B : ℝ}
    (hr : 0 < r) (hR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hInner : ∀ v ∈ sphere c r, ‖f v‖ ≤ A)
    (hOuter : ∀ v ∈ sphere c R, ‖f v‖ ≤ B)
    (hz₁ : r ≤ ‖z - c‖) (hz₂ : ‖z - c‖ ≤ R) :
    let weight := Real.log (‖z - c‖ / r) / Real.log (R / r)
    ‖f z‖ ≤ A ^ (1 - weight) * B ^ weight := by
  let a := Real.log (R / r)
  have hRpos := hr.trans hR
  have hapos : 0 < a := Real.log_pos ((one_lt_div hr).2 hR)
  have hexpa : Real.exp a = R / r := Real.exp_log (div_pos hRpos hr)
  let g : ℂ → ℂ := fun v => c + (r : ℂ) * Complex.exp v
  let F : ℂ → ℂ := f ∘ g
  have hgdist (v : ℂ) : dist (g v) c = r * Real.exp v.re := by
    rw [dist_eq_norm]
    dsimp [g]
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_exp]
  have hmap (v : ℂ) (hv : v ∈ verticalClosedStrip 0 a) : g v ∈ closedBall c R := by
    rw [mem_closedBall, hgdist]
    calc
      r * Real.exp v.re ≤ r * Real.exp a :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hv.2) hr.le
      _ = R := by rw [hexpa, mul_div_cancel₀ R hr.ne']
  have hclosure : closure (verticalStrip 0 a) ⊆ verticalClosedStrip 0 a :=
    (isClosed_Icc.preimage Complex.continuous_re).closure_subset_iff.mpr
      fun _ hv => ⟨hv.1.le, hv.2.le⟩
  have hdiff : DiffContOnCl ℂ F (verticalStrip 0 a) := by
    refine DifferentiableOn.diffContOnCl ?_
    intro v hv
    exact (((hf _ (hmap v (hclosure hv))).differentiableAt).comp v
      ((differentiableAt_id.cexp.const_mul _).const_add _)).differentiableWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hf.continuousOn
  have hBdd : BddAbove ((norm ∘ F) '' verticalClosedStrip 0 a) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hC (g v) (hmap v hv)
  have hleft (v : ℂ) (hv : v ∈ re ⁻¹' {0}) : ‖F v‖ ≤ A := by
    change v.re = 0 at hv
    apply hInner
    rw [mem_sphere, hgdist, hv, Real.exp_zero, mul_one]
  have hright (v : ℂ) (hv : v ∈ re ⁻¹' {a}) : ‖F v‖ ≤ B := by
    change v.re = a at hv
    apply hOuter
    rw [mem_sphere, hgdist, hv, hexpa, mul_div_cancel₀ R hr.ne']
  let v := Complex.log ((z - c) / (r : ℂ))
  have hzsub : z - c ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hr.trans_le hz₁))
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hvr : v.re = Real.log (‖z - c‖ / r) := by
    rw [Complex.log_re, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hv : v ∈ verticalClosedStrip 0 a := by
    constructor
    · rw [hvr]
      exact Real.log_nonneg ((one_le_div hr).2 hz₁)
    · rw [hvr]
      exact Real.log_le_log (div_pos (hr.trans_le hz₁) hr)
        (div_le_div_of_nonneg_right hz₂ hr.le)
  have hFv : F v = f z := by
    change f (c + (r : ℂ) * Complex.exp v) = f z
    rw [Complex.exp_log (div_ne_zero hzsub hrC), mul_div_cancel₀ _ hrC]
    congr 1
    abel
  have h := norm_le_interp_of_mem_verticalClosedStrip' hapos hv hdiff hBdd hleft hright
  rw [hFv, hvr, sub_zero, sub_zero] at h
  exact h


/-- The logarithmic Littlewood estimate gives subpower growth of zeta throughout
fixed disks whose left edge lies strictly to the right of the zero abscissa. -/
private theorem norm_riemannZeta_le_rpow_on_right_disks
    {θ σ eps : ℝ} (hθhalf : 1 / 2 ≤ θ) (hθone : θ < 1) (hσ : θ < σ)
    (heps : 0 < eps) (hzero : ∀ z : ℂ, θ < z.re → z ≠ 1 → riemannZeta z ≠ 0) :
    ∃ C > 0, ∃ T > 0, ∀ t : ℝ, T ≤ |t| →
      ∀ z ∈ closedBall (2 + (t : ℂ) * I) (2 - σ), ‖riemannZeta z‖ ≤ C * |t| ^ eps := by
  let σ₁ := min σ ((θ + 1) / 2)
  have hσ₁ : θ < σ₁ := lt_min hσ (by linarith)
  have hσ₁σ : σ₁ ≤ σ := min_le_left _ _
  have hσ₁one : σ₁ < 1 := (min_le_right _ _).trans_lt (by linarith)
  let η := (σ₁ - θ) / 4
  have hη : 0 < η := by dsimp [η]; linarith
  have hη₁ : η < 1 / 4 := by dsimp [η]; linarith
  let r := 1 - η
  let s := 2 - σ₁
  let R := 2 - θ - η
  have hr : 0 < r := by dsimp [r]; linarith
  have hrs : r < s := by dsimp [r, s]; linarith
  have hsR : s < R := by dsimp [s, R, η]; linarith
  have hR₀ : R < 2 - θ - η / 2 := by dsimp [R]; linarith
  let α := Real.log (s / r) / Real.log (R / r)
  have hlogR : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr (hrs.trans hsR))
  have hα : 0 < α := div_pos (Real.log_pos ((one_lt_div hr).mpr hrs)) hlogR
  have hα₁ : α < 1 :=
    (div_lt_one hlogR).2 (Real.log_lt_log (div_pos (hr.trans hrs) hr)
      (div_lt_div_of_pos_right hsR hr))
  obtain ⟨M, N, hM, hN, hlog⟩ :=
    exists_logZeta_ball_bounds_of_zero_free hθhalf hθone hzero hη hη₁
  let A := max M 1
  let B := max N 1
  obtain ⟨D, hD, hpower⟩ := sublinear_rpow_le_linear
    hα hα₁ (A := A * B ^ α) (by positivity) heps
  refine ⟨Real.exp D, Real.exp_pos _, max 6 (Real.exp 1), by positivity, ?_⟩
  intro t ht z hz
  let c : ℂ := 2 + (t : ℂ) * I
  have ht₆ : 6 ≤ |t| := (le_max_left _ _).trans ht
  have htpos : 0 < |t| := by linarith only [ht₆]
  have hlogt : 1 ≤ Real.log |t| := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans ht)
  obtain ⟨L, hL, hexp, hsmall, hlarge⟩ := hlog t ht₆
  have hzsmall : ‖z - c‖ ≤ s := by
    have hdist := mem_closedBall.mp hz
    rw [dist_eq_norm] at hdist
    dsimp [s]
    linarith only [hdist, hσ₁σ]
  have hzR : z ∈ closedBall c R := by
    rw [mem_closedBall, dist_eq_norm]
    exact hzsmall.trans hsR.le
  have hLanalytic : AnalyticOnNhd ℂ L (closedBall c R) :=
    (hL.analyticOnNhd isOpen_ball).mono (closedBall_subset_ball hR₀)
  have hboundL : ‖L z‖ ≤ A * B ^ α * (Real.log |t|) ^ α := by
    by_cases hzInner : ‖z - c‖ ≤ r
    · have hzin : z ∈ closedBall c r := by
        simpa only [mem_closedBall, dist_eq_norm] using hzInner
      have hA : M ≤ A := le_max_left _ _
      have h1B : 1 ≤ B ^ α := Real.one_le_rpow (le_max_right _ _) hα.le
      have h1t : 1 ≤ (Real.log |t|) ^ α := Real.one_le_rpow hlogt hα.le
      have hA₀ : 0 ≤ A := by positivity
      exact (hsmall z hzin).trans (hA.trans
        (le_mul_of_one_le_right (mul_nonneg hA₀ (by positivity)) h1t |>.trans'
          (le_mul_of_one_le_right hA₀ h1B)))
    · have hβ₀ : 0 ≤ Real.log (‖z - c‖ / r) / Real.log (R / r) := by
        exact div_nonneg (Real.log_nonneg ((one_le_div hr).2 (le_of_not_ge hzInner))) hlogR.le
      have hβ : Real.log (‖z - c‖ / r) / Real.log (R / r) ≤ α := by
        exact div_le_div_of_nonneg_right
          (Real.log_le_log (div_pos (hr.trans (lt_of_not_ge hzInner)) hr)
            (div_le_div_of_nonneg_right hzsmall hr.le)) hlogR.le
      let β := Real.log (‖z - c‖ / r) / Real.log (R / r)
      have hLinterp : ‖L z‖ ≤ A ^ (1 - β) * (B * Real.log |t|) ^ β :=
        norm_le_interp_of_mem_annulus hr (hrs.trans hsR) hLanalytic
          (fun v hv => (hsmall v (sphere_subset_closedBall hv)).trans (le_max_left _ _))
          (fun v hv => (hlarge v (sphere_subset_closedBall hv)).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith only [hlogt])))
          (le_of_not_ge hzInner) (hzsmall.trans hsR.le)
      have hAβ : A ^ (1 - β) ≤ A := by
        calc
          _ ≤ A ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (le_max_right _ _) (by linarith only [hβ₀])
          _ = A := Real.rpow_one A
      have hBlog : 1 ≤ B * Real.log |t| :=
        one_le_mul_of_one_le_of_one_le (le_max_right _ _) hlogt
      have hBβ := Real.rpow_le_rpow_of_exponent_le hBlog hβ
      calc
        _ ≤ A ^ (1 - β) * (B * Real.log |t|) ^ β := hLinterp
        _ ≤ A * (B * Real.log |t|) ^ α := by gcongr
        _ = _ := by rw [Real.mul_rpow (by positivity) (by linarith only [hlogt]), mul_assoc]
  have hLlin := hboundL.trans (hpower (Real.log |t|) (by linarith only [hlogt]))
  rw [← hexp z (closedBall_subset_ball hR₀ hzR), Complex.norm_exp]
  calc
    Real.exp (L z).re ≤ Real.exp (eps * Real.log |t| + D) :=
      Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hLlin)
    _ = Real.exp D * |t| ^ eps := by
      rw [Real.rpow_def_of_pos htpos, Real.exp_add, mul_comm, mul_comm eps]


/-- Zeta has subpower growth on fixed small disks crossing a zero-free edge
strictly between the critical line and the pole. -/
private theorem norm_riemannZeta_le_rpow_on_boundary_disks
    {θ eps : ℝ} (hθhalf : 1 / 2 < θ) (hθone : θ < 1)
    (heps : 0 < eps) (hzero : ∀ z : ℂ, θ < z.re → z ≠ 1 → riemannZeta z ≠ 0) :
    ∃ δ C T : ℝ, 0 < δ ∧ 0 < C ∧ 0 < T ∧ ∀ t : ℝ, T ≤ |t| →
      ∀ z ∈ closedBall ((θ : ℂ) + (t : ℂ) * I) δ, ‖riemannZeta z‖ ≤ C * |t| ^ eps := by
  let m : ℝ := 2 - θ
  let R : ℝ := 2 - (θ + 1 / 2) / 2
  have hm : 0 < m := by dsimp [m]; linarith
  have hmR : m < R := by dsimp [m, R]; linarith
  have hR₂ : R ≤ 2 := by dsimp [R]; linarith
  let weight : ℝ → ℝ := fun d =>
    Real.log ((m + d) / (m - d)) / Real.log (R / (m - d))
  have hw₀ : weight 0 = 0 := by simp [weight, hm.ne']
  have hm₀ : m - (0 : ℝ) ≠ 0 := by simpa only [sub_zero] using hm.ne'
  have hsub : ContinuousAt (fun d : ℝ => m - d) 0 :=
    continuousAt_const.sub continuousAt_id
  have hnum : ContinuousAt (fun d : ℝ => Real.log ((m + d) / (m - d))) 0 :=
    ((continuousAt_const.add continuousAt_id).div hsub hm₀).log (by
      change (m + 0) / (m - 0) ≠ 0
      simpa only [add_zero, sub_zero] using (div_pos hm hm).ne')
  have hden : ContinuousAt (fun d : ℝ => Real.log (R / (m - d))) 0 :=
    (continuousAt_const.div hsub hm₀).log
      (by
        change R / (m - 0) ≠ 0
        simpa only [sub_zero] using (div_pos (hm.trans hmR) hm).ne')
  have hcont : ContinuousAt weight 0 :=
    hnum.div hden (by simpa only [sub_zero] using (Real.log_pos ((one_lt_div hm).2 hmR)).ne')
  have hwEvent : ∀ᶠ d in nhds (0 : ℝ), weight d < eps / 2 := by
    have hnear : ∀ᶠ y in nhds (weight 0), y < eps / 2 := by
      rw [hw₀]
      exact eventually_lt_nhds (by linarith only [heps])
    exact hcont.eventually hnear
  obtain ⟨d₀, hd₀, hball⟩ := Metric.mem_nhds_iff.mp hwEvent
  let δ := min d₀ (min m (R - m)) / 2
  have hd : 0 < δ := div_pos (lt_min hd₀ (lt_min hm (sub_pos.mpr hmR))) (by norm_num)
  have hd₀' : δ < d₀ := by
    have h := min_le_left d₀ (min m (R - m))
    dsimp [δ]
    linarith only [h, hd₀]
  have hdm : δ < m := by
    have h := (min_le_right d₀ (min m (R - m))).trans (min_le_left m (R - m))
    dsimp [δ]
    linarith only [h, hm]
  have hdR : m + δ < R := by
    have h := (min_le_right d₀ (min m (R - m))).trans (min_le_right m (R - m))
    dsimp [δ]
    linarith only [h, hmR]
  have hweight : weight δ ≤ eps / 2 :=
    (hball (mem_ball_zero_iff.mpr (by simpa [Real.norm_eq_abs, abs_of_pos hd] using hd₀'))).le
  let r := m - δ
  have hr : 0 < r := sub_pos.mpr hdm
  have hrR : r < R := by dsimp [r]; linarith only [hmR, hd]
  obtain ⟨C₁, hC₁, T₁, hT₁, hinner⟩ :=
    norm_riemannZeta_le_rpow_on_right_disks hθhalf.le hθone (lt_add_of_pos_right θ hd)
      (show 0 < eps / 2 by linarith only [heps]) hzero
  let A := max C₁ 1
  let B : ℝ := 3 * (R + 3)
  have hA : 1 ≤ A := le_max_right _ _
  have hB : 1 ≤ B := by dsimp [B]; linarith only [hm, hmR]
  have hC : 0 < A * B ^ (eps / 2) := by positivity
  refine ⟨δ, A * B ^ (eps / 2), max T₁ 6, hd, hC, by positivity, ?_⟩
  intro t ht z hz
  have ht₁ : T₁ ≤ |t| := (le_max_left _ _).trans ht
  have ht₆ : 6 ≤ |t| := (le_max_right _ _).trans ht
  have htpos : 0 < |t| := by linarith only [ht₆]
  have htone : 1 ≤ |t| := by linarith only [ht₆]
  let c : ℂ := 2 + (t : ℂ) * I
  let center : ℂ := (θ : ℂ) + (t : ℂ) * I
  have hcRe : c.re = 2 := by simp [c, Complex.mul_re]
  have hcIm : c.im = t := by simp [c, Complex.mul_im]
  have hcenter : dist center c = m := by
    have heq : center - c = ((θ - 2 : ℝ) : ℂ) := by
      push_cast
      dsimp [center, c]
      ring
    rw [dist_eq_norm, heq, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    dsimp [m]
    ring
  have hzmax : ‖z - c‖ ≤ m + δ := by
    rw [← dist_eq_norm]
    have hzdist : dist z center ≤ δ := mem_closedBall.mp hz
    exact (dist_triangle z center c).trans (by linarith only [hzdist, hcenter])
  have hrEq : r = 2 - (θ + δ) := by dsimp [r, m]; ring
  have hinner' (v : ℂ) (hv : v ∈ closedBall c r) :
      ‖riemannZeta v‖ ≤ A * |t| ^ (eps / 2) := by
    rw [hrEq] at hv
    exact (hinner t ht₁ v hv).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hbounds (v : ℂ) (hv : v ∈ closedBall c R) : 1 / 2 ≤ v.re ∧ 1 ≤ |v.im| := by
    have hvdist := mem_closedBall.mp hv
    rw [dist_eq_norm] at hvdist
    have hre := (Complex.abs_re_le_norm (v - c)).trans hvdist
    have him := (Complex.abs_im_le_norm (v - c)).trans hvdist
    rw [Complex.sub_re, hcRe] at hre
    rw [Complex.sub_im, hcIm] at him
    have ht' : |t| ≤ |v.im| + R := by
      calc
        |t| = |v.im - (v.im - t)| := by rw [show v.im - (v.im - t) = t by ring]
        _ ≤ |v.im| + |v.im - t| := by
          simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le v.im 0 (v.im - t)
        _ ≤ _ := add_le_add le_rfl him
    constructor
    · have h := (abs_le.mp hre).1
      dsimp [R] at h
      linarith only [h, hθhalf]
    · linarith only [ht', ht₆, hR₂]
  have hf : AnalyticOnNhd ℂ riemannZeta (closedBall c R) := by
    intro v hv
    apply analyticOn_riemannZeta
    intro heq
    have h := (hbounds v hv).2
    rw [Set.mem_singleton_iff.mp heq] at h
    norm_num at h
  have houter (v : ℂ) (hv : v ∈ sphere c R) : ‖riemannZeta v‖ ≤ B * |t| := by
    have hv' := sphere_subset_closedBall hv
    have hnorm : ‖v‖ ≤ R + (2 + |t|) := by
      calc
        ‖v‖ = ‖(v - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖v - c‖ + ‖c‖ := norm_add_le _ _
        _ ≤ _ := by
          refine add_le_add (by simpa only [mem_closedBall, dist_eq_norm] using hv') ?_
          unfold c
          exact (norm_add_le _ _).trans (by simp [Complex.norm_real])
    have hR3 : 0 ≤ R + 2 := by linarith only [hm, hmR]
    have hlinear : R + 2 ≤ (R + 2) * |t| := le_mul_of_one_le_right hR3 htone
    exact (norm_riemannZeta_le_three_mul_norm (hbounds v hv').1 (hbounds v hv').2).trans
      (by dsimp [B]; nlinarith only [hnorm, hlinear])
  let X : ℝ := A * |t| ^ (eps / 2)
  let Y : ℝ := B * |t|
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le hA
    (Real.one_le_rpow htone (by linarith only [heps]))
  have hY : 1 ≤ Y := one_le_mul_of_one_le_of_one_le hB htone
  have hzbound : ‖riemannZeta z‖ ≤ X * Y ^ (eps / 2) := by
    by_cases hin : ‖z - c‖ ≤ r
    · have hzin : z ∈ closedBall c r := by simpa only [mem_closedBall, dist_eq_norm] using hin
      exact (hinner' z hzin).trans
        (le_mul_of_one_le_right (by linarith only [hX])
          (Real.one_le_rpow hY (by linarith only [heps])))
    · have hz₁ : r ≤ ‖z - c‖ := le_of_not_ge hin
      let β := Real.log (‖z - c‖ / r) / Real.log (R / r)
      have hlogpos : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).2 hrR)
      have hβ₀ : 0 ≤ β :=
        div_nonneg (Real.log_nonneg ((one_le_div hr).2 hz₁)) hlogpos.le
      have hβbound : β ≤ eps / 2 := by
        refine (div_le_div_of_nonneg_right
          (Real.log_le_log (div_pos (hr.trans_le hz₁) hr)
            (div_le_div_of_nonneg_right hzmax hr.le)) hlogpos.le).trans hweight
      have hXβ : X ^ (1 - β) ≤ X := by
        calc
          _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith only [hβ₀])
          _ = X := Real.rpow_one X
      have hYβ : Y ^ β ≤ Y ^ (eps / 2) := Real.rpow_le_rpow_of_exponent_le hY hβbound
      calc
        _ ≤ X ^ (1 - β) * Y ^ β := norm_le_interp_of_mem_annulus hr hrR hf
          (fun v hv => hinner' v (sphere_subset_closedBall hv)) houter hz₁
          (hzmax.trans hdR.le)
        _ ≤ X * Y ^ (eps / 2) := by gcongr
  refine hzbound.trans_eq ?_
  dsimp [X, Y]
  rw [Real.mul_rpow (by linarith only [hB]) htpos.le]
  calc
    _ = (A * B ^ (eps / 2)) * (|t| ^ (eps / 2) * |t| ^ (eps / 2)) := by ring
    _ = _ := by rw [← Real.rpow_add htpos, show eps / 2 + eps / 2 = eps by ring]

end DiskGrowth

section Exclusion

open Complex Filter MeasureTheory Metric Set
open scoped Topology BigOperators
open D5.S3.Weil.Mertens.MobiusDyadicEnergy (mobiusDyadicDifference)

/-- For finite weighted energy, a zero-free edge strictly between the critical
line and the pole cannot have arbitrarily high clusters containing a selected
total multiplicity of `q` within radius `|t| ^ (-p)` when `p (2q - 1) > 2`. -/
private theorem no_selectedZeroCluster_atHighOrdinate
    {θ p : ℝ} {q : ℕ} (hθhalf : 1 / 2 < θ) (hθone : θ < 1) (hp : 0 < p)
    (hq : 0 < q) (hexponent : 2 < p * (2 * (q : ℝ) - 1))
    (hRight : ∀ z : ℂ, θ < z.re → z ≠ 1 → riemannZeta z ≠ 0)
    (hLine : ∀ y : ℝ, riemannZeta ((θ : ℂ) + (y : ℂ) * I) ≠ 0)
    (hE : IntegrableOn
      (fun x : ℝ => mobiusDyadicDifference x ^ 2 * x ^ (-(2 * θ - 1))) (Ioi 1)) :
    ∃ R T : ℝ, 0 < R ∧ 0 < T ∧
      ∀ t : ℝ, T ≤ |t| →
        ∀ r : ℝ, 0 < r → r ≤ |t| ^ (-p) →
          ∀ D : Function.locallyFinsuppWithin (closedBall ((θ : ℂ) + (t : ℂ) * I) R) ℤ,
            0 ≤ D →
            D ≤ MeromorphicOn.divisor riemannZeta (closedBall ((θ : ℂ) + (t : ℂ) * I) R) →
            D.support ⊆ closedBall ((θ : ℂ) + (t : ℂ) * I) r →
            (∀ w ∈ D.support, w.re < θ) →
            (∑ᶠ u, (D u).toNat) ≠ q := by
  let n : ℕ := 2 * q - 1
  have hn : n + 1 = 2 * q := by dsimp [n]; omega
  have hnR : (n : ℝ) = 2 * (q : ℝ) - 1 := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) hn
    push_cast at h
    linarith
  let eps := (p * (n : ℝ) - 2) / 4
  have heps : 0 < eps := by dsimp [eps]; rw [hnR]; linarith
  let γ := p * (n : ℝ) - (2 + 2 * eps)
  have hγ : 0 < γ := by dsimp [γ, eps]; rw [hnR]; linarith
  obtain ⟨R, A, T₀, hR, hA, hT₀, hζ⟩ :=
    norm_riemannZeta_le_rpow_on_boundary_disks hθhalf hθone heps hRight
  let K : ℝ := 4 + 4 * Real.pi *
    (∫ x in Ioi (1 : ℝ), mobiusDyadicDifference x ^ 2 * x ^ (-(2 * θ - 1))) /
    (1 - (2 : ℝ) ^ (θ - 1)) ^ 2
  let C : ℝ := A * (4 / R) ^ q
  let L : ℝ := K * (16 * C ^ 2)
  have hsmall : ∀ᶠ x : ℝ in atTop, x ^ (-p) < min 1 (R / 2) :=
    (tendsto_rpow_neg_atTop hp).eventually
      (eventually_lt_nhds (lt_min zero_lt_one (half_pos hR)))
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hsmall
  have hlarge : ∀ᶠ x : ℝ in atTop, L < x ^ γ :=
    (tendsto_rpow_atTop hγ).eventually (eventually_gt_atTop L)
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp hlarge
  let T := max (R + 1) (max T₀ (max T₁ T₂))
  refine ⟨R, T, hR, (by dsimp [T]; positivity), ?_⟩
  intro t ht r hr hrsmall D hD hLe hcluster hleft hqD
  let x := |t|
  let c : ℂ := (θ : ℂ) + (t : ℂ) * I
  have hxR : R + 1 ≤ x := (le_max_left _ _).trans ht
  have hx₁ : 1 ≤ x := by linarith only [hxR, hR]
  have hx : 0 < x := by linarith only [hx₁]
  have hxT₀ : T₀ ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hxT₁ : T₁ ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  have hxT₂ : T₂ ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  have hrmin : r ≤ min 1 (R / 2) := hrsmall.trans (hT₁ x hxT₁).le
  have hr₁ : r ≤ 1 := hrmin.trans (min_le_left _ _)
  have hrR : r ≤ R / 2 := hrmin.trans (min_le_right _ _)
  have hRr : 0 < R - r := by linarith only [hR, hrR]
  have havoid : (1 : ℂ) ∉ closedBall c R := by
    intro h
    have hnorm := (Complex.abs_im_le_norm ((1 : ℂ) - c)).trans
      (show ‖(1 : ℂ) - c‖ ≤ R by simpa only [mem_closedBall, dist_eq_norm] using h)
    have hc : c.im = t := by simp [c, Complex.mul_im]
    simp only [Complex.sub_im, Complex.one_im, hc, zero_sub, abs_neg] at hnorm
    linarith only [hnorm, hxR]
  let M := A * x ^ eps
  have hM : 0 < M := by positivity
  have hmass := cluster_mass_le_of_mobiusDyadicEnergy
    (θ := θ) (T := t) (by linarith only [hθhalf]) (by linarith only [hθone])
    hθone.ne hr hr₁ hrR hM havoid hD hLe hcluster hleft
    (fun v hv => hζ t hxT₀ v (sphere_subset_closedBall hv)) hLine hE
  change 2 * r / ((2 * (1 + x)) ^ 2 * (M * (2 * r / (R - r)) ^ (∑ᶠ u, (D u).toNat)) ^ 2) ≤ K
    at hmass
  rw [hqD] at hmass
  have hK : 0 ≤ K := (by positivity : 0 ≤ 2 * r /
    ((2 * (1 + x)) ^ 2 * (M * (2 * r / (R - r)) ^ q) ^ 2)).trans hmass
  have hradius : 2 * r / (R - r) ≤ (4 / R) * r := by
    apply (div_le_iff₀ hRr).2
    have h := (mul_le_mul_of_nonneg_left hrR (show 0 ≤ 4 / R * r by positivity))
    have hcancel : (4 / R * r) * (R / 2) = 2 * r := by field_simp; ring
    linarith only [h, hcancel]
  have hfactor : M * (2 * r / (R - r)) ^ q ≤ C * x ^ eps * r ^ q := by
    calc
      _ ≤ M * ((4 / R) * r) ^ q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hradius q) hM.le
      _ = _ := by rw [mul_pow]; dsimp [M, C]; ring
  have hweight : 2 * (1 + x) ≤ 4 * x := by linarith only [hx₁]
  have hden :
      (2 * (1 + x)) ^ 2 * (M * (2 * r / (R - r)) ^ q) ^ 2 ≤
        (4 * x) ^ 2 * (C * x ^ eps * r ^ q) ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ (by positivity) hweight 2)
      (pow_le_pow_left₀ (by positivity) hfactor 2) (by positivity) (by positivity)
  have htwo : 2 * r ≤ K * ((4 * x) ^ 2 * (C * x ^ eps * r ^ q) ^ 2) := by
    have hmass' := (div_le_iff₀ (by positivity :
      0 < (2 * (1 + x)) ^ 2 * (M * (2 * r / (R - r)) ^ q) ^ 2)).1 hmass
    exact hmass'.trans (mul_le_mul_of_nonneg_left hden hK)
  have hrewrite :
      K * ((4 * x) ^ 2 * (C * x ^ eps * r ^ q) ^ 2) =
        (L * x ^ (2 + 2 * eps) * r ^ n) * r := by
    have hX : x ^ (2 + 2 * eps) = x ^ (2 : ℕ) * (x ^ eps) ^ (2 : ℕ) := by
      have htwoExp : (2 : ℝ) * eps = eps * ((2 : ℕ) : ℝ) := by push_cast; ring
      rw [Real.rpow_add hx, htwoExp, Real.rpow_mul_natCast hx.le eps 2]
      norm_num
    have hrad : (r ^ q) ^ 2 = r ^ n * r := by
      rw [← pow_mul, mul_comm q, ← hn, pow_succ]
    calc
      _ = L * (x ^ (2 : ℕ) * (x ^ eps) ^ (2 : ℕ)) * (r ^ q) ^ 2 := by
        dsimp [L]
        ring
      _ = _ := by rw [hX, hrad]; ring
  have hnormalized : 2 ≤ L * x ^ (2 + 2 * eps) * r ^ n :=
    (mul_le_mul_iff_of_pos_right hr).mp (hrewrite ▸ htwo)
  have hL : 0 ≤ L := mul_nonneg hK (by positivity)
  have hrpow : r ^ n ≤ x ^ (-p * (n : ℝ)) := by
    rw [Real.rpow_mul_natCast hx.le]
    exact pow_le_pow_left₀ hr.le hrsmall n
  have hbound : 2 ≤ L * x ^ (-γ) := by
    calc
      _ ≤ L * x ^ (2 + 2 * eps) * r ^ n := hnormalized
      _ ≤ L * x ^ (2 + 2 * eps) * x ^ (-p * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hrpow (mul_nonneg hL (by positivity))
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hx]
        congr 2
        dsimp [γ]
        ring
  have hstrict : L * x ^ (-γ) < 1 := by
    rw [Real.rpow_neg hx.le, ← div_eq_mul_inv]
    exact (div_lt_one (by positivity)).2 (hT₂ x hxT₂)
  linarith only [hbound, hstrict]

open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa zero_re_le_abscissa)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
  (exists_nontrivial_zero_re_ge_half)

/-- At the unattained real-part supremum of nontrivial zeta zeros, finite critical
Möbius energy excludes high zero clusters of selected multiplicity `q` in
radius at most `|t| ^ (-p)` if `p (2q - 1) > 2`. -/
theorem no_selectedZeroCluster_atHighOrdinate_of_unattainedZeroAbscissa
    {p : ℝ} {q : ℕ} (hΘ : zeroAbscissa < 1)
    (hunattained : ∀ z : ℂ, IsNontrivialZero z → z.re ≠ zeroAbscissa)
    (hp : 0 < p) (hq : 0 < q) (hexponent : 2 < p * (2 * (q : ℝ) - 1))
    (hE : IntegrableOn
      (fun x : ℝ => mobiusDyadicDifference x ^ 2 * x ^ (-(2 * zeroAbscissa - 1))) (Ioi 1)) :
    ∃ R T : ℝ, 0 < R ∧ 0 < T ∧
      ∀ t : ℝ, T ≤ |t| →
        ∀ r : ℝ, 0 < r → r ≤ |t| ^ (-p) →
          ∀ D : Function.locallyFinsuppWithin
              (closedBall ((zeroAbscissa : ℂ) + (t : ℂ) * I) R) ℤ,
            0 ≤ D →
            D ≤ MeromorphicOn.divisor riemannZeta
              (closedBall ((zeroAbscissa : ℂ) + (t : ℂ) * I) R) →
            D.support ⊆ closedBall ((zeroAbscissa : ℂ) + (t : ℂ) * I) r →
            (∀ w ∈ D.support, w.re < zeroAbscissa) →
            (∑ᶠ u, (D u).toNat) ≠ q := by
  have habscissa :
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
  obtain ⟨hΘhalf, hRight, hLine⟩ := habscissa
  exact no_selectedZeroCluster_atHighOrdinate hΘhalf hΘ hp hq hexponent hRight hLine hE

end Exclusion

end D5.S3.Weil.ZetaPntBounds.MobiusBoundaryClusterExclusion
