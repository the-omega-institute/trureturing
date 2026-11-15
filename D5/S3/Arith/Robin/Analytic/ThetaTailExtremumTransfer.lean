/- GID: D5/S3/Arith/Robin/Analytic/ThetaTailExtremumTransfer
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ThetaTailExtremumTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional same-exponent actual theta-tail oscillation transfers to both signs of B. -/
/- Copyright 2026 The Omega Institute
   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at
       http://www.apache.org/licenses/LICENSE-2.0
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License. -/

import D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
import D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature
import D5.S3.Weil.Mertens.ActualThetaTailLaplace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-! The positive branch controls the theta error at the same compact maximum
that supplies the signed tail height. Prime points use distinct left and right
germs. The extrema and prime-jump method is related to J.-L. Nicolas,
Petites valeurs de la fonction d'Euler, J. Number Theory 17 (1983), 375-388,
Theorem 3(c) and Section 4, DOI 10.1016/0022-314X(83)90055-0.
The two-sign compact bracketing here is a conditional proof arrangement;
neither RH nor literature priority is asserted. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.ThetaTailExtremumTransfer

open RHSharpArithmeticEnvelope (B N w Jpsi S tails finite_cancellation)

private def K (x : ℝ) : ℝ :=
  -D5.S3.Weil.Mertens.ActualThetaTailLaplace.F x

private def E (x : ℝ) : ℝ := Chebyshev.theta x - x

private def kernel (x : ℝ) : ℝ := E x * w x

private def jump (x : ℝ) : ℝ := by
  classical
  exact if ∃ p : ℕ, p.Prime ∧ (p : ℝ) = x then Real.log x else 0

private lemma jump_nat (n : ℕ) :
    jump (n : ℝ) = if n.Prime then Real.log (n : ℝ) else 0 := by
  have he : (∃ p : ℕ, p.Prime ∧ (p : ℝ) = (n : ℝ)) ↔ n.Prime := by
    constructor
    · rintro ⟨p, hp, he⟩
      have hpn : p = n := Nat.cast_injective he
      simpa only [hpn] using hp
    · intro hn
      exact ⟨n, hn, rfl⟩
  simp only [jump, he]

private lemma theta_nat_step (n : ℕ) :
    Chebyshev.theta ((n + 1 : ℕ) : ℝ) = Chebyshev.theta (n : ℝ) +
      if (n + 1).Prime then Real.log ((n + 1 : ℕ) : ℝ) else 0 := by
  classical
  simp only [Chebyshev.theta_eq_sum_primesLE_log]
  rw [Nat.primesLE_succ]
  split_ifs with hp
  · rw [Finset.sum_insert (Nat.notMem_primesLE n)]
    ring
  · simp

/- The right germ includes x. The left germ excludes x, including at primes. -/
private lemma theta_germs {x : ℝ} (hx : 2 < x) :
    (∀ᶠ y in 𝓝[Ici x] x, Chebyshev.theta y = Chebyshev.theta x) ∧
    (∀ᶠ y in 𝓝[Iio x] x, Chebyshev.theta y = Chebyshev.theta x - jump x) := by
  classical
  have hx0 : 0 ≤ x := by linarith
  constructor
  · filter_upwards [Ico_mem_nhdsGE (Nat.lt_floor_add_one x)] with y hy
    have hyfloor : ⌊y⌋₊ = ⌊x⌋₊ :=
      Nat.floor_eq_on_Ico ⌊x⌋₊ y ⟨(Nat.floor_le hx0).trans hy.1, hy.2⟩
    calc
      Chebyshev.theta y = Chebyshev.theta (⌊y⌋₊ : ℝ) :=
        Chebyshev.theta_eq_theta_coe_floor y
      _ = Chebyshev.theta (⌊x⌋₊ : ℝ) := by rw [hyfloor]
      _ = Chebyshev.theta x := (Chebyshev.theta_eq_theta_coe_floor x).symm
  · by_cases hnat : ∃ n : ℕ, (n : ℝ) = x
    · obtain ⟨n, rfl⟩ := hnat
      have hn1 : 1 ≤ n := by
        have : (1 : ℝ) ≤ (n : ℝ) := by linarith
        exact_mod_cast this
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast (Nat.sub_add_cancel hn1)
      have hstep := theta_nat_step (n - 1)
      rw [Nat.sub_add_cancel hn1] at hstep
      have hleft : Chebyshev.theta ((n - 1 : ℕ) : ℝ) =
          Chebyshev.theta (n : ℝ) - jump (n : ℝ) := by
        rw [jump_nat]
        linarith only [hstep]
      filter_upwards [Ico_mem_nhdsLT
        (show ((n - 1 : ℕ) : ℝ) < (n : ℝ) by linarith)] with y hy
      have hyfloor : ⌊y⌋₊ = n - 1 :=
        Nat.floor_eq_on_Ico (n - 1) y ⟨hy.1, by linarith [hy.2]⟩
      calc
        Chebyshev.theta y = Chebyshev.theta (⌊y⌋₊ : ℝ) :=
          Chebyshev.theta_eq_theta_coe_floor y
        _ = Chebyshev.theta ((n - 1 : ℕ) : ℝ) := by rw [hyfloor]
        _ = Chebyshev.theta (n : ℝ) - jump (n : ℝ) := hleft
    · have hfloorlt : (⌊x⌋₊ : ℝ) < x :=
        lt_of_le_of_ne (Nat.floor_le hx0) (fun he => hnat ⟨⌊x⌋₊, he⟩)
      have hnojump : ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) = x := by
        rintro ⟨p, _, hp⟩
        exact hnat ⟨p, hp⟩
      have hj : jump x = 0 := by simp only [jump, ite_eq_right hnojump]
      filter_upwards [Ico_mem_nhdsLT hfloorlt] with y hy
      have hyfloor : ⌊y⌋₊ = ⌊x⌋₊ :=
        Nat.floor_eq_on_Ico ⌊x⌋₊ y
          ⟨hy.1, hy.2.trans (Nat.lt_floor_add_one x)⟩
      rw [hj, sub_zero, Chebyshev.theta_eq_theta_coe_floor y, hyfloor]
      exact (Chebyshev.theta_eq_theta_coe_floor x).symm

private lemma jump_bounds {x : ℝ} (hx : 2 < x) :
    0 ≤ jump x ∧ jump x ≤ Real.log x := by
  have hl : 0 ≤ Real.log x := (Real.log_pos (by linarith : 1 < x)).le
  classical
  unfold jump
  split_ifs <;> constructor <;> first | exact hl | exact le_rfl

private lemma density_continuousAt {x : ℝ} (hx : 1 < x) : ContinuousAt w x := by
  have hx0 : x ≠ 0 := ne_of_gt (by linarith : 0 < x)
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  change ContinuousAt (fun t : ℝ => (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)) x
  exact ((Real.continuousAt_log hx0).add continuousAt_const).div
    ((continuousAt_id.pow 2).mul ((Real.continuousAt_log hx0).pow 2))
    (mul_ne_zero (pow_ne_zero 2 hx0) (pow_ne_zero 2 hl0))

private lemma density_pos {x : ℝ} (hx : 1 < x) : 0 < w x := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_pos hx
  dsimp [w, ActualRobinClockCovariance.activationDensity]
  positivity

private lemma kernel_measurable : Measurable kernel := by
  change Measurable (fun x : ℝ => (Chebyshev.theta x - x) *
    ((Real.log x + 1) / (x ^ 2 * Real.log x ^ 2)))
  exact (Chebyshev.theta_mono.measurable.sub measurable_id).mul (by fun_prop)

private lemma kernel_integrable {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn kernel (Ioi x) :=
  (D5.S3.Arith.Robin.ThetaTailRobinWitness.theta_tail_mertens_robin x hx).1

private lemma K_continuous : ContinuousOn K (Ici 2) := by
  change ContinuousOn (fun x => - -(∫ t in Ioi x, kernel t)) (Ici 2)
  simp only [neg_neg]
  exact (kernel_integrable (x := 2) le_rfl).continuousOn_Ici_primitive_Ioi

private lemma kernel_limits {x : ℝ} (hx : 2 < x) :
    Tendsto kernel (𝓝[Ioi x] x ⊓ ae volume) (𝓝 (E x * w x)) ∧
    Tendsto kernel (𝓝[Iic x] x ⊓ ae volume) (𝓝 ((E x - jump x) * w x)) := by
  have hg := theta_germs hx
  have hr : Tendsto Chebyshev.theta (𝓝[Ici x] x) (𝓝 (Chebyshev.theta x)) :=
    tendsto_const_nhds.congr' (by filter_upwards [hg.1] with y hy using hy.symm)
  have hl : Tendsto Chebyshev.theta (𝓝[Iio x] x) (𝓝 (Chebyshev.theta x - jump x)) :=
    tendsto_const_nhds.congr' (by filter_upwards [hg.2] with y hy using hy.symm)
  have hleft : 𝓝[Iic x] x ⊓ ae volume ≤ 𝓝[Iio x] x := by
    change (𝓝[Iic x] x ⊓ ae volume) ≤ 𝓝 x ⊓ 𝓟 (Iio x)
    refine le_inf (inf_le_left.trans nhdsWithin_le_nhds) ?_
    rw [le_principal_iff]
    have hle : ∀ᶠ y in 𝓝[Iic x] x ⊓ ae volume, y ≤ x :=
      Filter.Eventually.filter_mono inf_le_left
        (self_mem_nhdsWithin : ∀ᶠ y in 𝓝[Iic x] x, y ∈ Iic x)
    have hne : ∀ᶠ y in 𝓝[Iic x] x ⊓ ae volume, y ≠ x :=
      (volume.ae_ne x).filter_mono inf_le_right
    filter_upwards [hle, hne] with y hy hne
    exact lt_of_le_of_ne hy hne
  have hright : 𝓝[Ioi x] x ⊓ ae volume ≤ 𝓝[Ici x] x :=
    inf_le_left.trans (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hd := (density_continuousAt (show 1 < x by linarith)).tendsto
  constructor
  · exact ((hr.mono_left hright).sub (tendsto_id.mono_left
      (hright.trans nhdsWithin_le_nhds))).mul
        (hd.mono_left (hright.trans nhdsWithin_le_nhds))
  · have hlim := ((hl.mono_left hleft).sub (tendsto_id.mono_left
      (hleft.trans nhdsWithin_le_nhds))).mul
        (hd.mono_left (hleft.trans nhdsWithin_le_nhds))
    have hval : (Chebyshev.theta x - jump x - x) * w x =
        (E x - jump x) * w x := by dsimp [E]; ring
    rw [hval] at hlim
    exact hlim

private lemma K_deriv_from_limit {x c : ℝ} {s t : Set ℝ} (hx : 2 < x)
    [intervalIntegral.FTCFilter x (𝓝[s] x) (𝓝[t] x)]
    (hc : Tendsto kernel (𝓝[t] x ⊓ ae volume) (𝓝 c)) :
    HasDerivWithinAt K (-c) s x := by
  have hp := intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_right
    (f := kernel) (a := x) (b := x) (s := s) (t := t)
    (by simp : IntervalIntegrable kernel volume x x)
    kernel_measurable.aestronglyMeasurable.stronglyMeasurableAtFilter hc
  have hd := (hasDerivWithinAt_const (x := x) (s := s) (c := K x)).sub hp
  simp only [zero_sub] at hd
  apply hd.congr_of_eventuallyEq
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hx)] with y hy
    have hi := intervalIntegral.integral_Ioi_sub_Ioi'
      (kernel_integrable hx.le) (kernel_integrable hy.le)
    have he : K x - K y = ∫ t in x..y, kernel t := by
      simpa only [K, D5.S3.Weil.Mertens.ActualThetaTailLaplace.F,
        neg_neg, kernel, E] using hi
    change K y = K x - ∫ t in x..y, kernel t
    linarith only [he]
  · simp

private lemma K_one_sided_derivatives {x : ℝ} (hx : 2 < x) :
    HasDerivWithinAt K (-E x * w x) (Ici x) x ∧
    HasDerivWithinAt K (-(E x - jump x) * w x) (Iic x) x := by
  have hlim := kernel_limits hx
  constructor
  · simpa only [neg_mul] using
      K_deriv_from_limit (s := Ici x) (t := Ioi x) hx hlim.1
  · simpa only [neg_mul] using
      K_deriv_from_limit (s := Iic x) (t := Iic x) hx hlim.2

private def barrier (δ b x : ℝ) : ℝ := K x - δ * x ^ (-b)

private def r (δ b x : ℝ) : ℝ :=
  δ * b * x ^ (1 - b) * Real.log x ^ 2 / (Real.log x + 1)

private lemma r_mul_density {δ b x : ℝ} (hx : 2 < x) :
    r δ b x * w x = δ * b * x ^ (-b - 1) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have he : x ^ (1 - b) = x ^ (-b - 1) * x ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hx0]
    congr 1
    ring
  dsimp [r, w, ActualRobinClockCovariance.activationDensity]
  rw [he]
  field_simp [hx0.ne', hl.ne', (show Real.log x + 1 ≠ 0 by linarith)]

private lemma maximum_error_control {δ b x : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hb1 : b < 1) (hx : 2 < x)
    (hmax : IsLocalMax (barrier δ b) x) :
    r δ b x ≤ E x ∧ E x ≤ r δ b x + jump x ∧
      0 ≤ E x ∧ E x ≤ (δ * b + 1) * x ^ (1 - b) * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hw : 0 < w x := density_pos (by linarith)
  obtain ⟨hKr, hKl⟩ := K_one_sided_derivatives hx
  have hpower := (Real.hasDerivAt_rpow_const (x := x) (p := -b)
    (Or.inl hx0.ne')).const_mul δ
  have hR : HasDerivWithinAt (barrier δ b)
      (-E x * w x + δ * b * x ^ (-b - 1)) (Ici x) x := by
    convert hKr.sub hpower.hasDerivWithinAt using 1
    · rfl
    · ring
  have hL : HasDerivWithinAt (barrier δ b)
      (-(E x - jump x) * w x + δ * b * x ^ (-b - 1)) (Iic x) x := by
    convert hKl.sub hpower.hasDerivWithinAt using 1
    · rfl
    · ring
  have hrightdir : (1 : ℝ) ∈ posTangentConeAt (Ici x) x := by
    apply mem_posTangentConeAt_of_segment_subset
    exact (convex_Ici x).segment_subset self_mem_Ici (by simp)
  have hleftdir : (-1 : ℝ) ∈ posTangentConeAt (Iic x) x := by
    apply mem_posTangentConeAt_of_segment_subset
    exact (convex_Iic x).segment_subset self_mem_Iic (by simp)
  have hsR := (hmax.isLocalMaxOn (Ici x)).hasFDerivWithinAt_nonpos
    hR.hasFDerivWithinAt hrightdir
  have hsL := (hmax.isLocalMaxOn (Iic x)).hasFDerivWithinAt_nonpos
    hL.hasFDerivWithinAt hleftdir
  change 1 * (-E x * w x + δ * b * x ^ (-b - 1)) ≤ 0 at hsR
  change (-1) * (-(E x - jump x) * w x + δ * b * x ^ (-b - 1)) ≤ 0 at hsL
  rw [← r_mul_density hx] at hsR hsL
  have hlow : r δ b x ≤ E x := by
    apply (mul_le_mul_iff_left₀ hw).mp
    nlinarith only [hsR]
  have hupp : E x ≤ r δ b x + jump x := by
    apply (mul_le_mul_iff_left₀ hw).mp
    nlinarith only [hsL]
  have hr0 : 0 ≤ r δ b x := by dsimp [r]; positivity
  have hrbound : r δ b x ≤ δ * b * x ^ (1 - b) * Real.log x := by
    unfold r
    apply (div_le_iff₀ (by linarith : 0 < Real.log x + 1)).mpr
    have hm : 0 ≤ δ * b * x ^ (1 - b) * Real.log x := by positivity
    nlinarith only [hm]
  have hscale : 1 ≤ x ^ (1 - b) :=
    Real.one_le_rpow (by linarith) (by linarith)
  have hlogscale : Real.log x ≤ x ^ (1 - b) * Real.log x := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hscale hlog.le
  refine ⟨hlow, hupp, hr0.trans hlow, ?_⟩
  have hj := (jump_bounds hx).2
  nlinarith only [hupp, hrbound, hj, hlogscale]

private lemma exists_late_positive_maximum
    {b cplus cminus : ℝ} (hcp : 0 < cplus) (hcm : 0 < cminus)
    (hplus : ∀ T : ℝ, ∃ x : ℝ, max T 2 < x ∧ cplus * x ^ (-b) ≤ K x)
    (hminus : ∀ T : ℝ, ∃ x : ℝ, max T 2 < x ∧ K x ≤ -cminus * x ^ (-b))
    (T : ℝ) :
    ∃ x : ℝ, max T 2 < x ∧ (cplus / 2) * x ^ (-b) < K x ∧
      IsLocalMax (barrier (cplus / 2) b) x := by
  let δ : ℝ := cplus / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨L, hL, hKL⟩ := hminus (max T 2)
  obtain ⟨z, hz, hKz⟩ := hplus L
  obtain ⟨R, hR, hKR⟩ := hminus z
  have hL2 : 2 < L := (le_max_right _ _).trans_lt hL
  have hLz : L < z := (le_max_left _ _).trans_lt hz
  have hzR : z < R := (le_max_left _ _).trans_lt hR
  have hLR : L < R := hLz.trans hzR
  have hnegative {u : ℝ} (hu : 0 < u) (hKu : K u ≤ -cminus * u ^ (-b)) :
      barrier δ b u < 0 := by
    have hp : 0 < u ^ (-b) := Real.rpow_pos_of_pos hu _
    dsimp [barrier]
    nlinarith only [hKu, mul_pos hδ hp, mul_pos hcm hp]
  have hBL : barrier δ b L < 0 := hnegative (by linarith) hKL
  have hBR : barrier δ b R < 0 := hnegative (by linarith) hKR
  have hBz : 0 < barrier δ b z := by
    have hp : 0 < z ^ (-b) := Real.rpow_pos_of_pos (by linarith) _
    dsimp [barrier, δ]
    nlinarith only [hKz, mul_pos hcp hp]
  have hcont : ContinuousOn (barrier δ b) (Icc L R) := by
    apply (K_continuous.mono (fun u hu => hL2.le.trans hu.1)).sub
    intro u hu
    exact ((continuousAt_id.rpow_const
      (Or.inl (ne_of_gt (show 0 < u by linarith [hu.1])))).const_mul δ).continuousWithinAt
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨z, ⟨hLz.le, hzR.le⟩⟩ hcont
  have hpos : 0 < barrier δ b x :=
    hBz.trans_le ((isMaxOn_iff.mp hmax) z ⟨hLz.le, hzR.le⟩)
  have hLx : L < x := by
    rcases hx.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hpos
      linarith only [hpos, hBL]
  have hxR : x < R := by
    rcases hx.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hpos
      linarith only [hpos, hBR]
  refine ⟨x, ((le_max_left _ _).trans_lt hL).trans hLx, ?_, ?_⟩
  · change δ * x ^ (-b) < K x
    dsimp [barrier] at hpos
    linarith only [hpos]
  · exact hmax.isLocalMax (Icc_mem_nhds hLx hxR)

private lemma B_decomposition {x : ℝ} (hx : 2 ≤ x) :
    B x = K x + (Mertens.E₃ x + Mertens.E₂p x) + N x := by
  have ht := tails hx
  have hs : Jpsi x - S x = K x := by
    rw [Jpsi, S, ← integral_sub ht.1 ht.2.1]
    change (∫ t in Ioi x, (Chebyshev.psi t - t) * w t -
      (Chebyshev.psi t - Chebyshev.theta t) * w t) =
        -D5.S3.Weil.Mertens.ActualThetaTailLaplace.F x
    rw [D5.S3.Weil.Mertens.ActualThetaTailLaplace.F, neg_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    change (Chebyshev.psi t - t) * w t -
      (Chebyshev.psi t - Chebyshev.theta t) * w t = (Chebyshev.theta t - t) * w t
    ring
  rw [ht.2.2, hs]

private lemma N_nonpos {x : ℝ} (hx : 1 < x) (hθ : 1 < Chebyshev.theta x) :
    N x ≤ 0 := by
  have hg := D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature.loglog_tangent_gap_quadratic
    hx hθ
  dsimp only at hg
  have hm : 1 < max x (Chebyshev.theta x) := hx.trans_le (le_max_left _ _)
  have hl : 0 < Real.log (max x (Chebyshev.theta x)) := Real.log_pos hm
  have hm0 : 0 < max x (Chebyshev.theta x) := by linarith
  have hcurv : 0 ≤ ((1 + Real.log (max x (Chebyshev.theta x))) /
      ((max x (Chebyshev.theta x)) ^ 2 * Real.log (max x (Chebyshev.theta x)) ^ 2)) *
        (Chebyshev.theta x - x) ^ 2 / 2 := by positivity
  dsimp [N]
  linarith only [hg.1, hcurv]

private lemma eventually_theta_gt_one : ∀ᶠ x : ℝ in atTop, 1 < Chebyshev.theta x := by
  have hp := D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2.eventually
    (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hp, eventually_gt_atTop (2 : ℝ)] with x hx hx2
  have hx0 : 0 < x := by linarith
  have ht : x / 2 < Chebyshev.theta x := by
    have h := (lt_div_iff₀ hx0).mp hx
    linarith only [h]
  linarith only [ht, hx2]

/- Both estimates use the original exponent b. The two strict exponent
   hypotheses enter separate limits: 1-b>0 for 4/x and b>0 for log/x^b. -/
private lemma eventual_payment {b ε C : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      4 / x ≤ ε * x ^ (-b) ∧
      C * Real.log x / x ^ (2 * b) ≤ ε * x ^ (-b) := by
  have hf : Tendsto (fun x : ℝ => 4 * x ^ (-(1 - b))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - b)).const_mul 4
  have hq : Tendsto (fun x : ℝ => C * (Real.log x / x ^ b)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (isLittleO_log_rpow_atTop hb).tendsto_div_nhds_zero.const_mul C
  filter_upwards [hf.eventually_lt_const hε, hq.eventually_lt_const hε,
    eventually_gt_atTop (0 : ℝ)] with x hfx hqx hx0
  have hpower : 0 ≤ x ^ (-b) := Real.rpow_nonneg hx0.le _
  have hfinite : (4 * x ^ (-(1 - b))) * x ^ (-b) = 4 / x := by
    rw [mul_assoc, ← Real.rpow_add hx0,
      show -(1 - b) + -b = (-1 : ℝ) by ring, Real.rpow_neg_one]
    ring
  have hquad : (C * (Real.log x / x ^ b)) * x ^ (-b) =
      C * Real.log x / x ^ (2 * b) := by
    have hp : x ^ (2 * b) = x ^ b * x ^ b := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [hp, Real.rpow_neg hx0.le]
    field_simp [(Real.rpow_pos_of_pos hx0 b).ne']
  constructor
  · rw [← hfinite]
    exact mul_le_mul_of_nonneg_right hfx.le hpower
  · rw [← hquad]
    exact mul_le_mul_of_nonneg_right hqx.le hpower

private lemma N_bound_at_maximum {δ b x : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hb1 : b < 1)
    (hx : 2 < x) (hexp : Real.exp 2 ≤ x)
    (hmax : IsLocalMax (barrier δ b) x) :
    |N x| ≤ (8 * (δ * b + 1) ^ 2) * Real.log x / x ^ (2 * b) := by
  obtain ⟨_, _, hE0, hE⟩ := maximum_error_control hδ hb hb1 hx hmax
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have htheta : x / 2 ≤ Chebyshev.theta x := by
    dsimp [E] at hE0
    linarith only [hE0, hx0]
  have hdiv : E x / x ≤ (δ * b + 1) * x ^ (-b) * Real.log x := by
    have he : x ^ (1 - b) / x = x ^ (-b) := by
      rw [← Real.rpow_sub_one hx0.ne']
      congr 1
      ring
    calc
      E x / x ≤ ((δ * b + 1) * x ^ (1 - b) * Real.log x) / x :=
        div_le_div_of_nonneg_right hE hx0.le
      _ = (δ * b + 1) * (x ^ (1 - b) / x) * Real.log x := by ring
      _ = (δ * b + 1) * x ^ (-b) * Real.log x := by rw [he]
  have hs := pow_le_pow_left₀ (div_nonneg hE0 hx0.le) hdiv 2
  calc
    |N x| ≤ 8 * (E x / x) ^ 2 / Real.log x :=
      D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope.nonlinear_quadratic hexp htheta
    _ ≤ 8 * ((δ * b + 1) * x ^ (-b) * Real.log x) ^ 2 / Real.log x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hlog.le
    _ = (8 * (δ * b + 1) ^ 2) * Real.log x / x ^ (2 * b) := by
      have hp : x ^ (2 * b) = x ^ b * x ^ b := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      rw [hp, Real.rpow_neg hx0.le]
      field_simp [hlog.ne', (Real.rpow_pos_of_pos hx0 b).ne']

/-- The same-exponent, two-sign actual theta tail forces both signs of the
literal arithmetic B, with coefficients cplus/4 and cminus/2. -/
theorem actual_theta_tail_omega_pm_to_B
    {b cplus cminus : ℝ}
    (hb : 0 < b) (hb1 : b < 1)
    (hcp : 0 < cplus) (hcm : 0 < cminus)
    (hplus : ∀ T : ℝ, ∃ x : ℝ, max T 2 < x ∧
      cplus * Real.rpow x (-b) ≤
        -D5.S3.Weil.Mertens.ActualThetaTailLaplace.F x)
    (hminus : ∀ T : ℝ, ∃ x : ℝ, max T 2 < x ∧
      -D5.S3.Weil.Mertens.ActualThetaTailLaplace.F x ≤
        -cminus * Real.rpow x (-b)) :
    (∀ T : ℝ, ∃ x : ℝ, max T 2 < x ∧
      (cplus / 4) * Real.rpow x (-b) ≤
        D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.B x) ∧
    (∀ T : ℝ, ∃ x : ℝ, max T 2 < x ∧
      D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.B x ≤
        -(cminus / 2) * Real.rpow x (-b)) := by
  constructor
  · let δ : ℝ := cplus / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hpay := eventual_payment (C := 8 * (δ * b + 1) ^ 2)
      hb hb1 (show 0 < cplus / 8 by positivity)
    obtain ⟨X, hX⟩ := eventually_atTop.mp hpay
    intro T
    obtain ⟨x, hx, hKx, hmax⟩ := exists_late_positive_maximum hcp hcm hplus hminus
      (max (max T X) (Real.exp 2))
    have hxbig : max (max T X) (Real.exp 2) < x := (le_max_left _ _).trans_lt hx
    have hx2 : 2 < x := (le_max_right _ _).trans_lt hx
    have hxT : T < x := (le_max_left T X).trans_lt
      ((le_max_left _ _).trans_lt hxbig)
    have hxX : X ≤ x := ((le_max_right T X).trans
      (le_max_left _ _)).trans hxbig.le
    have hxexp : Real.exp 2 ≤ x := (le_max_right _ _).trans hxbig.le
    have hfinite := abs_le.mp (finite_cancellation hx2.le)
    have hquad := abs_le.mp (N_bound_at_maximum hδ hb hb1 hx2 hxexp hmax)
    have hp := hX x hxX
    refine ⟨x, max_lt hxT hx2, ?_⟩
    rw [B_decomposition hx2.le]
    change (cplus / 4) * x ^ (-b) ≤ K x + (Mertens.E₃ x + Mertens.E₂p x) + N x
    change δ * x ^ (-b) < K x at hKx
    dsimp [δ] at hKx hp hquad
    linarith only [hKx, hfinite.1, hquad.1, hp.1, hp.2]
  · have hpay := eventual_payment (C := 0) hb hb1
      (show 0 < cminus / 2 by positivity)
    obtain ⟨X, hX⟩ := eventually_atTop.mp (hpay.and eventually_theta_gt_one)
    intro T
    obtain ⟨x, hx, hKx⟩ := hminus (max T X)
    have hx2 : 2 < x := (le_max_right _ _).trans_lt hx
    have hxT : T < x := (le_max_left T X).trans_lt ((le_max_left _ _).trans_lt hx)
    have hxX : X ≤ x := (le_max_right T X).trans ((le_max_left _ _).trans hx.le)
    have hp := hX x hxX
    have hN := N_nonpos (by linarith : 1 < x) hp.2
    have hfinite := (abs_le.mp (finite_cancellation hx2.le)).2
    refine ⟨x, max_lt hxT hx2, ?_⟩
    rw [B_decomposition hx2.le]
    change K x ≤ -cminus * x ^ (-b) at hKx
    change K x + (Mertens.E₃ x + Mertens.E₂p x) + N x ≤ -(cminus / 2) * x ^ (-b)
    linarith only [hKx, hfinite, hN, hp.1.1]

end D5.S3.Arith.Robin.Analytic.ThetaTailExtremumTransfer


