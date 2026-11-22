/- GID: D5/S3/Arith/Robin/PriceRecord/IntegerInfimumSharpLimit
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/IntegerInfimumSharpLimit
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: The sharp limit of the normalized gap between the full integer and real infima. -/

import D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope
import D5.S3.Arith.Robin.PriceRecord.RealInfimumSecondOrder
import D5.S3.Arith.Robin.PriceRecord.ActualRoundingFullLimit
import D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature

/-! The finite integer squeeze combines the sum of exact prime price losses
with the tangent remainder at each allocation's own clock. The real
calibration error and the integer tangent error vanish separately. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.IntegerInfimumSharpLimit

open Real Finset Filter Set
open scoped Topology
open BoundaryPrimePrice OwnClockFixedSupport FixedSupportIntegerActivationEnvelope
open RealInfimumPrimeBoundary PrimeBoundarySecondOrder
open D5.S3.Arith.Robin.ActualRobinClockCovariance (g)
open D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature (loglog_tangent_gap_quadratic)

lemma fixed_price_tangent_bound {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) (hlog : 1 ≤ log (theta S)) {r : ℝ} (hr : 0 < r)
    {x : ℕ → ℝ} (hx : admissible S x) (hsmall : phi S x - baseline S < r) :
    let H := theta S
    let ell := log H
    let A := exp (ell * (exp r - 1)) - 1
    tangentRemainder H (clock S x) ≤ A ^ 2 / ell := by
  let H := theta S
  let ell := log H
  let T := clock S x
  let u := (T - H) / H
  let A := exp (ell * (exp r - 1)) - 1
  change tangentRemainder H T ≤ A ^ 2 / ell
  have hH : 1 < H := theta_gt_one hS hcard
  have hH0 : 0 < H := zero_lt_one.trans hH
  have hHT : H ≤ T := theta_le_clock hS hx
  have hT : 1 < T := hH.trans_le hHT
  have hell0 : 0 < ell := log_pos hH
  have hdef : 0 ≤ deficiency S x := by
    change 0 ≤ -(∑ p ∈ S, log (1 - probability p (x p)))
    apply neg_nonneg.mpr
    apply sum_nonpos
    intro p hp
    have hpR : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
    have hprob := probability_mem hpR (hx p hp)
    exact log_nonpos (sub_nonneg.mpr hprob.2.le) (sub_le_self _ hprob.1.le)
  have hobjective : phi S x - baseline S =
        terminalCost (clock S x) - terminalCost (theta S) + deficiency S x := by
    have hbenefit : (∑ p ∈ S, benefit p (x p)) =
        (∑ p ∈ S, log (1 - probability p (x p))) -
          (∑ p ∈ S, log (1 - (p : ℝ) ^ (-1 : ℝ))) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl (fun p hp => benefit_log
        (by exact_mod_cast (hS p hp).one_lt) (hx p hp))
    dsimp only [phi, baseline, deficiency]
    rw [hbenefit]
    ring
  have hloglog : log (log T) < log ell + r := by
    change terminalCost (clock S x) < terminalCost (theta S) + r
    linarith only [hobjective, hdef, hsmall]
  have hlogT : log T < ell * exp r := by
    simpa only [exp_add, exp_log hell0] using (log_lt_iff_lt_exp (log_pos hT)).mp hloglog
  have hclock : T < H * exp (ell * (exp r - 1)) := by
    have h := (log_lt_iff_lt_exp (zero_lt_one.trans hT)).mp hlogT
    rw [show ell * exp r = log H + ell * (exp r - 1) by
          change ell * exp r = ell + ell * (exp r - 1)
          ring,
        exp_add, exp_log hH0] at h
    exact h
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hHT) hH0.le
  have huA : u < A := by
    apply (div_lt_iff₀ hH0).mpr
    calc
      T - H < H * exp (ell * (exp r - 1)) - H := sub_lt_sub_right hclock H
      _ = A * H := by dsimp only [A]; ring
  have hA : 0 ≤ A := by
    have he : 0 ≤ exp r - 1 := by
      rw [sub_nonneg, ← exp_zero]
      exact exp_le_exp.mpr hr.le
    have h := exp_le_exp.mpr (mul_nonneg hell0.le he)
    exact sub_nonneg.mpr (by simpa only [exp_zero] using h)
  have hcurv := (loglog_tangent_gap_quadratic hH hT).2
  dsimp only at hcurv
  rw [min_eq_left hHT] at hcurv
  have hcoeff : (1 + ell) / (2 * ell) ≤ 1 :=
    (div_le_iff₀ (mul_pos (by norm_num) hell0)).mpr
      (by linarith only [show 1 ≤ ell from hlog])
  calc
    tangentRemainder H T ≤ (1 + ell) / (H ^ 2 * ell ^ 2) * (T - H) ^ 2 / 2 := by
      have hnormal : tangentRemainder H T =
          log (log H) + (T - H) / (H * log H) - log (log T) := by
        dsimp only [tangentRemainder, terminalCost, g]
        ring
      rw [hnormal]
      exact hcurv
    _ = (1 + ell) / (2 * ell) * (u ^ 2 / ell) := by
      dsimp only [u]
      field_simp [hH0.ne', hell0.ne'] <;> ring
    _ ≤ u ^ 2 / ell := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hcoeff (div_nonneg (sq_nonneg u) hell0.le)
    _ ≤ A ^ 2 / ell :=
      div_le_div_of_nonneg_right ((sq_le_sq₀ hu hA).mpr huA.le) hell0.le

/-- Evaluating all prime prices at the baseline clock gives an exact identity
with the tangent remainder at the vector's actual clock. -/
private theorem fixed_price_loss_identity (S : Finset ℕ) (x : ℕ → ℝ) :
    let H := theta S
    let lam := g H
    let b : ℕ → ℝ := fun p => boundary p lam
    let Q := phi S b - baseline S + tangentRemainder H (clock S b)
    phi S x - baseline S =
      Q + (∑ p ∈ S, priceLoss p lam (x p)) - tangentRemainder H (clock S x) := by
  let H := theta S
  let lam := g H
  let b : ℕ → ℝ := fun p => boundary p lam
  let Q := phi S b - baseline S + tangentRemainder H (clock S b)
  change phi S x - baseline S =
    Q + (∑ p ∈ S, priceLoss p lam (x p)) - tangentRemainder H (clock S x)
  have hprice (y : ℕ → ℝ) :
      (∑ p ∈ S, priceObjective p lam (y p)) =
        (∑ p ∈ S, benefit p (y p)) - lam * clock S y := by
    simp only [priceObjective, clock, sum_sub_distrib, mul_sum, mul_assoc]
  have hsum : (∑ p ∈ S, priceLoss p lam (x p)) =
      (∑ p ∈ S, benefit p (b p)) - (∑ p ∈ S, benefit p (x p)) +
        lam * (clock S x - clock S b) := by
    change (∑ p ∈ S, (priceObjective p lam (b p) - priceObjective p lam (x p))) = _
    rw [sum_sub_distrib, hprice, hprice]
    ring
  rw [hsum]
  dsimp only [Q, phi, tangentRemainder, lam]
  ring

/-- A lower bound on the total fixed-price loss gives a pointwise bound on the
whole sublevel, with the complementary range covered by the threshold. -/
private theorem fixed_price_sublevel_lower {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) (hlog : 1 ≤ log (theta S)) {r : ℝ} (hr : 0 < r)
    {x : ℕ → ℝ} (hx : admissible S x) {gap : ℝ}
    (hgap : gap ≤ ∑ p ∈ S, priceLoss p (g (theta S)) (x p)) :
    let H := theta S
    let ell := log H
    let lam := g H
    let b : ℕ → ℝ := fun p => boundary p lam
    let Q := phi S b - baseline S + tangentRemainder H (clock S b)
    let A := exp (ell * (exp r - 1)) - 1
    min r (Q + gap - A ^ 2 / ell) ≤ phi S x - baseline S := by
  dsimp only
  by_cases hlarge : r ≤ phi S x - baseline S
  · exact (min_le_left _ _).trans hlarge
  · have hcurve := fixed_price_tangent_bound hS hcard hlog hr hx (lt_of_not_ge hlarge)
    have hid := fixed_price_loss_identity S x
    dsimp only at hcurve hid
    refine (min_le_right _ _).trans ?_
    linarith only [hcurve, hid, hgap]

/-- The exact integer losses replace the zero real loss in the fixed-price
squeeze. The lower bound applies to the entire admissible image. One vector
of attaining integer exponents supplies the upper bound. -/
private theorem integer_infimum_fixed_price_squeeze {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) (hlog : 1 ≤ log (theta S)) {r : ℝ} (hr : 0 < r) :
    let H := theta S
    let ell := log H
    let lam := g H
    let b : ℕ → ℝ := fun p => boundary p lam
    let Q := phi S b - baseline S + tangentRemainder H (clock S b)
    let Δ := ∑ p ∈ S, integerGap p lam
    let A := exp (ell * (exp r - 1)) - 1
    min r (Q + Δ - A ^ 2 / ell) ≤ integerInfimum S ∧
      integerInfimum S ≤ Q + Δ := by
  classical
  let H := theta S
  let ell := log H
  let lam := g H
  let b : ℕ → ℝ := fun p => boundary p lam
  let Q := phi S b - baseline S + tangentRemainder H (clock S b)
  let Δ := ∑ p ∈ S, integerGap p lam
  let A := exp (ell * (exp r - 1)) - 1
  change min r (Q + Δ - A ^ 2 / ell) ≤ integerInfimum S ∧
    integerInfimum S ≤ Q + Δ
  have hH : 1 < H := theta_gt_one hS hcard
  have hlam : 0 < lam := by
    dsimp only [lam, g]
    exact one_div_pos.mpr (mul_pos (zero_lt_one.trans hH) (log_pos hH))
  have hpR (p : ℕ) (hp : p ∈ S) : (1 : ℝ) < p := by
    exact_mod_cast (hS p hp).one_lt
  have hx (a : ℕ → ℕ) (ha : supportedAdmissible S a) :
      admissible S (fun p => (a p : ℝ)) := by
    intro p hp
    change (1 : ℝ) ≤ (a p : ℝ)
    exact_mod_cast ha p hp
  have hnonempty : (integerValues S).Nonempty :=
    ⟨phi S (fun _ => (1 : ℝ)) - baseline S,
      fun _ => 1, fun _ _ => le_rfl, by simp only [Nat.cast_one]⟩
  have hbounded : BddBelow (integerValues S) := by
    refine ⟨0, ?_⟩
    rintro v ⟨a, ha, rfl⟩
    obtain ⟨hlower, hupper⟩ := real_infimum_bounds hS hcard (hx a ha)
    exact sub_nonneg.mpr (hlower.trans hupper)
  constructor
  · change min r (Q + Δ - A ^ 2 / ell) ≤ sInf (integerValues S)
    apply le_csInf hnonempty
    rintro v ⟨a, ha, rfl⟩
    have hloss : Δ ≤ ∑ p ∈ S, priceLoss p lam (a p : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hk : (1 : ℤ) ≤ (a p : ℤ) := by exact_mod_cast ha p hp
      simpa only [Int.cast_natCast] using
        (integer_gap_bounds (hpR p hp) hlam (a p : ℤ) hk).2
    exact fixed_price_sublevel_lower hS hcard hlog hr (gap := Δ) (hx a ha) hloss
  · have hattained (p : ℕ) : ∃ k : ℕ, 1 ≤ k ∧
        (p ∈ S → priceLoss p lam (k : ℝ) = integerGap p lam) := by
      by_cases hp : p ∈ S
      · obtain ⟨k, hk, hgap, _⟩ := integer_gap_attained (hpR p hp) hlam
        have hk0 : 0 ≤ k := (by norm_num : (0 : ℤ) ≤ 1).trans hk
        have hkNat : (1 : ℤ) ≤ (k.toNat : ℤ) := by
          simpa only [Int.toNat_of_nonneg hk0] using hk
        have hkReal : (k.toNat : ℝ) = (k : ℝ) := by
          simpa only [Int.cast_natCast] using
            congrArg (fun i : ℤ => (i : ℝ)) (Int.toNat_of_nonneg hk0)
        refine ⟨k.toNat, by exact_mod_cast hkNat, fun _ => ?_⟩
        rw [hkReal]
        exact hgap.symm
      · exact ⟨1, le_rfl, fun hpS => (hp hpS).elim⟩
    let a : ℕ → ℕ := fun p => Classical.choose (hattained p)
    have ha : supportedAdmissible S a := fun p _ => (Classical.choose_spec (hattained p)).1
    let x : ℕ → ℝ := fun p => (a p : ℝ)
    have hloss : (∑ p ∈ S, priceLoss p lam (x p)) = Δ := by
      apply sum_congr rfl
      intro p hp
      exact (Classical.choose_spec (hattained p)).2 hp
    have hid := fixed_price_loss_identity S x
    change phi S x - baseline S =
      Q + (∑ p ∈ S, priceLoss p lam (x p)) - tangentRemainder H (clock S x) at hid
    rw [hloss] at hid
    have hK := (tangent_remainder_nonnegative hH (clock_gt_one hS hcard (hx a ha))).1
    have hmem : phi S x - baseline S ∈ integerValues S := ⟨a, ha, rfl⟩
    calc
      integerInfimum S ≤ phi S x - baseline S := csInf_le hbounded hmem
      _ ≤ Q + Δ := by
        rw [hid]
        exact sub_le_self _ hK

private def prefixRoundingGap (P : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE P, integerGap (p : ℝ) (prefixPrice P)

private lemma prefix_cutoff_below_clock :
    ∀ᶠ P : ℕ in atTop, prefixY P < prefixH P := by
  have hratio : Tendsto (fun P : ℕ => prefixY P / prefixH P) atTop (𝓝 0) := by
    have h := prefix_Y_div_cutoff.div prefix_H_ratio (by norm_num : (1 : ℝ) ≠ 0)
    simp only [zero_div] at h
    apply h.congr'
    filter_upwards [eventual_scale_positivity] with P hP
    rcases hP with ⟨hH, _, _, _, _, hp, _⟩
    change (prefixY P / (P : ℝ)) / (prefixH P / (P : ℝ)) = prefixY P / prefixH P
    field_simp [hp.ne', hH.ne']
  filter_upwards [hratio.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventual_scale_positivity] with P hratio hP
  simpa only [one_mul] using (div_lt_iff₀ hP.1).mp hratio

/-- Both prime prefixes contain every prime with nonzero fixed-price loss. -/
private lemma prefix_gap_eq_clock_gap :
    ∀ᶠ P : ℕ in atTop, prefixRoundingGap P =
      ∑ p ∈ Nat.primesLE ⌊prefixH P⌋₊, integerGap (p : ℝ) (g (prefixH P)) := by
  classical
  filter_upwards [eventual_prefix_domains, eventual_scale_positivity,
    prefix_cutoff_below_clock] with P hdom hpos hyH
  rcases hdom with ⟨_, _, _, hlam, _, hyP⟩
  have hzero (p : ℕ) (hp : p.Prime) (hy : prefixY P ≤ (p : ℝ)) :
      integerGap (p : ℝ) (prefixPrice P) = 0 := by
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hY : 0 ≤ prefixY P := hpos.2.2.2.1.le
    have hYsq : prefixY P ^ 2 = prefixC P := sq_sqrt hpos.2.2.1.le
    have hcut : prefixC P ≤ (p : ℝ) ^ 2 := by
      rw [← hYsq]
      exact (sq_le_sq₀ hY (hY.trans hy)).2 hy
    exact (inactive_loss hpR hlam hcut (le_refl (1 : ℝ))).2.1
  let S := Nat.primesLE P
  let T := Nat.primesLE ⌊prefixH P⌋₊
  let f : ℕ → ℝ := fun p => integerGap (p : ℝ) (prefixPrice P)
  change (∑ p ∈ S, f p) = ∑ p ∈ T, f p
  have hS : (∑ p ∈ S ∩ T, f p) = ∑ p ∈ S, f p := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro p hp hnot
    have hprime := (Nat.mem_primesLE.mp hp).2
    have hHp : prefixH P < (p : ℝ) := by
      apply lt_of_not_ge
      intro hle
      exact hnot (Finset.mem_inter.mpr ⟨hp, Nat.mem_primesLE.mpr ⟨Nat.le_floor hle, hprime⟩⟩)
    exact hzero p hprime (hyH.trans hHp).le
  have hT : (∑ p ∈ S ∩ T, f p) = ∑ p ∈ T, f p := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro p hp hnot
    have hprime := (Nat.mem_primesLE.mp hp).2
    have hPp : P < p := by
      apply lt_of_not_ge
      intro hle
      exact hnot (Finset.mem_inter.mpr ⟨Nat.mem_primesLE.mpr ⟨hle, hprime⟩, hp⟩)
    exact hzero p hprime (hyP.trans (by exact_mod_cast hPp)).le
  exact hS.symm.trans hT

private lemma scaled_prefix_gap_limit :
    Tendsto (fun P : ℕ => sqrt (prefixH P) * prefixEll P * prefixRoundingGap P)
      atTop (𝓝 (2 * sqrt 2)) := by
  have h := (ActualRoundingFullLimit.actual_prime_gap_limit).comp prefixH_atTop
  apply h.congr'
  filter_upwards [prefix_gap_eq_clock_gap] with P hP
  change sqrt (prefixH P) * prefixEll P *
    (∑ p ∈ Nat.primesLE ⌊prefixH P⌋₊, integerGap (p : ℝ) (g (prefixH P))) =
      sqrt (prefixH P) * prefixEll P * prefixRoundingGap P
  rw [hP]

private lemma prefix_Q_small :
    Tendsto (fun P : ℕ => sqrt (prefixH P) * prefixQ P) atTop (𝓝 0) := by
  let l : ℕ → ℝ := fun P => log (prefixY P)
  have hlTop : Tendsto l atTop atTop := tendsto_log_atTop.comp prefix_Y_atTop
  have hi : Tendsto (fun P => 1 / l P) atTop (𝓝 0) := hlTop.const_div_atTop 1
  have hY : Tendsto (fun P : ℕ => prefixY P * l P * prefixQ P) atTop (𝓝 4) := by
    have h := ((calibrated_Q_second_order.mul (hi.pow 2)).add (hi.const_mul 4)).add_const 4
    norm_num at h
    apply h.congr'
    filter_upwards [eventual_scale_positivity] with P hP
    have hl : l P ≠ 0 := hP.2.2.2.2.1.ne'
    change l P ^ 2 * (prefixY P * l P * prefixQ P - 4 - 4 / l P) *
      (l P ^ 2)⁻¹ + 4 * (l P)⁻¹ + 4 = _
    field_simp [hl] <;> ring
  have hratio : Tendsto (fun P : ℕ => sqrt (prefixH P * prefixEll P) / prefixY P)
      atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using
      prefix_Y_div_sqrt_H_ell.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have h := ((hY.mul hratio).mul
    ((tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp prefixH_atTop)).const_div_atTop 1)).mul hi
  norm_num at h
  apply h.congr'
  filter_upwards [eventual_scale_positivity] with P hP
  rcases hP with ⟨hH, hell, _, hy, hl, _, _⟩
  change prefixY P * l P * prefixQ P *
    (sqrt (prefixH P * prefixEll P) / prefixY P) *
    (sqrt (prefixEll P))⁻¹ * (l P)⁻¹ = _
  rw [sqrt_mul hH.le]
  field_simp [hy.ne', (sqrt_pos.mpr hell).ne', show l P ≠ 0 from hl.ne'] <;> ring

private def sublevelRadius (P : ℕ) : ℝ := 1 / sqrt (prefixH P)

private def sublevelExcess (P : ℕ) : ℝ :=
  exp (prefixEll P * (exp (sublevelRadius P) - 1)) - 1

private lemma scaled_tangent_error_zero :
    Tendsto (fun P : ℕ => sqrt (prefixH P) * prefixEll P *
      (sublevelExcess P ^ 2 / prefixEll P)) atTop (𝓝 0) := by
  let u : ℕ → ℝ := fun P => prefixEll P * (exp (sublevelRadius P) - 1)
  have hrpos : ∀ᶠ P : ℕ in atTop, 0 < sublevelRadius P := by
    filter_upwards [eventual_scale_positivity] with P hP
    exact one_div_pos.mpr (sqrt_pos.mpr hP.1)
  have hrzero : Tendsto sublevelRadius atTop (𝓝 0) :=
    (tendsto_sqrt_atTop.comp prefixH_atTop).const_div_atTop 1
  have hellrzero : Tendsto (fun P => prefixEll P * sublevelRadius P)
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp prefixH_atTop
    simpa only [rpow_one, ← sqrt_eq_rpow, prefixEll, sublevelRadius, mul_one_div,
      Function.comp_def] using h
  have hfirst := exp_difference_quotient hrzero (hrpos.mono (fun _ h => h.ne'))
  have huzero : Tendsto u atTop (𝓝 0) := by
    have h := hellrzero.mul hfirst
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [hrpos] with P hr
    dsimp only [u]
    field_simp [hr.ne']
  have hinnerpos : ∀ᶠ P : ℕ in atTop, 0 < exp (sublevelRadius P) - 1 := by
    filter_upwards [hrpos] with P hr
    have h := exp_lt_exp.mpr hr
    rw [exp_zero] at h
    exact sub_pos.mpr h
  have hupos : ∀ᶠ P : ℕ in atTop, 0 < u P := by
    filter_upwards [eventual_scale_positivity, hinnerpos] with P hP hi
    exact mul_pos hP.2.1 hi
  have hsecond := exp_difference_quotient huzero (hupos.mono (fun _ h => h.ne'))
  have hratio : Tendsto (fun P => sublevelExcess P / (prefixEll P * sublevelRadius P))
      atTop (𝓝 1) := by
    have h := hsecond.mul hfirst
    simp only [one_mul] at h
    apply h.congr'
    filter_upwards [eventual_scale_positivity, hrpos, hinnerpos] with P hP hr hi
    change sublevelExcess P / u P * ((exp (sublevelRadius P) - 1) / sublevelRadius P) =
      sublevelExcess P / (prefixEll P * sublevelRadius P)
    dsimp only [u]
    field_simp [hP.2.1.ne', hr.ne', hi.ne']
  have hdecay : Tendsto (fun P : ℕ => prefixEll P ^ 2 / sqrt (prefixH P))
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2 : ℕ)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp prefixH_atTop
    simpa only [rpow_natCast, ← sqrt_eq_rpow, prefixEll, Function.comp_def] using h
  have h := (hratio.pow 2).mul hdecay
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventual_scale_positivity] with P hP
  dsimp only [sublevelRadius]
  field_simp [hP.2.1.ne', (sqrt_pos.mpr hP.1).ne']

/-- The sharp loss from requiring integer exponents in the complete original
Robin image, evaluated against the actual real infimum on the same support. -/
theorem actual_integer_infimum_sharp_limit :
    Tendsto (fun P : ℕ => sqrt (prefixH P) * prefixEll P *
      (integerInfimum (Nat.primesLE P) -
        (realInfimum (Nat.primesLE P) - baseline (Nat.primesLE P))))
      atTop (𝓝 (2 * sqrt 2)) := by
  let scale : ℕ → ℝ := fun P => sqrt (prefixH P) * prefixEll P
  let I : ℕ → ℝ := fun P => integerInfimum (Nat.primesLE P)
  let R : ℕ → ℝ := fun P => realInfimum (Nat.primesLE P) - baseline (Nat.primesLE P)
  let E : ℕ → ℝ := fun P => sublevelExcess P ^ 2 / prefixEll P
  have hellTop : Tendsto prefixEll atTop atTop := tendsto_log_atTop.comp prefixH_atTop
  have hInvEll : Tendsto (fun P : ℕ => 1 / prefixEll P) atTop (𝓝 0) :=
    hellTop.const_div_atTop 1
  have hGapSmall :
      Tendsto (fun P : ℕ => sqrt (prefixH P) * prefixRoundingGap P) atTop (𝓝 0) := by
    have h := scaled_prefix_gap_limit.mul hInvEll
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventual_scale_positivity] with P hP
    field_simp [hP.2.1.ne']
  have hQGap :
      ∀ᶠ P : ℕ in atTop, prefixQ P + prefixRoundingGap P ≤ sublevelRadius P := by
    have h := (prefix_Q_small.add hGapSmall).eventually_lt_const
      (show (0 : ℝ) + 0 < 1 by norm_num)
    filter_upwards [h, eventual_scale_positivity] with P hlt hP
    change sqrt (prefixH P) * prefixQ P + sqrt (prefixH P) * prefixRoundingGap P < 1 at hlt
    change prefixQ P + prefixRoundingGap P ≤ 1 / sqrt (prefixH P)
    apply (le_div_iff₀ (sqrt_pos.mpr hP.1)).2
    calc
      (prefixQ P + prefixRoundingGap P) * sqrt (prefixH P) =
          sqrt (prefixH P) * prefixQ P + sqrt (prefixH P) * prefixRoundingGap P := by ring
      _ ≤ 1 := hlt.le
  have hfinite : ∀ᶠ P : ℕ in atTop,
      0 ≤ prefixQ P + prefixRoundingGap P - I P ∧
      prefixQ P + prefixRoundingGap P - I P ≤ E P := by
    filter_upwards [eventual_prefix_domains, eventual_scale_positivity, hQGap]
      with P hdom hpos hsmall
    have hr : 0 < sublevelRadius P := one_div_pos.mpr (sqrt_pos.mpr hpos.1)
    have hb := integer_infimum_fixed_price_squeeze hdom.1 hdom.2.1 hdom.2.2.1 hr
    change min (sublevelRadius P) (prefixQ P + prefixRoundingGap P - E P) ≤ I P ∧
      I P ≤ prefixQ P + prefixRoundingGap P at hb
    have hE : 0 ≤ E P := div_nonneg (sq_nonneg _) hpos.2.1.le
    rw [min_eq_right ((sub_le_self _ hE).trans hsmall)] at hb
    exact ⟨sub_nonneg.mpr hb.2, by linarith only [hb.1]⟩
  have hIntError : Tendsto (fun P : ℕ => scale P * (prefixQ P + prefixRoundingGap P - I P))
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _ scaled_tangent_error_zero
    · filter_upwards [hfinite, eventual_scale_positivity] with P hfin hP
      exact mul_nonneg (mul_nonneg (sqrt_nonneg _) hP.2.1.le) hfin.1
    · filter_upwards [hfinite, eventual_scale_positivity] with P hfin hP
      exact mul_le_mul_of_nonneg_left hfin.2 (mul_nonneg (sqrt_nonneg _) hP.2.1.le)
  have hRealError : Tendsto (fun P : ℕ => scale P * (prefixQ P - R P)) atTop (𝓝 0) := by
    have h := ((RealInfimumSecondOrder.actual_calibration_error_negligible.mul hInvEll).mul
      ((tendsto_sqrt_atTop.comp hellTop).const_div_atTop 1))
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [eventual_scale_positivity] with P hP
    change prefixEll P * (scale P * sqrt (prefixEll P)) * (prefixQ P - R P) *
      (1 / prefixEll P) * (1 / sqrt (prefixEll P)) = _
    field_simp [hP.2.1.ne', (sqrt_pos.mpr hP.2.1).ne']
  have h := (scaled_prefix_gap_limit.add hRealError).sub hIntError
  simp only [add_zero, sub_zero] at h
  change Tendsto (fun P : ℕ => scale P * (I P - R P)) atTop (𝓝 (2 * sqrt 2))
  apply h.congr'
  exact Filter.Eventually.of_forall (fun P => by
    change scale P * prefixRoundingGap P + scale P * (prefixQ P - R P) -
      scale P * (prefixQ P + prefixRoundingGap P - I P) = scale P * (I P - R P)
    ring)

end D5.S3.Arith.Robin.PriceRecord.IntegerInfimumSharpLimit
