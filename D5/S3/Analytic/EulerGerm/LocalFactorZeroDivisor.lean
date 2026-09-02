/- GID: D5/S3/Analytic/EulerGerm/LocalFactorZeroDivisor
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/LocalFactorZeroDivisor
   mirror-E: none(waiver:evidence-recorded-in-theory-volume)
   anchors: []
   digest: The normalized golden germ product vanishes exactly at a zero local factor. -/

import D5.S3.Analytic.EulerGerm.GoldenGermSecondOrderFactorization
import Mathlib.Analysis.Complex.AbsMax

/- Library-search audit trail (2026-09-03):
   * D5 has no declaration with any of the three target theorem names, no
     single-local-factor analyticity theorem on `Re s > 0`, and no strict
     center-versus-boundary minimum-modulus zero criterion.
   * The frozen `golden_germ_second_order_factorization` supplies the exact
     normalized factor and its summable deviation. Existing D5 product
     nonvanishing proofs demonstrate the pinned `tprod` nonzero lemma but do
     not characterize this normalized product's complete zero set.
   * Pinned Mathlib supplies `tprod_one_add_ne_zero_of_summable`,
     `tprod_of_exists_eq_zero`,
     `Complex.differentiableOn_tsum_of_summable_norm`, and
     `Complex.exists_mem_frontier_isMaxOn_norm`; each is used directly below.
   * Exact D5 and pinned-Mathlib shape searches found no theorem subsuming any
     target statement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.EulerGerm.LocalFactorZeroDivisor

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GoldenGermSecondOrderFactorization
open Metric Set

noncomputable section

private theorem natCast_le_o5Beta (v : Nat) : (v : Real) <= o5Beta v := by
  cases v with
  | zero => simp [o5_beta_zero]
  | succ v =>
      have hgrowth := o5_beta_growth (v + 1)
      have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
        Real.sq_sqrt (by norm_num)
      have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
      have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
      have hinv_pos : 0 < 1 / Real.goldenRatio :=
        one_div_pos.mpr Real.goldenRatio_pos
      push_cast at hgrowth ⊢
      nlinarith

private theorem real_local_factor_summable {sigma : Real} (hsigma : 0 < sigma)
    (p : Nat) (hp : p.Prime) :
    Summable (fun v : Nat => (p : Real) ^ (-sigma * o5Beta v)) := by
  let q : Real := (p : Real) ^ (-sigma)
  have hp_one : (1 : Real) <= p := by exact_mod_cast hp.one_lt.le
  have hp_pos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hq_nonneg : 0 <= q := Real.rpow_nonneg hp_pos.le _
  have hq_lt_one : q < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hsigma)
  have hq_norm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq_nonneg]
    exact hq_lt_one
  have hgeom : Summable (fun v : Nat => q ^ v) :=
    summable_geometric_of_norm_lt_one hq_norm
  apply Summable.of_nonneg_of_le
    (fun _ => Real.rpow_nonneg hp_pos.le _)
    (fun v => ?_) hgeom
  have hexponent : -sigma * o5Beta v <= -sigma * (v : Real) := by
    nlinarith [natCast_le_o5Beta v]
  calc
    (p : Real) ^ (-sigma * o5Beta v) <= (p : Real) ^ (-sigma * (v : Real)) :=
      Real.rpow_le_rpow_of_exponent_le hp_one hexponent
    _ = q ^ v := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]

private theorem local_mode_norm_le (p : Nat) (hp : p.Prime) {sigma : Real}
    {s : Complex} (hs : sigma < s.re) (v : Nat) :
    ‖(p : Complex) ^ (-s * (o5Beta v : Complex))‖ <=
      ‖(p : Complex) ^ (-(sigma : Complex) * (o5Beta v : Complex))‖ := by
  apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos hp.pos
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  have hbeta : 0 <= o5Beta v :=
    (Nat.cast_nonneg v).trans (natCast_le_o5Beta v)
  nlinarith

private theorem germLocalFactor_differentiableOn (p : Nat) (hp : p.Prime)
    (sigma : Real) (hsigma : 0 < sigma) :
    DifferentiableOn Complex (fun s : Complex => germLocalFactor s p)
      {s : Complex | sigma < s.re} := by
  let U : Set Complex := {s : Complex | sigma < s.re}
  let u : Nat -> Real := fun v =>
    ‖(p : Complex) ^ (-(sigma : Complex) * (o5Beta v : Complex))‖
  have hu : Summable u := by
    refine (real_local_factor_summable hsigma p hp).congr fun v => ?_
    simp only [u, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hterms : ∀ v : Nat,
      DifferentiableOn Complex (fun s : Complex =>
        (p : Complex) ^ (-s * (o5Beta v : Complex))) U := by
    intro v
    have hbase : (p : Complex) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact ((differentiable_id.neg.mul_const (o5Beta v : Complex)).const_cpow
      (.inl hbase)).differentiableOn
  have hsum := Complex.differentiableOn_tsum_of_summable_norm hu hterms hU
    (fun v s hs => local_mode_norm_le p hp hs v)
  simpa [germLocalFactor, U] using hsum

/-- A prime-local golden germ factor is analytic on its natural half-plane
`Re s > 0`. This regularity statement does not assert a local-factor zero;
the numerical prime-two evidence is recorded in the theory volume. -/
theorem germLocalFactor_analyticOnNhd_pos (p : ℕ) (hp : p.Prime) :
    AnalyticOnNhd ℂ (fun s : ℂ => germLocalFactor s p)
      {s : ℂ | 0 < s.re} := by
  intro s hs
  change 0 < s.re at hs
  let sigma : Real := s.re / 2
  have hsigma : 0 < sigma := by dsimp [sigma]; linarith
  have hssigma : sigma < s.re := by dsimp [sigma]; linarith
  have hU : IsOpen {z : Complex | sigma < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact (germLocalFactor_differentiableOn p hp sigma hsigma).analyticAt
    (hU.mem_nhds hssigma)

/-- A strict center-versus-boundary norm gap forces a zero in the open ball.
The criterion does not establish such a gap, and therefore asserts no golden
local-factor zero; the numerical evidence is recorded in the theory volume. -/
theorem exists_zero_in_ball_of_boundary_norm_gt_center
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c r))
    (hgap : ∀ z ∈ Metric.sphere c r, ‖f c‖ < ‖f z‖) :
    ∃ z ∈ Metric.ball c r, f z = 0 := by
  by_cases hc : f c = 0
  · exact ⟨c, mem_ball_self hr, hc⟩
  by_contra hzero
  push Not at hzero
  have hnonzero : ∀ z ∈ closedBall c r, f z ≠ 0 := by
    intro z hz
    rw [← ball_union_sphere] at hz
    rcases hz with hz | hz
    · exact hzero z hz
    · exact norm_ne_zero_iff.mp <|
        ne_of_gt ((norm_nonneg (f c)).trans_lt (hgap z hz))
  have hinv : AnalyticOnNhd Complex f⁻¹ (closedBall c r) := hf.inv hnonzero
  have hdiff : DiffContOnCl Complex f⁻¹ (ball c r) :=
    hinv.differentiableOn.diffContOnCl_ball Subset.rfl
  obtain ⟨z, hzfront, hzmax⟩ :=
    Complex.exists_mem_frontier_isMaxOn_norm isBounded_ball
      (nonempty_ball.mpr hr) hdiff
  have hzsphere : z ∈ sphere c r := frontier_ball_subset_sphere hzfront
  have hcenter_le : ‖(f c)⁻¹‖ <= ‖(f z)⁻¹‖ :=
    hzmax (subset_closure (mem_ball_self hr))
  have hboundary_lt : ‖(f z)⁻¹‖ < ‖(f c)⁻¹‖ := by
    rw [norm_inv, norm_inv]
    simpa only [one_div] using
      one_div_lt_one_div_of_lt (norm_pos_iff.mpr hc) (hgap z hzsphere)
  exact (not_lt_of_ge hcenter_le) hboundary_lt

private theorem normalized_mode_norm_lt_one (s : Complex) (hs : 0 < s.re)
    (c : Real) (hc : 0 < c) (p : Nat.Primes) :
    ‖(p : Complex) ^ (-s * (c : Complex))‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  rw [show (-s * (c : Complex)).re = -s.re * c by norm_num]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.prop.one_lt) (mul_neg_of_neg_of_pos (by linarith) hc)

private theorem normalized_factor_ne_zero_iff (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 4 < s.re) (p : Nat.Primes) :
    ((1 - (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
        (1 + (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
        germLocalFactor s p ≠ 0) ↔ germLocalFactor s p ≠ 0 := by
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  let x : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
  let y : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
  have hxlt : ‖x‖ < 1 := by
    exact normalized_mode_norm_lt_one s hspos
      (Real.goldenRatio ^ 2) (by positivity) p
  have hylt : ‖y‖ < 1 := by
    exact normalized_mode_norm_lt_one s hspos
      (Real.goldenRatio ^ 3) (by positivity) p
  have hxplus : 1 + x ≠ 0 := by
    intro h
    have hx : x = -1 := by linear_combination h
    rw [hx, norm_neg, norm_one] at hxlt
    exact (lt_irrefl 1) hxlt
  have hyminus : 1 - y ≠ 0 := by
    intro h
    have hy : y = 1 := (sub_eq_zero.mp h).symm
    rw [hy, norm_one] at hylt
    exact (lt_irrefl 1) hylt
  change ((1 - y) * (1 + x)⁻¹ * germLocalFactor s p ≠ 0) ↔ _
  constructor
  · intro h hlocal
    apply h
    simp [hlocal]
  · intro hlocal
    exact mul_ne_zero (mul_ne_zero hyminus (inv_ne_zero hxplus)) hlocal

/-- On the frozen second-order half-plane, the normalized correction product
vanishes exactly when a golden local factor vanishes. This characterization
does not assert that either zero set is inhabited; the numerical prime-two
evidence is recorded in the theory volume. -/
theorem G3_eq_zero_iff_exists_local_factor_zero (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 4 < s.re) :
    (∏' p : Nat.Primes,
      (1 - (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
        (1 + (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
        germLocalFactor s p) = 0 ↔
      ∃ p : Nat.Primes, germLocalFactor s p = 0 := by
  let F : Nat.Primes -> Complex := fun p =>
    (1 - (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
      (1 + (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
      germLocalFactor s p
  have hdev : Summable (fun p : Nat.Primes => ‖F p - 1‖) := by
    simpa [F] using golden_germ_second_order_factorization.2 s hs
  constructor
  · intro hprod
    by_contra hlocal
    push Not at hlocal
    have hF : ∀ p, F p ≠ 0 := by
      intro p
      exact (normalized_factor_ne_zero_iff s hs p).2 (hlocal p)
    have hne : (∏' p : Nat.Primes, F p) ≠ 0 := by
      have hone (p : Nat.Primes) : 1 + (F p - 1) = F p := by ring
      have := tprod_one_add_ne_zero_of_summable
        (f := fun p : Nat.Primes => F p - 1)
        (fun p => by rw [hone p]; exact hF p) hdev
      rw [tprod_congr hone] at this
      exact this
    exact hne (by simpa [F] using hprod)
  · rintro ⟨p, hp⟩
    change (∏' p : Nat.Primes, F p) = 0
    apply tprod_of_exists_eq_zero
    exact ⟨p, by simp [F, hp]⟩

#print axioms germLocalFactor_analyticOnNhd_pos
#print axioms exists_zero_in_ball_of_boundary_norm_gt_center
#print axioms G3_eq_zero_iff_exists_local_factor_zero

end

end D5.S3.Analytic.EulerGerm.LocalFactorZeroDivisor
