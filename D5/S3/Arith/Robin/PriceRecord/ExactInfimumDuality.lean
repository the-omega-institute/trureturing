/- GID: D5/S3/Arith/Robin/PriceRecord/ExactInfimumDuality
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ExactInfimumDuality
   mirror-E: none(waiver:general-real-analysis)
   anchors: []
   utility: none
   digest: Exact nested-log envelopes for the genuine real and supported-integer infima. -/

import D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus
import D5.S3.Arith.Robin.PriceRecord.RealInfimumUniformDuality
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Source candidate awaiting native verification. The exact fixed-price
identity gives Q + sum priceLoss = w + U for every admissible vector, with
w and U nonnegative. Monotonicity and the one-Lipschitz inequality for the
nested logarithm yield the global envelope before passing to the image infima.
The canonical quadratic logarithm supplier gives its explicit error bound.
No objective, domain, infimum, clock cutoff or minimizer is substituted. -/

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ExactInfimumDuality

open Real Set Finset
open D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus
  (log_one_add_quadratic)
open D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice
open D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
open D5.S3.Arith.Robin.PriceRecord.RealInfimumUniformDuality

private lemma log_one_add_increment {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    log (1 + y) - log (1 + x) ≤ y - x := by
  have hx1 : 0 < 1 + x := by linarith
  have hy1 : 0 < 1 + y := by linarith
  calc
    log (1 + y) - log (1 + x) = log ((1 + y) / (1 + x)) :=
      (log_div hy1.ne' hx1.ne').symm
    _ ≤ (1 + y) / (1 + x) - 1 :=
      log_le_sub_one_of_pos (div_pos hy1 hx1)
    _ = (y - x) / (1 + x) := by field_simp [hx1.ne']; ring
    _ ≤ y - x := by
      apply (div_le_iff₀ hx1).mpr
      nlinarith only [mul_nonneg hx (sub_nonneg.mpr hxy)]

private lemma nested_log_mono {ell q₁ q₂ : ℝ} (hell : 0 < ell)
    (hq₁ : 0 ≤ q₁) (hq₂ : q₁ ≤ q₂) :
    log (1 + log (1 + ell * q₁) / ell) ≤
      log (1 + log (1 + ell * q₂) / ell) := by
  have hz₁ : 0 ≤ ell * q₁ := mul_nonneg hell.le hq₁
  have hinner : log (1 + ell * q₁) ≤ log (1 + ell * q₂) :=
    log_le_log (by linarith) (by nlinarith only [mul_le_mul_of_nonneg_left hq₂ hell.le])
  have ha₁ : 0 ≤ log (1 + ell * q₁) / ell :=
    div_nonneg (log_nonneg (by linarith)) hell.le
  exact log_le_log (by linarith)
    (add_le_add_left (div_le_div_of_nonneg_right hinner hell.le) 1)

private lemma nested_log_one_lipschitz {ell q₁ q₂ : ℝ} (hell : 1 ≤ ell)
    (hq₁ : 0 ≤ q₁) (hq₂ : q₁ ≤ q₂) :
    log (1 + log (1 + ell * q₂) / ell) -
        log (1 + log (1 + ell * q₁) / ell) ≤ q₂ - q₁ := by
  have hell0 : 0 < ell := by linarith
  let a₁ := log (1 + ell * q₁) / ell
  let a₂ := log (1 + ell * q₂) / ell
  have hz₁ : 0 ≤ ell * q₁ := mul_nonneg hell0.le hq₁
  have hz₁₂ : ell * q₁ ≤ ell * q₂ := mul_le_mul_of_nonneg_left hq₂ hell0.le
  have ha₁ : 0 ≤ a₁ := div_nonneg (log_nonneg (by linarith)) hell0.le
  have ha₁₂ : a₁ ≤ a₂ := div_le_div_of_nonneg_right
    (log_le_log (by linarith) (by linarith only [hz₁₂])) hell0.le
  have hinner := log_one_add_increment hz₁ hz₁₂
  have hscaled : (log (1 + ell * q₂) - log (1 + ell * q₁)) / ell ≤ q₂ - q₁ := by
    apply (div_le_iff₀ hell0).mpr
    nlinarith only [hinner]
  have hadiff : a₂ - a₁ ≤ q₂ - q₁ := by
    simpa only [a₁, a₂, sub_div] using hscaled
  exact (log_one_add_increment ha₁ ha₁₂).trans hadiff

private lemma nested_log_error {ell q : ℝ} (hell : 1 ≤ ell) (hq : 0 ≤ q) :
    0 ≤ q - log (1 + log (1 + ell * q) / ell) ∧
      q - log (1 + log (1 + ell * q) / ell) ≤
        (ell + 1) * q ^ 2 / 2 := by
  have hell0 : 0 < ell := by linarith
  have hz : 0 ≤ ell * q := mul_nonneg hell0.le hq
  let a := log (1 + ell * q) / ell
  have ha0 : 0 ≤ a := div_nonneg (log_nonneg (by linarith)) hell0.le
  have haq : a ≤ q := by
    apply (div_le_iff₀ hell0).mpr
    have h := log_le_sub_one_of_pos (by linarith : 0 < 1 + ell * q)
    nlinarith only [h]
  have halower : q - ell * q ^ 2 / 2 ≤ a := by
    have h := div_le_div_of_nonneg_right (log_one_add_quadratic hz) hell0.le
    have heq : (ell * q - (ell * q) ^ 2 / 2) / ell = q - ell * q ^ 2 / 2 := by
      field_simp [hell0.ne']
      <;> ring
    rw [heq] at h
    exact h
  have hout : a - a ^ 2 / 2 ≤ log (1 + a) := log_one_add_quadratic ha0
  have hsq : a ^ 2 ≤ q ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr haq) (add_nonneg hq ha0)]
  have hupper : log (1 + a) ≤ a := by
    have h := log_le_sub_one_of_pos (by linarith : 0 < 1 + a)
    linarith only [h]
  change 0 ≤ q - log (1 + a) ∧ q - log (1 + a) ≤ (ell + 1) * q ^ 2 / 2
  constructor
  · linarith only [haq, hupper]
  · nlinarith only [halower, hout, hsq]

private lemma boundary_vector_admissible (S : Finset ℕ) (lam : ℝ) :
    admissible S (fun p => boundary p lam) := by
  intro p hp
  exact le_max_left _ _

private lemma real_q_nonnegative {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) (hlog : 1 ≤ log (theta S)) :
    let H := theta S
    let ell := log H
    let lam := 1 / (H * ell)
    let b : ℕ → ℝ := fun p => boundary p lam
    let Q := phi S b - baseline S + tangentRemainder H (clock S b)
    0 ≤ Q := by
  let H := theta S
  let ell := log H
  let lam := 1 / (H * ell)
  let b : ℕ → ℝ := fun p => boundary p lam
  change 0 ≤ phi S b - baseline S + tangentRemainder H (clock S b)
  have hb : admissible S b := boundary_vector_admissible S lam
  have hphi := real_infimum_bounds hS hcard hb
  have hrem := (tangent_remainder_nonnegative (theta_gt_one hS hcard)
    (clock_gt_one hS hcard hb)).1
  exact add_nonneg (sub_nonneg.mpr (hphi.1.trans hphi.2)) hrem

private lemma integer_q_nonnegative {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) (hlog : 1 ≤ log (theta S)) :
    let H := theta S
    let ell := log H
    let lam := 1 / (H * ell)
    let b : ℕ → ℝ := fun p => boundary p lam
    let Q := phi S b - baseline S + tangentRemainder H (clock S b)
    let G := ∑ p ∈ S, integerGap p lam
    0 ≤ Q ∧ 0 ≤ G := by
  refine ⟨real_q_nonnegative hS hcard hlog, ?_⟩
  have hH : 0 < theta S := by linarith [theta_gt_one hS hcard]
  have hell : 0 < log (theta S) := by linarith
  have hlam : 0 < 1 / (theta S * log (theta S)) :=
    one_div_pos.mpr (mul_pos hH hell)
  apply sum_nonneg
  intro p hp
  exact (integer_gap_bounds (by exact_mod_cast (hS p hp).one_lt) hlam
    (1 : ℤ) le_rfl).1

private lemma fixed_price_envelope_pointwise {S : Finset ℕ}
    (hS : primeSupport S) (hcard : 3 ≤ S.card) (hlog : 1 ≤ log (theta S))
    {C : ℝ} (hC : 0 ≤ C) {x : ℕ → ℝ} (hx : admissible S x)
    (hprice : C ≤ ∑ p ∈ S, priceLoss p
      (1 / (theta S * log (theta S))) (x p)) :
    let H := theta S
    let ell := log H
    let lam := 1 / (H * ell)
    let b : ℕ → ℝ := fun p => boundary p lam
    let Q := phi S b - baseline S + tangentRemainder H (clock S b)
    log (1 + log (1 + ell * (Q + C)) / ell) ≤
      phi S x - baseline S := by
  let H := theta S
  let ell := log H
  let lam := 1 / (H * ell)
  let b : ℕ → ℝ := fun p => boundary p lam
  let Q := phi S b - baseline S + tangentRemainder H (clock S b)
  let T := clock S x
  let w := (T - H) / (H * ell)
  let U := -(∑ p ∈ S, log (1 - probability p (x p)))
  change log (1 + log (1 + ell * (Q + C)) / ell) ≤ phi S x - baseline S
  change C ≤ ∑ p ∈ S, priceLoss p lam (x p) at hprice
  have hH : 1 < H := theta_gt_one hS hcard
  have hH0 : 0 < H := by linarith
  have hell : 1 ≤ ell := hlog
  have hell0 : 0 < ell := by linarith
  have hHT : H ≤ T := theta_le_clock hS hx
  have hw : 0 ≤ w := div_nonneg (sub_nonneg.mpr hHT) (mul_pos hH0 hell0).le
  have hgap := gap_identity_nonnegative hS hx
  have hU : 0 ≤ U := hgap.2
  have hQ : 0 ≤ Q := real_q_nonnegative hS hcard hlog
  have hscale : (T - H) / H = ell * w := by
    dsimp only [w]
    field_simp [hH0.ne', hell0.ne']
    <;> ring
  have hdiff : terminalCost T - terminalCost H =
      log (1 + log (1 + ell * w) / ell) := by
    have ht := terminal_cost_increment hH hHT
    rw [hscale] at ht
    exact ht
  have hdelta : phi S x - baseline S =
      log (1 + log (1 + ell * w) / ell) + U := by
    have hid : phi S x - baseline S = terminalCost T - terminalCost H + U := by
      simpa only [U, sub_eq_add_neg] using hgap.1
    rw [hdiff] at hid
    exact hid
  have hpricecost : D5.S3.Arith.Robin.ActualRobinClockCovariance.g H * (T - H) = w := by
    change (1 / (H * ell)) * (T - H) = (T - H) / (H * ell)
    ring
  have hrem : tangentRemainder H T = w - (terminalCost T - terminalCost H) := by
    dsimp only [tangentRemainder]
    rw [hpricecost]
    ring
  have heq := fixed_price_identity S x
  -- Canonical g H is definitionally 1/(H*log H); this change pays the price normalization.
  change phi S x - baseline S = Q + (∑ p ∈ S, priceLoss p lam (x p)) -
    tangentRemainder H T at heq
  have hlinear : Q + (∑ p ∈ S, priceLoss p lam (x p)) = w + U := by
    rw [hrem] at heq
    have hid : phi S x - baseline S = terminalCost T - terminalCost H + U := by
      simpa only [U, sub_eq_add_neg] using hgap.1
    linarith only [heq, hid]
  have hdual : Q + C ≤ w + U := by linarith only [hprice, hlinear]
  have hmono := nested_log_mono hell0 (add_nonneg hQ hC) hdual
  have hlip := nested_log_one_lipschitz hell hw (show w ≤ w + U by linarith only [hU])
  linarith only [hmono, hlip, hdelta]

private lemma real_upper_q {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) (hlog : 1 ≤ log (theta S)) :
    let H := theta S
    let ell := log H
    let lam := 1 / (H * ell)
    let b : ℕ → ℝ := fun p => boundary p lam
    let Q := phi S b - baseline S + tangentRemainder H (clock S b)
    realInfimum S - baseline S ≤ Q := by
  let lam := 1 / (theta S * log (theta S))
  let b : ℕ → ℝ := fun p => boundary p lam
  change realInfimum S - baseline S ≤
    phi S b - baseline S + tangentRemainder (theta S) (clock S b)
  have hb : admissible S b := boundary_vector_admissible S lam
  have hdom := real_values_nonempty_bdd_below hS hcard
  have hinf : realInfimum S ≤ phi S b := csInf_le hdom.2 ⟨b, hb, rfl⟩
  have hrem := (tangent_remainder_nonnegative (theta_gt_one hS hcard)
    (clock_gt_one hS hcard hb)).1
  linarith only [hinf, hrem]

private lemma integer_upper_q {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) (hlog : 1 ≤ log (theta S)) :
    let H := theta S
    let ell := log H
    let lam := 1 / (H * ell)
    let b : ℕ → ℝ := fun p => boundary p lam
    let Q := phi S b - baseline S + tangentRemainder H (clock S b)
    let G := ∑ p ∈ S, integerGap p lam
    integerInfimum S - baseline S ≤ Q + G := by
  -- The supplier already constructs finite primewise integer attainers and
  -- applies csInf_le to the literal integer image. Only its public .2 is used.
  simpa only [D5.S3.Arith.Robin.ActualRobinClockCovariance.g] using
    (integer_infimum_uniform_sandwich hS hcard hlog (r := 1) (by norm_num)).2

private lemma real_lower_nested_log {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) (hlog : 1 ≤ log (theta S)) :
    let H := theta S
    let ell := log H
    let lam := 1 / (H * ell)
    let b : ℕ → ℝ := fun p => boundary p lam
    let Q := phi S b - baseline S + tangentRemainder H (clock S b)
    log (1 + log (1 + ell * Q) / ell) ≤ realInfimum S - baseline S := by
  let H := theta S
  let ell := log H
  let lam := 1 / (H * ell)
  let b : ℕ → ℝ := fun p => boundary p lam
  let Q := phi S b - baseline S + tangentRemainder H (clock S b)
  let L := log (1 + log (1 + ell * Q) / ell)
  change L ≤ realInfimum S - baseline S
  have hH : 1 < H := theta_gt_one hS hcard
  have hell : 1 ≤ ell := hlog
  have hlam : 0 < lam := one_div_pos.mpr
    (mul_pos (by linarith) (by linarith))
  have hpointwise (x : ℕ → ℝ) (hx : admissible S x) : L ≤ phi S x - baseline S := by
    have hloss : (0 : ℝ) ≤ ∑ p ∈ S, priceLoss p lam (x p) := by
      apply sum_nonneg
      intro p hp
      exact sub_nonneg.mpr (boundary_maximum
        (by exact_mod_cast (hS p hp).one_lt) hlam (hx p hp))
    simpa only [add_zero] using fixed_price_envelope_pointwise hS hcard hlog
      (C := 0) le_rfl hx hloss
  have hdom := real_values_nonempty_bdd_below hS hcard
  have hinf : L + baseline S ≤ realInfimum S := by
    apply le_csInf hdom.1
    rintro value ⟨x, hx, rfl⟩
    linarith only [hpointwise x hx]
  linarith only [hinf]

private lemma integer_lower_nested_log {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) (hlog : 1 ≤ log (theta S)) :
    let H := theta S
    let ell := log H
    let lam := 1 / (H * ell)
    let b : ℕ → ℝ := fun p => boundary p lam
    let Q := phi S b - baseline S + tangentRemainder H (clock S b)
    let G := ∑ p ∈ S, integerGap p lam
    log (1 + log (1 + ell * (Q + G)) / ell) ≤ integerInfimum S - baseline S := by
  let H := theta S
  let ell := log H
  let lam := 1 / (H * ell)
  let b : ℕ → ℝ := fun p => boundary p lam
  let Q := phi S b - baseline S + tangentRemainder H (clock S b)
  let G := ∑ p ∈ S, integerGap p lam
  let L := log (1 + log (1 + ell * (Q + G)) / ell)
  change L ≤ integerInfimum S - baseline S
  have hH : 1 < H := theta_gt_one hS hcard
  have hell : 1 ≤ ell := hlog
  have hlam : 0 < lam := one_div_pos.mpr
    (mul_pos (by linarith) (by linarith))
  have hG : 0 ≤ G := (integer_q_nonnegative hS hcard hlog).2
  have hpointwise (a : ℕ → ℤ) (ha : ∀ p ∈ S, 1 ≤ a p) :
      L ≤ phi S (fun p => (a p : ℝ)) - baseline S := by
    have hx : admissible S (fun p => (a p : ℝ)) := by
      intro p hp
      change (1 : ℝ) ≤ (a p : ℝ)
      exact_mod_cast ha p hp
    have hloss : G ≤ ∑ p ∈ S, priceLoss p lam (a p : ℝ) := by
      apply sum_le_sum
      intro p hp
      exact (integer_gap_bounds (by exact_mod_cast (hS p hp).one_lt)
        hlam (a p) (ha p hp)).2
    exact fixed_price_envelope_pointwise hS hcard hlog hG hx hloss
  have hdom := integer_values_nonempty_bdd_below hS hcard
  have hinf : L + baseline S ≤ integerInfimum S := by
    apply le_csInf hdom.1
    rintro value ⟨a, ha, rfl⟩
    linarith only [hpointwise a ha]
  linarith only [hinf]

/-- Genuine real sInf envelope, with its explicit quadratic error. -/
theorem real_infimum_nested_log_sandwich {S : Finset ℕ}
    (hS : primeSupport S) (hcard : 3 ≤ S.card)
    (hlog : 1 ≤ log (theta S)) :
    let H := theta S
    let ell := log H
    let lam := 1 / (H * ell)
    let b : ℕ → ℝ := fun p => boundary p lam
    let Q := phi S b - baseline S + tangentRemainder H (clock S b)
    let I := realInfimum S - baseline S
    let g := fun q : ℝ => log (1 + log (1 + ell * q) / ell)
    0 ≤ Q ∧ g Q ≤ I ∧ I ≤ Q ∧
      0 ≤ Q - I ∧ Q - I ≤ (ell + 1) * Q ^ 2 / 2 := by
  let H := theta S
  let ell := log H
  let lam := 1 / (H * ell)
  let b : ℕ → ℝ := fun p => boundary p lam
  let Q := phi S b - baseline S + tangentRemainder H (clock S b)
  let I := realInfimum S - baseline S
  let g := fun q : ℝ => log (1 + log (1 + ell * q) / ell)
  change 0 ≤ Q ∧ g Q ≤ I ∧ I ≤ Q ∧
    0 ≤ Q - I ∧ Q - I ≤ (ell + 1) * Q ^ 2 / 2
  have hQ : 0 ≤ Q := real_q_nonnegative hS hcard hlog
  have hL : g Q ≤ I := real_lower_nested_log hS hcard hlog
  have hU : I ≤ Q := real_upper_q hS hcard hlog
  have hE := nested_log_error hlog hQ
  have hlast : Q - I ≤ (ell + 1) * Q ^ 2 / 2 := by
    have he : Q - g Q ≤ (ell + 1) * Q ^ 2 / 2 := hE.2
    linarith only [hL, he]
  exact ⟨hQ, hL, hU, sub_nonneg.mpr hU, hlast⟩

/-- The literal integer image, with its complete fixed-price rounding gap. -/
theorem integer_infimum_nested_log_sandwich {S : Finset ℕ}
    (hS : primeSupport S) (hcard : 3 ≤ S.card)
    (hlog : 1 ≤ log (theta S)) :
    let H := theta S
    let ell := log H
    let lam := 1 / (H * ell)
    let b : ℕ → ℝ := fun p => boundary p lam
    let Q := phi S b - baseline S + tangentRemainder H (clock S b)
    let G := ∑ p ∈ S, integerGap p lam
    let I := integerInfimum S - baseline S
    let g := fun q : ℝ => log (1 + log (1 + ell * q) / ell)
    0 ≤ Q ∧ 0 ≤ G ∧ g (Q + G) ≤ I ∧ I ≤ Q + G ∧
      0 ≤ (Q + G) - I ∧
      (Q + G) - I ≤ (ell + 1) * (Q + G) ^ 2 / 2 := by
  let H := theta S
  let ell := log H
  let lam := 1 / (H * ell)
  let b : ℕ → ℝ := fun p => boundary p lam
  let Q := phi S b - baseline S + tangentRemainder H (clock S b)
  let G := ∑ p ∈ S, integerGap p lam
  let I := integerInfimum S - baseline S
  let g := fun q : ℝ => log (1 + log (1 + ell * q) / ell)
  change 0 ≤ Q ∧ 0 ≤ G ∧ g (Q + G) ≤ I ∧ I ≤ Q + G ∧
    0 ≤ (Q + G) - I ∧ (Q + G) - I ≤ (ell + 1) * (Q + G) ^ 2 / 2
  have hq : 0 ≤ Q ∧ 0 ≤ G := integer_q_nonnegative hS hcard hlog
  have hL : g (Q + G) ≤ I := integer_lower_nested_log hS hcard hlog
  have hU : I ≤ Q + G := integer_upper_q hS hcard hlog
  have hq0 : 0 ≤ Q + G := add_nonneg hq.1 hq.2
  have hE := nested_log_error hlog hq0
  have hlast : (Q + G) - I ≤ (ell + 1) * (Q + G) ^ 2 / 2 := by
    have he : (Q + G) - g (Q + G) ≤ (ell + 1) * (Q + G) ^ 2 / 2 := hE.2
    linarith only [hL, he]
  exact ⟨hq.1, hq.2, hL, hU, sub_nonneg.mpr hU, hlast⟩

end D5.S3.Arith.Robin.PriceRecord.ExactInfimumDuality
