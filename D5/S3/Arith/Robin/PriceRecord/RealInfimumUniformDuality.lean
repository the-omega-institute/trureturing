/- GID: D5/S3/Arith/Robin/PriceRecord/RealInfimumUniformDuality
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/RealInfimumUniformDuality
   mirror-E: none(waiver:general-real-analysis)
   anchors: []
   utility: none
   digest: Uniform finite fixed-price bounds for the genuine real and integer infima. -/

import D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus
import D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Source candidate awaiting native verification. The objective, real domain,
real infimum, baseline, boundary and integer gap retain their imported meanings.
The integer infimum is the literal image infimum on supported integer vectors.

At the fixed price g(theta S), the exact price-loss identity and the canonical
quadratic logarithm inequality give a lower bound for every admissible vector.
A sublevel argument controls the clock without restricting the infimum domain.
Primewise integer price attainers give the integer upper bound; a global
nonlinear minimizer is neither assumed nor asserted. -/

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.RealInfimumUniformDuality

open Real Set Finset
open D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus
  (log_one_add_quadratic)
open D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice
open D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport

private lemma nested_log_quadratic {ell u : ℝ} (hell : 1 ≤ ell) (hu : 0 ≤ u) :
    u / ell - u ^ 2 / ell ≤ log (1 + log (1 + u) / ell) := by
  have hell0 : 0 < ell := by linarith
  let w := log (1 + u)
  let v := w / ell
  have hw0 : 0 ≤ w := log_nonneg (by linarith)
  have hwu : w ≤ u := by
    have h := log_le_sub_one_of_pos (by linarith : 0 < 1 + u)
    dsimp only [w]
    linarith
  have hv0 : 0 ≤ v := div_nonneg hw0 hell0.le
  have hveq : v * ell = w := div_mul_cancel₀ w hell0.ne'
  have hvw : v ≤ w := by
    nlinarith only [hveq, mul_nonneg hv0 (sub_nonneg.mpr hell)]
  have hvu : v ≤ u := hvw.trans hwu
  have hsq : v ^ 2 * ell ≤ u ^ 2 := by
    calc
      v ^ 2 * ell = w * v := by rw [← hveq]; ring
      _ ≤ u * u := mul_le_mul hwu hvu hv0 hu
      _ = u ^ 2 := by ring
  have hwlower : u - u ^ 2 / 2 ≤ w := log_one_add_quadratic hu
  have hvlower := mul_le_mul_of_nonneg_right (log_one_add_quadratic hv0) hell0.le
  have hscaled : u - u ^ 2 ≤ log (1 + v) * ell := by
    nlinarith only [hwlower, hvlower, hsq, hveq]
  calc
    u / ell - u ^ 2 / ell = (u - u ^ 2) / ell := by ring
    _ ≤ log (1 + v) := (div_le_iff₀ hell0).mpr hscaled
    _ = log (1 + log (1 + u) / ell) := rfl

lemma terminal_cost_increment {H T : ℝ} (hH : 1 < H) (hHT : H ≤ T) :
    terminalCost T - terminalCost H =
      log (1 + log (1 + (T - H) / H) / log H) := by
  have hH0 : 0 < H := by linarith
  have hT : 1 < T := hH.trans_le hHT
  have hT0 : 0 < T := by linarith
  have hu : 1 + (T - H) / H = T / H := by
    field_simp [hH0.ne']
    <;> ring
  have hinner : log (1 + (T - H) / H) = log T - log H := by
    rw [hu, log_div hT0.ne' hH0.ne']
  have houter : 1 + log (1 + (T - H) / H) / log H = log T / log H := by
    rw [hinner]
    field_simp [(log_pos hH).ne']
    <;> ring
  dsimp only [terminalCost]
  rw [houter, log_div (log_pos hT).ne' (log_pos hH).ne']

private lemma nested_log_lt_clock_bound {ell u r : ℝ}
    (hell : 0 < ell) (hu : 0 ≤ u)
    (hsmall : log (1 + log (1 + u) / ell) < r) :
    u < exp (ell * (exp r - 1)) - 1 := by
  have hw0 : 0 ≤ log (1 + u) := log_nonneg (by linarith)
  have hv0 : 0 ≤ log (1 + u) / ell := div_nonneg hw0 hell.le
  have hfirst := (log_lt_iff_lt_exp (by linarith :
    0 < 1 + log (1 + u) / ell)).mp hsmall
  have hquot : log (1 + u) / ell < exp r - 1 := by linarith
  have hinner : log (1 + u) < ell * (exp r - 1) := by
    simpa only [mul_comm] using (div_lt_iff₀ hell).mp hquot
  have hsecond := (log_lt_iff_lt_exp (by linarith : 0 < 1 + u)).mp hinner
  linarith

lemma gap_identity_nonnegative {S : Finset ℕ} (hS : primeSupport S)
    {x : ℕ → ℝ} (hx : admissible S x) :
    phi S x - baseline S =
      terminalCost (clock S x) - terminalCost (theta S) -
        (∑ p ∈ S, log (1 - probability p (x p))) ∧
      0 ≤ -(∑ p ∈ S, log (1 - probability p (x p))) := by
  have hbenefit : (∑ p ∈ S, benefit p (x p)) =
      (∑ p ∈ S, log (1 - probability p (x p))) -
        (∑ p ∈ S, log (1 - (p : ℝ) ^ (-1 : ℝ))) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    exact benefit_log (by exact_mod_cast (hS p hp).one_lt) (hx p hp)
  constructor
  · dsimp only [phi, baseline]
    rw [hbenefit]
    ring
  · apply neg_nonneg.mpr
    apply sum_nonpos
    intro p hp
    have hm := probability_mem (by exact_mod_cast (hS p hp).one_lt) (hx p hp)
    have h := log_le_log (by linarith : 0 < 1 - probability p (x p))
      (show 1 - probability p (x p) ≤ 1 by linarith)
    simpa only [log_one] using h

/-- The literal objective image over integer vectors on this same support.
Values outside S do not affect phi; there is no finite search surrogate. -/
def integerInfimum (S : Finset ℕ) : ℝ :=
  sInf {v : ℝ | ∃ a : ℕ → ℤ, (∀ p ∈ S, 1 ≤ a p) ∧
    phi S (fun p => (a p : ℝ)) = v}

lemma integer_values_nonempty_bdd_below {S : Finset ℕ}
    (hS : primeSupport S) (hcard : 3 ≤ S.card) :
    ({v : ℝ | ∃ a : ℕ → ℤ, (∀ p ∈ S, 1 ≤ a p) ∧
      phi S (fun p => (a p : ℝ)) = v}).Nonempty ∧
    BddBelow {v : ℝ | ∃ a : ℕ → ℤ, (∀ p ∈ S, 1 ≤ a p) ∧
      phi S (fun p => (a p : ℝ)) = v} := by
  constructor
  · refine ⟨phi S (fun _ => ((1 : ℤ) : ℝ)), fun _ => 1, ?_, rfl⟩
    intro p hp
    exact le_rfl
  · refine ⟨baseline S, ?_⟩
    rintro value ⟨a, ha, rfl⟩
    have hx : admissible S (fun p => (a p : ℝ)) := by
      intro p hp
      change (1 : ℝ) ≤ (a p : ℝ)
      exact_mod_cast ha p hp
    have hb := real_infimum_bounds hS hcard hx
    exact hb.1.trans hb.2

lemma fixed_price_identity (S : Finset ℕ) (x : ℕ → ℝ) :
    let H := theta S
    let lam := D5.S3.Arith.Robin.ActualRobinClockCovariance.g H
    let b : ℕ → ℝ := fun p => boundary p lam
    phi S x - baseline S =
      (phi S b - baseline S + tangentRemainder H (clock S b)) +
        (∑ p ∈ S, priceLoss p lam (x p)) -
          tangentRemainder H (clock S x) := by
  let H := theta S
  let lam := D5.S3.Arith.Robin.ActualRobinClockCovariance.g H
  let b : ℕ → ℝ := fun p => boundary p lam
  change phi S x - baseline S =
    (phi S b - baseline S + tangentRemainder H (clock S b)) +
      (∑ p ∈ S, priceLoss p lam (x p)) - tangentRemainder H (clock S x)
  have hsum (y : ℕ → ℝ) :
      (∑ p ∈ S, priceObjective p lam (y p)) =
        (∑ p ∈ S, benefit p (y p)) - lam * clock S y := by
    simp only [priceObjective, clock, sum_sub_distrib, mul_sum, mul_assoc]
  have hloss : (∑ p ∈ S, priceLoss p lam (x p)) =
      (∑ p ∈ S, benefit p (b p)) - (∑ p ∈ S, benefit p (x p)) +
        lam * (clock S x - clock S b) := by
    change (∑ p ∈ S, (priceObjective p lam (b p) -
      priceObjective p lam (x p))) = _
    rw [sum_sub_distrib, hsum, hsum]
    ring
  rw [hloss]
  dsimp only [phi, tangentRemainder, lam]
  ring

/-- Shared pointwise argument. C is paid by the actual fixed-price loss sum,
not by an assumed bound on phi, an infimum or a selected optimizer. -/
private lemma fixed_price_uniform_pointwise {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) (hlog : 1 ≤ log (theta S)) {r : ℝ} (hr : 0 < r)
    {C : ℝ} {x : ℕ → ℝ} (hx : admissible S x)
    (hprice : C ≤ ∑ p ∈ S, priceLoss p
      (D5.S3.Arith.Robin.ActualRobinClockCovariance.g (theta S)) (x p)) :
    let H := theta S
    let ell := log H
    let lam := D5.S3.Arith.Robin.ActualRobinClockCovariance.g H
    let b : ℕ → ℝ := fun p => boundary p lam
    let Q := phi S b - baseline S + tangentRemainder H (clock S b)
    let A := exp (ell * (exp r - 1)) - 1
    min r (Q + C - A ^ 2 / ell) ≤ phi S x - baseline S := by
  let H := theta S
  let ell := log H
  let lam := D5.S3.Arith.Robin.ActualRobinClockCovariance.g H
  let b : ℕ → ℝ := fun p => boundary p lam
  let Q := phi S b - baseline S + tangentRemainder H (clock S b)
  let A := exp (ell * (exp r - 1)) - 1
  change min r (Q + C - A ^ 2 / ell) ≤ phi S x - baseline S
  change C ≤ ∑ p ∈ S, priceLoss p lam (x p) at hprice
  have hH : 1 < H := theta_gt_one hS hcard
  have hH0 : 0 < H := by linarith
  have hell : 1 ≤ ell := hlog
  have hell0 : 0 < ell := by linarith
  have hA : 0 ≤ A := by
    have her : 0 ≤ exp r - 1 := by
      have h := exp_le_exp.mpr hr.le
      simpa only [exp_zero, sub_nonneg] using h
    have h := exp_le_exp.mpr (mul_nonneg hell0.le her)
    dsimp only [A]
    simpa only [exp_zero, sub_nonneg] using h
  let T := clock S x
  let u := (T - H) / H
  have hHT : H ≤ T := theta_le_clock hS hx
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hHT) hH0.le
  have hid := gap_identity_nonnegative hS hx
  have hdiff : terminalCost T - terminalCost H =
      log (1 + log (1 + u) / ell) := terminal_cost_increment hH hHT
  have hquad : u / ell - u ^ 2 / ell ≤ terminalCost T - terminalCost H := by
    rw [hdiff]
    exact nested_log_quadratic hell hu
  have hpricecost : lam * (T - H) = u / ell := by
    dsimp only [lam, D5.S3.Arith.Robin.ActualRobinClockCovariance.g, u, ell]
    field_simp [hH0.ne', (log_pos hH).ne']
    <;> ring
  have heq : phi S x - baseline S =
      Q + (∑ p ∈ S, priceLoss p lam (x p)) -
        (terminalCost H + lam * (T - H) - terminalCost T) :=
    fixed_price_identity S x
  have hdual : Q + C - (lam * (T - H) -
      (terminalCost T - terminalCost H)) ≤ phi S x - baseline S := by
    linarith only [heq, hprice]
  have hquadratic : Q + C - u ^ 2 / ell ≤ phi S x - baseline S := by
    rw [hpricecost] at hdual
    linarith only [hdual, hquad]
  by_cases hlarge : r ≤ phi S x - baseline S
  · exact (min_le_left _ _).trans hlarge
  · have hsmall : phi S x - baseline S < r := lt_of_not_ge hlarge
    have hterminal : terminalCost T - terminalCost H < r := by
      have heq' : phi S x - baseline S = terminalCost T - terminalCost H -
          (∑ p ∈ S, log (1 - probability p (x p))) := hid.1
      linarith only [heq', hid.2, hsmall]
    have huA : u < A := nested_log_lt_clock_bound hell0 hu (by
      rw [← hdiff]
      exact hterminal)
    have hsq : u ^ 2 ≤ A ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr huA.le) (add_nonneg hA hu)]
    have hquot : u ^ 2 / ell ≤ A ^ 2 / ell :=
      div_le_div_of_nonneg_right hsq hell0.le
    exact (min_le_right _ _).trans (by linarith only [hquot, hquadratic])

/-- A finite lower bound on the actual sInf over ALL admissible real vectors.
No attainment, stationary point, convergence, PNT or RH premise is used. -/
theorem real_infimum_uniform_lower {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) (hlog : 1 ≤ log (theta S)) {r : ℝ} (hr : 0 < r) :
    let H := theta S
    let ell := log H
    let lam := D5.S3.Arith.Robin.ActualRobinClockCovariance.g H
    let b : ℕ → ℝ := fun p => boundary p lam
    let Q := phi S b - baseline S + tangentRemainder H (clock S b)
    let A := exp (ell * (exp r - 1)) - 1
    min r (Q - A ^ 2 / ell) ≤ realInfimum S - baseline S := by
  let H := theta S
  let ell := log H
  let lam := D5.S3.Arith.Robin.ActualRobinClockCovariance.g H
  let b : ℕ → ℝ := fun p => boundary p lam
  let Q := phi S b - baseline S + tangentRemainder H (clock S b)
  let A := exp (ell * (exp r - 1)) - 1
  change min r (Q - A ^ 2 / ell) ≤ realInfimum S - baseline S
  have hH : 1 < H := theta_gt_one hS hcard
  have hlam : 0 < lam := by
    dsimp only [lam, D5.S3.Arith.Robin.ActualRobinClockCovariance.g]
    exact one_div_pos.mpr (mul_pos (by linarith) (log_pos hH))
  have hpointwise (x : ℕ → ℝ) (hx : admissible S x) :
      min r (Q - A ^ 2 / ell) ≤ phi S x - baseline S := by
    have hloss : (0 : ℝ) ≤ ∑ p ∈ S, priceLoss p lam (x p) := by
      apply sum_nonneg
      intro p hp
      exact sub_nonneg.mpr (boundary_maximum
        (by exact_mod_cast (hS p hp).one_lt) hlam (hx p hp))
    have h := fixed_price_uniform_pointwise hS hcard hlog hr (C := 0) hx hloss
    simpa only [add_zero] using h
  have hdomain := real_values_nonempty_bdd_below hS hcard
  have hinf : min r (Q - A ^ 2 / ell) + baseline S ≤ realInfimum S := by
    apply le_csInf hdomain.1
    rintro value ⟨x, hx, rfl⟩
    linarith only [hpointwise x hx]
  linarith only [hinf]

/-- A finite sandwich for the literal supported-integer infimum. The lower
bound is uniform over every admissible integer vector; the upper bound uses
only local fixed-price integer gap attainers, not a global phi minimizer. -/
theorem integer_infimum_uniform_sandwich {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) (hlog : 1 ≤ log (theta S)) {r : ℝ} (hr : 0 < r) :
    let H := theta S
    let ell := log H
    let lam := D5.S3.Arith.Robin.ActualRobinClockCovariance.g H
    let b : ℕ → ℝ := fun p => boundary p lam
    let Q := phi S b - baseline S + tangentRemainder H (clock S b)
    let G := ∑ p ∈ S, integerGap p lam
    let A := exp (ell * (exp r - 1)) - 1
    min r (Q + G - A ^ 2 / ell) ≤ integerInfimum S - baseline S ∧
      integerInfimum S - baseline S ≤ Q + G := by
  classical
  let H := theta S
  let ell := log H
  let lam := D5.S3.Arith.Robin.ActualRobinClockCovariance.g H
  let b : ℕ → ℝ := fun p => boundary p lam
  let Q := phi S b - baseline S + tangentRemainder H (clock S b)
  let G := ∑ p ∈ S, integerGap p lam
  let A := exp (ell * (exp r - 1)) - 1
  change min r (Q + G - A ^ 2 / ell) ≤ integerInfimum S - baseline S ∧
    integerInfimum S - baseline S ≤ Q + G
  have hH : 1 < H := theta_gt_one hS hcard
  have hlam : 0 < lam := by
    dsimp only [lam, D5.S3.Arith.Robin.ActualRobinClockCovariance.g]
    exact one_div_pos.mpr (mul_pos (by linarith) (log_pos hH))
  have hdomain := integer_values_nonempty_bdd_below hS hcard
  constructor
  · have hpointwise (a : ℕ → ℤ) (ha : ∀ p ∈ S, 1 ≤ a p) :
        min r (Q + G - A ^ 2 / ell) ≤
          phi S (fun p => (a p : ℝ)) - baseline S := by
      have hx : admissible S (fun p => (a p : ℝ)) := by
        intro p hp
        change (1 : ℝ) ≤ (a p : ℝ)
        exact_mod_cast ha p hp
      have hloss : G ≤ ∑ p ∈ S, priceLoss p lam (a p : ℝ) := by
        apply sum_le_sum
        intro p hp
        exact (integer_gap_bounds (by exact_mod_cast (hS p hp).one_lt)
          hlam (a p) (ha p hp)).2
      exact fixed_price_uniform_pointwise hS hcard hlog hr (C := G) hx hloss
    have hinf : min r (Q + G - A ^ 2 / ell) + baseline S ≤ integerInfimum S := by
      apply le_csInf hdomain.1
      rintro value ⟨a, ha, rfl⟩
      linarith only [hpointwise a ha]
    linarith only [hinf]
  · have hlocal : ∀ p : {p : ℕ // p ∈ S}, ∃ k : ℤ,
        1 ≤ k ∧ integerGap (p : ℕ) lam = priceLoss (p : ℕ) lam k := by
      intro p
      obtain ⟨k, hk, hgap, _⟩ := integer_gap_attained (p := (p.val : ℝ))
        (by exact_mod_cast (hS p.val p.property).one_lt) hlam
      exact ⟨k, hk, hgap⟩
    choose k hk hgap using hlocal
    let a : ℕ → ℤ := fun p => if hp : p ∈ S then k ⟨p, hp⟩ else 1
    have ha : ∀ p ∈ S, 1 ≤ a p := by
      intro p hp
      simpa only [a, dif_pos hp] using hk ⟨p, hp⟩
    have hx : admissible S (fun p => (a p : ℝ)) := by
      intro p hp
      change (1 : ℝ) ≤ (a p : ℝ)
      exact_mod_cast ha p hp
    have hloss : (∑ p ∈ S, priceLoss p lam (a p : ℝ)) = G := by
      apply sum_congr rfl
      intro p hp
      simpa only [a, dif_pos hp] using (hgap ⟨p, hp⟩).symm
    have hid := fixed_price_identity S (fun p => (a p : ℝ))
    change phi S (fun p => (a p : ℝ)) - baseline S =
      Q + (∑ p ∈ S, priceLoss p lam (a p : ℝ)) -
        tangentRemainder H (clock S (fun p => (a p : ℝ))) at hid
    rw [hloss] at hid
    have hrem : 0 ≤ tangentRemainder H (clock S (fun p => (a p : ℝ))) :=
      (tangent_remainder_nonnegative hH (clock_gt_one hS hcard hx)).1
    have hinf : integerInfimum S ≤ phi S (fun p => (a p : ℝ)) :=
      csInf_le hdomain.2 ⟨a, ha, rfl⟩
    linarith only [hid, hrem, hinf]

end D5.S3.Arith.Robin.PriceRecord.RealInfimumUniformDuality
