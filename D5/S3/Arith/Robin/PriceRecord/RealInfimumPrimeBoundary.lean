/- GID: D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary
   mirror-E: none(waiver:general-real-analysis)
   anchors: []
   utility: none
   digest: Exact finite prime-prefix formulas at the genuine fixed-price boundary. -/

import D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! All objective and infimum definitions retain the canonical input semantics;
no attainment or asymptotic premise is
introduced. The finite squeeze is proved here on the full real image.

The active side includes equality p^2 = cutoff lam. At equality its clock
increment is zero and its probability agrees with the inactive formula. -/

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.RealInfimumPrimeBoundary

open Real Set Finset Filter
open scoped Topology
open scoped Chebyshev
open BoundaryPrimePrice OwnClockFixedSupport

def deficiency (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  -(∑ p ∈ S, log (1 - probability p (a p)))

private lemma cutoff_pos {lam : ℝ} (hlam : 0 < lam) : 0 < cutoff lam := by
  dsimp [cutoff]
  positivity

private lemma active_boundary {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam)
    (hactive : p ^ 2 ≤ cutoff lam) : boundary p lam = critical p lam := by
  have hp0 : 0 < p := by linarith
  have hlog := log_le_log (pow_pos hp0 2) hactive
  rw [log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hc : 1 ≤ critical p lam := by
    dsimp [critical]
    have hq : 2 ≤ log (cutoff lam) / log p :=
      (le_div_iff₀ (log_pos hp)).mpr (by linarith)
    linarith
  exact max_eq_right hc

private lemma inactive_boundary {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam)
    (hinactive : cutoff lam ≤ p ^ 2) : boundary p lam = 1 := by
  have hlog := log_le_log (cutoff_pos hlam) hinactive
  rw [log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hc : critical p lam ≤ 1 := by
    dsimp [critical]
    have hq : log (cutoff lam) / log p ≤ 2 :=
      (div_le_iff₀ (log_pos hp)).mpr (by linarith)
    linarith
  exact max_eq_left hc

private lemma boundary_clock_term {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam) :
    (boundary p lam - 1) * log p =
      if p ^ 2 ≤ cutoff lam then log (cutoff lam) - 2 * log p else 0 := by
  split_ifs with h
  · rw [active_boundary hp hlam h]
    dsimp [critical]
    field_simp [(log_pos hp).ne']
    <;> ring
  · rw [inactive_boundary hp hlam (le_of_not_ge h)]
    ring

private lemma boundary_probability {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam) :
    probability p (boundary p lam) =
      if p ^ 2 ≤ cutoff lam then 1 / cutoff lam else 1 / p ^ 2 := by
  have hp0 : 0 < p := by linarith
  split_ifs with h
  · rw [active_boundary hp hlam h]
    dsimp [probability, critical]
    rw [sub_add_cancel, rpow_neg hp0.le, rpow_def_of_pos hp0]
    rw [show log p * (log (cutoff lam) / log p) = log (cutoff lam) by
      field_simp [(log_pos hp).ne']]
    rw [exp_log (cutoff_pos hlam)]
    simp only [one_div]
  · rw [inactive_boundary hp hlam (le_of_not_ge h)]
    norm_num [probability, rpow_neg, hp0.le, rpow_two, one_div]

/-- Both finite formulas, for any finite prime support. No prime distribution
theorem or limiting assumption is involved. Equality belongs to the head. -/
theorem finite_boundary_sums {S : Finset ℕ} (hS : primeSupport S)
    {lam : ℝ} (hlam : 0 < lam) :
    let A := S.filter (fun p : ℕ => (p : ℝ) ^ 2 ≤ cutoff lam)
    let b : ℕ → ℝ := fun p => boundary p lam
    (clock S b - theta S =
      (A.card : ℝ) * log (cutoff lam) - 2 * theta A) ∧
    (deficiency S b = (A.card : ℝ) * (-log (1 - 1 / cutoff lam)) +
      ∑ p ∈ S \ A, -log (1 - 1 / (p : ℝ) ^ 2)) := by
  classical
  dsimp only
  let A := S.filter (fun p : ℕ => (p : ℝ) ^ 2 ≤ cutoff lam)
  let b : ℕ → ℝ := fun p => boundary p lam
  change (clock S b - theta S =
      (A.card : ℝ) * log (cutoff lam) - 2 * theta A) ∧
    (deficiency S b = (A.card : ℝ) * (-log (1 - 1 / cutoff lam)) +
      ∑ p ∈ S \ A, -log (1 - 1 / (p : ℝ) ^ 2))
  have hAsub : A ⊆ S := filter_subset _ _
  constructor
  · calc
      clock S b - theta S = ∑ p ∈ S, (b p - 1) * log (p : ℝ) := by
        dsimp [clock, theta]
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro p _
        ring
      _ = ∑ p ∈ A, (log (cutoff lam) - 2 * log (p : ℝ)) := by
        rw [sum_filter]
        apply sum_congr rfl
        intro p hp
        exact boundary_clock_term (by exact_mod_cast (hS p hp).one_lt) hlam
      _ = (A.card : ℝ) * log (cutoff lam) - 2 * theta A := by
        rw [sum_sub_distrib]
        simp only [sum_const, nsmul_eq_mul, theta, mul_sum]
  · have hsplit := sum_sdiff hAsub (f := fun p : ℕ => -log (1 - probability p (b p)))
    have hhead : (∑ p ∈ A, -log (1 - probability p (b p))) =
        (A.card : ℝ) * (-log (1 - 1 / cutoff lam)) := by
      calc
        _ = ∑ _p ∈ A, -log (1 - 1 / cutoff lam) := by
          apply sum_congr rfl
          intro p hp
          have hpmem := mem_filter.mp hp
          rw [boundary_probability (by exact_mod_cast (hS p hpmem.1).one_lt) hlam,
            if_pos hpmem.2]
        _ = _ := by simp only [sum_const, nsmul_eq_mul]
    have htail : (∑ p ∈ S \ A, -log (1 - probability p (b p))) =
        ∑ p ∈ S \ A, -log (1 - 1 / (p : ℝ) ^ 2) := by
      apply sum_congr rfl
      intro p hp
      obtain ⟨hpS, hpA⟩ := mem_sdiff.mp hp
      have hinactive : ¬ (p : ℝ) ^ 2 ≤ cutoff lam := by
        intro h
        exact hpA (mem_filter.mpr ⟨hpS, h⟩)
      rw [boundary_probability (by exact_mod_cast (hS p hpS).one_lt) hlam,
        if_neg hinactive]
    dsimp [deficiency]
    rw [← sum_neg_distrib]
    linarith only [hsplit, hhead, htail]

private lemma active_prefix {P : ℕ} {lam : ℝ} (hlam : 0 < lam) :
    (Nat.primesLE P).filter (fun p : ℕ => (p : ℝ) ^ 2 ≤ cutoff lam) =
      Nat.primesLE ⌊min (P : ℝ) (sqrt (cutoff lam))⌋₊ := by
  classical
  have hx0 : 0 ≤ min (P : ℝ) (sqrt (cutoff lam)) :=
    le_min (Nat.cast_nonneg _) (sqrt_nonneg _)
  ext p
  simp only [mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpP, hprime⟩, hpC⟩
    refine ⟨(Nat.le_floor_iff hx0).mpr (le_min ?_ ?_), hprime⟩
    · exact_mod_cast hpP
    · exact (le_sqrt (Nat.cast_nonneg _) (cutoff_pos hlam).le).mpr hpC
  · rintro ⟨hpx, hprime⟩
    have hreal := (Nat.le_floor_iff hx0).mp hpx
    have hpP : p ≤ P := by exact_mod_cast (le_min_iff.mp hreal).1
    exact ⟨⟨hpP, hprime⟩,
      (le_sqrt (Nat.cast_nonneg _) (cutoff_pos hlam).le).mp (le_min_iff.mp hreal).2⟩

private lemma prefix_sdiff {P n : ℕ} :
    Nat.primesLE P \ Nat.primesLE n = (Finset.Ioc n P).filter Nat.Prime := by
  classical
  ext p
  by_cases hp : p.Prime <;>
    simp [Nat.mem_primesLE, hp, not_le, and_comm, and_left_comm, and_assoc]

/-- Literal finite prime-prefix boundary formulas. The cutoff is min(P,y),
so even y>P, the empty head, prime ties, and the upper endpoint are covered. -/
theorem prime_prefix_boundary_formulas (P : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    let x := min (P : ℝ) (sqrt (cutoff lam))
    let b : ℕ → ℝ := fun p => boundary p lam
    (clock (Nat.primesLE P) b - theta (Nat.primesLE P) =
      (Nat.primeCounting ⌊x⌋₊ : ℝ) * log (cutoff lam) - 2 * θ x) ∧
    (deficiency (Nat.primesLE P) b =
      (Nat.primeCounting ⌊x⌋₊ : ℝ) * (-log (1 - 1 / cutoff lam)) +
      ∑ p ∈ (Finset.Ioc ⌊x⌋₊ P).filter Nat.Prime, -log (1 - 1 / (p : ℝ) ^ 2)) := by
  have hS : primeSupport (Nat.primesLE P) := fun p hp => (Nat.mem_primesLE.mp hp).2
  have h := finite_boundary_sums hS hlam
  dsimp only at h ⊢
  rw [active_prefix hlam] at h
  rw [Nat.primesLE_card_eq_primeCounting, prefix_sdiff] at h
  simpa only [theta, ← Chebyshev.theta_eq_sum_primesLE] using h

/-- The linear dual quantity uses the actual boundary and exact baseline.
The identity is valid without requiring a stationary or attained minimizer. -/
theorem boundary_dual_identity {S : Finset ℕ} (hS : primeSupport S)
    {lam : ℝ} (hlam : 0 < lam) :
    let b : ℕ → ℝ := fun p => boundary p lam
    phi S b - baseline S =
      terminalCost (clock S b) - terminalCost (theta S) + deficiency S b := by
  let b : ℕ → ℝ := fun p => boundary p lam
  have hbenefit : (∑ p ∈ S, benefit p (b p)) =
      (∑ p ∈ S, log (1 - probability p (b p))) -
        (∑ p ∈ S, log (1 - (p : ℝ) ^ (-1 : ℝ))) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl (fun p hp => benefit_log
      (by exact_mod_cast (hS p hp).one_lt) (le_max_left _ _))
  change phi S b - baseline S = _
  dsimp only [phi, baseline, deficiency]
  rw [hbenefit]
  ring

/-- The fixed-price Q has its genuine finite prime meaning, rather than a
new definition chosen to assume the target asymptotic. -/
theorem fixed_price_Q_identity {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) :
    let H := theta S
    let lam := D5.S3.Arith.Robin.ActualRobinClockCovariance.g H
    let b : ℕ → ℝ := fun p => boundary p lam
    phi S b - baseline S + tangentRemainder H (clock S b) =
      deficiency S b + (clock S b - H) / (H * log H) := by
  have hH : 1 < theta S := theta_gt_one hS hcard
  have hlam : 0 < D5.S3.Arith.Robin.ActualRobinClockCovariance.g (theta S) := by
    dsimp [D5.S3.Arith.Robin.ActualRobinClockCovariance.g]
    exact one_div_pos.mpr (mul_pos (by linarith) (log_pos hH))
  have hid := boundary_dual_identity hS hlam
  dsimp only at hid ⊢
  rw [hid]
  dsimp only [tangentRemainder, D5.S3.Arith.Robin.ActualRobinClockCovariance.g]
  ring

/-- Finite lower and upper bounds on the literal all-vector sInf. The
lower bound uses pointwise price maximization and conditional completeness. -/
theorem real_infimum_fixed_price_squeeze {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) (hlog : 1 ≤ log (theta S)) {r : ℝ} (hr : 0 < r) :
    let H := theta S
    let ell := log H
    let lam := D5.S3.Arith.Robin.ActualRobinClockCovariance.g H
    let b : ℕ → ℝ := fun p => boundary p lam
    let Q := phi S b - baseline S + tangentRemainder H (clock S b)
    let A := exp (ell * (exp r - 1)) - 1
    min r (Q - A ^ 2 / ell) ≤ realInfimum S - baseline S ∧
      realInfimum S - baseline S ≤ Q := by
  let H := theta S
  let ell := log H
  let lam := D5.S3.Arith.Robin.ActualRobinClockCovariance.g H
  let b : ℕ → ℝ := fun p => boundary p lam
  let Q := phi S b - baseline S + tangentRemainder H (clock S b)
  let A := exp (ell * (exp r - 1)) - 1
  change min r (Q - A ^ 2 / ell) ≤ realInfimum S - baseline S ∧
    realInfimum S - baseline S ≤ Q
  have hb : admissible S b := fun _ _ => le_max_left _ _
  have hH : 1 < H := theta_gt_one hS hcard
  have hH0 : 0 < H := lt_trans zero_lt_one hH
  have hell : 1 ≤ ell := hlog
  have hell0 : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hlam : 0 < lam := by
    dsimp only [lam, D5.S3.Arith.Robin.ActualRobinClockCovariance.g]
    exact one_div_pos.mpr (mul_pos hH0 (log_pos hH))
  have hA : 0 ≤ A := by
    have her : 0 ≤ exp r - 1 := sub_nonneg.mpr (by simpa using exp_le_exp.mpr hr.le)
    exact sub_nonneg.mpr (by
      simpa only [A, exp_zero] using exp_le_exp.mpr (mul_nonneg hell0.le her))
  constructor
  · -- This is a lower bound at every original admissible vector, before sInf.
    have hloglower (z : ℝ) (hz : 0 ≤ z) : z - z ^ 2 / 2 ≤ log (1 + z) := by
      apply le_trans ?_ (le_log_one_add_of_nonneg hz)
      apply (le_div_iff₀ (by linarith : 0 < z + 2)).mpr
      nlinarith only [mul_nonneg hz (sq_nonneg z)]
    have hpointwise (x : ℕ → ℝ) (hx : admissible S x) :
        min r (Q - A ^ 2 / ell) ≤ phi S x - baseline S := by
      let T := clock S x
      let u := (T - H) / H
      have hHT : H ≤ T := theta_le_clock hS hx
      have hT : 1 < T := hH.trans_le hHT
      have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hHT) hH0.le
      have hw0 : 0 ≤ log (1 + u) := log_nonneg (by linarith)
      have hv0 : 0 ≤ log (1 + u) / ell := div_nonneg hw0 hell0.le
      have hdiff : terminalCost T - terminalCost H =
          log (1 + log (1 + u) / ell) := by
        have hu1 : 1 + u = T / H := by
          dsimp [u]
          field_simp [hH0.ne']
          <;> ring
        have hi : log (1 + u) = log T - log H := by
          rw [hu1, log_div (lt_trans zero_lt_one hT).ne' hH0.ne']
        have ho : 1 + log (1 + u) / ell = log T / log H := by
          rw [hi]
          dsimp [ell]
          field_simp [(log_pos hH).ne']
          <;> ring
        dsimp only [terminalCost]
        rw [ho, log_div (log_pos hT).ne' (log_pos hH).ne']
      have hquad : u / ell - u ^ 2 / ell ≤ terminalCost T - terminalCost H := by
        let w := log (1 + u)
        let v := w / ell
        have hwu : w ≤ u := by
          have h := log_le_sub_one_of_pos (by linarith : 0 < 1 + u)
          dsimp only [w]
          linarith only [h]
        have hveq : v * ell = w := div_mul_cancel₀ w hell0.ne'
        have hvw : v ≤ w := by
          nlinarith only [hveq, mul_nonneg hv0 (sub_nonneg.mpr hell)]
        have hvu : v ≤ u := hvw.trans hwu
        have hsq : v ^ 2 * ell ≤ u ^ 2 := by
          calc
            v ^ 2 * ell = w * v := by rw [← hveq]; ring
            _ ≤ u * u := mul_le_mul hwu hvu hv0 hu
            _ = u ^ 2 := by ring
        have hinner := hloglower u hu
        have houter := mul_le_mul_of_nonneg_right (hloglower v hv0) hell0.le
        have hscaled : u - u ^ 2 ≤ log (1 + v) * ell := by
          nlinarith only [hinner, houter, hsq, hveq]
        rw [hdiff]
        exact (show u / ell - u ^ 2 / ell = (u - u ^ 2) / ell by ring).trans_le
          ((div_le_iff₀ hell0).mpr hscaled)
      have hbenefit : (∑ p ∈ S, benefit p (x p)) =
          (∑ p ∈ S, log (1 - probability p (x p))) -
            (∑ p ∈ S, log (1 - (p : ℝ) ^ (-1 : ℝ))) := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl (fun p hp => benefit_log
          (by exact_mod_cast (hS p hp).one_lt) (hx p hp))
      have hid : phi S x - baseline S =
          terminalCost T - terminalCost H -
            (∑ p ∈ S, log (1 - probability p (x p))) := by
        dsimp only [phi, baseline, T, H]
        rw [hbenefit]
        ring
      have hdef : 0 ≤ -(∑ p ∈ S, log (1 - probability p (x p))) := by
        apply neg_nonneg.mpr
        apply sum_nonpos
        intro p hp
        have hprob := probability_mem (p := (p : ℝ)) (by exact_mod_cast (hS p hp).one_lt) (hx p hp)
        have h := log_le_log (by linarith : 0 < 1 - probability p (x p))
          (show 1 - probability p (x p) ≤ 1 by linarith)
        simpa only [Function.comp_def, log_one] using h
      have hprice : (∑ p ∈ S, priceObjective p lam (x p)) ≤
          ∑ p ∈ S, priceObjective p lam (b p) :=
        sum_le_sum (fun p hp => boundary_maximum
          (by exact_mod_cast (hS p hp).one_lt) hlam (hx p hp))
      simp only [priceObjective, sum_sub_distrib, mul_assoc, ← mul_sum] at hprice
      change (∑ p ∈ S, benefit p (x p)) - lam * clock S x ≤
        (∑ p ∈ S, benefit p (b p)) - lam * clock S b at hprice
      have hpricecost : lam * (T - H) = u / ell := by
        dsimp only [lam, D5.S3.Arith.Robin.ActualRobinClockCovariance.g, u, ell]
        field_simp [hH0.ne', (log_pos hH).ne']
        <;> ring
      have hdual : Q - (lam * (T - H) -
          (terminalCost T - terminalCost H)) ≤ phi S x - baseline S := by
        dsimp only [Q, phi, tangentRemainder, lam, T] at hprice ⊢
        linarith only [hprice]
      have hquadratic : Q - u ^ 2 / ell ≤ phi S x - baseline S := by
        rw [hpricecost] at hdual
        linarith only [hdual, hquad]
      by_cases hlarge : r ≤ phi S x - baseline S
      · exact (min_le_left _ _).trans hlarge
      · have hsmall : phi S x - baseline S < r := lt_of_not_ge hlarge
        have hterminal : terminalCost T - terminalCost H < r := by
          linarith only [hid, hdef, hsmall]
        have huA : u < A := by
          have hfirst := (log_lt_iff_lt_exp (by linarith :
            0 < 1 + log (1 + u) / ell)).mp (by rw [← hdiff]; exact hterminal)
          have hquot : log (1 + u) / ell < exp r - 1 := by linarith only [hfirst]
          have hinner : log (1 + u) < ell * (exp r - 1) := by
            simpa only [mul_comm] using (div_lt_iff₀ hell0).mp hquot
          have hsecond := (log_lt_iff_lt_exp (by linarith : 0 < 1 + u)).mp hinner
          dsimp only [A]
          linarith only [hsecond]
        have hsq : u ^ 2 ≤ A ^ 2 := by
          nlinarith only [mul_nonneg (sub_nonneg.mpr huA.le) (add_nonneg hA hu)]
        have hquot := div_le_div_of_nonneg_right hsq hell0.le
        exact (min_le_right _ _).trans (by linarith only [hquot, hquadratic])
    have hdomain := real_values_nonempty_bdd_below hS hcard
    have hinf : min r (Q - A ^ 2 / ell) + baseline S ≤ realInfimum S := by
      apply le_csInf hdomain.1
      rintro value ⟨x, hx, rfl⟩
      linarith only [hpointwise x hx]
    linarith only [hinf]
  · have hu := (real_infimum_bounds hS hcard hb).2
    have ht := (tangent_remainder_nonnegative hH (clock_gt_one hS hcard hb)).1
    change realInfimum S - baseline S ≤
      phi S b - baseline S + tangentRemainder H (clock S b)
    linarith only [hu, ht]


open QuantitativePrimeAbel

def prefixH (P : ℕ) : ℝ := theta (Nat.primesLE P)
def prefixEll (P : ℕ) : ℝ := log (prefixH P)
def prefixPrice (P : ℕ) : ℝ :=
  D5.S3.Arith.Robin.ActualRobinClockCovariance.g (prefixH P)
def prefixC (P : ℕ) : ℝ := cutoff (prefixPrice P)
def prefixY (P : ℕ) : ℝ := sqrt (prefixC P)
def prefixBoundary (P : ℕ) : ℕ → ℝ := fun p => boundary p (prefixPrice P)
def prefixQ (P : ℕ) : ℝ :=
  phi (Nat.primesLE P) (prefixBoundary P) - baseline (Nat.primesLE P) +
    tangentRemainder (prefixH P) (clock (Nat.primesLE P) (prefixBoundary P))

private lemma prefixH_eq_theta (P : ℕ) : prefixH P = θ (P : ℝ) := by
  exact (Chebyshev.theta_eq_sum_primesLE_log P).symm

private lemma prefixC_identity (P : ℕ) : prefixC P = 1 + prefixH P * prefixEll P := by
  simp only [prefixC, prefixPrice, cutoff,
    D5.S3.Arith.Robin.ActualRobinClockCovariance.g, one_div, inv_inv, prefixEll]

/-- The actual baseline clock has the ordinary theta-PNT normalization. -/
theorem prefix_H_ratio :
    Tendsto (fun P : ℕ => prefixH P / (P : ℝ)) atTop (𝓝 1) := by
  have h := D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2.comp
    tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, ← prefixH_eq_theta] using h

theorem prefixH_atTop : Tendsto prefixH atTop atTop := by
  have h := Filter.Tendsto.pos_mul_atTop (by norm_num : (0 : ℝ) < 1)
    prefix_H_ratio (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with P hP
  exact div_mul_cancel₀ _ (by exact_mod_cast hP.ne')

private theorem prefixEll_atTop : Tendsto prefixEll atTop atTop :=
  Real.tendsto_log_atTop.comp prefixH_atTop

private theorem prefixC_atTop : Tendsto prefixC atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ prefixH_atTop
  filter_upwards [prefixH_atTop.eventually (eventually_ge_atTop (0 : ℝ)),
    prefixEll_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with P hH he
  rw [prefixC_identity]
  nlinarith only [hH, he]

/-- Both genuine cutoff endpoints tend to infinity. -/
theorem prefix_Y_atTop : Tendsto prefixY atTop atTop :=
  Real.tendsto_sqrt_atTop.comp prefixC_atTop

/-- The actual fixed-price cutoff is below P by a vanishing relative factor.
This pays the endpoint-separation hypothesis of the finite-tail supplier. -/
theorem prefix_Y_div_cutoff :
    Tendsto (fun P : ℕ => prefixY P / (P : ℝ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun P : ℕ => 1 / (P : ℝ)) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop 1
  have hlog : Tendsto (fun P => prefixEll P / prefixH P) atTop (𝓝 0) := by
    exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp prefixH_atTop
  have hc : Tendsto (fun P : ℕ => prefixC P / (P : ℝ) ^ 2) atTop (𝓝 0) := by
    have h := (hi.pow 2).add ((prefix_H_ratio.pow 2).mul hlog)
    norm_num at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      prefixH_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with P hP hH
    rw [prefixC_identity]
    dsimp only [prefixEll]
    field_simp [hH.ne', show (P : ℝ) ≠ 0 by exact_mod_cast hP.ne']
    <;> ring
  have h := hc.sqrt
  simp only [sqrt_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    prefixC_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with P hP hC
  rw [sqrt_div hC.le, sqrt_sq (Nat.cast_nonneg P)]
  rfl

/-- The actual finite support/cardinality, price, and all cutoff conditions
hold together, before any use of the full head or the finite tail. -/
theorem eventual_prefix_domains :
    ∀ᶠ P : ℕ in atTop,
      primeSupport (Nat.primesLE P) ∧ 3 ≤ (Nat.primesLE P).card ∧
      1 ≤ prefixEll P ∧ 0 < prefixPrice P ∧ 2 < prefixY P ∧ prefixY P < (P : ℝ) := by
  have hcard := Nat.tendsto_primeCounting.eventually (eventually_ge_atTop (3 : ℕ))
  filter_upwards [hcard, prefixEll_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    prefixH_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    prefix_Y_atTop.eventually (eventually_gt_atTop (2 : ℝ)),
    prefix_Y_div_cutoff.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (0 : ℕ)] with P hc hell hH hy hr hP
  have hprice : 0 < prefixPrice P := by
    dsimp only [prefixPrice, D5.S3.Arith.Robin.ActualRobinClockCovariance.g]
    exact one_div_pos.mpr (mul_pos (by linarith) (log_pos hH))
  refine ⟨(fun p hp => (Nat.mem_primesLE.mp hp).2), ?_, hell, hprice, hy, ?_⟩
  · simpa only [Nat.primesLE_card_eq_primeCounting] using hc
  · simpa only [one_mul] using
      (div_lt_iff₀ (show (0 : ℝ) < P by exact_mod_cast hP)).mp hr



private lemma prefix_H_ell_atTop :
    Tendsto (fun P : ℕ => prefixH P * prefixEll P) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ prefixH_atTop
  filter_upwards [prefixH_atTop.eventually (eventually_ge_atTop (0 : ℝ)),
    prefixEll_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with P hH he
  nlinarith only [hH, he]

/-- Every denominator used below is eventually strictly positive. -/
theorem eventual_scale_positivity :
    ∀ᶠ P : ℕ in atTop,
      0 < prefixH P ∧ 0 < prefixEll P ∧ 0 < prefixC P ∧
      0 < prefixY P ∧ 0 < log (prefixY P) ∧
      0 < (P : ℝ) ∧ 0 < log (P : ℝ) := by
  filter_upwards [eventual_prefix_domains, eventually_gt_atTop (1 : ℕ)] with P h hP
  have hH : 0 < prefixH P := lt_trans zero_lt_one (theta_gt_one h.1 h.2.1)
  have he : 0 < prefixEll P := lt_of_lt_of_le zero_lt_one h.2.2.1
  have hC : 0 < prefixC P := by rw [prefixC_identity]; positivity
  have hy : 1 < prefixY P := lt_trans (by norm_num) h.2.2.2.2.1
  have hp : (1 : ℝ) < P := by exact_mod_cast hP
  exact ⟨hH, he, hC, lt_trans zero_lt_one hy, log_pos hy,
    lt_trans zero_lt_one hp, log_pos hp⟩

/-- The additive one in the actual cutoff is negligible. -/
theorem prefix_C_div_H_ell :
    Tendsto (fun P : ℕ => prefixC P / (prefixH P * prefixEll P))
      atTop (𝓝 (1 : ℝ)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add (prefix_H_ell_atTop.const_div_atTop 1)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventual_scale_positivity] with P hP
  rcases hP with ⟨hH, he, hC, hy, hly, hp, hlp⟩
  rw [prefixC_identity]
  field_simp [hH.ne', he.ne']
  <;> ring

/-- Logarithms are split only on the paid positive eventual domain. -/
theorem eventual_log_C_identity :
    ∀ᶠ P : ℕ in atTop,
      log (prefixC P) = prefixEll P + log (prefixEll P) +
        log (prefixC P / (prefixH P * prefixEll P)) := by
  filter_upwards [eventual_scale_positivity] with P hP
  rcases hP with ⟨hH, he, hC, hy, hly, hp, hlp⟩
  rw [log_div hC.ne' (mul_ne_zero hH.ne' he.ne'), log_mul hH.ne' he.ne']
  change log (prefixC P) = log (prefixH P) + log (prefixEll P) +
    (log (prefixC P) - (log (prefixH P) + log (prefixEll P)))
  ring

/-- The genuine cutoff logarithm is asymptotic to ell/2. -/
theorem prefix_log_Y_div_ell :
    Tendsto (fun P : ℕ => log (prefixY P) / prefixEll P)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hsmall : Tendsto (fun P : ℕ => log (prefixEll P) / prefixEll P)
      atTop (𝓝 (0 : ℝ)) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp prefixEll_atTop
  have hlog : Tendsto
      (fun P : ℕ => log (prefixC P / (prefixH P * prefixEll P)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp prefix_C_div_H_ell
  have hc : Tendsto (fun P : ℕ => log (prefixC P) / prefixEll P)
      atTop (𝓝 (1 : ℝ)) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).add hsmall).add
      (hlog.div_atTop prefixEll_atTop)
    norm_num only [add_zero] at h
    apply h.congr'
    filter_upwards [eventual_log_C_identity, eventual_scale_positivity] with P hC hP
    rcases hP with ⟨hH, he, hCp, hy, hly, hp, hlp⟩
    rw [hC]
    field_simp [he.ne']
    <;> ring
  have h := hc.div_const 2
  apply h.congr'
  filter_upwards [eventual_scale_positivity] with P hP
  rcases hP with ⟨hH, he, hC, hy, hly, hp, hlp⟩
  dsimp only [prefixY]
  rw [log_sqrt hC.le]
  ring

/-- The square-root correction tends to one for the actual C. -/
theorem prefix_Y_div_sqrt_H_ell :
    Tendsto (fun P : ℕ => prefixY P / sqrt (prefixH P * prefixEll P))
      atTop (𝓝 (1 : ℝ)) := by
  have h := prefix_C_div_H_ell.sqrt
  simp only [sqrt_one] at h
  apply h.congr'
  filter_upwards [eventual_scale_positivity] with P hP
  rcases hP with ⟨hH, he, hC, hy, hly, hp, hlp⟩
  rw [sqrt_div hC.le]
  rfl

-- A consumed analytic helper, used for BOTH exponentials. Its argument's
-- nonzero eventual domain is proved at each call, not assumed globally.
lemma exp_difference_quotient {α : Type*} {l : Filter α} {u : α → ℝ}
    (hu : Tendsto u l (𝓝 (0 : ℝ))) (hu0 : ∀ᶠ a in l, u a ≠ 0) :
    Tendsto (fun a => (exp (u a) - 1) / u a) l (𝓝 (1 : ℝ)) := by
  have hd : Tendsto (fun t : ℝ => (exp t - 1) / t)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [zero_add, exp_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_exp 0).tendsto_slope_zero
  have hu' : Tendsto u l (𝓝[≠] (0 : ℝ)) := tendsto_nhdsWithin_iff.mpr
    ⟨hu, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hu0⟩
  exact hd.comp hu'



end D5.S3.Arith.Robin.PriceRecord.RealInfimumPrimeBoundary
