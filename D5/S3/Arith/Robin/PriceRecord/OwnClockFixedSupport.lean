/- GID: D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport
   mirror-E: none(waiver:general-real-analysis)
   anchors: []
   utility: none
   digest: Exact fixed-support nonlinear own-clock loss relative to the real infimum. -/

import D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice
import D5.S3.Arith.Robin.LogarithmBounds

/-! The infimum is taken over the same fixed support and exponent domain as
the nonlinear objective. No attainment, uniqueness, six-band estimate or RH
conclusion is asserted. -/

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport

open Real Set Finset
open D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice

def primeSupport (S : Finset ℕ) : Prop := ∀ p ∈ S, Nat.Prime p

def admissible (S : Finset ℕ) (x : ℕ → ℝ) : Prop := ∀ p ∈ S, 1 ≤ x p

def theta (S : Finset ℕ) : ℝ := ∑ p ∈ S, log (p : ℝ)

def clock (S : Finset ℕ) (x : ℕ → ℝ) : ℝ := ∑ p ∈ S, x p * log (p : ℝ)

def terminalCost (L : ℝ) : ℝ := log (log L)

/-- The Euler constant and the full nonlinear terminal cost are retained. -/
def phi (S : Finset ℕ) (x : ℕ → ℝ) : ℝ :=
  eulerMascheroniConstant + terminalCost (clock S x) - ∑ p ∈ S, benefit p (x p)

def realValues (S : Finset ℕ) : Set ℝ :=
  {r | ∃ x : ℕ → ℝ, admissible S x ∧ phi S x = r}

def realInfimum (S : Finset ℕ) : ℝ := sInf (realValues S)

def baseline (S : Finset ℕ) : ℝ :=
  eulerMascheroniConstant + terminalCost (theta S) +
    ∑ p ∈ S, log (1 - (p : ℝ) ^ (-1 : ℝ))

/-- Reuse the canonical reciprocal-log kernel, evaluated at this vector's clock. -/
def ownPrice (S : Finset ℕ) (x : ℕ → ℝ) : ℝ :=
  D5.S3.Arith.Robin.ActualRobinClockCovariance.g (clock S x)

def ownBoundary (S : Finset ℕ) (x : ℕ → ℝ) : ℕ → ℝ :=
  fun p => boundary p (ownPrice S x)

def tangentRemainder (L T : ℝ) : ℝ :=
  terminalCost L + D5.S3.Arith.Robin.ActualRobinClockCovariance.g L * (T - L) -
    terminalCost T

def roundingSum (S : Finset ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ p ∈ S, integerGap p (ownPrice S x)

lemma theta_gt_one {S : Finset ℕ} (hS : primeSupport S) (hcard : 3 ≤ S.card) :
    1 < theta S := by
  have hhalf : (1 / 2 : ℝ) ≤ log 2 := by
    have h := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hsum : ∑ p ∈ S, (1 / 2 : ℝ) ≤ ∑ p ∈ S, log (p : ℝ) := by
    apply sum_le_sum
    intro p hp
    exact hhalf.trans (log_le_log (by norm_num) (by exact_mod_cast (hS p hp).two_le))
  have hc : (3 : ℝ) ≤ S.card := by exact_mod_cast hcard
  have hs : (S.card : ℝ) * (1 / 2) ≤ theta S := by
    simpa only [sum_const, nsmul_eq_mul, theta] using hsum
  nlinarith

lemma theta_le_clock {S : Finset ℕ} (hS : primeSupport S)
    {x : ℕ → ℝ} (hx : admissible S x) : theta S ≤ clock S x := by
  apply sum_le_sum
  intro p hp
  have hpR : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hx p hp) (log_pos hpR).le

lemma clock_gt_one {S : Finset ℕ} (hS : primeSupport S) (hcard : 3 ≤ S.card)
    {x : ℕ → ℝ} (hx : admissible S x) : 1 < clock S x :=
  (theta_gt_one hS hcard).trans_le (theta_le_clock hS hx)

lemma own_price_pos {S : Finset ℕ} (hS : primeSupport S) (hcard : 3 ≤ S.card)
    {x : ℕ → ℝ} (hx : admissible S x) : 0 < ownPrice S x := by
  have hL := clock_gt_one hS hcard hx
  dsimp [ownPrice, D5.S3.Arith.Robin.ActualRobinClockCovariance.g]
  exact one_div_pos.mpr (mul_pos (by linarith) (log_pos hL))

lemma own_boundary_admissible (S : Finset ℕ) (x : ℕ → ℝ) :
    admissible S (ownBoundary S x) := by
  intro p hp
  exact le_max_left _ _

private lemma baseline_lower {S : Finset ℕ} (hS : primeSupport S) (hcard : 3 ≤ S.card)
    {x : ℕ → ℝ} (hx : admissible S x) : baseline S ≤ phi S x := by
  have htheta := theta_gt_one hS hcard
  have hclock := theta_le_clock hS hx
  have hg : terminalCost (theta S) ≤ terminalCost (clock S x) :=
    log_le_log (log_pos htheta) (log_le_log (by linarith) hclock)
  have hf : ∑ p ∈ S, benefit p (x p) ≤
      -(∑ p ∈ S, log (1 - (p : ℝ) ^ (-1 : ℝ))) := by
    rw [← sum_neg_distrib]
    apply sum_le_sum
    intro p hp
    have hpR : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
    have hu := probability_mem hpR (hx p hp)
    have hlog : log (1 - probability p (x p)) ≤ 0 := by
      simpa using log_le_log (by linarith : 0 < 1 - probability p (x p))
        (show 1 - probability p (x p) ≤ 1 by linarith)
    rw [benefit_log hpR (hx p hp)]
    linarith
  dsimp only [baseline, phi]
  linarith

/-- Both conditional-completeness obligations are established for this exact domain. -/
theorem real_values_nonempty_bdd_below {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) : (realValues S).Nonempty ∧ BddBelow (realValues S) := by
  constructor
  · exact ⟨phi S (fun _ => 1), fun _ => 1, (by intro p hp; exact le_rfl), rfl⟩
  · refine ⟨baseline S, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    exact baseline_lower hS hcard hx

/-- In particular the reference value cannot be chosen to assume the gap theorem. -/
theorem real_infimum_bounds {S : Finset ℕ} (hS : primeSupport S) (hcard : 3 ≤ S.card)
    {x : ℕ → ℝ} (hx : admissible S x) :
    baseline S ≤ realInfimum S ∧ realInfimum S ≤ phi S x := by
  have hd := real_values_nonempty_bdd_below hS hcard
  constructor
  · exact le_csInf hd.1 (by rintro r ⟨y, hy, rfl⟩; exact baseline_lower hS hcard hy)
  · exact csInf_le hd.2 ⟨x, hx, rfl⟩

private lemma sum_price (S : Finset ℕ) (x : ℕ → ℝ) (lam : ℝ) :
    (∑ p ∈ S, priceObjective p lam (x p)) =
      (∑ p ∈ S, benefit p (x p)) - lam * clock S x := by
  simp only [priceObjective, clock, sum_sub_distrib, mul_sum, mul_assoc]

private lemma nonlinear_identity (S : Finset ℕ) (x : ℕ → ℝ) :
    phi S x - realInfimum S =
      (phi S (ownBoundary S x) - realInfimum S) +
        (∑ p ∈ S, priceLoss p (ownPrice S x) (x p)) +
          tangentRemainder (clock S x) (clock S (ownBoundary S x)) := by
  have hsum : (∑ p ∈ S, priceLoss p (ownPrice S x) (x p)) =
      (∑ p ∈ S, benefit p (ownBoundary S x p)) -
        (∑ p ∈ S, benefit p (x p)) +
          ownPrice S x * (clock S x - clock S (ownBoundary S x)) := by
    change (∑ p ∈ S, (priceObjective p (ownPrice S x) (ownBoundary S x p) -
      priceObjective p (ownPrice S x) (x p))) = _
    rw [sum_sub_distrib, sum_price, sum_price]
    ring
  rw [hsum]
  dsimp only [phi, tangentRemainder, ownPrice]
  ring

/-- The own-clock correction has the concave-tangent sign, with no T=L premise.
The equality case is included; strictness is exactly L != T. -/
theorem tangent_remainder_nonnegative {L T : ℝ} (hL : 1 < L) (hT : 1 < T) :
    0 ≤ tangentRemainder L T ∧ (0 < tangentRemainder L T ↔ L ≠ T) := by
  by_cases heq : L = T
  · subst T
    simp [tangentRemainder]
  · have ht := D5.S3.Arith.Robin.RestrictedDivisorStrictInventory.loglog_tangent hL hT heq
    have hpos : 0 < tangentRemainder L T := by
      dsimp [terminalCost, tangentRemainder]
      nlinarith only [ht]
    exact ⟨hpos.le, ⟨fun _ => heq, fun _ => hpos⟩⟩

/-- Exact three-term identity for every admissible real vector, with all three
terms nonnegative. The real reference is b at clock T, not b at clock L. -/
theorem own_clock_decomposition {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) {x : ℕ → ℝ} (hx : admissible S x) :
    phi S x - realInfimum S =
      (phi S (ownBoundary S x) - realInfimum S) +
        (∑ p ∈ S, priceLoss p (ownPrice S x) (x p)) +
          tangentRemainder (clock S x) (clock S (ownBoundary S x)) ∧
    0 ≤ phi S (ownBoundary S x) - realInfimum S ∧
    (∀ p ∈ S, 0 ≤ priceLoss p (ownPrice S x) (x p)) ∧
    0 ≤ tangentRemainder (clock S x) (clock S (ownBoundary S x)) := by
  have hb := own_boundary_admissible S x
  have hL := clock_gt_one hS hcard hx
  have hT := clock_gt_one hS hcard hb
  refine ⟨nonlinear_identity S x, sub_nonneg.mpr (real_infimum_bounds hS hcard hb).2, ?_,
    (tangent_remainder_nonnegative hL hT).1⟩
  intro p hp
  have hpR : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
  exact sub_nonneg.mpr (boundary_maximum hpR (own_price_pos hS hcard hx) (hx p hp))

/-- The loss sum bounds the exact two-candidate penalty for EVERY integer
vector. Price optimality of the supplied vector is not a hypothesis. -/
theorem all_integer_gap {S : Finset ℕ} (hS : primeSupport S) (hcard : 3 ≤ S.card)
    (a : ℕ → ℤ) (ha : ∀ p ∈ S, 1 ≤ a p) :
    0 ≤ roundingSum S (fun p => (a p : ℝ)) ∧
      roundingSum S (fun p => (a p : ℝ)) ≤
        phi S (fun p => (a p : ℝ)) - realInfimum S := by
  let x : ℕ → ℝ := fun p => (a p : ℝ)
  have hx : admissible S x := by intro p hp; exact_mod_cast ha p hp
  have hlam := own_price_pos hS hcard hx
  have hd := own_clock_decomposition hS hcard hx
  have hsum : roundingSum S x ≤ ∑ p ∈ S, priceLoss p (ownPrice S x) (x p) := by
    apply sum_le_sum
    intro p hp
    have hpR : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
    obtain ⟨k, hk, hgap, hopt⟩ := integer_gap_attained hpR hlam
    rw [hgap]
    exact sub_le_sub_left (hopt (a p) (ha p hp)) _
  constructor
  · exact sum_nonneg (fun p hp =>
      (integer_gap_bounds (by exact_mod_cast (hS p hp).one_lt) hlam (a p) (ha p hp)).1)
  · change roundingSum S x ≤ phi S x - realInfimum S
    linarith [hd.1, hd.2.1, hd.2.2.2]

end D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
