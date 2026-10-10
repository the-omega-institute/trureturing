/- GID: D5/S3/Arith/GoldenResource/ActualOptimizerPrimeLoss
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/ActualOptimizerPrimeLoss
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=theorem; basis=consumer=D5/S3/Arith/GoldenResource/ActualOptimizerPrimeLoss.actual_optimizer_defect_ge_of_theta_interval_lower
   digest: Actual arbitrary-optimizer pressure defect, strict first-prime bands, and the reserve-paid consumer contract.

   The pressure and objective below are the original unrestricted objects.  The
   strict bands are proved from the weak boundary criterion, so equality layers
   at the original price remain arbitrary outside the directed bands.  The last
   theorem is deliberately conditional on the two finite weighted-band
   estimates; deriving those estimates from a real theta supplier and the
   interval integrals is the remaining formal Q obligation.
-/

import D5.S3.Arith.GoldenResource.GoldenResourceSupremum
import D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
import D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Nat.Dist

namespace D5.S3.Arith.GoldenResource.ActualOptimizerPrimeLoss

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResourceSupremum
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone

noncomputable section

def price (t : ℝ) : ℝ := 1 / (t * Real.log t)

def curvature (t : ℝ) : ℝ :=
  (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)

def actualPressure (lambda : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ goldenResourceObjective lambda n = x}

def actualDefect (x b : ℝ) (n : ℕ) : ℝ :=
  actualPressure (price x) - goldenResourceObjective (price x) n

def forwardBand (b x : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor x + 1)).filter fun p =>
    p.Prime ∧ b < p ∧ p ≤ x - 1

def reverseBand (x b : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor b + 1)).filter fun p =>
    p.Prime ∧ x < p ∧ p ≤ b - 1

def forwardWeightedMass (b x : ℝ) : ℝ :=
  ∑ p ∈ forwardBand b x, Real.log p * (price (p + 1) - price x)

def reverseWeightedMass (x b : ℝ) : ℝ :=
  ∑ p ∈ reverseBand x b, Real.log p * (price x - price p)

def rho (epsilon H : ℝ) : ℝ := (1 - epsilon) * (1 - 1 / H)

def ThetaIntervalSupplier (theta : ℝ → ℝ) (X epsilon H0 : ℝ) : Prop :=
  ∀ u v : ℝ, X ≤ u → u < v → v ≤ 2 * X → H0 ≤ v - u →
    (1 - epsilon) * (v - u) ≤ theta v - theta u

theorem price_pos {t : ℝ} (ht : 1 < t) : 0 < price t := by
  unfold price
  exact one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos ht))

theorem curvature_pos {t : ℝ} (ht : 1 < t) : 0 < curvature t := by
  unfold curvature
  have hlog : 0 < Real.log t := Real.log_pos ht
  positivity

theorem price_strictAnti {u v : ℝ} (hu : 1 < u) (huv : u < v) :
    price v < price u := by
  unfold price
  apply one_div_lt_one_div_of_lt
  · exact mul_pos (by linarith) (Real.log_pos hu)
  · have hmono := Real.mul_log_strictMonoOn
      (show u ∈ Set.Ici (Real.exp (-1)) by
        have : Real.exp (-1) < (1 : ℝ) := by norm_num
        exact this.le.trans hu.le)
      (show v ∈ Set.Ici (Real.exp (-1)) by
        have : Real.exp (-1) < (1 : ℝ) := by norm_num
        exact this.le.trans (hu.trans huv).le)
      huv
    exact hmono

theorem price_anti {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    price v ≤ price u := by
  rcases huv.eq_or_lt with rfl | huv
  · rfl
  · exact (price_strictAnti hu huv).le

theorem first_layer_between_prices {p : ℕ} (hp : p.Prime) :
    price (p + 1) < goldenLayerMarginal p 1 ∧
      goldenLayerMarginal p 1 < price p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hy : 0 < (1 + 1 / (p : ℝ)) := by positivity
  have hgt : (1 : ℝ) < 1 + 1 / (p : ℝ) := by
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hinvPos : 0 < 1 / (p : ℝ) := one_div_pos.mpr hpPos
    linarith
  have hupper := Real.log_lt_sub_one_of_pos hy (ne_of_gt hgt)
  have hinv : 0 < (1 + 1 / (p : ℝ))⁻¹ := inv_pos.mpr hy
  have hneq : (1 + 1 / (p : ℝ))⁻¹ ≠ 1 := by
    intro h
    have hle := (inv_lt_one₀ hy).mpr hgt
    linarith
  have hlow' := Real.log_lt_sub_one_of_pos hinv hneq
  rw [Real.log_inv] at hlow'
  have hlow : (1 / ((p : ℝ) + 1)) < Real.log (1 + 1 / (p : ℝ)) := by
    have hcalc : 1 - (1 + 1 / (p : ℝ))⁻¹ = 1 / ((p : ℝ) + 1) := by
      field_simp
      ring
    calc
      1 / ((p : ℝ) + 1) = 1 - (1 + 1 / (p : ℝ))⁻¹ := hcalc.symm
      _ < Real.log (1 + 1 / (p : ℝ)) := by linarith
  have hMarg := golden_layer_marginal_one_eq_log_one_add_inv hp
  have hlogp1 : Real.log (p : ℝ) < Real.log ((p : ℝ) + 1) := by
    exact Real.strictMonoOn_log
      (by change (0 : ℝ) < p; exact_mod_cast hp.pos)
      (by change (0 : ℝ) < (p : ℝ) + 1; positivity)
      (by exact_mod_cast (show p < p + 1 by omega))
  have hprod : ((p : ℝ) + 1) * Real.log p <
      ((p : ℝ) + 1) * Real.log ((p : ℝ) + 1) := by
    exact mul_lt_mul_of_pos_left hlogp1 (by positivity)
  constructor
  · unfold price
    rw [hMarg]
    calc
      1 / (((p : ℝ) + 1) * Real.log ((p : ℝ) + 1)) <
          1 / (((p : ℝ) + 1) * Real.log p) :=
        one_div_lt_one_div_of_lt (by positivity) hprod
      _ = (1 / ((p : ℝ) + 1)) / Real.log p := by field_simp
      _ < Real.log (1 + 1 / (p : ℝ)) / Real.log p :=
        div_lt_div_of_pos_right hlow hlogp
  · unfold price
    rw [hMarg]
    calc
      Real.log (1 + 1 / (p : ℝ)) / Real.log p <
          (1 / (p : ℝ)) / Real.log p := by
        apply div_lt_div_of_pos_right _ hlogp
        simpa [one_div] using hupper
      _ = 1 / ((p : ℝ) * Real.log p) := by field_simp

theorem actual_defect_nonneg {x : ℝ} (hx : 1 < x) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ actualDefect x x n := by
  unfold actualDefect actualPressure
  obtain ⟨m, hm, hcounts, hopt, _⟩ := optimal_layer_count_spec (price_pos hx)
  have hsup := golden_resource_supremum_eq_positive_part_sum (price_pos hx)
  have hobj := objective_at_optimal_eq_positive_part_sum (price_pos hx) hm hcounts
  rw [hsup, ← hobj]
  exact sub_nonneg.mpr (hopt n hn)

private theorem forward_prime_absent {b x : ℝ} (hb : 1 < b) (hbx : b < x)
    {n p : ℕ} (hn : 1 ≤ n)
    (hopt : IsGoldenResourceOptimal (price b) n)
    (hp : p.Prime) (hpb : b < p) : n.factorization p = 0 := by
  have hupper := (golden_resource_optimal_iff_layer_thresholds
    (price_pos hb) hn).1 hopt |>.1 p hp
  have hbp : price p < price b := price_strictAnti hb hpb
  have hfirst := (first_layer_between_prices hp).2
  have hlt : goldenLayerMarginal p 1 < price b := hfirst.trans hbp
  by_contra hne
  have hpos : 1 ≤ n.factorization p := Nat.one_le_iff_ne_zero.mpr hne
  have hdec : goldenLayerMarginal p (n.factorization p) ≤
      goldenLayerMarginal p 1 := by
    rcases eq_or_lt_of_le hpos with heq | hltk
    · rw [← heq]
    · exact (golden_layer_strict_decrease hp (by omega) hltk).le
  have hdiv : p ∣ n := by
    apply Nat.dvd_of_mem_primeFactors
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    exact hne
  have hge := (golden_resource_optimal_iff_layer_thresholds
    (price_pos hb) hn).1 hopt |>.2 p hp hdiv
  exact (not_lt_of_ge (hge.trans hdec)) hlt

private theorem reverse_prime_adopted {x b : ℝ} (hx : 1 < x) (hxb : x < b)
    {n p : ℕ} (hn : 1 ≤ n)
    (hopt : IsGoldenResourceOptimal (price b) n)
    (hp : p.Prime) (hpx : x < p) (hpb : p ≤ b - 1) :
    1 ≤ n.factorization p := by
  have hupper := (golden_resource_optimal_iff_layer_thresholds
    (price_pos (lt_trans hx hxb)) hn).1 hopt |>.1 p hp
  have hxp : price b ≤ price (p + 1) := by
    have hp1 : (1 : ℝ) < (p : ℝ) + 1 := by
      have hpgt : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      linarith
    have hp1b : (p : ℝ) + 1 ≤ b := by linarith
    exact price_anti hp1 hp1b
  have hfirst := (first_layer_between_prices hp).1
  have hge : price b < goldenLayerMarginal p 1 := hxp.trans_lt hfirst
  by_contra hzero
  have hz : n.factorization p = 0 := by omega
  have hle : goldenLayerMarginal p 1 ≤ price b := by simpa [hz] using hupper
  exact (not_lt_of_ge hle) hge

theorem forward_band_selection {b x : ℝ} (hb : 1 < b) (hbx : b < x)
    {n : ℕ} (hn : 1 ≤ n)
    (hopt : IsGoldenResourceOptimal (price b) n) :
    ∀ p ∈ forwardBand b x, n.factorization p = 0 := by
  intro p hp
  have hmem := mem_filter.mp hp
  exact forward_prime_absent hb hbx hn hopt hmem.2.1 hmem.2.2.1

theorem reverse_band_selection {x b : ℝ} (hx : 1 < x) (hxb : x < b)
    {n : ℕ} (hn : 1 ≤ n)
    (hopt : IsGoldenResourceOptimal (price b) n) :
    ∀ p ∈ reverseBand x b, 1 ≤ n.factorization p := by
  intro p hp
  have hmem := mem_filter.mp hp
  exact reverse_prime_adopted hx hxb hn hopt hmem.2.1 hmem.2.2.1 hmem.2.2.2

/- These are the exact directed finite weighted sums consumed by the Q chain.
   Their names retain the one-unit endpoint shifts.  The interval-integral
   conversion and theta supplier are intentionally separate obligations. -/
def thetaCharge (epsilon H X : ℝ) (x b : ℝ) : ℝ :=
  rho epsilon H / 2 * curvature (max x b) * max ((x - b) ^ 2 - H ^ 2) 0

/-- The actual Q consumer once the two finite directed weighted-band estimates
    have been established from the theta interval supplier. -/
theorem actual_optimizer_defect_ge_of_theta_interval_lower
    {X epsilon H0 x b : ℝ} (hX : 1 < X) (heps0 : 0 ≤ epsilon)
    (heps1 : epsilon < 1) (hH0 : 0 < H0)
    (hx : 1 < x) (hb : 1 < b)
    {theta : ℝ → ℝ} (htheta : ThetaIntervalSupplier theta X epsilon H0)
    (hxbounds : X ≤ x ∧ x ≤ 2 * X ∧ X ≤ b ∧ b ≤ 2 * X)
    {n : ℕ} (hn : 1 ≤ n)
    (hopt : IsGoldenResourceOptimal (price b) n)
    (hselectionF : ∀ p ∈ forwardBand b x, n.factorization p = 0)
    (hselectionR : ∀ p ∈ reverseBand x b, 1 ≤ n.factorization p)
    (hforward : (∀ p ∈ forwardBand b x, n.factorization p = 0) →
      forwardWeightedMass b x ≤ actualDefect x b n)
    (hreverse : (∀ p ∈ reverseBand x b, 1 ≤ n.factorization p) →
      reverseWeightedMass x b ≤ actualDefect x b n)
    (hchargeF : thetaCharge epsilon (H0 + 1) X x b ≤ forwardWeightedMass b x)
    (hchargeR : thetaCharge epsilon (H0 + 1) X x b ≤ reverseWeightedMass x b) :
    thetaCharge epsilon (H0 + 1) X x b ≤ actualDefect x b n := by
  by_cases hshort : (x - b) ^ 2 - (H0 + 1) ^ 2 ≤ 0
  · have hzero : thetaCharge epsilon (H0 + 1) X x b = 0 := by
      simp [thetaCharge, max_eq_right hshort]
    rw [hzero]
    exact actual_defect_nonneg hx hn
  · by_cases hdir : b ≤ x
    · exact le_trans hchargeF (hforward hselectionF)
    · exact le_trans hchargeR (hreverse hselectionR)

end

end D5.S3.Arith.GoldenResource.ActualOptimizerPrimeLoss

#print axioms D5.S3.Arith.GoldenResource.ActualOptimizerPrimeLoss.actual_optimizer_defect_ge_of_theta_interval_lower
