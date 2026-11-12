/- GID: D5/S3/Arith/Robin/PriceRecord/ActualMovingBoundaryLocalization
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualMovingBoundaryLocalization
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: One-sided displaced-root localization at the original full record. -/
import D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
import D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
import D5.S3.Arith.Robin.PriceRecord.HigherLayerInsertionRegret

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualMovingBoundaryLocalization
open Finset Real
open scoped BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
open D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff

/- The finite exchanges below precede any adjacent-layer separation. Insertion
above Q_j uses v_p(m)+1<=j; deletion below Q_j uses j<=v_p(m).
Recordhood is always at the original mu, including the signed strict mass gap. -/

private theorem marginal_antitone {p a b : ℕ} (hp : p.Prime)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    goldenLayerMarginal p b ≤ goldenLayerMarginal p a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact (golden_layer_strict_decrease hp ha hlt).le

private theorem insertion_bound {m j p : ℕ} (hm : 0 < m) (hj : 2 ≤ j)
    (hp : p.Prime) (hQp : layerPrime m j < p) {r : ℝ}
    (hr : 2 ≤ r) (hpr : (p : ℝ) ≤ r) :
    beta j r ≤ goldenLayerMarginal p (m.factorization p + 1) := by
  have hv := valuation_above_layer_prime hm (by omega : 1 ≤ j) hp hQp
  have hreal : 2 ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hb := (beta_strictAntiOn hj).antitoneOn hreal hr hpr
  rw [beta_nat hp (by omega : 1 ≤ j)] at hb
  exact hb.trans (marginal_antitone hp (by omega) (by omega))

private theorem deletion_bound {m j p : ℕ} (hj : 2 ≤ j)
    (hp : p.Prime)
    (hanti : ∀ q r : ℕ, q.Prime → r.Prime → q < r →
      m.factorization r ≤ m.factorization q)
    (hpQ : p ≤ layerPrime m j) {r : ℝ} (hr : 2 ≤ r) (hrp : r ≤ (p : ℝ)) :
    goldenLayerMarginal p (m.factorization p) ≤ beta j r := by
  have hv := valuation_below_layer_prime hp hanti hpQ
  have hreal : 2 ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hb := (beta_strictAntiOn hj).antitoneOn hr hreal hrp
  rw [beta_nat hp (by omega : 1 ≤ j)] at hb
  exact (marginal_antitone hp (by omega) hv).trans hb

private theorem lower_probe_exchange {m j : ℕ} {mu lambda e W a r : ℝ}
    (hm : 0 < m) (hj : 2 ≤ j) (hrecord : FullRecord m mu)
    (First S : Finset ℕ)
    (hFirst : ∀ p ∈ First, p.Prime ∧ p ∣ m ∧
      log (p : ℝ) ≤ W ∧ beta 1 (p : ℝ) ≤ (1 + e) * lambda)
    (hS : ∀ p ∈ S, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ r)
    (hdis : Disjoint First S) (hr : 2 ≤ r)
    (hN : 0 ≤ logMass S) (hfull : logMass S < logMass First)
    (hQa : (layerPrime m j : ℝ) < a) :
    ∃ D ⊆ First, logMass S < logMass D ∧ logMass D ≤ logMass S + W ∧
      beta j r * logMass S < (1 + e) * lambda * logMass D -
        mu * (logMass D - logMass S) := by
  obtain ⟨D, hDF, hND, hDN⟩ := subset_just_above First (fun p => log (p : ℝ))
    hN (fun p hp => (hFirst p hp).2.2.1) hfull
  refine ⟨D, hDF, hND, hDN, ?_⟩
  apply exchange_mass_bound hm hrecord D S
    (fun p hp => (hFirst p (hDF hp)).1) (fun p hp => (hS p hp).1)
    (fun p hp => (hFirst p (hDF hp)).2.1) (hdis.mono_left hDF) hND
  · unfold logMass
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hf := hFirst p (hDF hp)
    have hv : 1 ≤ m.factorization p :=
      (hf.1.dvd_iff_one_le_factorization hm.ne').mp hf.2.1
    have hb := marginal_antitone hf.1 (by norm_num : 1 ≤ 1) hv
    rw [← beta_nat hf.1 (by norm_num : 1 ≤ 1)] at hb
    exact mul_le_mul_of_nonneg_right (hb.trans hf.2.2.2) (log_natCast_nonneg p)
  · unfold logMass
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hs := hS p hp
    have hQp : layerPrime m j < p := by exact_mod_cast hQa.trans_le hs.2.1
    exact mul_le_mul_of_nonneg_right
      (insertion_bound hm hj hs.1 hQp hr hs.2.2) (log_natCast_nonneg p)

private theorem upper_probe_exchange {m j : ℕ} {mu lambda e W r b : ℝ}
    (hm : 0 < m) (hj : 2 ≤ j) (hrecord : FullRecord m mu)
    (hanti : ∀ q t : ℕ, q.Prime → t.Prime → q < t →
      m.factorization t ≤ m.factorization q)
    (First S : Finset ℕ)
    (hFirst : ∀ p ∈ First, p.Prime ∧ m.factorization p = 0 ∧
      log (p : ℝ) ≤ W ∧ (1 - e) * lambda ≤ beta 1 (p : ℝ))
    (hS : ∀ p ∈ S, p.Prime ∧ r ≤ (p : ℝ) ∧ (p : ℝ) ≤ b)
    (hdis : Disjoint S First) (hr : 2 ≤ r)
    (hN : 0 < logMass S) (hfull : logMass S ≤ logMass First)
    (hbQ : b ≤ (layerPrime m j : ℝ)) :
    ∃ U ⊆ First, logMass U < logMass S ∧ logMass S ≤ logMass U + W ∧
      (1 - e) * lambda * logMass U < beta j r * logMass S -
        mu * (logMass S - logMass U) := by
  obtain ⟨U, hUF, hUN, hNU⟩ := subset_just_below First (fun p => log (p : ℝ))
    hN (fun p hp => (hFirst p hp).2.2.1) hfull
  have hpQ : ∀ p ∈ S, p ≤ layerPrime m j := by
    intro p hp
    exact_mod_cast (hS p hp).2.2.trans hbQ
  have hdiv : ∀ p ∈ S, p ∣ m := by
    intro p hp
    have hv := valuation_below_layer_prime (hS p hp).1 hanti (hpQ p hp)
    exact ((hS p hp).1.dvd_iff_one_le_factorization hm.ne').mpr
      ((by omega : 1 ≤ j).trans hv)
  refine ⟨U, hUF, hUN, hNU, ?_⟩
  apply exchange_mass_bound hm hrecord S U (fun p hp => (hS p hp).1)
    (fun p hp => (hFirst p (hUF hp)).1) hdiv (hdis.mono_right hUF) hUN
  · unfold logMass
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_right
      (deletion_bound hj (hS p hp).1 hanti (hpQ p hp) hr (hS p hp).2.1)
      (log_natCast_nonneg p)
  · unfold logMass
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hf := hFirst p (hUF hp)
    rw [hf.2.1, zero_add, ← beta_nat hf.1 (by norm_num : 1 ≤ 1)]
    exact mul_le_mul_of_nonneg_right hf.2.2.2 (log_natCast_nonneg p)

end D5.S3.Arith.Robin.PriceRecord.ActualMovingBoundaryLocalization
