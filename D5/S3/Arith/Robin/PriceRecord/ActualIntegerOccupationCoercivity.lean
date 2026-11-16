/- GID: D5/S3/Arith/Robin/PriceRecord/ActualIntegerOccupationCoercivity
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualIntegerOccupationCoercivity
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Uniform quantitative second-layer occupation coercivity for all positive integers. -/

import D5.S3.Arith.GoldenLocalThreshold
import D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel

/-! Uniform occupation coercivity from the exact unrestricted integer pressure.
The common-support charge pays each selected local loss once. Uniform moving
margins and the global prime-number-theorem error control the boundary window;
a clipped optimization retains the finite-clock remainder at zero defect. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity

open Finset Real Filter Asymptotics
open scoped Topology
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenLayerMarginalDecay
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResourceSupremum
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel

-- Bind the existing owner increment; only the product order is normalized.
private lemma local_step {p : ℕ} (hp : p.Prime) (lam : ℝ) (a : ℕ) :
    goldenPrimeLocalObjective lam p (a + 1) - goldenPrimeLocalObjective lam p a =
      log p * (goldenLayerMarginal p (a + 1) - lam) := by
  simpa only [mul_comm] using
    (D5.S3.Arith.GoldenLocalThreshold.golden_prime_local_objective_diff hp lam a)

-- Reuse the strict-count interval and the existing local maximum theorem.
lemma count_maximal {lam : ℝ} (hlam : 0 < lam) {p : ℕ} (hp : p.Prime)
    (a : ℕ) :
    goldenPrimeLocalObjective lam p a ≤
      goldenPrimeLocalObjective lam p (optimalLayerCount lam p) := by
  have hinterval := positive_layers_eq_count_interval hlam hp
  have hu : goldenLayerMarginal p (optimalLayerCount lam p + 1) ≤ lam := by
    apply le_of_not_gt
    intro hg
    have hm : optimalLayerCount lam p + 1 ∈
        {k : ℕ | 1 ≤ k ∧ p.Prime ∧ lam < goldenLayerMarginal p k} :=
      ⟨by omega, hp, hg⟩
    rw [hinterval] at hm
    exact Nat.not_succ_le_self _ hm.2
  have hl : optimalLayerCount lam p = 0 ∨
      lam ≤ goldenLayerMarginal p (optimalLayerCount lam p) := by
    by_cases h : optimalLayerCount lam p = 0
    · exact Or.inl h
    · right
      have hm : optimalLayerCount lam p ∈ Set.Icc 1 (optimalLayerCount lam p) :=
        ⟨by omega, le_rfl⟩
      rw [← hinterval] at hm
      exact hm.2.2.le
  exact golden_prime_local_objective_maximal_of_threshold hp lam hu hl a

-- A hole pays layer 2 even when its exponent is ZERO.
private lemma hole_loss {lam : ℝ} (hlam : 0 < lam) {p a : ℕ} (hp : p.Prime)
    (ha : a ≤ 1) (hg : lam ≤ goldenLayerMarginal p 2) :
    log p * (goldenLayerMarginal p 2 - lam) ≤
      goldenPrimeLocalObjective lam p (optimalLayerCount lam p) -
        goldenPrimeLocalObjective lam p a := by
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have h01 : goldenPrimeLocalObjective lam p 0 ≤ goldenPrimeLocalObjective lam p 1 := by
    have hm : lam ≤ goldenLayerMarginal p 1 :=
      hg.trans (golden_layer_strict_decrease hp (by norm_num) (by norm_num)).le
    have hs := local_step hp lam 0
    norm_num only [zero_add] at hs
    nlinarith [mul_nonneg hlp.le (sub_nonneg.mpr hm)]
  have ha1 : goldenPrimeLocalObjective lam p a ≤ goldenPrimeLocalObjective lam p 1 := by
    interval_cases a
    · exact h01
    · exact le_rfl
  have h2 := count_maximal hlam hp 2
  have hs := local_step hp lam 1
  norm_num only at hs
  linarith

-- An excess pays layer 2; arbitrarily many later layers only add loss.
private lemma excess_loss {lam : ℝ} (hlam : 0 < lam) {p a : ℕ} (hp : p.Prime)
    (ha : 2 ≤ a) (hg : goldenLayerMarginal p 2 ≤ lam) :
    log p * (lam - goldenLayerMarginal p 2) ≤
      goldenPrimeLocalObjective lam p (optimalLayerCount lam p) -
        goldenPrimeLocalObjective lam p a := by
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hdown : AntitoneOn (goldenPrimeLocalObjective lam p) (Set.Ici 1) := by
    apply antitoneOn_of_add_one_le Set.ordConnected_Ici
    intro k _ hk _
    change 1 ≤ k at hk
    have hm : goldenLayerMarginal p (k + 1) ≤ lam := by
      rcases eq_or_lt_of_le (show 2 ≤ k + 1 by omega) with heq | hlt
      · simpa only [← heq] using hg
      · exact (golden_layer_strict_decrease hp (by norm_num) hlt).le.trans hg
    have hs := local_step hp lam k
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hlp.le (sub_nonpos.mpr hm)]
  have ha2 : goldenPrimeLocalObjective lam p a ≤ goldenPrimeLocalObjective lam p 2 :=
    hdown (by norm_num) (by change 1 ≤ a; omega) ha
  have h1 := count_maximal hlam hp 1
  have hs := local_step hp lam 1
  norm_num only at hs
  nlinarith

/-- The SAME actual unrestricted defect pays the complete local optimality
loss on any finite set of genuine primes. Missing primes and primes beyond z
are both allowed. No harmonic-reference reserve enters this inequality. -/
lemma actual_local_gap_sum_le_defect {z : ℝ} (hz : 1 < z) {n : ℕ} (hn : 1 ≤ n)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ p ∈ S, (goldenPrimeLocalObjective (referencePrice z) p
        (optimalLayerCount (referencePrice z) p) -
      goldenPrimeLocalObjective (referencePrice z) p (n.factorization p))) ≤
        actualDefect z n := by
  classical
  have hlam : 0 < referencePrice z :=
    one_div_pos.mpr (mul_pos (by linarith) (log_pos hz))
  obtain ⟨U, hU, hc, _, _⟩ := optimal_layer_count_spec hlam
  let T := (U.primeFactors ∪ n.primeFactors) ∪ S
  have hUT : U.primeFactors ⊆ T := by
    intro p hp; simp only [T, mem_union]; tauto
  have hnT : n.primeFactors ⊆ T := by
    intro p hp; simp only [T, mem_union]; tauto
  have hST : S ⊆ T := subset_union_right
  have hprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · rcases mem_union.mp hp with hp | hp
      · exact Nat.prime_of_mem_primeFactors hp
      · exact Nat.prime_of_mem_primeFactors hp
    · exact hS p hp
  have hpressure : actualPressure z = goldenResourceObjective (referencePrice z) U := by
    unfold actualPressure
    rw [golden_resource_supremum_eq_positive_part_sum hlam,
      ← objective_at_optimal_eq_positive_part_sum hlam hU hc]
  have hsum : actualDefect z n = ∑ p ∈ T,
      (goldenPrimeLocalObjective (referencePrice z) p
          (optimalLayerCount (referencePrice z) p) -
        goldenPrimeLocalObjective (referencePrice z) p (n.factorization p)) := by
    unfold actualDefect
    rw [hpressure, golden_resource_objective_sum_on (referencePrice z) hU T hUT,
      golden_resource_objective_sum_on (referencePrice z) hn T hnT, sum_sub_distrib]
    simp_rw [hc]
  rw [hsum]
  exact sum_le_sum_of_subset_of_nonneg hST (fun p hp _ =>
    sub_nonneg.mpr (count_maximal hlam (hprime p hp) _))

-- The SAME unrestricted pressure pays weighted positive-part local losses.
-- The common support includes missing primes through H and p > z through X.
private lemma common_support_charge {z : ℝ} (hz : 1 < z) {n : ℕ} (hn : 1 ≤ n)
    (H X : Finset ℕ) (hdisj : Disjoint H X)
    (hH : ∀ p ∈ H, p.Prime ∧ n.factorization p ≤ 1)
    (hX : ∀ p ∈ X, p.Prime ∧ 2 ≤ n.factorization p) :
    (∑ p ∈ H, max (log p * (goldenLayerMarginal p 2 - referencePrice z)) 0) +
      (∑ p ∈ X, max (log p * (referencePrice z - goldenLayerMarginal p 2)) 0) ≤
        actualDefect z n := by
  classical
  have hlam : 0 < referencePrice z :=
    one_div_pos.mpr (mul_pos (by linarith) (log_pos hz))
  let gap : ℕ → ℝ := fun p =>
    goldenPrimeLocalObjective (referencePrice z) p
        (optimalLayerCount (referencePrice z) p) -
      goldenPrimeLocalObjective (referencePrice z) p (n.factorization p)
  have hprime : ∀ p ∈ H ∪ X, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact (hH p hp).1
    · exact (hX p hp).1
  have hgap0 : ∀ p ∈ H ∪ X, 0 ≤ gap p := by
    intro p hp
    exact sub_nonneg.mpr (count_maximal hlam (hprime p hp) _)
  have hh : ∀ p ∈ H,
      max (log p * (goldenLayerMarginal p 2 - referencePrice z)) 0 ≤ gap p := by
    intro p hp
    have hpS := mem_union_left X hp
    have hlp : 0 ≤ log (p : ℝ) := log_natCast_nonneg p
    apply max_le _ (hgap0 p hpS)
    by_cases hg : referencePrice z ≤ goldenLayerMarginal p 2
    · dsimp only [gap]
      exact hole_loss hlam (hH p hp).1 (hH p hp).2 hg
    · exact (mul_nonpos_of_nonneg_of_nonpos hlp
        (sub_nonpos.mpr (le_of_not_ge hg))).trans (hgap0 p hpS)
  have hx : ∀ p ∈ X,
      max (log p * (referencePrice z - goldenLayerMarginal p 2)) 0 ≤ gap p := by
    intro p hp
    have hpS := mem_union_right H hp
    have hlp : 0 ≤ log (p : ℝ) := log_natCast_nonneg p
    apply max_le _ (hgap0 p hpS)
    by_cases hg : goldenLayerMarginal p 2 ≤ referencePrice z
    · dsimp only [gap]
      exact excess_loss hlam (hX p hp).1 (hX p hp).2 hg
    · exact (mul_nonpos_of_nonneg_of_nonpos hlp
        (sub_nonpos.mpr (le_of_not_ge hg))).trans (hgap0 p hpS)
  calc
    _ ≤ (∑ p ∈ H, gap p) + ∑ p ∈ X, gap p :=
      add_le_add (sum_le_sum hh) (sum_le_sum hx)
    _ = ∑ p ∈ H ∪ X, gap p := (sum_union hdisj).symm
    _ ≤ actualDefect z n := actual_local_gap_sum_le_defect hz hn (H ∪ X) hprime

-- The old constant-margin estimate is a consumer of the weighted core.
private lemma constant_margin_charge {z : ℝ} (hz : 1 < z) {n : ℕ} (hn : 1 ≤ n)
    (H X : Finset ℕ) (hdisj : Disjoint H X) {ρ : ℝ} (_hρ : 0 ≤ ρ)
    (hH : ∀ p ∈ H, p.Prime ∧ n.factorization p ≤ 1 ∧
      ρ ≤ goldenLayerMarginal p 2 - referencePrice z)
    (hX : ∀ p ∈ X, p.Prime ∧ 2 ≤ n.factorization p ∧
      ρ ≤ referencePrice z - goldenLayerMarginal p 2) :
    ρ * ((∑ p ∈ H, log p) + ∑ p ∈ X, log p) ≤ actualDefect z n := by
  have hcharge := common_support_charge hz hn H X hdisj
    (fun p hp => ⟨(hH p hp).1, (hH p hp).2.1⟩)
    (fun p hp => ⟨(hX p hp).1, (hX p hp).2.1⟩)
  calc
    _ = (∑ p ∈ H, ρ * log p) + ∑ p ∈ X, ρ * log p := by
      rw [← mul_sum, ← mul_sum]; ring
    _ ≤ (∑ p ∈ H, max (log p * (goldenLayerMarginal p 2 - referencePrice z)) 0) +
        ∑ p ∈ X, max (log p * (referencePrice z - goldenLayerMarginal p 2)) 0 := by
      apply add_le_add
      · apply sum_le_sum
        intro p hp
        apply le_trans _ (le_max_left _ _)
        nlinarith [mul_le_mul_of_nonneg_left (hH p hp).2.2 (log_natCast_nonneg p)]
      · apply sum_le_sum
        intro p hp
        apply le_trans _ (le_max_left _ _)
        nlinarith [mul_le_mul_of_nonneg_left (hX p hp).2.2 (log_natCast_nonneg p)]
    _ ≤ _ := hcharge

-- Exact local marginal; its lower bound retains the first finite-clock error.
private lemma second_marginal {p : ℕ} (hp : p.Prime) :
    goldenLayerMarginal p 2 = log (1 + 1 / ((p : ℝ) * (p + 1))) / log p ∧
    1 / (((p : ℝ) ^ 2 + p + 1) * log p) ≤ goldenLayerMarginal p 2 ∧
    goldenLayerMarginal p 2 ≤ 1 / ((p : ℝ) ^ 2 * log p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlp : 0 < log (p : ℝ) := log_pos hp1
  have hi : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp1
  have hd : 1 - (p : ℝ)⁻¹ ^ 2 ≠ 0 :=
    (sub_pos.mpr (pow_lt_one₀ (inv_nonneg.mpr hp0.le) hi (by norm_num))).ne'
  have hratio : (1 - (p : ℝ)⁻¹ ^ 3) / (1 - (p : ℝ)⁻¹ ^ 2) =
      1 + 1 / ((p : ℝ) * (p + 1)) := by
    apply (div_eq_iff hd).mpr
    field_simp [hp0.ne', (show (p : ℝ) + 1 ≠ 0 by positivity)] <;> ring
  have heq : goldenLayerMarginal p 2 =
      log (1 + 1 / ((p : ℝ) * (p + 1))) / log p := by
    unfold goldenLayerMarginal
    change log ((1 - (p : ℝ)⁻¹ ^ 3) / (1 - (p : ℝ)⁻¹ ^ 2)) / log p = _
    rw [hratio]
  refine ⟨heq, ?_, ?_⟩
  · have harg : 0 < 1 + 1 / ((p : ℝ) * (p + 1)) := by positivity
    have hg := Real.one_sub_inv_le_log_of_pos harg
    have hr : 1 - (1 + 1 / ((p : ℝ) * (p + 1)))⁻¹ =
        1 / ((p : ℝ) ^ 2 + p + 1) := by
      field_simp [hp0.ne', harg.ne', (show (p : ℝ) + 1 ≠ 0 by positivity),
        (show (p : ℝ) ^ 2 + p + 1 ≠ 0 by positivity)] <;> ring
    rw [hr] at hg
    rw [heq, ← div_div]
    exact div_le_div_of_nonneg_right hg hlp.le
  · have hu := golden_layer_marginal_le_inv_pow hp (by norm_num : 1 ≤ 2)
    calc
      goldenLayerMarginal p 2 ≤ (p : ℝ)⁻¹ ^ 2 / log p := hu
      _ = 1 / ((p : ℝ) ^ 2 * log p) := by
        rw [inv_pow]
        field_simp [hp0.ne', hlp.ne'] <;> ring

private lemma sqrt_two_bounds :
    (5 / 4 : ℝ) ≤ sqrt 2 ∧ sqrt 2 ≤ 2 ∧ (sqrt 2) ^ 2 = 2 := by
  have h0 := sqrt_nonneg (2 : ℝ)
  have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  constructor
  · nlinarith
  constructor
  · nlinarith
  · exact hs

-- Uniform in eta, including eta = 8/log z; no moving-limit interchange.
set_option maxHeartbeats 800000 in
private lemma far_margins {z η : ℝ} (hz : 1 < z) (hL : 32 ≤ log z)
    (hsmall : sqrt 2 / sqrt z + 1 / z ≤ 1 / log z)
    (hηa : 8 / log z ≤ η) (hηb : η ≤ 1 / 4) :
    (∀ p : ℕ, p.Prime → (p : ℝ) ≤ (sqrt 2 - η) * sqrt z →
      η / (2 * (z * log z)) ≤ goldenLayerMarginal p 2 - referencePrice z) ∧
    (∀ p : ℕ, p.Prime → (sqrt 2 + η) * sqrt z < (p : ℝ) →
      η / (2 * (z * log z)) ≤ referencePrice z - goldenLayerMarginal p 2) := by
  have hz0 : 0 < z := by linarith
  have hr : 0 < sqrt z := sqrt_pos.mpr hz0
  have hr2 : (sqrt z) ^ 2 = z := sq_sqrt hz0.le
  have hl : 0 < log z := log_pos hz
  have hc := sqrt_two_bounds
  have hη : 0 < η := (div_pos (by norm_num) hl).trans_le hηa
  have hηL : 8 ≤ η * log z := (div_le_iff₀ hl).mp hηa
  have hrec : 1 / log z ≤ η / 8 := by
    apply (div_le_iff₀ hl).mpr
    nlinarith
  have herr : sqrt 2 * sqrt z + 1 ≤ z / log z := by
    have ht := mul_le_mul_of_nonneg_right hsmall hz0.le
    have hzdiv : z / sqrt z = sqrt z :=
      (div_eq_iff hr.ne').mpr (by nlinarith [hr2])
    have heq : (sqrt 2 / sqrt z + 1 / z) * z = sqrt 2 * sqrt z + 1 := by
      calc
        _ = sqrt 2 * (z / sqrt z) + 1 := by
          field_simp [hz0.ne', hr.ne'] <;> ring
        _ = _ := by rw [hzdiv]
    rw [heq] at ht
    simpa only [div_mul_eq_mul_div, one_mul] using ht
  have hrecZ := mul_le_mul_of_nonneg_right hrec hz0.le
  have hlogr : log (sqrt z) = log z / 2 := log_sqrt hz0.le
  constructor
  · intro p hp hpt
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
    let t : ℝ := sqrt 2 - η
    change (p : ℝ) ≤ t * sqrt z at hpt
    have ht1 : 1 ≤ t := by dsimp [t]; linarith [hc.1]
    have ht0 : 0 < t := by linarith
    have ht2 : t ≤ 2 := by dsimp [t]; linarith [hc.2.1]
    have htlog : log t ≤ 1 := by
      have h := log_le_sub_one_of_pos ht0
      linarith
    have hlpbound : log (p : ℝ) ≤ log z / 2 + 1 := by
      have hm := log_le_log hp0 hpt
      rw [log_mul ht0.ne' hr.ne', hlogr] at hm
      linarith
    have htSq : t ^ 2 ≤ 2 - 2 * η := by
      have hsqη : η ^ 2 ≤ η / 4 := by
        nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hηb)]
      have hprod := mul_le_mul_of_nonneg_right hc.1 hη.le
      dsimp [t]
      nlinarith [hc.2.2]
    have hpSq : (p : ℝ) ^ 2 ≤ t ^ 2 * z := by
      calc
        (p : ℝ) ^ 2 ≤ (t * sqrt z) ^ 2 := pow_le_pow_left₀ hp0.le hpt 2
        _ = t ^ 2 * z := by rw [mul_pow, hr2]
    have hpc : (p : ℝ) ≤ sqrt 2 * sqrt z := by
      dsimp [t] at hpt
      nlinarith [mul_nonneg hη.le hr.le]
    have hpoly : (p : ℝ) ^ 2 + p + 1 ≤ (2 - 15 * η / 8) * z := by
      have htZ := mul_le_mul_of_nonneg_right htSq hz0.le
      have hrecZ' : z / log z ≤ η * z / 8 := by
        convert hrecZ using 1 <;> ring
      calc
        (p : ℝ) ^ 2 + p + 1 ≤ t ^ 2 * z + (sqrt 2 * sqrt z + 1) := by
          linarith only [hpSq, hpc]
        _ ≤ (2 - 2 * η) * z + z / log z := add_le_add htZ herr
        _ ≤ (2 - 2 * η) * z + η * z / 8 := add_le_add le_rfl hrecZ'
        _ = _ := by ring
    have hlogscaled : log (p : ℝ) ≤ (1 / 2 + η / 8) * log z := by
      nlinarith
    have hfactor0 : 0 ≤ 2 - 15 * η / 8 := by linarith
    have hfactor : (2 - 15 * η / 8) * (1 / 2 + η / 8) ≤ 1 - η / 2 := by
      nlinarith [sq_nonneg η]
    have hden : ((p : ℝ) ^ 2 + p + 1) * log p ≤ (1 - η / 2) * (z * log z) := by
      calc
        ((p : ℝ) ^ 2 + p + 1) * log p ≤
            ((2 - 15 * η / 8) * z) * ((1 / 2 + η / 8) * log z) :=
          mul_le_mul hpoly hlogscaled hlp.le (mul_nonneg hfactor0 hz0.le)
        _ = ((2 - 15 * η / 8) * (1 / 2 + η / 8)) * (z * log z) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (mul_pos hz0 hl).le
    have hden0 : 0 < ((p : ℝ) ^ 2 + p + 1) * log p := by positivity
    have hcomp : (1 + η / 2) * (((p : ℝ) ^ 2 + p + 1) * log p) ≤ z * log z := by
      calc
        _ ≤ (1 + η / 2) * ((1 - η / 2) * (z * log z)) :=
          mul_le_mul_of_nonneg_left hden (by linarith)
        _ = (1 - η ^ 2 / 4) * (z * log z) := by ring
        _ ≤ _ := mul_le_of_le_one_left (mul_pos hz0 hl).le (by nlinarith [sq_nonneg η])
    have hinv : (1 + η / 2) / (z * log z) ≤
        1 / (((p : ℝ) ^ 2 + p + 1) * log p) := by
      apply (div_le_div_iff₀ (mul_pos hz0 hl) hden0).mpr
      simpa only [one_mul] using hcomp
    have hmargin := hinv.trans (second_marginal hp).2.1
    have heq : (1 + η / 2) / (z * log z) = referencePrice z + η / (2 * (z * log z)) := by
      unfold referencePrice
      field_simp [hz0.ne', hl.ne'] <;> ring
    rw [heq] at hmargin
    linarith
  · intro p hp hpt
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
    let t : ℝ := sqrt 2 + η
    change t * sqrt z < (p : ℝ) at hpt
    have ht1 : 1 ≤ t := by dsimp [t]; linarith [hc.1]
    have ht0 : 0 < t := by linarith
    have ht2 : t ≤ 2 := by dsimp [t]; nlinarith [hc.2.2, hc.1]
    have hpr : sqrt z ≤ (p : ℝ) := by
      calc
        sqrt z = 1 * sqrt z := by ring
        _ ≤ t * sqrt z := mul_le_mul_of_nonneg_right ht1 hr.le
        _ ≤ (p : ℝ) := hpt.le
    have hlpbound : log z / 2 ≤ log (p : ℝ) := by
      rw [← hlogr]
      exact log_le_log hr hpr
    have htp : t ^ 2 * z ≤ (p : ℝ) ^ 2 := by
      calc
        t ^ 2 * z = (t * sqrt z) ^ 2 := by rw [mul_pow, hr2]
        _ ≤ (p : ℝ) ^ 2 := pow_le_pow_left₀ (mul_pos ht0 hr).le hpt.le 2
    have htSq : t ^ 2 ≤ 4 := by
      calc
        t ^ 2 ≤ (2 : ℝ) ^ 2 := pow_le_pow_left₀ ht0.le ht2 2
        _ = 4 := by norm_num
    have htSqLower : 2 + 5 * η / 2 ≤ t ^ 2 := by
      have hprod := mul_le_mul_of_nonneg_right hc.1 hη.le
      dsimp [t]
      nlinarith [hc.2.2, sq_nonneg η]
    have hfactor : 2 ≤ (1 - η / 2) * t ^ 2 := by
      have hm := mul_le_mul_of_nonneg_left htSq (show 0 ≤ η / 2 by positivity)
      nlinarith
    have hden : t ^ 2 * (z * log z) / 2 ≤ (p : ℝ) ^ 2 * log p := by
      have h := mul_le_mul htp hlpbound (by positivity : 0 ≤ log z / 2)
        (sq_nonneg (p : ℝ))
      nlinarith
    have hweighted : z * log z ≤
        (1 - η / 2) * ((p : ℝ) ^ 2 * log p) := by
      have hm := mul_le_mul_of_nonneg_left hden (show 0 ≤ 1 - η / 2 by linarith)
      have hf := mul_le_mul_of_nonneg_right hfactor (mul_pos hz0 hl).le
      nlinarith
    have hinv : 1 / ((p : ℝ) ^ 2 * log p) ≤ (1 - η / 2) / (z * log z) := by
      apply (div_le_div_iff₀ (mul_pos (pow_pos hp0 2) hlp) (mul_pos hz0 hl)).mpr
      simpa only [one_mul] using hweighted
    have hmargin := (second_marginal hp).2.2.trans hinv
    have heq : (1 - η / 2) / (z * log z) = referencePrice z - η / (2 * (z * log z)) := by
      unfold referencePrice
      field_simp [hz0.ne', hl.ne'] <;> ring
    rw [heq] at hmargin
    linarith

-- Finite arbitrary submasks of a literal real-endpoint prime interval.
private lemma sum_log_interval {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ A < (p : ℝ) ∧ (p : ℝ) ≤ B) :
    (∑ p ∈ P, log p) ≤ Chebyshev.theta B - Chebyshev.theta A := by
  classical
  have hsub : Nat.primesLE ⌊A⌋₊ ⊆ Nat.primesLE ⌊B⌋₊ := by
    intro p hp
    obtain ⟨hpA, hpp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (hA.trans hAB)).mpr
      (((Nat.le_floor_iff hA).mp hpA).trans hAB), hpp⟩
  have hPS : P ⊆ Nat.primesLE ⌊B⌋₊ \ Nat.primesLE ⌊A⌋₊ := by
    intro p hp
    obtain ⟨hpp, hAp, hpB⟩ := hP p hp
    refine mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr
      ⟨(Nat.le_floor_iff (hA.trans hAB)).mpr hpB, hpp⟩, ?_⟩
    intro hpA
    exact (not_le_of_gt hAp) ((Nat.le_floor_iff hA).mp (Nat.mem_primesLE.mp hpA).1)
  calc
    (∑ p ∈ P, log p) ≤
        ∑ p ∈ Nat.primesLE ⌊B⌋₊ \ Nat.primesLE ⌊A⌋₊, log p :=
      sum_le_sum_of_subset_of_nonneg hPS (fun p _ _ => log_natCast_nonneg p)
    _ = Chebyshev.theta B - Chebyshev.theta A := by
      rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE,
        ← sum_sdiff hsub]
      ring

-- A global PNT bound at BOTH real endpoints supplies the entire boundary window.
private lemma theta_window {T z η : ℝ} (hz : 1 < z) (hL : 32 ≤ log z)
    (hT : T ≤ sqrt z)
    (hθ : ∀ y : ℝ, T ≤ y → |Chebyshev.theta y - y| ≤ y / log y ^ 2)
    (hηa : 8 / log z ≤ η) (hηb : η ≤ 1 / 4) :
    Chebyshev.theta ((sqrt 2 + η) * sqrt z) -
        Chebyshev.theta ((sqrt 2 - η) * sqrt z) ≤ 4 * η * sqrt z := by
  have hl : 0 < log z := log_pos hz
  have hr : 0 < sqrt z := sqrt_pos.mpr (by linarith)
  have hc := sqrt_two_bounds
  have hη : 0 < η := (div_pos (by norm_num) hl).trans_le hηa
  let A := (sqrt 2 - η) * sqrt z
  let B := (sqrt 2 + η) * sqrt z
  have hrA : sqrt z ≤ A := by
    have hcoef : 1 ≤ sqrt 2 - η := by linarith [hc.1]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef hr.le
  have hrB : sqrt z ≤ B := by
    have hcoef : 1 ≤ sqrt 2 + η := by linarith [hc.1]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef hr.le
  have hA0 : 0 < A := hr.trans_le hrA
  have hB0 : 0 < B := hr.trans_le hrB
  have hlogA : log z / 2 ≤ log A := by
    have h := log_le_log hr hrA
    rwa [log_sqrt (by linarith : 0 ≤ z)] at h
  have hlogB : log z / 2 ≤ log B := by
    have h := log_le_log hr hrB
    rwa [log_sqrt (by linarith : 0 ≤ z)] at h
  have herror (y : ℝ) (hy : 0 < y) (hly : log z / 2 ≤ log y) :
      y / log y ^ 2 ≤ 4 * y / log z ^ 2 := by
    have hly0 : 0 < log y := by linarith
    apply (div_le_div_iff₀ (pow_pos hly0 2) (pow_pos hl 2)).mpr
    have hs : log z ^ 2 ≤ 4 * log y ^ 2 := by
      have hm := pow_le_pow_left₀ (by positivity : 0 ≤ log z / 2) hly 2
      nlinarith only [hm]
    nlinarith [mul_le_mul_of_nonneg_right hs hy.le]
  have ha := (hθ A (hT.trans hrA))
  have hb := (hθ B (hT.trans hrB))
  have ha' : A - 4 * A / log z ^ 2 ≤ Chebyshev.theta A := by
    have he := herror A hA0 hlogA
    linarith [(abs_le.mp ha).1]
  have hb' : Chebyshev.theta B ≤ B + 4 * B / log z ^ 2 := by
    have he := herror B hB0 hlogB
    linarith [(abs_le.mp hb).2]
  have hηL : 8 ≤ η * log z := (div_le_iff₀ hl).mp hηa
  have hsmall : 8 * sqrt 2 / log z ^ 2 ≤ 2 * η := by
    apply (div_le_iff₀ (pow_pos hl 2)).mpr
    have hm := mul_le_mul_of_nonneg_right hηL hl.le
    nlinarith [hc.2.1]
  have hrem : 4 * A / log z ^ 2 + 4 * B / log z ^ 2 ≤ 2 * η * sqrt z := by
    have heq : 4 * A / log z ^ 2 + 4 * B / log z ^ 2 =
        (8 * sqrt 2 / log z ^ 2) * sqrt z := by dsimp [A, B]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hsmall hr.le
  have hwidth : B - A = 2 * η * sqrt z := by dsimp [A, B]; ring
  change Chebyshev.theta B - Chebyshev.theta A ≤ _
  linarith

-- The z threshold is existential, determined only by global asymptotic bounds.
private lemma eventual_geometry :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ 32 ≤ log z ∧
      sqrt 2 / sqrt z + 1 / z ≤ 1 / log z ∧
      ∀ η : ℝ, 8 / log z ≤ η → η ≤ 1 / 4 →
        Chebyshev.theta ((sqrt 2 + η) * sqrt z) -
          Chebyshev.theta ((sqrt 2 - η) * sqrt z) ≤ 4 * η * sqrt z := by
  have hθev : ∀ᶠ y : ℝ in atTop,
      |Chebyshev.theta y - y| ≤ y / log y ^ 2 := by
    filter_upwards [(theta_error_log_power 2).bound (by norm_num : (0 : ℝ) < 1),
      eventually_ge_atTop (2 : ℝ)] with y hy hy2
    have hy0 : 0 ≤ y / log y ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
    simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg hy0] using hy
  obtain ⟨T, hT⟩ := eventually_atTop.mp hθev
  have hh : Tendsto (fun z : ℝ => log z / sqrt z) atTop (𝓝 0) := by
    simpa only [pow_one, rpow_one, ← sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop 1 (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have ho : Tendsto (fun z : ℝ => log z / z) atTop (𝓝 0) := by
    simpa only [pow_one, rpow_one] using
      (isLittleO_log_rpow_rpow_atTop 1 (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hsum : Tendsto (fun z : ℝ => sqrt 2 * (log z / sqrt z) + log z / z)
      atTop (𝓝 0) := by simpa using (hh.const_mul (sqrt 2)).add ho
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    tendsto_log_atTop.eventually_ge_atTop (32 : ℝ),
    tendsto_sqrt_atTop.eventually_ge_atTop T,
    hsum.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with z hz hL hr hsmall
  refine ⟨hz, hL, ?_, fun η ha hb => theta_window hz hL hr hT ha hb⟩
  apply (le_div_iff₀ (log_pos hz)).mpr
  have heq : (sqrt 2 / sqrt z + 1 / z) * log z =
      sqrt 2 * (log z / sqrt z) + log z / z := by ring
  rw [heq]
  exact hsmall.le

-- Literal sums only: H/X here are arbitrary finite masks, not new global owners.
private lemma fixed_eta_bound {z η : ℝ} (hz : 1 < z) (hL : 32 ≤ log z)
    (hsmall : sqrt 2 / sqrt z + 1 / z ≤ 1 / log z)
    (hwindow : Chebyshev.theta ((sqrt 2 + η) * sqrt z) -
      Chebyshev.theta ((sqrt 2 - η) * sqrt z) ≤ 4 * η * sqrt z)
    (hηa : 8 / log z ≤ η) (hηb : η ≤ 1 / 4)
    {n : ℕ} (hn : 1 ≤ n) (H X : Finset ℕ)
    (hH : ∀ p ∈ H, p.Prime ∧ (p : ℝ) ≤ sqrt 2 * sqrt z ∧ n.factorization p ≤ 1)
    (hX : ∀ p ∈ X, p.Prime ∧ sqrt 2 * sqrt z < (p : ℝ) ∧ 2 ≤ n.factorization p) :
    ((∑ p ∈ H, log p) + ∑ p ∈ X, log p) / sqrt z ≤
      4 * η + 2 * (sqrt z * log z * actualDefect z n) / η := by
  classical
  let A := (sqrt 2 - η) * sqrt z
  let B := (sqrt 2 + η) * sqrt z
  let Hf := H.filter (fun p : ℕ => (p : ℝ) ≤ A)
  let Xf := X.filter (fun p : ℕ => B < (p : ℝ))
  let Hc := H \ Hf
  let Xc := X \ Xf
  have hr : 0 < sqrt z := sqrt_pos.mpr (by linarith)
  have hl : 0 < log z := log_pos hz
  have hz0 : 0 < z := by linarith
  have hη : 0 < η := (div_pos (by norm_num) hl).trans_le hηa
  have hdisj : Disjoint H X := by
    apply disjoint_left.mpr
    intro p hpH hpX
    exact (not_lt_of_ge (hH p hpH).2.1) (hX p hpX).2.1
  have hff : Disjoint Hf Xf :=
    hdisj.mono (filter_subset _ _) (filter_subset _ _)
  have hcc : Disjoint Hc Xc :=
    hdisj.mono sdiff_subset sdiff_subset
  have hfar := far_margins hz hL hsmall hηa hηb
  have hcharge := constant_margin_charge hz hn Hf Xf hff
    (ρ := η / (2 * (z * log z))) (by positivity)
    (by
      intro p hp
      obtain ⟨hpH, hpA⟩ := mem_filter.mp hp
      exact ⟨(hH p hpH).1, (hH p hpH).2.2, hfar.1 p (hH p hpH).1 hpA⟩)
    (by
      intro p hp
      obtain ⟨hpX, hBp⟩ := mem_filter.mp hp
      exact ⟨(hX p hpX).1, (hX p hpX).2.2, hfar.2 p (hX p hpX).1 hBp⟩)
  have hA0 : 0 ≤ A := by
    have hc := sqrt_two_bounds
    dsimp [A]
    exact mul_nonneg (by linarith [hc.1]) hr.le
  have hAB : A ≤ B :=
    mul_le_mul_of_nonneg_right (show sqrt 2 - η ≤ sqrt 2 + η by linarith) hr.le
  have hnear : (∑ p ∈ Hc, log p) + ∑ p ∈ Xc, log p ≤ 4 * η * sqrt z := by
    rw [← sum_union hcc]
    apply (sum_log_interval hA0 hAB (Hc ∪ Xc) ?_).trans hwindow
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · obtain ⟨hpH, hpf⟩ := mem_sdiff.mp hp
      have hAp : A < (p : ℝ) := by
        by_contra h
        exact hpf (mem_filter.mpr ⟨hpH, le_of_not_gt h⟩)
      refine ⟨(hH p hpH).1, hAp, ?_⟩
      have hpc := (hH p hpH).2.1
      dsimp [B]
      nlinarith [mul_nonneg hη.le hr.le]
    · obtain ⟨hpX, hpf⟩ := mem_sdiff.mp hp
      have hpB : (p : ℝ) ≤ B := by
        by_contra h
        exact hpf (mem_filter.mpr ⟨hpX, lt_of_not_ge h⟩)
      refine ⟨(hX p hpX).1, ?_, hpB⟩
      have hcp := (hX p hpX).2.1
      dsimp [A]
      nlinarith [mul_nonneg hη.le hr.le]
  have hsplit : ((∑ p ∈ H, log p) + ∑ p ∈ X, log p) =
      ((∑ p ∈ Hf, log p) + ∑ p ∈ Xf, log p) +
        ((∑ p ∈ Hc, log p) + ∑ p ∈ Xc, log p) := by
    have hh : (∑ p ∈ H \ Hf, log p) + (∑ p ∈ Hf, log p) = ∑ p ∈ H, log p :=
      sum_sdiff (filter_subset _ _)
    have hx : (∑ p ∈ X \ Xf, log p) + (∑ p ∈ Xf, log p) = ∑ p ∈ X, log p :=
      sum_sdiff (filter_subset _ _)
    change (∑ p ∈ Hc, log p) + (∑ p ∈ Hf, log p) = _ at hh
    change (∑ p ∈ Xc, log p) + (∑ p ∈ Xf, log p) = _ at hx
    linarith
  have hcharge' : η * ((∑ p ∈ Hf, log p) + ∑ p ∈ Xf, log p) ≤
      2 * (z * log z) * actualDefect z n := by
    have hc : η * ((∑ p ∈ Hf, log p) + ∑ p ∈ Xf, log p) /
        (2 * (z * log z)) ≤ actualDefect z n := by
      convert hcharge using 1 <;> ring
    have hc' := (div_le_iff₀ (show 0 < 2 * (z * log z) by positivity)).mp hc
    nlinarith only [hc']
  have hscale : 2 * (z * log z) * actualDefect z n =
      2 * (sqrt z * log z * actualDefect z n) * sqrt z := by
    calc
      _ = 2 * ((sqrt z) ^ 2 * log z) * actualDefect z n := by rw [sq_sqrt hz0.le]
      _ = _ := by ring
  rw [hscale] at hcharge'
  have hfarSum : ((∑ p ∈ Hf, log p) + ∑ p ∈ Xf, log p) ≤
      2 * (sqrt z * log z * actualDefect z n) * sqrt z / η := by
    apply (le_div_iff₀ hη).mpr
    nlinarith only [hcharge']
  apply (div_le_iff₀ hr).mpr
  rw [hsplit]
  calc
    _ ≤ 2 * (sqrt z * log z * actualDefect z n) * sqrt z / η + 4 * η * sqrt z :=
      add_le_add hfarSum hnear
    _ = _ := by ring

-- At d=0 use eta=8/L, which stays strictly positive; never divide by sqrt d.
private lemma clipped_optimization {b d L : ℝ} (hL : 32 ≤ L) (hd : 0 ≤ d)
    (hfamily : ∀ η : ℝ, 8 / L ≤ η → η ≤ 1 / 4 → b ≤ 4 * η + 2 * d / η) :
    b ≤ 6 * sqrt d + 8 * d + 32 / L := by
  have hL0 : 0 < L := by linarith
  have ha : 0 < 8 / L := by positivity
  have ha4 : 8 / L ≤ 1 / 4 := by apply (div_le_iff₀ hL0).mpr; linarith
  have hs : 0 ≤ sqrt d := sqrt_nonneg d
  have hs2 : (sqrt d) ^ 2 = d := sq_sqrt hd
  by_cases hsmall : sqrt d ≤ 1 / 4
  · let η := max (8 / L) (sqrt d)
    have hηa : 8 / L ≤ η := le_max_left _ _
    have hηb : η ≤ 1 / 4 := max_le ha4 hsmall
    have hη0 : 0 < η := ha.trans_le hηa
    have hsη : sqrt d ≤ η := le_max_right _ _
    have hηsum : η ≤ 8 / L + sqrt d := by
      apply max_le <;> linarith
    have hquot : 2 * d / η ≤ 2 * sqrt d := by
      apply (div_le_iff₀ hη0).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hsη) hs]
    have hb := hfamily η hηa hηb
    have hid : 4 * (8 / L) = 32 / L := by ring
    nlinarith
  · have hb := hfamily (1 / 4) ha4 le_rfl
    have hlarge : 1 / 4 < sqrt d := lt_of_not_ge hsmall
    have hb' : b ≤ 1 + 8 * d := by convert hb using 1 <;> ring
    have hrem : 0 ≤ 32 / L := by positivity
    nlinarith

/-- Uniform quantitative occupation coercivity for arbitrary finite actual masks.
The positive integer is unrestricted; X has no upper support cutoff. -/
theorem eventually_quantitative_actual_occupation_defect :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z : ℝ, Z ≤ z → ∀ n : ℕ, 1 ≤ n →
      ∀ H X : Finset ℕ,
      (∀ p ∈ H, p.Prime ∧ (p : ℝ) ≤ sqrt 2 * sqrt z ∧ n.factorization p ≤ 1) →
      (∀ p ∈ X, p.Prime ∧ sqrt 2 * sqrt z < (p : ℝ) ∧ 2 ≤ n.factorization p) →
      ((∑ p ∈ H, log p) + ∑ p ∈ X, log p) / sqrt z ≤
        6 * sqrt (sqrt z * log z * actualDefect z n) +
          8 * (sqrt z * log z * actualDefect z n) + 32 / log z := by
  classical
  obtain ⟨Z₀, hZ₀⟩ := eventually_atTop.mp eventual_geometry
  refine ⟨max 2 Z₀, le_max_left _ _, ?_⟩
  intro z hz n hn H X hH hX
  obtain ⟨hz1, hL, hsmall, hwindow⟩ := hZ₀ z ((le_max_right _ _).trans hz)
  have hdef : 0 ≤ actualDefect z n := by
    have h := actual_reserve_prime_mask hz1 (∅ : Finset ℕ)
      (by intro p hp; simp at hp) hn
    exact h.2.2.1
  have hd : 0 ≤ sqrt z * log z * actualDefect z n :=
    mul_nonneg (mul_nonneg (sqrt_nonneg z) (log_pos hz1).le) hdef
  apply clipped_optimization hL hd
  intro η hηa hηb
  exact fixed_eta_bound hz1 hL hsmall (hwindow η hηa hηb) hηa hηb hn H X hH hX

end D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity

end
