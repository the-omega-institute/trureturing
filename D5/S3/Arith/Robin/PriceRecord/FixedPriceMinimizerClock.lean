/- GID: D5/S3/Arith/Robin/PriceRecord/FixedPriceMinimizerClock
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FixedPriceMinimizerClock
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: A uniform clock limit for supported integer Robin minimizers at moving fixed prices. -/

import D5.S3.Arith.Robin.PriceRecord.FixedLayerFiniteActivation
import D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
import D5.S3.Arith.Robin.PriceRecord.RealInfimumPrimeBoundary
import D5.S3.Arith.Robin.PriceRecord.IntegerInfimumSecondOrder
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The clock of a fixed-price integer Robin minimizer

Coordinate updates yield weak optimality inequalities on both sides of an active
layer. The second layer gives the leading clock by the prime number theorem.
A common reciprocal-price bound controls the sum of all higher layers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.FixedPriceMinimizerClock

open Filter Finset Real
open scoped BigOperators Topology Chebyshev
open FixedSupportIntegerActivationEnvelope (supportedAdmissible linearCost clockIncrement eulerTerm)
open FixedLayerFiniteActivation (localCost layerGain layerGain_eq_eulerTerm_sub)
open HigherLayerLogSlope (gain beta beta_nat beta_strictAntiOn gain_le_inv_pow
  powerSum powerSum_succ)
open HigherLayerClampedCutoff (cutoff_occupancy)
open RealInfimumPrimeBoundary
  (prefixH prefixEll prefixPrice prefix_H_ratio prefixH_atTop prefixEll_atTop)
open IntegerInfimumSecondOrder (log_pow_over_H_rpow)
open D5.S3.Arith.GoldenResourceOptimalInteger
  (goldenLayerMarginal golden_layer_strict_decrease)

/-- The literal fixed-price minimum condition on supported exponent vectors. -/
def IsMinimizer (S : Finset ℕ) (lam : ℝ) (a : ℕ → ℕ) : Prop :=
  supportedAdmissible S a ∧
    ∀ b : ℕ → ℕ, supportedAdmissible S b → linearCost S lam a ≤ linearCost S lam b

private theorem local_minimal {S : Finset ℕ} {lam : ℝ} {a : ℕ → ℕ}
    (ha : IsMinimizer S lam a) {p : ℕ} (hp : p ∈ S) {k : ℕ} (hk : 1 ≤ k) :
    localCost p (lam * log (p : ℝ)) (a p) ≤ localCost p (lam * log (p : ℝ)) k := by
  classical
  let b := Function.update a p k
  have hb : supportedAdmissible S b := by
    intro q hq
    by_cases he : q = p
    · subst q
      simpa [b] using hk
    · simpa [b, Function.update_of_ne he] using ha.1 q hq
  have hsplit (v : ℕ → ℕ) :
      linearCost S lam v = ∑ q ∈ S, localCost q (lam * log (q : ℝ)) (v q) := by
    unfold linearCost
    apply sum_congr rfl
    intro q _
    unfold localCost
    ring
  have hrest : (∑ q ∈ S.erase p, localCost q (lam * log (q : ℝ)) (b q)) =
      ∑ q ∈ S.erase p, localCost q (lam * log (q : ℝ)) (a q) := by
    apply sum_congr rfl
    intro q hq
    exact congrArg (localCost q (lam * log (q : ℝ)))
      (Function.update_of_ne (mem_erase.mp hq).1 k a)
  have h := ha.2 b hb
  rw [hsplit a, hsplit b,
    ← sum_erase_add S (fun q => localCost q (lam * log (q : ℝ)) (a q)) hp,
    ← sum_erase_add S (fun q => localCost q (lam * log (q : ℝ)) (b q)) hp,
    hrest] at h
  exact le_of_add_le_add_left (by simpa only [b, Function.update_self] using h)

private theorem local_succ_sub {p : ℕ} (hp : p.Prime) (k : ℕ) (lam : ℝ) :
    localCost p (lam * log (p : ℝ)) (k + 1) -
      localCost p (lam * log (p : ℝ)) k =
      (lam - goldenLayerMarginal p (k + 1)) * log (p : ℝ) := by
  have hGain := layerGain_eq_eulerTerm_sub hp (show 1 ≤ k + 1 by omega)
  simp only [layerGain, Nat.add_sub_cancel] at hGain
  unfold localCost
  push_cast
  rw [sub_mul]
  linarith only [hGain]

/-- Included and excluded layers both retain equality at the marginal price. -/
private theorem layer_optimality {S : Finset ℕ} {lam : ℝ} {a : ℕ → ℕ}
    (ha : IsMinimizer S lam a) {p j : ℕ} (hpS : p ∈ S) (hp : p.Prime) (hj : 2 ≤ j) :
    (j ≤ a p → lam ≤ beta j (p : ℝ)) ∧ (a p < j → beta j (p : ℝ) ≤ lam) := by
  rw [beta_nat hp (by omega : 1 ≤ j)]
  constructor
  · intro hja
    have hk : 1 ≤ a p - 1 := by omega
    have hm := local_minimal ha hpS hk
    have hstep := local_succ_sub hp (a p - 1) lam
    rw [show a p - 1 + 1 = a p by omega] at hstep
    have hprod : (lam - goldenLayerMarginal p (a p)) * log (p : ℝ) ≤ 0 := by
      rw [← hstep]
      exact sub_nonpos.mpr hm
    have hlast : lam ≤ goldenLayerMarginal p (a p) :=
      sub_nonpos.mp (nonpos_of_mul_nonpos_left hprod hp.log_pos)
    rcases eq_or_lt_of_le hja with he | hlt
    · simpa only [he] using hlast
    · exact hlast.trans (golden_layer_strict_decrease hp (by omega) hlt).le
  · intro haj
    have hm := local_minimal ha hpS (show 1 ≤ a p + 1 by omega)
    have hprod : 0 ≤ (lam - goldenLayerMarginal p (a p + 1)) * log (p : ℝ) := by
      rw [← local_succ_sub hp (a p) lam]
      exact sub_nonneg.mpr hm
    have hnext : goldenLayerMarginal p (a p + 1) ≤ lam :=
      sub_nonneg.mp (nonneg_of_mul_nonneg_left hprod hp.log_pos)
    rcases eq_or_lt_of_le (show a p + 1 ≤ j by omega) with he | hlt
    · simpa only [he] using hnext
    · exact (golden_layer_strict_decrease hp (by omega) hlt).le.trans hnext

private def headClock (P : ℕ) (a : ℕ → ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE P).filter (fun p => 2 ≤ a p), log (p : ℝ)

private def higherClock (P : ℕ) (a : ℕ → ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE P, ∑ _j ∈ Finset.Ioc 2 (a p), log (p : ℝ)

private theorem clock_split {P : ℕ} {a : ℕ → ℕ} (ha : supportedAdmissible (Nat.primesLE P) a) :
    clockIncrement (Nat.primesLE P) a = headClock P a + higherClock P a := by
  simp only [clockIncrement, headClock, higherClock, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
  by_cases h : 2 ≤ a p
  · simp only [ite_eq_left h, Nat.cast_sub h, Nat.cast_ofNat]
    ring
  · have he : a p = 1 := by
      have ha1 := ha p hp
      omega
    norm_num [he]

private theorem head_bounds {P : ℕ} {lam x y : ℝ} {a : ℕ → ℕ}
    (ha : IsMinimizer (Nat.primesLE P) lam a) (hlam : 0 < lam)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hxP : x ≤ (P : ℝ))
    (hlo : lam < beta 2 x) (hhi : beta 2 y < lam) :
    θ x ≤ headClock P a ∧ headClock P a ≤ θ y := by
  classical
  simp only [Chebyshev.theta_eq_sum_primesLE, headClock]
  constructor
  · apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpx, hprime⟩ := Nat.mem_primesLE.mp hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      have hpxR := (Nat.le_floor_iff (show 0 ≤ x by linarith)).mp hpx
      have hpP : p ≤ P := by exact_mod_cast hpxR.trans hxP
      have hpS := Nat.mem_primesLE.mpr ⟨hpP, hprime⟩
      have hroot := (cutoff_occupancy (by decide : 2 ≤ (2 : ℕ)) hlam hx).mp hlo
      have hprofit := (cutoff_occupancy (by decide : 2 ≤ (2 : ℕ)) hlam hp2).mpr
        (hpxR.trans_lt hroot)
      have htake : 2 ≤ a p := by
        by_contra! hskip
        exact (not_le_of_gt hprofit) ((layer_optimality ha hpS hprime le_rfl).2 hskip)
      exact mem_filter.mpr ⟨hpS, htake⟩
    · intro p hp _
      exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.log_pos.le
  · apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpS, htake⟩ := mem_filter.mp hp
      have hprime := (Nat.mem_primesLE.mp hpS).2
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      have hpy : (p : ℝ) ≤ y := by
        by_contra! hbad
        have hdrop := (beta_strictAntiOn (by decide : 2 ≤ (2 : ℕ)))
          (show y ∈ Set.Ici 2 from hy) (show (p : ℝ) ∈ Set.Ici 2 from hp2) hbad
        have hactive := (layer_optimality ha hpS hprime le_rfl).1 htake
        exact (not_lt_of_ge hactive) (hdrop.trans hhi)
      exact Nat.mem_primesLE.mpr
        ⟨(Nat.le_floor_iff (show 0 ≤ y by linarith)).mpr hpy, hprime⟩
    · intro p hp _
      exact (Nat.mem_primesLE.mp hp).2.log_pos.le

private theorem active_pow_bound {P : ℕ} {lam B : ℝ} {a : ℕ → ℕ}
    (ha : IsMinimizer (Nat.primesLE P) lam a) (hlam : 0 < lam)
    (hB : 1 ≤ lam * log 2 * B) {p j : ℕ} (hpS : p ∈ Nat.primesLE P)
    (hj : 2 ≤ j) (hja : j ≤ a p) : (p : ℝ) ^ j ≤ B := by
  have hp := (Nat.mem_primesLE.mp hpS).2
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hbeta := (layer_optimality ha hpS hp hj).1 hja
  change lam ≤ gain j (p : ℝ) / log (p : ℝ) at hbeta
  have hgain : lam * log (p : ℝ) ≤ gain j (p : ℝ) :=
    (le_div_iff₀ hp.log_pos).mp hbeta
  have hpow : lam * log 2 * (p : ℝ) ^ j ≤ 1 :=
    (le_div_iff₀ (pow_pos hp0 j)).mp
      ((mul_le_mul_of_nonneg_left (log_le_log (by norm_num) hp2) hlam.le).trans
        (hgain.trans (gain_le_inv_pow hp0 (by omega))))
  exact (le_of_mul_le_mul_left (hpow.trans hB) (mul_pos hlam hlog2))

private theorem higher_bounds {P : ℕ} {lam B : ℝ} {a : ℕ → ℕ}
    (ha : IsMinimizer (Nat.primesLE P) lam a) (hlam : 0 < lam)
    (hB1 : 1 ≤ B) (hB : 1 ≤ lam * log 2 * B) :
    0 ≤ higherClock P a ∧ higherClock P a ≤ log B / log 2 * θ (B ^ (1 / 3 : ℝ)) := by
  classical
  have hB0 : 0 ≤ B := by linarith
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  let T := (Nat.primesLE P).filter (fun p => 3 ≤ a p)
  have htop (p : ℕ) (hp : p ∈ T) : (p : ℝ) ^ (a p) ≤ B := by
    obtain ⟨hpS, ha3⟩ := mem_filter.mp hp
    exact active_pow_bound ha hlam hB hpS (by omega) le_rfl
  refine ⟨sum_nonneg (fun p hp => sum_nonneg (fun _ _ => (Nat.mem_primesLE.mp hp).2.log_pos.le)), ?_⟩
  have hfilter : higherClock P a = ∑ p ∈ T, ∑ _j ∈ Finset.Ioc 2 (a p), log (p : ℝ) := by
    dsimp only [T, higherClock]
    rw [sum_filter]
    apply sum_congr rfl
    intro p _
    by_cases hp : 3 ≤ a p
    · rw [ite_eq_left hp]
    · rw [ite_eq_right hp, Ioc_eq_empty_of_le (show a p ≤ 2 by omega), sum_empty]
  have hsub : T ⊆ Nat.primesLE ⌊B ^ (1 / 3 : ℝ)⌋₊ := by
    intro p hp
    obtain ⟨hpS, ha3⟩ := mem_filter.mp hp
    have hpPrime := (Nat.mem_primesLE.mp hpS).2
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_lt.le
    have hpow := (pow_le_pow_right₀ hp1 ha3).trans (htop p hp)
    have hroot := rpow_le_rpow (pow_nonneg (Nat.cast_nonneg p) 3) hpow
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have hcube : ((p : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) = p := by
      rw [one_div]
      exact pow_rpow_inv_natCast (Nat.cast_nonneg p) (by decide : (3 : ℕ) ≠ 0)
    rw [hcube] at hroot
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (rpow_nonneg hB0 _)).mpr hroot, hpPrime⟩
  have hcount (p : ℕ) (hp : p ∈ T) : (a p : ℝ) ≤ log B / log 2 := by
    have hpPrime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
    have hpow := (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hp2 (a p)).trans (htop p hp)
    apply (le_div_iff₀ hlog2).mpr
    rw [← log_pow]
    exact log_le_log (by positivity : 0 < (2 : ℝ) ^ a p) hpow
  rw [hfilter, Chebyshev.theta_eq_sum_primesLE]
  calc
    _ ≤ ∑ p ∈ T, (log B / log 2) * log (p : ℝ) := by
      apply sum_le_sum
      intro p hp
      rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
      have hcard : ((a p - 2 : ℕ) : ℝ) ≤ (a p : ℝ) := by
        exact_mod_cast Nat.sub_le (a p) 2
      exact mul_le_mul_of_nonneg_right (hcard.trans (hcount p hp))
        (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.log_pos.le
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => (Nat.mem_primesLE.mp hp).2.log_pos.le))
        (div_nonneg (log_nonneg hB1) hlog2.le)

private theorem sqrt_prefix_atTop : Tendsto (fun P => sqrt (prefixH P)) atTop atTop :=
  tendsto_sqrt_atTop.comp prefixH_atTop

private theorem normalized_price {lam : ℕ → ℝ}
    (hlam : Tendsto (fun P => lam P / prefixPrice P) atTop (𝓝 1)) :
    Tendsto (fun P => lam P * (prefixH P * log (prefixH P))) atTop (𝓝 1) := by
  simpa only [prefixPrice, D5.S3.Arith.Robin.ActualRobinClockCovariance.g,
    one_div, div_inv_eq_mul] using hlam

private theorem log_two_half : (1 / 2 : ℝ) < log 2 :=
  (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans log_two_gt_d9

/-- An eventually valid majorant for the reciprocal of the price at prime two. -/
private def majorant (P : ℕ) : ℝ := 4 * (prefixH P * log (prefixH P))

private theorem majorant_atTop : Tendsto majorant atTop atTop :=
  (prefixH_atTop.atTop_mul_atTop₀ prefixEll_atTop).const_mul_atTop (by norm_num)

private def higherBound (P : ℕ) : ℝ :=
  log (majorant P) / log 2 * θ (majorant P ^ (1 / 3 : ℝ))

private theorem eventual_price_bounds {lam : ℕ → ℝ}
    (hlam : Tendsto (fun P => lam P / prefixPrice P) atTop (𝓝 1)) :
    ∀ᶠ P : ℕ in atTop, 0 < lam P ∧ 1 ≤ majorant P ∧ 1 ≤ lam P * log 2 * majorant P := by
  filter_upwards [(normalized_price hlam).eventually (eventually_gt_nhds
      (by norm_num : (1 / 2 : ℝ) < 1)), majorant_atTop.eventually_ge_atTop 1,
    prefixH_atTop.eventually_gt_atTop 1] with P hnorm hB1 hH
  have hHL : 0 < prefixH P * log (prefixH P) :=
    mul_pos (zero_lt_one.trans hH) (log_pos hH)
  have hnorm' : (1 / 2 : ℝ) < lam P * (prefixH P * log (prefixH P)) := hnorm
  have hlamP : 0 < lam P := by
    by_contra! h
    linarith only [mul_nonpos_of_nonpos_of_nonneg h hHL.le, hnorm']
  refine ⟨hlamP, hB1, ?_⟩
  calc
    1 = (1 : ℝ) * 1 := by ring
    _ ≤ (2 * (lam P * (prefixH P * log (prefixH P)))) * (2 * log 2) :=
      mul_le_mul (by linarith only [hnorm']) (by linarith only [log_two_half])
        zero_le_one (by linarith only [hnorm'])
    _ = _ := by unfold majorant; ring

private theorem endpoint_test {lam : ℕ → ℝ}
    (hlam : Tendsto (fun P => lam P / prefixPrice P) atTop (𝓝 1))
    {c : ℝ} (hc : 0 < c) (b : ℝ) :
    Tendsto (fun P =>
      lam P * log (c * sqrt (prefixH P)) *
        ((c * sqrt (prefixH P)) ^ 2 + b * (c * sqrt (prefixH P) + 1)))
      atTop (𝓝 (c ^ 2 / 2)) := by
  have hlog : Tendsto (fun P => log (c * sqrt (prefixH P)) / log (prefixH P))
      atTop (𝓝 (1 / 2)) := by
    have h := (prefixEll_atTop.const_div_atTop (log c)).add
      (tendsto_const_nhds (x := (1 / 2 : ℝ)))
    rw [zero_add] at h
    apply h.congr'
    filter_upwards [prefixH_atTop.eventually_gt_atTop 1] with P hH
    have hH0 := zero_lt_one.trans hH
    change log c / log (prefixH P) + 1 / 2 =
      log (c * sqrt (prefixH P)) / log (prefixH P)
    rw [log_mul hc.ne' (sqrt_pos.mpr hH0).ne', log_sqrt hH0.le]
    field_simp [(log_pos hH).ne'] <;> ring
  have hs : Tendsto (fun P => sqrt (prefixH P) / prefixH P) atTop (𝓝 0) := by
    simpa only [sqrt_div_self'] using sqrt_prefix_atTop.const_div_atTop (1 : ℝ)
  have hx : Tendsto (fun P => ((c * sqrt (prefixH P)) ^ 2 +
        b * (c * sqrt (prefixH P) + 1)) / prefixH P) atTop (𝓝 (c ^ 2)) := by
    have h := (tendsto_const_nhds (x := c ^ 2)).add
      (((hs.const_mul c).add (prefixH_atTop.const_div_atTop (1 : ℝ))).const_mul b)
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    filter_upwards [prefixH_atTop.eventually_gt_atTop 0] with P hH
    change c ^ 2 + b * (c * (sqrt (prefixH P) / prefixH P) + 1 / prefixH P) =
      ((c * sqrt (prefixH P)) ^ 2 + b * (c * sqrt (prefixH P) + 1)) / prefixH P
    rw [mul_pow, sq_sqrt hH.le]
    field_simp [hH.ne'] <;> ring
  have h := ((normalized_price hlam).mul hlog).mul hx
  have hlimit : (1 : ℝ) * (1 / 2) * c ^ 2 = c ^ 2 / 2 := by ring
  rw [hlimit] at h
  apply h.congr'
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1] with P hH
  have hH0 := zero_lt_one.trans hH
  field_simp [hH0.ne', (log_pos hH).ne'] <;> ring

private theorem gain_two_lower {x : ℝ} (hx : 2 ≤ x) :
    1 / (x ^ 2 + x + 1) ≤ gain 2 x := by
  have hsum : powerSum 2 x = x ^ 2 + x := by
    calc
      powerSum 2 x = powerSum 1 x + x ^ 2 := powerSum_succ 1 x
      _ = _ := by simp [powerSum, add_comm]
  have hpos : 0 < x := by linarith
  have hden : 0 < x ^ 2 + x := by positivity
  have h := one_sub_inv_le_log_of_pos (show 0 < 1 + 1 / (x ^ 2 + x) by positivity)
  have he : 1 - (1 + 1 / (x ^ 2 + x))⁻¹ = 1 / (x ^ 2 + x + 1) := by
    field_simp [hden.ne', (by positivity : x ^ 2 + x + 1 ≠ 0)]
    ring
  simpa only [he, gain, hsum] using h

private theorem endpoint_inside_prefix (c : ℝ) :
    ∀ᶠ P : ℕ in atTop, c * sqrt (prefixH P) ≤ (P : ℝ) := by
  have h := ((prefix_H_ratio.const_mul c).mul
    (sqrt_prefix_atTop.const_div_atTop (1 : ℝ)))
  simp only [mul_zero] at h
  filter_upwards [h.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)),
    prefixH_atTop.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)] with P hh hH hP
  have hs := sqrt_pos.mpr hH
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hh' : c * (prefixH P / (P : ℝ)) * (1 / sqrt (prefixH P)) < 1 := hh
  have hsq : prefixH P * (1 / sqrt (prefixH P)) = sqrt (prefixH P) := by
    calc
      _ = sqrt (prefixH P) ^ 2 * (1 / sqrt (prefixH P)) :=
        congrArg (fun t : ℝ => t * (1 / sqrt (prefixH P))) (sq_sqrt hH.le).symm
      _ = _ := by field_simp [hs.ne']
  have he : c * (prefixH P / (P : ℝ)) * (1 / sqrt (prefixH P)) =
      (c * sqrt (prefixH P)) / (P : ℝ) := by
    calc
      _ = (c * (prefixH P * (1 / sqrt (prefixH P)))) / (P : ℝ) := by ring
      _ = _ := by rw [hsq]
  rw [he] at hh'
  simpa only [one_mul] using ((div_lt_iff₀ hP0).mp hh').le

private theorem head_squeeze {lam : ℕ → ℝ}
    (hlam : Tendsto (fun P => lam P / prefixPrice P) atTop (𝓝 1))
    {c d : ℝ} (hc : 0 < c) (hcs : c < sqrt 2) (hsd : sqrt 2 < d) :
    ∀ᶠ P : ℕ in atTop, ∀ a, IsMinimizer (Nat.primesLE P) (lam P) a →
      θ (c * sqrt (prefixH P)) ≤ headClock P a ∧ headClock P a ≤ θ (d * sqrt (prefixH P)) := by
  have hd := hc.trans (hcs.trans hsd)
  have hs0 := sqrt_nonneg (2 : ℝ)
  have hsq := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hclim : c ^ 2 / 2 < 1 := by
    nlinarith only [hsq, mul_pos (sub_pos.mpr hcs) (add_pos_of_pos_of_nonneg hc hs0)]
  have hdlim : 1 < d ^ 2 / 2 := by
    nlinarith only [hsq, mul_pos (sub_pos.mpr hsd) (add_pos_of_pos_of_nonneg hd hs0)]
  filter_upwards [eventual_price_bounds hlam, endpoint_inside_prefix c,
    (sqrt_prefix_atTop.const_mul_atTop hc).eventually_ge_atTop 2,
    (sqrt_prefix_atTop.const_mul_atTop hd).eventually_ge_atTop 2,
    (endpoint_test hlam hc 1).eventually (eventually_lt_nhds hclim),
    (endpoint_test hlam hd 0).eventually (eventually_gt_nhds hdlim)]
    with P hprice hxP hx hy htlo hthi
  intro a ha
  let x := c * sqrt (prefixH P)
  let y := d * sqrt (prefixH P)
  have hx2 : 2 ≤ x := hx
  have hy2 : 2 ≤ y := hy
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have htestx : lam P * log x * (x ^ 2 + 1 * (x + 1)) < 1 := htlo
  have htesty : 1 < lam P * log y * (y ^ 2 + 0 * (y + 1)) := hthi
  have hlo : lam P < beta 2 x := by
    change lam P < gain 2 x / log x
    apply (lt_div_iff₀ (log_pos (show 1 < x by linarith))).mpr
    apply lt_of_lt_of_le _ (gain_two_lower hx2)
    apply (lt_div_iff₀ (show 0 < x ^ 2 + x + 1 by positivity)).mpr
    simpa only [one_mul, add_assoc] using htestx
  have hhi : beta 2 y < lam P := by
    change gain 2 y / log y < lam P
    apply (div_lt_iff₀ (log_pos (show 1 < y by linarith))).mpr
    apply (gain_le_inv_pow hy0 (by decide : 1 ≤ (2 : ℕ))).trans_lt
    apply (div_lt_iff₀ (pow_pos hy0 2)).mpr
    simpa only [zero_mul, add_zero] using htesty
  exact head_bounds ha hprice.1 hx2 hy2 hxP hlo hhi

private theorem normalized_theta {c : ℝ} (hc : 0 < c) :
    Tendsto (fun P => θ (c * sqrt (prefixH P)) / sqrt (prefixH P)) atTop (𝓝 c) := by
  have h := (EulerLayerRootCorrection.prime_number_limits.2.comp
    (sqrt_prefix_atTop.const_mul_atTop hc)).const_mul c
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [prefixH_atTop.eventually_gt_atTop 0] with P hH
  change c * (θ (c * sqrt (prefixH P)) / (c * sqrt (prefixH P))) =
    θ (c * sqrt (prefixH P)) / sqrt (prefixH P)
  field_simp [hc.ne', (sqrt_pos.mpr hH).ne']

private theorem higher_bound_tendsto :
    Tendsto (fun P => higherBound P / sqrt (prefixH P)) atTop (𝓝 0) := by
  have hcubic : Tendsto (fun P => majorant P ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp majorant_atTop
  have htheta := (EulerLayerRootCorrection.prime_number_limits.2.comp hcubic).eventually
    (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))
  have hsmall : Tendsto (fun P => 48 * (log (prefixH P) ^ (2 : ℕ) /
      prefixH P ^ (1 / 6 : ℝ))) atTop (𝓝 0) := by
    simpa only [prefixEll, mul_zero] using
      (log_pow_over_H_rpow 2 (by norm_num : (0 : ℝ) < 1 / 6)).const_mul 48
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsmall
  · filter_upwards [majorant_atTop.eventually_ge_atTop 1] with P hP
    exact div_nonneg (mul_nonneg (div_nonneg (log_nonneg hP) (log_pos (by norm_num)).le)
      (Chebyshev.theta_nonneg _)) (sqrt_nonneg _)
  · filter_upwards [prefixH_atTop.eventually_ge_atTop 4, prefixEll_atTop.eventually_ge_atTop 1,
      htheta] with P hH hL hthetaP
    let H := prefixH P
    have hH4 : 4 ≤ H := hH
    have hH0 : 0 < H := by linarith
    have hL1 : 1 ≤ log H := hL
    have hL0 : 0 < log H := by linarith
    have hrootPos : 0 < majorant P ^ (1 / 3 : ℝ) := by
      apply rpow_pos_of_pos _ _
      change 0 < 4 * (H * log H)
      positivity
    have htheta' : θ (majorant P ^ (1 / 3 : ℝ)) / majorant P ^ (1 / 3 : ℝ) < 2 :=
      hthetaP
    have htheta2 := ((div_lt_iff₀ hrootPos).mp htheta').le
    have hlog : log (majorant P) ≤ 3 * log H := by
      change log (4 * (H * log H)) ≤ 3 * log H
      rw [log_mul (by norm_num : (4 : ℝ) ≠ 0) (mul_ne_zero hH0.ne' hL0.ne'),
        log_mul hH0.ne' hL0.ne']
      linarith only [log_le_log (by norm_num : (0 : ℝ) < 4) hH4,
        log_le_sub_one_of_pos hL0]
    have hcap : log (majorant P) / log 2 ≤ 6 * log H := by
      apply (div_le_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))).mpr
      exact hlog.trans (by
        have hm := mul_le_mul_of_nonneg_left log_two_half.le (show 0 ≤ 6 * log H by positivity)
        nlinarith only [hm])
    have hroot : majorant P ^ (1 / 3 : ℝ) ≤ 4 * (H ^ (1 / 3 : ℝ) * log H) := by
      change (4 * (H * log H)) ^ (1 / 3 : ℝ) ≤ _
      rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (mul_nonneg hH0.le hL0.le),
        mul_rpow hH0.le hL0.le]
      apply mul_le_mul (rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 4)
        (by norm_num : (1 / 3 : ℝ) ≤ 1)) _ (by positivity) (by norm_num)
      exact mul_le_mul_of_nonneg_left
        (rpow_le_self_of_one_le hL1 (by norm_num)) (rpow_nonneg hH0.le _)
    have hbound : higherBound P ≤ 48 * (H ^ (1 / 3 : ℝ) * log H ^ 2) := by
      calc
        _ ≤ (6 * log H) * (2 * (4 * (H ^ (1 / 3 : ℝ) * log H))) :=
          mul_le_mul hcap (htheta2.trans (mul_le_mul_of_nonneg_left hroot (by norm_num)))
            (Chebyshev.theta_nonneg _) (by positivity)
        _ = _ := by ring
    have hpow : H ^ (1 / 3 : ℝ) / sqrt H = 1 / H ^ (1 / 6 : ℝ) := by
      rw [sqrt_eq_rpow, ← rpow_sub hH0, show (1 / 3 : ℝ) - 1 / 2 = -(1 / 6) by norm_num,
        rpow_neg hH0.le]
      exact (one_div _).symm
    calc
      _ ≤ (48 * (H ^ (1 / 3 : ℝ) * log H ^ 2)) / sqrt H :=
        div_le_div_of_nonneg_right hbound (sqrt_nonneg H)
      _ = 48 * (log H ^ 2 / H ^ (1 / 6 : ℝ)) := by
        calc
          _ = 48 * (log H ^ 2 * (H ^ (1 / 3 : ℝ) / sqrt H)) := by ring
          _ = _ := by rw [hpow]; ring

/-- The clock bounds are uniform in all minimizers at each sufficiently large prime prefix. -/
theorem fixed_price_minimizer_clock_eventually_between {lam : ℕ → ℝ}
    (hlam : Tendsto (fun P => lam P / prefixPrice P) atTop (𝓝 1))
    {l r : ℝ} (hl : l < sqrt 2) (hr : sqrt 2 < r) :
    ∀ᶠ P : ℕ in atTop, ∀ a, IsMinimizer (Nat.primesLE P) (lam P) a →
      l < clockIncrement (Nat.primesLE P) a / sqrt (prefixH P) ∧
      clockIncrement (Nat.primesLE P) a / sqrt (prefixH P) < r := by
  let c := (max l 0 + sqrt 2) / 2
  let d := (sqrt 2 + r) / 2
  have hs : 0 < sqrt (2 : ℝ) := sqrt_pos.mpr (by norm_num)
  have hmax : max l 0 < sqrt 2 := max_lt_iff.mpr ⟨hl, hs⟩
  have hc : 0 < c := by dsimp [c]; linarith only [le_max_right l 0, hs]
  have hlc : l < c := by dsimp [c]; linarith only [le_max_left l 0, hmax]
  have hcs : c < sqrt 2 := by dsimp [c]; linarith only [hmax]
  have hsd : sqrt 2 < d := by dsimp [d]; linarith only [hr]
  have hdr : d < r := by dsimp [d]; linarith only [hr]
  have hd : 0 < d := hs.trans hsd
  have hu := (normalized_theta hd).add higher_bound_tendsto
  rw [add_zero] at hu
  filter_upwards [head_squeeze hlam hc hcs hsd, eventual_price_bounds hlam,
    (normalized_theta hc).eventually (eventually_gt_nhds hlc),
    hu.eventually (eventually_lt_nhds hdr)] with P hhead hprice hlow hupp
  intro a ha
  obtain ⟨hheadLow, hheadHigh⟩ := hhead a ha
  obtain ⟨htail0, htailHigh⟩ := higher_bounds ha hprice.1 hprice.2.1 hprice.2.2
  have hlow' : l < θ (c * sqrt (prefixH P)) / sqrt (prefixH P) := hlow
  have hupp' : θ (d * sqrt (prefixH P)) / sqrt (prefixH P) +
      higherBound P / sqrt (prefixH P) < r := hupp
  have hsP := sqrt_nonneg (prefixH P)
  rw [clock_split ha.1, add_div]
  exact ⟨hlow'.trans_le ((div_le_div_of_nonneg_right hheadLow hsP).trans
      (le_add_of_nonneg_right (div_nonneg htail0 hsP))),
    (add_le_add (div_le_div_of_nonneg_right hheadHigh hsP)
      (div_le_div_of_nonneg_right htailHigh hsP)).trans_lt hupp'⟩

/-- Every eventual selection of supported fixed-price minimizers has the same clock limit. -/
theorem fixed_price_minimizer_clock_tendsto {lam : ℕ → ℝ} {a : ℕ → ℕ → ℕ}
    (hlam : Tendsto (fun P => lam P / prefixPrice P) atTop (𝓝 1))
    (ha : ∀ᶠ P : ℕ in atTop, IsMinimizer (Nat.primesLE P) (lam P) (a P)) :
    Tendsto (fun P => clockIncrement (Nat.primesLE P) (a P) / sqrt (prefixH P))
      atTop (𝓝 (sqrt 2)) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro l hl
    have hr : sqrt (2 : ℝ) < sqrt 2 + 1 := by linarith
    filter_upwards [fixed_price_minimizer_clock_eventually_between hlam hl hr, ha] with P h hmin
    exact (h (a P) hmin).1
  · intro r hr
    have hl : sqrt (2 : ℝ) - 1 < sqrt 2 := by linarith
    filter_upwards [fixed_price_minimizer_clock_eventually_between hlam hl hr, ha] with P h hmin
    exact (h (a P) hmin).2

end D5.S3.Arith.Robin.PriceRecord.FixedPriceMinimizerClock
