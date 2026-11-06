/- GID: D5/S3/Arith/Robin/PriceRecord/NonlinearPrimeExclusion
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/NonlinearPrimeExclusion
   mirror-E: none(waiver:nonlinear-real-root-construction)
   anchors: []
   utility: none
   digest: Nonlinear deletion and insertion barriers for the same original Robin minimum. -/

import D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
import D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand
import D5.S3.Arith.Robin.LogarithmBounds
import D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-! Exact nonlinear barriers; all integer comparisons use the original margin. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.NonlinearPrimeExclusion

open D5.S3.Weil.GronwallLowerEnvelope
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualGlobalBracketing
open D5.S3.Arith.Robin.PaddingRatio
open D5.S3.Arith.Robin.ActualRobinInterval
open D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
open D5.S3.Arith.Robin.RestrictedDivisorStrictInventory
open D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand

/-- The exact one-layer deletion barrier. -/
def deletionBarrier (L x : ℝ) : ℝ := L - L ^ (x / (x + 1)) - Real.log x

/-- The exact fresh-prime insertion barrier. -/
def insertionBarrier (L x : ℝ) : ℝ := Real.log x - L ^ (1 + 1 / x) + L

private theorem deletion_strictAnti {L : ℝ} (hL : 1 < L) :
    StrictAntiOn (deletionBarrier L) (Set.Ioi 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by change 1 < x at hx; linarith
  have hy0 : 0 < y := by change 1 < y at hy; linarith
  have hr : x / (x + 1) < y / (y + 1) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hp := Real.rpow_lt_rpow_of_exponent_lt hL hr
  have hl := Real.log_lt_log hx0 hxy
  dsimp [deletionBarrier]
  linarith

private theorem insertion_strictMono {L : ℝ} (hL : 1 < L) :
    StrictMonoOn (insertionBarrier L) (Set.Ioi 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by change 1 < x at hx; linarith
  have hr : 1 + 1 / y < 1 + 1 / x := by
    linarith only [one_div_lt_one_div_of_lt hx0 hxy]
  have hp := Real.rpow_lt_rpow_of_exponent_lt hL hr
  have hl := Real.log_lt_log hx0 hxy
  dsimp [insertionBarrier]
  linarith

private theorem loglog_comparison {L y c : ℝ} (hL : 1 < L) (hy : 1 < y)
    (hc : 0 < c) :
    Real.log (Real.log L) - Real.log (Real.log y) ≤ Real.log c ↔
      L ^ (1 / c) ≤ y := by
  have hL0 : 0 < L := by linarith
  have hy0 : 0 < y := by linarith
  have hlL := Real.log_pos hL
  have hly := Real.log_pos hy
  rw [← Real.log_div hlL.ne' hly.ne',
    Real.log_le_log_iff (div_pos hlL hly) hc, div_le_iff₀ hly]
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hL0 _) hy0,
    Real.log_rpow hL0]
  have he : 1 / c * Real.log L = Real.log L / c := by ring
  rw [he, div_le_iff₀ hc]
  constructor <;> intro h <;> nlinarith only [h]

private theorem deletion_test {L x : ℝ} (hL : 1 < L) (hx : 1 < x)
    (hy : 1 < L - Real.log x) :
    0 ≤ deletionBarrier L x ↔
      Real.log (Real.log L) - Real.log (Real.log (L - Real.log x)) ≤
        Real.log (1 + 1 / x) := by
  have hx0 : 0 < x := by linarith
  have he : 1 / (1 + 1 / x) = x / (x + 1) := by field_simp
  rw [loglog_comparison hL hy (by positivity), he]
  dsimp [deletionBarrier]
  constructor <;> intro h <;> linarith

private theorem insertion_test {L x : ℝ} (hL : 1 < L) (hx : 1 < x) :
    0 ≤ insertionBarrier L x ↔
      Real.log (1 + 1 / x) ≤
        Real.log (Real.log (L + Real.log x)) - Real.log (Real.log L) := by
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have hlx := Real.log_pos hx
  have hy : 1 < L + Real.log x := by linarith
  have hc : 0 < 1 + 1 / x := by positivity
  rw [← Real.log_div (Real.log_pos hy).ne' (Real.log_pos hL).ne',
    Real.log_le_log_iff hc (div_pos (Real.log_pos hy) (Real.log_pos hL)),
    le_div_iff₀ (Real.log_pos hL)]
  rw [← Real.log_rpow hL0,
    Real.log_le_log_iff (Real.rpow_pos_of_pos hL0 _) (by linarith : 0 < L + Real.log x)]
  dsimp [insertionBarrier]
  constructor <;> intro h <;> nlinarith only [h]

private theorem deletion_half_pos {L : ℝ} (hL : 16 < L) :
    0 < deletionBarrier L (L / 2) := by
  have hL0 : 0 < L := by linarith
  have hl := Real.log_pos (by linarith : 1 < L)
  have hlog16 : Real.log (16 : ℝ) ≤ 4 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h2 ⊢
    linarith
  have hb := Real.log_le_sub_one_of_pos (div_pos hL0 (by norm_num : (0 : ℝ) < 16))
  rw [Real.log_div hL0.ne' (by norm_num : (16 : ℝ) ≠ 0)] at hb
  have hsmall : 2 + 2 * Real.log L < L := by linarith
  let v := 2 * Real.log L / (L + 2)
  have hv : 0 < v := div_pos (by positivity) (by linarith)
  have hexp : 1 + v < Real.exp v := by linarith only [Real.add_one_lt_exp hv.ne']
  have hinv : Real.exp (-v) < 1 / (1 + v) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (by linarith) hexp
  have hid : L - L / (1 + v) - Real.log L =
      Real.log L * (L - 2 - 2 * Real.log L) / (L + 2 + 2 * Real.log L) := by
    dsimp [v]
    field_simp
    ring
  have hnorm : L - L / (1 + v) > Real.log L := by
    have hh : 0 < Real.log L * (L - 2 - 2 * Real.log L) /
        (L + 2 + 2 * Real.log L) :=
      div_pos (mul_pos hl (by linarith)) (by positivity)
    linarith only [hid, hh]
  have hp : L ^ ((L / 2) / (L / 2 + 1)) = L * Real.exp (-v) := by
    rw [Real.rpow_def_of_pos hL0]
    calc
      Real.exp (Real.log L * ((L / 2) / (L / 2 + 1))) = Real.exp (Real.log L - v) := by
        congr 1
        dsimp [v]
        field_simp
        ring
      _ = L * Real.exp (-v) := by rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hL0]
  have hloghalf : Real.log (L / 2) < Real.log L :=
    Real.log_lt_log (by positivity) (by linarith)
  dsimp [deletionBarrier]
  rw [hp]
  have hm := mul_lt_mul_of_pos_left hinv hL0
  rw [mul_one_div] at hm
  linarith

private theorem deletion_cutoff_neg {L z : ℝ} (hL : 16 < L) (hz : 11 < z)
    (hzL : z < L) (hroot : firstLayerPrice z = 1 / (L * Real.log L)) :
    deletionBarrier L z < 0 := by
  have hL1 : 1 < L := by linarith
  have hz1 : 1 < z := by linarith
  have hlz := Real.log_pos hz1
  have hy : 1 < L - Real.log z := by
    have hlog := Real.log_lt_sub_one_of_pos (by linarith : 0 < L) (by linarith : L ≠ 1)
    have hmono := Real.log_lt_log (by linarith : 0 < z) hzL
    linarith
  have hprice : Real.log (1 + 1 / z) = Real.log z / (L * Real.log L) := by
    change Real.log (1 + 1 / z) / Real.log z = _ at hroot
    exact (div_eq_iff hlz.ne').mp hroot |>.trans (by ring)
  have ht := loglog_tangent hL1 hy (by linarith : L ≠ L - Real.log z)
  change _ < (L - Real.log z - L) * (1 / (L * Real.log L)) at ht
  have hstrict : Real.log (1 + 1 / z) <
      Real.log (Real.log L) - Real.log (Real.log (L - Real.log z)) := by
    rw [hprice]
    have ht' : Real.log (Real.log (L - Real.log z)) - Real.log (Real.log L) <
        -(Real.log z / (L * Real.log L)) := by
      convert ht using 1 <;> ring
    linarith only [ht']
  by_contra hn
  have htest := (deletion_test hL1 hz1 hy).mp (le_of_not_gt hn)
  linarith

private theorem insertion_at_clock_neg {L : ℝ} (hL : 1 < L) :
    insertionBarrier L L < 0 := by
  have hL0 : 0 < L := by linarith
  have hl := Real.log_pos hL
  have hv : 0 < Real.log L / L := div_pos hl hL0
  have he := Real.add_one_lt_exp hv.ne'
  have hp : L ^ (1 + 1 / L) = L * Real.exp (Real.log L / L) := by
    rw [Real.rpow_def_of_pos hL0,
      show Real.log L * (1 + 1 / L) = Real.log L + Real.log L / L by ring,
      Real.exp_add, Real.exp_log hL0]
  dsimp [insertionBarrier]
  rw [hp]
  have hm := mul_lt_mul_of_pos_left he hL0
  have hh : L * (Real.log L / L) = Real.log L := by field_simp
  linarith

private theorem insertion_far_pos {L : ℝ} (hL : 1 < L) :
    0 < insertionBarrier L (Real.exp (L ^ 2)) := by
  have hL0 : 0 < L := by linarith
  have hx : 1 < Real.exp (L ^ 2) := Real.one_lt_exp_iff.mpr (sq_pos_of_pos hL0)
  have hr : 1 + 1 / Real.exp (L ^ 2) < 2 := by
    have hi := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hx
    simp only [div_one] at hi
    linarith
  have hp := Real.rpow_lt_rpow_of_exponent_lt hL hr
  rw [Real.rpow_two] at hp
  dsimp [insertionBarrier]
  rw [Real.log_exp]
  linarith

private theorem barrier_roots {L z : ℝ} (hL : 16 < L) (hz : 11 < z)
    (hzL : z < L) (hhalf : L - z < 1 / 2)
    (hroot : firstLayerPrice z = 1 / (L * Real.log L)) :
    ∃ α β : ℝ, L / 2 < α ∧ α < z ∧ L < β ∧
      deletionBarrier L α = 0 ∧ insertionBarrier L β = 0 ∧
      (∀ x : ℝ, 1 < x → deletionBarrier L x = 0 → x = α) ∧
      (∀ x : ℝ, 1 < x → insertionBarrier L x = 0 → x = β) := by
  have hL1 : 1 < L := by linarith
  have hL0 : 0 < L := by linarith
  have hhalf1 : 1 < L / 2 := by linarith
  have hhz : L / 2 < z := by linarith
  have ha := deletion_half_pos hL
  have hzneg := deletion_cutoff_neg hL hz hzL hroot
  have hcA : ContinuousOn (deletionBarrier L) (Set.Icc (L / 2) z) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.sub continuousOn_const
      apply (Real.continuous_const_rpow hL0.ne').continuousOn.comp
      · exact continuousOn_id.div (continuousOn_id.add continuousOn_const)
          (fun x hx => by change x + 1 ≠ 0; have := hx.1; linarith)
      · exact Set.mapsTo_univ _ _
    · exact continuousOn_id.log (fun x hx => by change x ≠ 0; have := hx.1; linarith)
  obtain ⟨α, hα, hαroot⟩ := intermediate_value_Icc' hhz.le hcA ⟨hzneg.le, ha.le⟩
  have hαlo : L / 2 < α := lt_of_le_of_ne hα.1 (by intro he; rw [← he] at hαroot; linarith)
  have hαhi : α < z := lt_of_le_of_ne hα.2 (by intro he; rw [he] at hαroot; linarith)
  let b := Real.exp (L ^ 2)
  have hLb : L < b := by
    have hl := Real.log_le_sub_one_of_pos hL0
    apply (Real.log_lt_iff_lt_exp hL0).mp
    nlinarith
  have hbpos := insertion_far_pos hL1
  have hLneg := insertion_at_clock_neg hL1
  have hcB : ContinuousOn (insertionBarrier L) (Set.Icc L b) := by
    apply ContinuousOn.add
    apply ContinuousOn.sub
    · exact continuousOn_id.log (fun x hx => ne_of_gt (hL0.trans_le hx.1))
    · apply (Real.continuous_const_rpow hL0.ne').continuousOn.comp
      · exact continuousOn_const.add (continuousOn_const.div continuousOn_id
          (fun x hx => ne_of_gt (hL0.trans_le hx.1)))
      · exact Set.mapsTo_univ _ _
    · exact continuousOn_const
  obtain ⟨β, hβ, hβroot⟩ := intermediate_value_Icc hLb.le hcB ⟨hLneg.le, hbpos.le⟩
  have hβlo : L < β := lt_of_le_of_ne hβ.1 (by intro he; rw [← he] at hβroot; linarith)
  refine ⟨α, β, hαlo, hαhi, hβlo, hαroot, hβroot, ?_, ?_⟩
  · intro x hx he
    exact (deletion_strictAnti hL1).injOn hx (hhalf1.trans hαlo) (he.trans hαroot.symm)
  · intro x hx he
    exact (insertion_strictMono hL1).injOn hx (hL1.trans hβlo) (he.trans hβroot.symm)

private theorem support_cofactor_domain {N p : ℕ} (hN : 55440 < N)
    (hbase : 55440 ∣ N) (hp : p.Prime) (hd : p ∣ N) : 5040 < N / p := by
  have heq : N / p * p = N := Nat.div_mul_cancel hd
  have hpos : 0 < N / p := Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
  by_cases hsmall : p ≤ 11
  · have hb : 5040 * p ≤ 55440 := by omega
    nlinarith [hp.pos]
  · have hlarge : 11 < p := by omega
    have hn : ¬ p ∣ 55440 := by
      intro h
      have hfac : p ∣ 2 ^ 4 * 3 ^ 2 * 5 * 7 * 11 := by norm_num at h ⊢; exact h
      simp only [hp.dvd_mul] at hfac
      rcases hfac with (((h | h) | h) | h) | h
      · have := Nat.le_of_dvd (by norm_num : 0 < 2) (hp.dvd_of_dvd_pow h); omega
      · have := Nat.le_of_dvd (by norm_num : 0 < 3) (hp.dvd_of_dvd_pow h); omega
      all_goals have := Nat.le_of_dvd (by norm_num) h; omega
    have hcop : Nat.Coprime 55440 p := (hp.coprime_iff_not_dvd.mpr hn).symm
    have hb : 55440 ∣ N / p := hcop.dvd_of_dvd_mul_right (heq.symm ▸ hbase)
    have := Nat.le_of_dvd hpos hb
    omega

theorem W_first_delta {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hf : n.factorization p = 0) :
    W (n * p) - W n = Real.log (1 + 1 / (p : ℝ)) := by
  have hd := golden_resource_objective_single_layer_delta 0 hn hp
  rw [golden_resource_sigma_identity 0 (by nlinarith [hp.pos] : 1 ≤ n * p),
    golden_resource_sigma_identity 0 hn] at hd
  simp only [zero_mul, sub_zero, hf, zero_add,
    golden_layer_marginal_one_eq_log_one_add_inv hp,
    div_mul_cancel₀ _ hp.log_pos.ne'] at hd
  exact hd

private theorem minimum_deletion_barrier {N p : ℕ} (hN : 55440 < N)
    (hbase : 55440 ∣ N) (hmin : ∀ m : ℕ, 5040 < m → robinLogMargin N ≤ robinLogMargin m)
    (hp : p.Prime) (hd : p ∣ N) (hf : N.factorization p = 1)
    (hL : 1 < Real.log (N : ℝ)) :
    0 ≤ deletionBarrier (Real.log N) p := by
  have hc := support_cofactor_domain hN hbase hp hd
  have hco : 0 < N / p := by omega
  have heq : N / p * p = N := Nat.div_mul_cancel hd
  have hfac : (N / p).factorization p = 0 := by
    have hh := congrArg (fun m : ℕ => m.factorization p) heq
    simp only [Nat.factorization_mul hco.ne' hp.ne_zero, Finsupp.coe_add,
      Pi.add_apply, hp.factorization, Finsupp.single_eq_same] at hh
    omega
  have hw := W_first_delta (by omega : 1 ≤ N / p) hp hfac
  rw [heq] at hw
  have hclock : Real.log (N / p : ℕ) = Real.log (N : ℝ) - Real.log p := by
    have hh := congrArg (fun m : ℕ => Real.log (m : ℝ)) heq
    rw [Nat.cast_mul, Real.log_mul (Nat.cast_pos.mpr hco).ne'
      (Nat.cast_pos.mpr hp.pos).ne'] at hh
    linarith
  have hy : 1 < Real.log (N : ℝ) - Real.log p := by
    rw [← hclock]
    exact (Real.log_pos_iff (Real.log_pos (by exact_mod_cast (show 1 < N / p by omega))).le).mp
      (D5.S3.Arith.Robin.PaddingRatio.loglog_pos (by omega : 5041 ≤ N / p))
  apply (deletion_test hL (by exact_mod_cast hp.one_lt) hy).mpr
  have hm := hmin (N / p) hc
  rw [margin_eq_threshold_sub_W, margin_eq_threshold_sub_W, hclock] at hm
  dsimp [robinThreshold] at hm
  linarith

private theorem minimum_insertion_barrier {N p : ℕ} (hN : 5040 < N)
    (hmin : ∀ m : ℕ, 5040 < m → robinLogMargin N ≤ robinLogMargin m)
    (hp : p.Prime) (hd : ¬ p ∣ N) (hL : 1 < Real.log (N : ℝ)) :
    0 ≤ insertionBarrier (Real.log N) p := by
  have hw := W_first_delta (by omega : 1 ≤ N) hp (Nat.factorization_eq_zero_of_not_dvd hd)
  have hc : 5040 < N * p := by nlinarith [hp.one_lt]
  have hm := hmin (N * p) hc
  have hclock : Real.log (N * p : ℕ) = Real.log (N : ℝ) + Real.log p := by
    rw [Nat.cast_mul, Real.log_mul (Nat.cast_pos.mpr (by omega : 0 < N)).ne'
      (Nat.cast_pos.mpr hp.pos).ne']
  apply (insertion_test hL (by exact_mod_cast hp.one_lt)).mpr
  rw [margin_eq_threshold_sub_W, margin_eq_threshold_sub_W, hclock] at hm
  dsimp [robinThreshold] at hm
  linarith

/-- Roots on the full real domain, and an OPEN interval containing no prime. -/
def NonlinearPrimeGap (N : ℕ) (z α β : ℝ) : Prop :=
  Real.log N / 2 < α ∧ α < z ∧ z < Real.log N ∧ Real.log N < β ∧
    deletionBarrier (Real.log N) α = 0 ∧ insertionBarrier (Real.log N) β = 0 ∧
    (∀ x : ℝ, 1 < x → deletionBarrier (Real.log N) x = 0 → x = α) ∧
    (∀ x : ℝ, 1 < x → insertionBarrier (Real.log N) x = 0 → x = β) ∧
    (∀ p : ℕ, p.Prime → α < (p : ℝ) → β ≤ (p : ℝ))

private theorem gap_of_original_minimum {N : ℕ} {z : ℝ} (hN : 55440 < N)
    (hbase : 55440 ∣ N) (hL : 16 < Real.log (N : ℝ))
    (hmin : ∀ m : ℕ, 5040 < m → robinLogMargin N ≤ robinLogMargin m)
    (hp0 : 0 < price (Real.log N)) (hNm : N = maximalInteger (price (Real.log N)))
    (hz : 11 < z) (hzL : z < Real.log (N : ℝ)) (hhalf : Real.log N - z < 1 / 2)
    (hroot : firstLayerPrice z = 1 / (Real.log N * Real.log (Real.log N)))
    (hsupport : N.primeFactors = Nat.primesLE ⌊z⌋₊) :
    ∃ α β : ℝ, NonlinearPrimeGap N z α β := by
  obtain ⟨α, β, hαlo, hαz, hLβ, hα, hβ, huα, huβ⟩ :=
    barrier_roots hL hz hzL hhalf hroot
  have hL1 : 1 < Real.log (N : ℝ) := by linarith
  have hα1 : 1 < α := by linarith
  have hβ1 : 1 < β := by linarith
  refine ⟨α, β, hαlo, hαz, hzL, hLβ, hα, hβ, huα, huβ, ?_⟩
  intro p hp hαp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  by_cases hd : p ∣ N
  · have hmem : p ∈ N.primeFactors := hp.mem_primeFactors hd (by omega)
    have hpP : p ≤ D5.S3.Arith.Robin.OriginalEndpointPrimeTail.largestPrime N :=
      Finset.le_sup (f := id) hmem
    have hP2 : 2 ≤ D5.S3.Arith.Robin.OriginalEndpointPrimeTail.largestPrime N :=
      hp.two_le.trans hpP
    have hPf : D5.S3.Arith.Robin.OriginalEndpointPrimeTail.largestPrime N ≤ ⌊z⌋₊ := by
      apply Finset.sup_le
      intro q hq
      rw [hsupport] at hq
      exact (Nat.mem_primesLE.mp hq).1
    have hPz : (D5.S3.Arith.Robin.OriginalEndpointPrimeTail.largestPrime N : ℝ) ≤ z :=
      (Nat.cast_le.mpr hPf).trans (Nat.floor_le (by linarith : 0 ≤ z))
    have hs : 2 * Real.sqrt (D5.S3.Arith.Robin.OriginalEndpointPrimeTail.largestPrime N : ℝ) <
        Real.log (N : ℝ) / 2 := by
      have hP0 : (0 : ℝ) ≤ D5.S3.Arith.Robin.OriginalEndpointPrimeTail.largestPrime N := Nat.cast_nonneg _
      have hsq := Real.sq_sqrt hP0
      have hs0 := Real.sqrt_nonneg (D5.S3.Arith.Robin.OriginalEndpointPrimeTail.largestPrime N : ℝ)
      nlinarith [sq_nonneg (Real.log (N : ℝ) - 16)]
    have hf := (endpoint_first_layer_band hp0 (Or.inr hNm) hP2 hp
      (le_of_lt (hs.trans (hαlo.trans hαp))) hpP).2
    have ha := minimum_deletion_barrier hN hbase hmin hp hd hf hL1
    have hn := deletion_strictAnti hL1 hα1 hp1 hαp
    rw [hα] at hn
    exact (not_lt_of_ge ha hn).elim
  · have hb := minimum_insertion_barrier (by omega : 5040 < N) hmin hp hd hL1
    by_contra hn
    have hpb : (p : ℝ) < β := lt_of_not_ge hn
    have hneg := insertion_strictMono hL1 hp1 hβ1 hpb
    rw [hβ] at hneg
    linarith

/-- The sole original nonpositive Robin failure constructs the SAME global minimum,
optimizer, cutoff and unique nonlinear deletion/insertion roots. Endpoints may tie. -/
theorem failure_has_nonlinear_prime_gap
    (hfailure : ∃ n : ℕ, 5040 < n ∧ robinLogMargin n ≤ 0) :
    ∃ (N : ℕ) (z : ℝ), 55440 < N ∧ robinLogMargin N ≤ 0 ∧
      (∀ m : ℕ, 5040 < m → robinLogMargin N ≤ robinLogMargin m) ∧
      0 < price (Real.log N) ∧ price (Real.log N) < boundaryPrice ∧
      IsGoldenResourceOptimal (price (Real.log N)) N ∧
      (∀ m : ℕ, 1 ≤ m → m ≠ N →
        goldenResourceObjective (price (Real.log N)) m <
          goldenResourceObjective (price (Real.log N)) N) ∧
      N = strictInteger (price (Real.log N)) ∧
      N = maximalInteger (price (Real.log N)) ∧
      (∀ p k : ℕ, p.Prime → 1 ≤ k →
        price (Real.log N) ≠ goldenLayerMarginal p k) ∧
      11 < z ∧ 0 < Real.log N - z ∧ Real.log N - z < 1 / 2 ∧
      firstLayerPrice z = 1 / (Real.log N * Real.log (Real.log N)) ∧
      (∀ t : ℝ, 1 < t →
        firstLayerPrice t = 1 / (Real.log N * Real.log (Real.log N)) → t = z) ∧
      N.primeFactors = Nat.primesLE ⌊z⌋₊ ∧
      ∃ α β : ℝ, NonlinearPrimeGap N z α β := by
  obtain ⟨N, z, hN, hSN, hmin, hp0, hpb, hopt, hstrict, hNs, hNm, hnotie,
    hz, hM0, hMhalf, hroot, hunique, hsupport⟩ := failure_has_unique_half_shift_cutoff hfailure
  have hNlarge : 223092870 ≤ N := by
    by_contra h
    have hf := D5.S3.Arith.Robin.FewDistinctPrimes.robin_lt_223092870
      (by omega : 5040 < N) (by omega : N < 223092870)
    have hnR : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hsR : 0 < (ArithmeticFunction.sigma 1 N : ℝ) :=
      Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos 1 N (by omega))
    have hll := loglog_pos (by omega : 5041 ≤ N)
    have hden : 0 < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log N) :=
      mul_pos (Real.exp_pos _) hll
    have hratio_eq : robinRatio N = ((ArithmeticFunction.sigma 1 N : ℝ) / N) /
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log N)) := by
      simp only [robinRatio, div_eq_mul_inv, mul_inv_rev]
      ring
    have hratio_lt : robinRatio N < 1 := by
      rw [hratio_eq]
      exact (div_lt_one hden).mpr hf
    have hratio_pos : 0 < robinRatio N :=
      div_pos hsR (mul_pos (mul_pos (Real.exp_pos _) hnR) hll)
    have hmargin : 0 < robinLogMargin N := by
      rw [robin_log_margin_eq_neg_log (by omega : 5041 ≤ N)]
      exact neg_pos.mpr (Real.log_neg hratio_pos hratio_lt)
    linarith only [hSN, hmargin]
  have hL : 16 < Real.log (N : ℝ) := by
    apply (Real.lt_log_iff_exp_lt (Nat.cast_pos.mpr (by omega))).mpr
    have hexp : Real.exp (16 : ℝ) = Real.exp 1 ^ 16 := by
      simp [Real.exp_nat_mul]
    rw [hexp]
    have hp : Real.exp 1 ^ 16 < (3 : ℝ) ^ 16 :=
      pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num)
    have hn : (223092870 : ℝ) ≤ N := by exact_mod_cast hNlarge
    norm_num at hp
    linarith only [hp, hn, hexp]
  have hbase : 55440 ∣ N := by
    have hd := weak_dvd_weak hp0 boundaryPrice_spec.1 hpb.le
    change boundaryCap ∣ maximalInteger (price (Real.log N)) at hd
    rw [boundaryCap_eq_55440, ← hNm] at hd
    exact hd
  obtain ⟨α, β, hgap⟩ := gap_of_original_minimum hN hbase hL hmin hp0 hNm hz
    (by linarith only [hM0]) hMhalf hroot hsupport
  exact ⟨N, z, hN, hSN, hmin, hp0, hpb, hopt, hstrict, hNs, hNm, hnotie,
    hz, hM0, hMhalf, hroot, hunique, hsupport, α, β, hgap⟩

#print axioms failure_has_nonlinear_prime_gap

end D5.S3.Arith.Robin.PriceRecord.NonlinearPrimeExclusion
