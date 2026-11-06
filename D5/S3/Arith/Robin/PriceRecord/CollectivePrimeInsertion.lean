/- GID: D5/S3/Arith/Robin/PriceRecord/CollectivePrimeInsertion
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/CollectivePrimeInsertion
   mirror-E: none(waiver:nonlinear-real-root-construction)
   anchors: []
   utility: none
   digest: Collective insertion restrictions at the same original Robin minimum. -/

import D5.S3.Arith.Robin.PriceRecord.NonlinearPrimeExclusion
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Deriv

set_option autoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.CollectivePrimeInsertion

open D5.S3.Arith.Robin.PriceRecord.NonlinearPrimeExclusion
open D5.S3.Arith.Robin.ActualRobinInterval
open D5.S3.Weil.GronwallLowerEnvelope
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.Robin.PaddingRatio
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualGlobalBracketing
open D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff

/-- The literal nonlinear barrier for inserting k fresh prime factors. -/
def collectiveInsertionBarrier (L : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  L + k * Real.log x - L ^ ((1 + 1 / x) ^ k)

private theorem barrier_strictMono {L : ℝ} {k : ℕ} (hL : 1 < L) (hk : 1 ≤ k) :
    StrictMonoOn (collectiveInsertionBarrier L k) (Set.Ioi 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by change 1 < x at hx; linarith
  have hy0 : 0 < y := by change 1 < y at hy; linarith
  have hr : 1 + 1 / y < 1 + 1 / x := by
    linarith only [one_div_lt_one_div_of_lt hx0 hxy]
  have hp := pow_lt_pow_left₀ hr (by positivity : 0 ≤ 1 + 1 / y) (by omega : k ≠ 0)
  have hpow := Real.rpow_lt_rpow_of_exponent_lt hL hp
  have hl := mul_lt_mul_of_pos_left (Real.log_lt_log hx0 hxy)
    (by exact_mod_cast (show 0 < k by omega) : (0 : ℝ) < k)
  dsimp [collectiveInsertionBarrier]
  linarith

private theorem barrier_at_clock_neg {L : ℝ} {k : ℕ} (hL : 1 < L) (hk : 1 ≤ k) :
    collectiveInsertionBarrier L k L < 0 := by
  have hL0 : 0 < L := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hl := Real.log_pos hL
  have hb := one_add_mul_le_pow (by linarith [one_div_pos.mpr hL0] : (-2 : ℝ) ≤ 1 / L) k
  have hp := Real.rpow_le_rpow_of_exponent_le hL.le hb
  have he := Real.add_one_lt_exp (ne_of_gt (div_pos (mul_pos hk0 hl) hL0))
  have hid : L ^ (1 + (k : ℝ) * (1 / L)) =
      L * Real.exp ((k : ℝ) * Real.log L / L) := by
    rw [Real.rpow_def_of_pos hL0,
      show Real.log L * (1 + (k : ℝ) * (1 / L)) =
        Real.log L + (k : ℝ) * Real.log L / L by ring,
      Real.exp_add, Real.exp_log hL0]
  rw [hid] at hp
  have hm := mul_lt_mul_of_pos_left he hL0
  have hc : L * ((k : ℝ) * Real.log L / L) = (k : ℝ) * Real.log L := by field_simp
  dsimp [collectiveInsertionBarrier]
  linarith

private theorem barrier_far_pos {L : ℝ} {k : ℕ} (hL : 1 < L) (hk : 1 ≤ k) :
    0 < collectiveInsertionBarrier L k (Real.exp (L ^ ((2 : ℕ) ^ k))) := by
  have hL0 : 0 < L := by linarith
  have hA : 0 < L ^ ((2 : ℕ) ^ k) := pow_pos hL0 _
  have hx : 1 < Real.exp (L ^ ((2 : ℕ) ^ k)) := Real.one_lt_exp_iff.mpr hA
  have hr : 1 + 1 / Real.exp (L ^ ((2 : ℕ) ^ k)) < 2 := by
    have := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hx
    simp only [div_one] at this
    linarith
  have hp := pow_lt_pow_left₀ hr (by positivity :
    0 ≤ 1 + 1 / Real.exp (L ^ ((2 : ℕ) ^ k))) (by omega : k ≠ 0)
  have hpow := Real.rpow_lt_rpow_of_exponent_lt hL hp
  rw [show (2 : ℝ) ^ k = (((2 : ℕ) ^ k : ℕ) : ℝ) by norm_cast,
    Real.rpow_natCast] at hpow
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm := mul_le_mul_of_nonneg_right hk1 hA.le
  dsimp [collectiveInsertionBarrier]
  rw [Real.log_exp]
  linarith

/-- For every positive k the actual barrier has a unique root above L, on all x>1. -/
theorem collective_insertion_root_exists_unique {L : ℝ} (hL : 1 < L) {k : ℕ} (hk : 1 ≤ k) :
    ∃ β : ℝ, L < β ∧ collectiveInsertionBarrier L k β = 0 ∧
      (∀ x : ℝ, 1 < x → collectiveInsertionBarrier L k x = 0 → x = β) ∧
      (∀ x : ℝ, 1 < x → (collectiveInsertionBarrier L k x < 0 ↔ x < β)) ∧
      (∀ x : ℝ, 1 < x → (0 < collectiveInsertionBarrier L k x ↔ β < x)) := by
  let b := Real.exp (L ^ ((2 : ℕ) ^ k))
  have hL0 : 0 < L := by linarith
  have hLb : L < b := by
    apply (Real.log_lt_iff_lt_exp hL0).mp
    have hlog := Real.log_lt_sub_one_of_pos hL0 (ne_of_gt hL)
    have hpow : L ≤ L ^ ((2 : ℕ) ^ k) := le_self_pow₀ hL.le (by positivity)
    linarith
  have hneg := barrier_at_clock_neg hL hk
  have hpos := barrier_far_pos hL hk
  have hc : ContinuousOn (collectiveInsertionBarrier L k) (Set.Icc L b) := by
    apply ContinuousOn.sub
    · exact continuousOn_const.add (continuousOn_const.mul
        (continuousOn_id.log (fun x hx => ne_of_gt (hL0.trans_le hx.1))))
    · apply (Real.continuous_const_rpow hL0.ne').continuousOn.comp
      · exact (continuousOn_const.add (continuousOn_const.div continuousOn_id
          (fun x hx => ne_of_gt (hL0.trans_le hx.1)))).pow k
      · exact Set.mapsTo_univ _ _
  obtain ⟨β, hβ, hroot⟩ := intermediate_value_Icc hLb.le hc ⟨hneg.le, hpos.le⟩
  have hβlo : L < β := lt_of_le_of_ne hβ.1 (by intro he; rw [← he] at hroot; linarith)
  have hβ1 := hL.trans hβlo
  have hm := barrier_strictMono hL hk
  refine ⟨β, hβlo, hroot, ?_, ?_, ?_⟩
  · intro x hx he
    exact hm.injOn hx hβ1 (he.trans hroot.symm)
  · intro x hx
    constructor
    · intro hn
      by_contra hh
      have := hm.monotoneOn hβ1 hx (le_of_not_gt hh)
      rw [hroot] at this
      linarith
    · intro hh
      have := hm hx hβ1 hh
      rwa [hroot] at this
  · intro x hx
    constructor
    · intro hp
      by_contra hh
      have := hm.monotoneOn hx hβ1 (le_of_not_gt hh)
      rw [hroot] at this
      linarith
    · intro hh
      have := hm hβ1 hx hh
      rwa [hroot] at this

private theorem barrier_test {L x : ℝ} (k : ℕ) (hL : 1 < L) (hx : 1 < x) :
    (0 ≤ collectiveInsertionBarrier L k x ↔
      (k : ℝ) * Real.log (1 + 1 / x) ≤
        Real.log (Real.log (L + k * Real.log x)) - Real.log (Real.log L)) ∧
    (0 < collectiveInsertionBarrier L k x ↔
      (k : ℝ) * Real.log (1 + 1 / x) <
        Real.log (Real.log (L + k * Real.log x)) - Real.log (Real.log L)) := by
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have hy : 1 < L + k * Real.log x := by
    have := mul_nonneg (Nat.cast_nonneg k) (Real.log_pos hx).le
    linarith
  have hc : 0 < 1 + 1 / x := by positivity
  have hp : 0 < (1 + 1 / x) ^ k := pow_pos hc _
  have hweak : (k : ℝ) * Real.log (1 + 1 / x) ≤
      Real.log (Real.log (L + k * Real.log x)) - Real.log (Real.log L) ↔
      L ^ ((1 + 1 / x) ^ k) ≤ L + k * Real.log x := by
    rw [← Real.log_pow, ← Real.log_div (Real.log_pos hy).ne' (Real.log_pos hL).ne',
      Real.log_le_log_iff hp (div_pos (Real.log_pos hy) (Real.log_pos hL)),
      le_div_iff₀ (Real.log_pos hL), ← Real.log_rpow hL0,
      Real.log_le_log_iff (Real.rpow_pos_of_pos hL0 _) (by linarith)]
  have hstrict : (k : ℝ) * Real.log (1 + 1 / x) <
      Real.log (Real.log (L + k * Real.log x)) - Real.log (Real.log L) ↔
      L ^ ((1 + 1 / x) ^ k) < L + k * Real.log x := by
    rw [← Real.log_pow, ← Real.log_div (Real.log_pos hy).ne' (Real.log_pos hL).ne',
      Real.log_lt_log_iff hp (div_pos (Real.log_pos hy) (Real.log_pos hL)),
      lt_div_iff₀ (Real.log_pos hL), ← Real.log_rpow hL0,
      Real.log_lt_log_iff (Real.rpow_pos_of_pos hL0 _) (by linarith)]
  constructor
  · rw [hweak]; dsimp [collectiveInsertionBarrier]; constructor <;> intro h <;> linarith
  · rw [hstrict]; dsimp [collectiveInsertionBarrier]; constructor <;> intro h <;> linarith

/-- Increasing the number of simultaneous insertions strictly raises the nonlinear root. -/
theorem collective_insertion_roots_strict_order {L β γ : ℝ} {k : ℕ}
    (hL : 1 < L) (hk : 1 ≤ k) (hβ : L < β) (hγ : L < γ)
    (hb : collectiveInsertionBarrier L k β = 0)
    (hc : collectiveInsertionBarrier L (k + 1) γ = 0) : β < γ := by
  have hβ1 := hL.trans hβ
  have ht := Real.log_pos hβ1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hx : 1 < L + (k : ℝ) * Real.log β := by nlinarith
  have hy : 1 < L + (k + 1 : ℝ) * Real.log β := by nlinarith
  have hs := loglog_strictConcaveOn.secant_strict_mono hL hx hy
    (by nlinarith : L + (k : ℝ) * Real.log β ≠ L)
    (by nlinarith : L + (k + 1 : ℝ) * Real.log β ≠ L)
    (by linarith : L + (k : ℝ) * Real.log β < L + (k + 1 : ℝ) * Real.log β)
  have hbeq : (k : ℝ) * Real.log (1 + 1 / β) =
      Real.log (Real.log (L + k * Real.log β)) - Real.log (Real.log L) := by
    have hw := (barrier_test k hL hβ1).1.mp (by rw [hb])
    have hn := (barrier_test k hL hβ1).2.not.mp (by rw [hb]; exact lt_irrefl 0)
    exact le_antisymm hw (le_of_not_gt hn)
  rw [show L + (k : ℝ) * Real.log β - L = (k : ℝ) * Real.log β by ring,
    show L + (k + 1 : ℝ) * Real.log β - L = (k + 1 : ℝ) * Real.log β by ring] at hs
  have hs' := (div_lt_div_iff₀ (mul_pos (by linarith : (0 : ℝ) < k + 1) ht)
    (mul_pos hk0 ht)).mp hs
  rw [← hbeq] at hs'
  have hnext : ¬ 0 ≤ collectiveInsertionBarrier L (k + 1) β := by
    intro hh
    have hw := (barrier_test (k + 1) hL hβ1).1.mp hh
    push_cast at hw
    have hw' := mul_le_mul_of_nonneg_right hw (mul_pos hk0 ht).le
    nlinarith only [hs', hw']
  have hm := barrier_strictMono hL (by omega : 1 ≤ k + 1)
  by_contra hn
  have hh := hm.monotoneOn (hL.trans hγ) hβ1 (le_of_not_gt hn)
  rw [hc] at hh
  exact hnext hh

private theorem payoff_strictConvex :
    StrictConvexOn ℝ Set.univ (fun t : ℝ => Real.log (1 + Real.exp (-t))) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Real.log (1 + Real.exp (-t)))
      (-(1 / (1 + Real.exp t))) t := by
    have he := (((hasDerivAt_id t).neg.exp).const_add 1).log
      (by positivity : 1 + Real.exp (-t) ≠ 0)
    convert he using 1
    · rfl
    · dsimp
      rw [Real.exp_neg]
      field_simp
      <;> ring
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_univ)
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
  intro x hx y hy hxy
  rw [(hd x).deriv, (hd y).deriv]
  have hh := one_div_lt_one_div_of_lt (by positivity : 0 < 1 + Real.exp x)
    (show 1 + Real.exp x < 1 + Real.exp y by linarith [Real.exp_lt_exp.mpr hxy])
  linarith

private theorem finite_W_increment {N : ℕ} (hN : 1 ≤ N) (S : Finset ℕ)
    (hp : ∀ p ∈ S, p.Prime) (hf : ∀ p ∈ S, ¬ p ∣ N) :
    W (N * ∏ p ∈ S, p) - W N = ∑ p ∈ S, Real.log (1 + 1 / (p : ℝ)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
    have hprime := hp p (Finset.mem_insert_self p S)
    have hps : ∀ q ∈ S, q.Prime := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    have hfs : ∀ q ∈ S, ¬ q ∣ N := fun q hq => hf q (Finset.mem_insert_of_mem hq)
    have hprod : 0 < ∏ q ∈ S, q := Finset.prod_pos (fun q hq => (hps q hq).pos)
    have hnot : ¬ p ∣ ∏ q ∈ S, q := hprime.prime.not_dvd_finsetProd (by
      intro q hq hd
      have he := (hps q hq).eq_one_or_self_of_dvd p hd
      rcases he with he | he
      · exact hprime.ne_one he
      · exact hpS (he ▸ hq))
    have hnotN := hf p (Finset.mem_insert_self p S)
    have hnotM : ¬ p ∣ N * ∏ q ∈ S, q := by
      rw [hprime.dvd_mul]
      exact not_or_intro hnotN hnot
    have hd := W_first_delta (by nlinarith : 1 ≤ N * ∏ q ∈ S, q) hprime
      (Nat.factorization_eq_zero_of_not_dvd hnotM)
    have hi := ih hps hfs
    rw [Finset.prod_insert hpS, Finset.sum_insert hpS,
      show N * (p * ∏ q ∈ S, q) = (N * ∏ q ∈ S, q) * p by ac_rfl]
    linarith

private theorem finite_clock {N : ℕ} (hN : 1 ≤ N) (S : Finset ℕ)
    (hp : ∀ p ∈ S, p.Prime) :
    Real.log (N * ∏ p ∈ S, p : ℕ) = Real.log (N : ℝ) + ∑ p ∈ S, Real.log (p : ℝ) := by
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (show N ≠ 0 by omega))
    (by exact_mod_cast (Finset.prod_ne_zero_iff.mpr (fun p hpS => (hp p hpS).ne_zero))),
    Nat.cast_prod, Real.log_prod (fun p hpS => by exact_mod_cast (hp p hpS).ne_zero)]

/-- The literal finite insertion comparison, using N times the product of actual distinct fresh primes. -/
theorem minimum_finite_fresh_insertion {N : ℕ} (hN : 5040 < N)
    (hmin : ∀ m : ℕ, 5040 < m → robinLogMargin N ≤ robinLogMargin m)
    (hL : 1 < Real.log (N : ℝ)) (S : Finset ℕ)
    (hp : ∀ p ∈ S, p.Prime) (hf : ∀ p ∈ S, ¬ p ∣ N) :
    (Real.log (N : ℝ)) ^ (∏ p ∈ S, (1 + 1 / (p : ℝ))) ≤
      Real.log (N : ℝ) + ∑ p ∈ S, Real.log (p : ℝ) := by
  have hprod : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p h => (hp p h).pos)
  have hM : 5040 < N * ∏ p ∈ S, p := by nlinarith
  have hw := finite_W_increment (by omega : 1 ≤ N) S hp hf
  have hc := finite_clock (by omega : 1 ≤ N) S hp
  have hm := hmin _ hM
  rw [margin_eq_threshold_sub_W, margin_eq_threshold_sub_W, hc] at hm
  dsimp [robinThreshold] at hm
  have hs0 : 0 ≤ ∑ p ∈ S, Real.log (p : ℝ) :=
    Finset.sum_nonneg (fun p h => (hp p h).log_pos.le)
  have hy : 1 < Real.log (N : ℝ) + ∑ p ∈ S, Real.log (p : ℝ) := by linarith
  have hpay : Real.log (∏ p ∈ S, (1 + 1 / (p : ℝ))) ≤
      Real.log (Real.log (Real.log N + ∑ p ∈ S, Real.log (p : ℝ))) -
        Real.log (Real.log (Real.log N)) := by
    rw [Real.log_prod (fun (p : ℕ) h => ne_of_gt (by
      have := (hp p h).pos
      positivity : 0 < 1 + 1 / (p : ℝ)))]
    linarith
  have hP : 0 < ∏ p ∈ S, (1 + 1 / (p : ℝ)) := Finset.prod_pos (fun p h => by
    have := (hp p h).pos
    positivity)
  rw [← Real.log_div (Real.log_pos hy).ne' (Real.log_pos hL).ne',
    Real.log_le_log_iff hP (div_pos (Real.log_pos hy) (Real.log_pos hL)),
    le_div_iff₀ (Real.log_pos hL)] at hpay
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos (by linarith : 0 < Real.log (N : ℝ)) _)
    (by linarith : 0 < Real.log (N : ℝ) + ∑ p ∈ S, Real.log (p : ℝ))).mp
  rwa [Real.log_rpow (by linarith : 0 < Real.log (N : ℝ))]

/-- Distinctness makes the log-payoff Jensen comparison strictly stronger than the equal-prime tuple. -/
private theorem strict_payoff_mean (S : Finset ℕ) (hk : 2 ≤ S.card)
    (hp : ∀ p ∈ S, p.Prime) :
    (S.card : ℝ) * Real.log
      (1 + 1 / Real.exp ((∑ p ∈ S, Real.log (p : ℝ)) / S.card)) <
        ∑ p ∈ S, Real.log (1 + 1 / (p : ℝ)) := by
  have hk0 : (0 : ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
  have hweights : ∑ _p ∈ S, (1 / (S.card : ℝ)) = 1 := by
    simp [hk0.ne']
  have hne : ∃ p ∈ S, ∃ q ∈ S, Real.log (p : ℝ) ≠ Real.log (q : ℝ) := by
    obtain ⟨p, hps, q, hqs, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    refine ⟨p, hps, q, hqs, ?_⟩
    intro he
    have he' : (p : ℝ) = (q : ℝ) := Real.log_injOn_pos
      (by change (0 : ℝ) < p; exact_mod_cast (hp p hps).pos)
      (by change (0 : ℝ) < q; exact_mod_cast (hp q hqs).pos) he
    exact hpq (Nat.cast_injective he')
  have hj := payoff_strictConvex.map_sum_lt (t := S) (w := fun _ : ℕ => 1 / (S.card : ℝ))
    (p := fun p : ℕ => Real.log (p : ℝ)) (fun _ _ => one_div_pos.mpr hk0) hweights
    (fun _ _ => Set.mem_univ _) hne
  simp only [smul_eq_mul, ← Finset.mul_sum] at hj
  have hterms : ∑ p ∈ S, Real.log (1 + Real.exp (-Real.log (p : ℝ))) =
      ∑ p ∈ S, Real.log (1 + 1 / (p : ℝ)) := by
    apply Finset.sum_congr rfl
    intro p hps
    rw [Real.exp_neg, Real.exp_log (Nat.cast_pos.mpr (hp p hps).pos), one_div]
  rw [hterms] at hj
  have he : -(1 / (S.card : ℝ) * ∑ p ∈ S, Real.log (p : ℝ)) =
      -((∑ p ∈ S, Real.log (p : ℝ)) / S.card) := by ring
  rw [he, Real.exp_neg] at hj
  have hmul := mul_lt_mul_of_pos_left hj hk0
  convert hmul using 1 <;> field_simp <;> ring

/-- Distinct actual fresh-prime sets with at least two members have mean strictly above the root. -/
theorem fresh_tuple_mean_gt_root {N : ℕ} {β : ℝ} (hN : 5040 < N)
    (hmin : ∀ m : ℕ, 5040 < m → robinLogMargin N ≤ robinLogMargin m)
    (hL : 1 < Real.log (N : ℝ)) (S : Finset ℕ) (hk : 2 ≤ S.card)
    (hp : ∀ p ∈ S, p.Prime) (hf : ∀ p ∈ S, ¬ p ∣ N)
    (hβ : Real.log (N : ℝ) < β)
    (hroot : collectiveInsertionBarrier (Real.log N) S.card β = 0) :
    β < Real.exp ((∑ p ∈ S, Real.log (p : ℝ)) / S.card) := by
  let G := Real.exp ((∑ p ∈ S, Real.log (p : ℝ)) / S.card)
  have hk0 : (0 : ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
  have hsum : 0 < ∑ p ∈ S, Real.log (p : ℝ) := Finset.sum_pos
    (fun p h => (hp p h).log_pos) (Finset.card_pos.mp (by omega))
  have hG : 1 < G := Real.one_lt_exp_iff.mpr (div_pos hsum hk0)
  have hj := strict_payoff_mean S hk hp
  have hi := minimum_finite_fresh_insertion hN hmin hL S hp hf
  have hL0 : 0 < Real.log (N : ℝ) := by linarith
  have hy : 1 < Real.log (N : ℝ) + ∑ p ∈ S, Real.log (p : ℝ) := by linarith
  have hP : 0 < ∏ p ∈ S, (1 + 1 / (p : ℝ)) := Finset.prod_pos (fun p h => by
    have := (hp p h).pos
    positivity)
  have hpay : ∑ p ∈ S, Real.log (1 + 1 / (p : ℝ)) ≤
      Real.log (Real.log (Real.log N + ∑ p ∈ S, Real.log (p : ℝ))) -
        Real.log (Real.log (Real.log N)) := by
    have hh := (Real.log_le_log_iff (Real.rpow_pos_of_pos hL0 _) (by linarith)).mpr hi
    rw [Real.log_rpow hL0] at hh
    have hd := (le_div_iff₀ (Real.log_pos hL)).mpr hh
    have hl := (Real.log_le_log_iff hP (div_pos (Real.log_pos hy) (Real.log_pos hL))).mpr hd
    rw [Real.log_prod (fun (p : ℕ) h => ne_of_gt (by
      have := (hp p h).pos
      positivity : 0 < 1 + 1 / (p : ℝ))),
      Real.log_div (Real.log_pos hy).ne' (Real.log_pos hL).ne'] at hl
    exact hl
  have hclock : (S.card : ℝ) * Real.log G = ∑ p ∈ S, Real.log (p : ℝ) := by
    dsimp [G]
    rw [Real.log_exp]
    field_simp
  have hpos : 0 < collectiveInsertionBarrier (Real.log N) S.card G := by
    apply (barrier_test S.card hL hG).2.mpr
    rw [hclock]
    exact hj.trans_le hpay
  by_contra hn
  have hm := (barrier_strictMono hL (by omega : 1 ≤ S.card)).monotoneOn hG
    (hL.trans hβ) (le_of_not_gt hn)
  rw [hroot] at hm
  linarith

/-- Exact initial support turns the strict geometric-mean test into a RIGHT-CLOSED prime bound. -/
theorem fresh_prime_closed_cutoff_card_lt {N k : ℕ} {z β : ℝ}
    (hN : 5040 < N) (hmin : ∀ m : ℕ, 5040 < m → robinLogMargin N ≤ robinLogMargin m)
    (hL : 1 < Real.log (N : ℝ)) (hz : 0 ≤ z)
    (hsupport : N.primeFactors = Nat.primesLE ⌊z⌋₊) (hk : 2 ≤ k)
    (hβ : Real.log (N : ℝ) < β) (hroot : collectiveInsertionBarrier (Real.log N) k β = 0) :
    ((Nat.primesLE ⌊β⌋₊).filter (fun (p : ℕ) => z < (p : ℝ))).card < k := by
  classical
  by_contra hn
  obtain ⟨S, hST, hcard⟩ := Finset.exists_subset_card_eq (le_of_not_gt hn)
  have hmem (p : ℕ) (hpS : p ∈ S) : p.Prime ∧ z < (p : ℝ) ∧ (p : ℝ) ≤ β := by
    have hm := Finset.mem_filter.mp (hST hpS)
    have hprime := Nat.mem_primesLE.mp hm.1
    exact ⟨hprime.2, hm.2, (Nat.cast_le.mpr hprime.1).trans
      (Nat.floor_le (by linarith : 0 ≤ β))⟩
  have hprime : ∀ p ∈ S, p.Prime := fun p h => (hmem p h).1
  have hfresh : ∀ p ∈ S, ¬ p ∣ N := by
    intro p hpS hd
    have hfac := (hprime p hpS).mem_primeFactors hd (by omega : N ≠ 0)
    rw [hsupport] at hfac
    have hle := (Nat.cast_le.mpr (Nat.mem_primesLE.mp hfac).1).trans (Nat.floor_le hz)
    exact (not_lt_of_ge hle) (hmem p hpS).2.1
  have hrootS : collectiveInsertionBarrier (Real.log N) S.card β = 0 := by rwa [hcard]
  have hmean := fresh_tuple_mean_gt_root hN hmin hL S (by omega) hprime hfresh hβ hrootS
  have hsum : (∑ p ∈ S, Real.log (p : ℝ)) ≤ (S.card : ℝ) * Real.log β := by
    calc
      _ ≤ ∑ _p ∈ S, Real.log β := Finset.sum_le_sum (fun p hpS =>
        Real.log_le_log (Nat.cast_pos.mpr (hprime p hpS).pos) (hmem p hpS).2.2)
      _ = _ := by simp
  have hk0 : (0 : ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
  have hquot : (∑ p ∈ S, Real.log (p : ℝ)) / S.card ≤ Real.log β :=
    (div_le_iff₀ hk0).mpr (by nlinarith only [hsum])
  have hbound := Real.exp_le_exp.mpr hquot
  rw [Real.exp_log (by linarith : 0 < β)] at hbound
  linarith

/-- All collective restrictions keep the original integer, cutoff and singleton endpoint. -/
def CollectivePrimeRestrictions (N : ℕ) (z β : ℝ) : Prop :=
  ∃ b : ℕ → ℝ, b 1 = β ∧
    (∀ k : ℕ, 1 ≤ k → Real.log N < b k ∧
      collectiveInsertionBarrier (Real.log N) k (b k) = 0 ∧
      (∀ x : ℝ, 1 < x → collectiveInsertionBarrier (Real.log N) k x = 0 → x = b k) ∧
      (∀ x : ℝ, 1 < x → (collectiveInsertionBarrier (Real.log N) k x < 0 ↔ x < b k)) ∧
      (∀ x : ℝ, 1 < x → (0 < collectiveInsertionBarrier (Real.log N) k x ↔ b k < x))) ∧
    (∀ k : ℕ, 1 ≤ k → b k < b (k + 1)) ∧
    (∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p ∈ S, ¬ p ∣ N) →
      (Real.log N) ^ (∏ p ∈ S, (1 + 1 / (p : ℝ))) ≤
        Real.log N + ∑ p ∈ S, Real.log (p : ℝ)) ∧
    (∀ S : Finset ℕ, 2 ≤ S.card → (∀ p ∈ S, p.Prime) → (∀ p ∈ S, ¬ p ∣ N) →
      b S.card < Real.exp ((∑ p ∈ S, Real.log (p : ℝ)) / S.card)) ∧
    (∀ k : ℕ, 2 ≤ k →
      ((Nat.primesLE ⌊b k⌋₊).filter (fun (p : ℕ) => z < (p : ℝ))).card < k)

/-- The sole original nonpositive failure preserves its full optimizer/nonlinear-gap bundle
and strengthens that SAME N,z with simultaneous fresh-prime restrictions. -/
theorem failure_has_collective_prime_restrictions
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
      ∃ α β : ℝ, NonlinearPrimeGap N z α β ∧ CollectivePrimeRestrictions N z β := by
  classical
  obtain ⟨N, z, hN, hSN, hmin, hp0, hpb, hopt, hstrict, hNs, hNm, hnotie,
    hz, hM0, hMhalf, hroot, hunique, hsupport, α, β, hgap⟩ :=
    failure_has_nonlinear_prime_gap hfailure
  have hL : 1 < Real.log (N : ℝ) := by linarith
  let b : ℕ → ℝ := fun k => if hk : 1 ≤ k then
    Classical.choose (collective_insertion_root_exists_unique hL hk) else 0
  have hb (k : ℕ) (hk : 1 ≤ k) := Classical.choose_spec
    (collective_insertion_root_exists_unique hL hk)
  have hb' (k : ℕ) (hk : 1 ≤ k) : Real.log N < b k ∧
      collectiveInsertionBarrier (Real.log N) k (b k) = 0 ∧
      (∀ x : ℝ, 1 < x → collectiveInsertionBarrier (Real.log N) k x = 0 → x = b k) ∧
      (∀ x : ℝ, 1 < x → (collectiveInsertionBarrier (Real.log N) k x < 0 ↔ x < b k)) ∧
      (∀ x : ℝ, 1 < x → (0 < collectiveInsertionBarrier (Real.log N) k x ↔ b k < x)) := by
    simpa only [b, dite_eq_left hk] using hb k hk
  have hb1 := hb' 1 (by omega)
  have hsingle : insertionBarrier (Real.log N) (b 1) = 0 := by
    have he := hb1.2.1
    simp only [collectiveInsertionBarrier, pow_one, Nat.cast_one, one_mul] at he
    dsimp [insertionBarrier]
    linarith only [he]
  have hgap_keep := hgap
  obtain ⟨hαlo, hαz, hzL, hLβ, hαroot, hβroot, huα, huβ, hprimes⟩ := hgap
  have hsame : b 1 = β := huβ _ (hL.trans hb1.1) hsingle
  refine ⟨N, z, hN, hSN, hmin, hp0, hpb, hopt, hstrict, hNs, hNm, hnotie,
    hz, hM0, hMhalf, hroot, hunique, hsupport, α, β, hgap_keep, b, hsame, hb', ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact collective_insertion_roots_strict_order hL hk (hb' k hk).1
      (hb' (k + 1) (by omega)).1 (hb' k hk).2.1 (hb' (k + 1) (by omega)).2.1
  · intro S hp hf
    exact minimum_finite_fresh_insertion (by omega) hmin hL S hp hf
  · intro S hk hp hf
    exact fresh_tuple_mean_gt_root (by omega) hmin hL S hk hp hf
      (hb' S.card (by omega)).1 (hb' S.card (by omega)).2.1
  · intro k hk
    exact fresh_prime_closed_cutoff_card_lt (by omega) hmin hL (by linarith) hsupport hk
      (hb' k (by omega)).1 (hb' k (by omega)).2.1

#print axioms failure_has_collective_prime_restrictions

end D5.S3.Arith.Robin.PriceRecord.CollectivePrimeInsertion
