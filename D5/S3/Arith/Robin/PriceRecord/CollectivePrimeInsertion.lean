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
  have hx : 1 < L + (k : ℝ) * Real.log β := by positivity; nlinarith
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
    nlinarith
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
    rw [Real.exp_neg]
    field_simp
    <;> ring
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_univ)
    (by fun_prop)
  intro x hx y hy hxy
  rw [(hd x).deriv, (hd y).deriv]
  have hh := one_div_lt_one_div_of_lt (by positivity : 0 < 1 + Real.exp x)
    (add_lt_add_left (Real.exp_lt_exp.mpr hxy) 1)
  linarith

end D5.S3.Arith.Robin.PriceRecord.CollectivePrimeInsertion
