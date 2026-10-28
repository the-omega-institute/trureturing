/- GID: D5/S3/Arith/Robin/EulerLayerRootCorrection
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/EulerLayerRootCorrection
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Exact target statement for the strict Euler inventory root-scale correction; proof open. -/

import D5.S3.Arith.Robin.EulerLayerInventoryGrowth

namespace D5.S3.Arith.Robin.EulerLayerRootCorrection

open Finset Filter Asymptotics
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenLayerMarginalDecay
open scoped Chebyshev Topology

noncomputable section

def strict_inventory_third_layer_mass (U : ℕ) : ℝ :=
  ∑ q ∈ U.primeFactors.filter (fun q => 3 ≤ U.factorization q),
    ((U.factorization q - 2 : ℕ) : ℝ) * Real.log q

/- The complete contribution of layers at least three has the explicit finite
   envelope needed for the root-scale argument. -/
theorem strict_inventory_third_layer_bound {t : ℝ} (ht : 2 ≤ t) {U : ℕ}
    (hU : 0 < U)
    (hstrict : ∀ q : ℕ, q.Prime →
      U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) :
    strict_inventory_third_layer_mass U ≤
      ((3 * t) ^ (1 / 3 : ℝ) + 1) *
        Real.log (t * Real.log t / Real.log 2) := by
  let S := U.primeFactors.filter (fun q => 3 ≤ U.factorization q)
  let B := Real.log (t * Real.log t / Real.log 2)
  have ht0 : 0 < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hquot : 1 < t * Real.log t / Real.log 2 := by
    have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) (by linarith)
    have hmul : 2 * Real.log 2 ≤ t * Real.log t := by
      exact mul_le_mul ht hlt (Real.log_nonneg (by norm_num)) (by positivity)
    have htwo : (1 : ℝ) < 2 := by norm_num
    apply (lt_div_iff₀ hlog2).mpr
    nlinarith
  have hB : 0 ≤ B := Real.log_nonneg hquot.le
  have hterm (q : ℕ) (hqS : q ∈ S) :
      ((U.factorization q - 2 : ℕ) : ℝ) * Real.log q ≤ B := by
    have hqU : q ∈ U.primeFactors := (mem_filter.mp hqS).1
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqU
    have he : 3 ≤ U.factorization q := (mem_filter.mp hqS).2
    have hqa : 1 ≤ U.factorization q := by omega
    have hbound := EulerLayerInventoryGrowth.active_power_bound
      (show 1 < t by linarith) hstrict hq hqa (k := U.factorization q) le_rfl
    have hlogq : 0 < Real.log (q : ℝ) :=
      Real.log_pos (by exact_mod_cast hq.one_lt)
    have hlog2q : Real.log 2 ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hq.two_le)
    have hpowlog : (q : ℝ) ^ U.factorization q * Real.log 2 < t * Real.log t :=
      (mul_le_mul_of_nonneg_left hlog2q (pow_nonneg (by positivity) _)).trans_lt hbound
    have hpow : (q : ℝ) ^ U.factorization q < t * Real.log t / Real.log 2 :=
      (lt_div_iff₀ hlog2).mpr hpowlog
    have hqpowpos : 0 < (q : ℝ) ^ U.factorization q :=
      pow_pos (by exact_mod_cast hq.pos) _
    have hlogged := Real.strictMonoOn_log hqpowpos
      (div_pos (mul_pos ht0 hlogt) hlog2) hpow
    have helog : (U.factorization q : ℝ) * Real.log q < B := by
      simpa [B, Real.log_pow] using hlogged
    have hsub : ((U.factorization q - 2 : ℕ) : ℝ) ≤ (U.factorization q : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    rw [Nat.cast_sub (by omega)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsub) hlogq.le]
  have hqroot (q : ℕ) (hqS : q ∈ S) :
      (q : ℝ) < (3 * t) ^ (1 / 3 : ℝ) := by
    have hqU : q ∈ U.primeFactors := (mem_filter.mp hqS).1
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqU
    have he : 3 ≤ U.factorization q := (mem_filter.mp hqS).2
    have hpow := EulerLayerInventoryGrowth.active_power_linear_cutoff ht hstrict hq
      (k := 3) (by norm_num) he
    apply (Real.rpow_lt_rpow_iff (by positivity) (by positivity)
      (by norm_num : (0 : ℝ) < 3)).mp
    have hpowR : (q : ℝ) ^ (3 : ℝ) < 3 * t := by
      calc
        (q : ℝ) ^ (3 : ℝ) = (q : ℝ) ^ (3 : ℕ) := by
          norm_num [Real.rpow_natCast]
        _ < 3 * t := by simpa using hpow
    have hyR : ((3 * t) ^ (1 / 3 : ℝ)) ^ (3 : ℝ) = 3 * t := by
      have hy := Real.rpow_inv_natCast_pow (x := 3 * t) (n := 3)
        (by positivity) (by norm_num)
      convert hy using 1 <;> norm_num [Real.rpow_natCast]
    exact hpowR.trans_eq hyR.symm
  have hcard : (S.card : ℝ) ≤ (3 * t) ^ (1 / 3 : ℝ) + 1 := by
    have hsub : S ⊆ Finset.range (⌊(3 * t) ^ (1 / 3 : ℝ)⌋₊ + 1) := by
      intro q hqS
      rw [Finset.mem_range]
      exact_mod_cast (hqroot q hqS).trans (Nat.lt_floor_add_one _)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_range] at hc
    have hfloor : (⌊(3 * t) ^ (1 / 3 : ℝ)⌋₊ : ℝ) ≤ (3 * t) ^ (1 / 3 : ℝ) :=
      Nat.floor_le (by positivity)
    have hcR : (S.card : ℝ) ≤ (⌊(3 * t) ^ (1 / 3 : ℝ)⌋₊ : ℝ) + 1 := by
      exact_mod_cast hc
    nlinarith [hcR, hfloor]
  have hsum := Finset.sum_le_card_nsmul S
    (fun q => ((U.factorization q - 2 : ℕ) : ℝ) * Real.log q) B hterm
  change (∑ q ∈ S, ((U.factorization q - 2 : ℕ) : ℝ) * Real.log q) ≤ _
  have hsumR : (∑ q ∈ S, ((U.factorization q - 2 : ℕ) : ℝ) * Real.log q) ≤
      (S.card : ℝ) * B := by
    simpa [nsmul_eq_mul] using hsum
  simpa [S, B] using
    (hsumR.trans (mul_le_mul_of_nonneg_right hcard hB))

theorem strict_inventory_third_layer_vanishing :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t → ∀ U : ℕ, 0 < U →
      (∀ q : ℕ, q.Prime →
        U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
      strict_inventory_third_layer_mass U / Real.sqrt t < ε := by
  have hlog2lower : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hrootcoeff : (3 : ℝ) ^ (1 / 3 : ℝ) ≤ 3 := by
    calc
      (3 : ℝ) ^ (1 / 3 : ℝ) ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 3 := by norm_num
  have hscale : ∀ᶠ t : ℝ in atTop,
      ((3 * t) ^ (1 / 3 : ℝ) + 1) * Real.log (t * Real.log t / Real.log 2) /
          Real.sqrt t ≤ 240 * t ^ (-(7 / 60 : ℝ)) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hlogtle : Real.log t ≤ t := Real.log_le_self ht0.le
    have hargpos : 0 < t * Real.log t / Real.log 2 :=
      div_pos (mul_pos ht0 hlogt) (Real.log_pos (by norm_num))
    have hlogtle' : Real.log t < t := by
      exact (Real.log_lt_sub_one_of_pos ht0 (by linarith)).trans_le (by linarith)
    have hargle : t * Real.log t / Real.log 2 < 2 * t ^ 2 := by
      apply (div_lt_iff₀ (Real.log_pos (by norm_num))).mpr
      nlinarith [hlog2lower]
    have hlogarg : Real.log (t * Real.log t / Real.log 2) ≤
        60 * t ^ (1 / 20 : ℝ) := by
      have htargetpos : 0 < 2 * t ^ 2 := by positivity
      have hmono := Real.strictMonoOn_log hargpos htargetpos hargle
      have hrewrite : Real.log (2 * t ^ 2) = Real.log 2 + 2 * Real.log t := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        norm_num
      have hlog2t : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) (by linarith)
      have hlogarg' : Real.log (t * Real.log t / Real.log 2) ≤ 3 * Real.log t := by
        calc
          _ ≤ Real.log (2 * t ^ 2) := hmono.le
          _ = Real.log 2 + 2 * Real.log t := hrewrite
          _ ≤ 3 * Real.log t := by linarith
      have hlogpow := Real.log_le_rpow_div ht0.le (by norm_num : (0 : ℝ) < 1 / 20)
      have hlogpow' : Real.log t ≤ 20 * t ^ (1 / 20 : ℝ) := by
        calc
          _ ≤ t ^ (1 / 20 : ℝ) / (1 / 20 : ℝ) := hlogpow
          _ = 20 * t ^ (1 / 20 : ℝ) := by field_simp
      calc
        _ ≤ 3 * Real.log t := hlogarg'
        _ ≤ 3 * (20 * t ^ (1 / 20 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hlogpow' (by norm_num)
        _ = 60 * t ^ (1 / 20 : ℝ) := by ring
    have hroot : (3 * t) ^ (1 / 3 : ℝ) + 1 ≤ 4 * t ^ (1 / 3 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) ht0.le]
      have htroot : 1 ≤ t ^ (1 / 3 : ℝ) := by
        exact Real.one_le_rpow (by linarith) (by norm_num)
      nlinarith [hrootcoeff]
    have hnum : ((3 * t) ^ (1 / 3 : ℝ) + 1) *
        Real.log (t * Real.log t / Real.log 2) ≤
        240 * t ^ (23 / 60 : ℝ) := by
      have hpowpos : 0 ≤ t ^ (1 / 3 : ℝ) := by positivity
      have hlog2t : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) (by linarith)
      have hmul2 : 2 * Real.log 2 ≤ t * Real.log t :=
        mul_le_mul ht hlog2t (Real.log_nonneg (by norm_num)) (by positivity)
      have hargone : 1 ≤ t * Real.log t / Real.log 2 := by
        apply (le_div_iff₀ (Real.log_pos (by norm_num))).mpr
        nlinarith [hmul2]
      have hlogpos : 0 ≤ Real.log (t * Real.log t / Real.log 2) := by
        exact Real.log_nonneg hargone
      have hmul := mul_le_mul hroot hlogarg hlogpos (by positivity)
      have hpow := Real.rpow_add ht0 (1 / 3 : ℝ) (1 / 20 : ℝ)
      nlinarith
    have hdiv := div_le_div_of_nonneg_right hnum (Real.sqrt_pos.2 ht0).le
    have hsqrt : Real.sqrt t = t ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow t
    calc
      _ ≤ 240 * t ^ (23 / 60 : ℝ) / t ^ (1 / 2 : ℝ) := by simpa [hsqrt] using hdiv
      _ = 240 * t ^ (-(7 / 60 : ℝ)) := by
        rw [mul_div_assoc, ← Real.rpow_sub ht0]
        congr 1
        ring_nf
  intro ε hε
  have hpowlim : Tendsto (fun t : ℝ => 240 * t ^ (-(7 / 60 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 60)).const_mul 240
  have hevent := hpowlim.eventually_lt_const hε
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hevent.and hscale)
  refine ⟨max T 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro t ht U hU hstrict
  have ht2 : 2 ≤ t := (le_max_right T 2).trans ht
  have hmass := strict_inventory_third_layer_bound ht2 hU hstrict
  have hratio := div_le_div_of_nonneg_right hmass
    (Real.sqrt_pos.2 (show 0 < t by linarith)).le
  have hT' := hT t ((le_max_left T 2).trans ht)
  exact hratio.trans_lt (hT'.2.trans_lt hT'.1)

/-!
The paper/theory target is retained verbatim as a proposition. No theorem is
claimed here: the missing proof must establish the uniform second-layer cutoff
at `sqrt 2 * sqrt t`, the vanishing of all actual layers at least three, and
the root-scale Costa--Pereira limit for `psi - theta`.
-/
def strict_inventory_root_correction_statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t → ∀ U : ℕ, 0 < U →
    (∀ q : ℕ, q.Prime →
      U.factorization q =
        D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount.optimalLayerCount
          (1 / (t * Real.log t)) q) →
    |(Real.log U - Chebyshev.psi t) / Real.sqrt t - (Real.sqrt 2 - 1)| < ε

end

end D5.S3.Arith.Robin.EulerLayerRootCorrection
