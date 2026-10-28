/- GID: D5/S3/Arith/Robin/EulerLayerRootCorrection
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/EulerLayerRootCorrection
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Third-layer vanishing is proved; the exact strict Euler inventory root-scale correction remains open. -/

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

private theorem prime_number_limits :
    Tendsto (fun t : ℝ => ψ t / t) atTop (𝓝 1) ∧
      Tendsto (fun t : ℝ => θ t / t) atTop (𝓝 1) := by
  obtain ⟨c, hc, hpnt⟩ := MediumPNT
  have hexp : Tendsto (fun t : ℝ => Real.exp (-c * Real.log t ^ (1 / 10 : ℝ)))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hc)).mpr
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
        Real.tendsto_log_atTop))
  have hsmall : (fun t : ℝ => t * Real.exp (-c * Real.log t ^ (1 / 10 : ℝ)))
      =o[atTop] (fun t => t) := by
    simpa using (isBigO_refl (fun t : ℝ => t) atTop).mul_isLittleO
      ((isLittleO_one_iff ℝ).mpr hexp)
  have hpsi := (hpnt.trans_isLittleO hsmall).tendsto_div_nhds_zero
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt t / t) atTop (𝓝 0) := by
    simpa only [Real.sqrt_div_self, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop)
  have hsqrto : Real.sqrt =o[atTop] (fun t : ℝ => t) :=
    isLittleO_of_tendsto (fun t ht => by simp [ht]) hsqrt
  have htail := (Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsqrto).tendsto_div_nhds_zero
  have hp : Tendsto (fun t : ℝ => ψ t / t) atTop (𝓝 1) := by
    have h := hpsi.add_const 1
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [Pi.sub_apply, id_eq]
    field_simp
    <;> ring
  refine ⟨hp, ?_⟩
  have h := hp.sub htail
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [Pi.sub_apply]
  ring

private theorem theta_sqrt_scale {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => θ (c * Real.sqrt t) / Real.sqrt t) atTop (𝓝 c) := by
  have h := (prime_number_limits.2.comp
    (Real.tendsto_sqrt_atTop.const_mul_atTop hc)).mul_const c
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  field_simp

private theorem psi_small_power {r : ℝ} (hr : 0 < r) (hr2 : r < 1 / 2) :
    Tendsto (fun t : ℝ => ψ (t ^ r) / Real.sqrt t) atTop (𝓝 0) := by
  have h := (prime_number_limits.1.comp (tendsto_rpow_atTop hr)).mul
    (tendsto_rpow_neg_atTop (sub_pos.mpr hr2))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.sqrt_eq_rpow, neg_sub, Real.rpow_sub ht]
  field_simp

private theorem psi_theta_root_limit :
    Tendsto (fun t : ℝ => (ψ t - θ t) / Real.sqrt t) atTop (𝓝 1) := by
  have hroot : Tendsto (fun t : ℝ => ψ (t ^ (2 : ℝ)⁻¹) / Real.sqrt t)
      atTop (𝓝 1) := by
    simpa [Real.sqrt_eq_rpow, one_div] using
      prime_number_limits.1.comp Real.tendsto_sqrt_atTop
  have h3 := psi_small_power (r := (3 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have h5 := psi_small_power (r := (5 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have h7 := psi_small_power (r := (7 : ℝ)⁻¹) (by norm_num) (by norm_num)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using (hroot.add h3).add h7)
    (by simpa using (hroot.add h3).add h5)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simpa [add_div] using div_le_div_of_nonneg_right
      (Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi ht) (Real.sqrt_nonneg t)
  · filter_upwards [] with t
    simpa [add_div] using div_le_div_of_nonneg_right
      (Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi t) (Real.sqrt_nonneg t)

private theorem second_cutoff_scale {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ =>
      (((c * Real.sqrt t) ^ 2 + c * Real.sqrt t + 1) / t) *
        (Real.log (c * Real.sqrt t) / Real.log t)) atTop (𝓝 (c ^ 2 / 2)) := by
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt t / t) atTop (𝓝 0) := by
    simpa only [Real.sqrt_div_self, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop)
  have hinv : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  have hpoly : Tendsto (fun t : ℝ => ((c * Real.sqrt t) ^ 2 + c * Real.sqrt t + 1) / t)
      atTop (𝓝 (c ^ 2)) := by
    have h := ((tendsto_const_nhds (x := c ^ 2)).add (hsqrt.const_mul c)).add hinv
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hs := Real.sq_sqrt ht.le
    field_simp
    nlinarith
  have hlog : Tendsto (fun t : ℝ => Real.log (c * Real.sqrt t) / Real.log t)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have h := (tendsto_const_nhds (x := Real.log c)).div_atTop Real.tendsto_log_atTop
    have h := h.add_const (1 / 2 : ℝ)
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    rw [Real.log_mul (ne_of_gt hc) (ne_of_gt (Real.sqrt_pos.2 (by linarith))),
      Real.log_sqrt (by linarith)]
    field_simp
    <;> ring
  simpa [div_eq_mul_inv] using hpoly.mul hlog

/-!
The paper/theory target is retained verbatim as a proposition. No theorem is
claimed here: the missing proof must establish the uniform second-layer cutoff
at `sqrt 2 * sqrt t` and the root-scale Costa--Pereira limit for `psi - theta`.
The complete actual layers at least three are supplied by the preceding
vanishing theorem.
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
