/- GID: D5/S3/Arith/Robin/ActualIntegerHeightJump
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualIntegerHeightJump
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Maximal occupied prime powers control actual Robin height jumps and first crossings. -/

import D5.S3.Arith.Robin.ActualIntegerLogEnvelope
import D5.S3.Arith.GoldenResource.GoldenResourcePriceInterval
import Mathlib.Data.Finset.Max

/-! All heights and quotients below are those of actual natural integers. Unbounded height,
when used for a first crossing, is an explicit hypothesis rather than an oscillation theorem. -/

noncomputable section

namespace D5.S3.Arith.Robin.ActualIntegerHeightJump

open Finset Filter
open scoped Topology
open D5.S3.Arith.Robin.OriginalFirstClockTransport
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.GoldenLayerMarginalDecay
open D5.S3.Arith.Robin.ActualIntegerLogEnvelope

/-- The actual logarithmic divisor-sum ratio, totalized at zero. -/
def divisorLog (n : ℕ) : ℝ := Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n)

/-- The original scaled Robin excess on natural integers. -/
def actualHeight (eta : ℝ) (n : ℕ) : ℝ :=
  (Real.log (n : ℝ)) ^ eta * (originalObjective n - Real.eulerMascheroniConstant)

/-- Every maximizing prime is allowed, including ties between occupied prime powers. -/
def MaximalPrimePower (m q : ℕ) : Prop :=
  q ∈ m.primeFactors ∧ ∀ p ∈ m.primeFactors,
    p ^ m.factorization p ≤ q ^ m.factorization q

private theorem maximal_exists {m : ℕ} (hm : 1 < m) :
    ∃ q, MaximalPrimePower m q := by
  have hne : m.primeFactors.Nonempty := by
    rw [Nat.nonempty_primeFactors]
    omega
  obtain ⟨q, hq, hmax⟩ := exists_max_image m.primeFactors
    (fun p => p ^ m.factorization p) hne
  exact ⟨q, hq, hmax⟩

private theorem maximal_clock_bound {m q : ℕ} (hm : 0 < m)
    (hq : MaximalPrimePower m q) :
    Real.log (m : ℝ) ≤ (q : ℝ) ^ m.factorization q *
      Real.log ((q : ℝ) ^ m.factorization q) := by
  let Q := q ^ m.factorization q
  have hprime := Nat.prime_of_mem_primeFactors hq.1
  have ha : 1 ≤ m.factorization q :=
    hprime.factorization_pos_of_dvd hm.ne' (Nat.dvd_of_mem_primeFactors hq.1)
  have hqQ : q ≤ Q := Nat.le_self_pow (by omega) q
  have hQ : 1 ≤ Q := hprime.one_lt.le.trans hqQ
  have hsub : m.primeFactors ⊆ Icc 1 Q := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hap := hpp.factorization_pos_of_dvd hm.ne' (Nat.dvd_of_mem_primeFactors hp)
    exact mem_Icc.mpr ⟨hpp.pos, (Nat.le_self_pow (by omega) p).trans (hq.2 p hp)⟩
  have hcard : m.primeFactors.card ≤ Q := by
    have := card_le_card hsub
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using this
  have hsum : Real.log (m : ℝ) ≤ (m.primeFactors.card : ℝ) * Real.log (Q : ℝ) := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
    rw [Nat.support_factorization]
    calc
      _ ≤ ∑ p ∈ m.primeFactors, Real.log (Q : ℝ) := by
        apply sum_le_sum
        intro p hp
        rw [← Real.log_pow]
        apply Real.log_le_log
        · exact pow_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos) _
        · exact_mod_cast hq.2 p hp
      _ = _ := by simp
  have hQR : (Q : ℝ) = (q : ℝ) ^ m.factorization q := by simp [Q]
  rw [← hQR]
  exact hsum.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
    (Real.log_nonneg (by exact_mod_cast hQ)))

private theorem removal_delta {m q : ℕ} (hm : 0 < m)
    (hq : q ∈ m.primeFactors) :
    0 < m / q ∧ m / q < m ∧
      0 < divisorLog m - divisorLog (m / q) ∧
      divisorLog m - divisorLog (m / q) ≤ ((q : ℝ) ^ m.factorization q)⁻¹ := by
  have hp := Nat.prime_of_mem_primeFactors hq
  have hd := Nat.dvd_of_mem_primeFactors hq
  have hn : 0 < m / q := Nat.div_pos (Nat.le_of_dvd hm hd) hp.pos
  have heq : m / q * q = m := Nat.div_mul_cancel hd
  have hfac : (m / q).factorization q + 1 = m.factorization q := by
    have h := congrArg (fun n : ℕ => n.factorization q) heq
    simpa [Nat.factorization_mul hn.ne' hp.ne_zero, hp.factorization] using h
  have h := golden_resource_objective_single_layer_delta 0 (by omega : 1 ≤ m / q) hp
  rw [heq, golden_resource_sigma_identity 0 (by omega : 1 ≤ m),
    golden_resource_sigma_identity 0 (by omega : 1 ≤ m / q)] at h
  simp only [zero_mul, sub_zero, hfac] at h
  change divisorLog m - divisorLog (m / q) = _ at h
  have ha : 1 ≤ m.factorization q := by omega
  have hlq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  refine ⟨hn, Nat.div_lt_self hm hp.one_lt, ?_, ?_⟩
  · rw [h]
    exact mul_pos (D5.S3.Arith.GoldenResource.GoldenResourcePriceInterval.marginal_pos hp ha) hlq
  · rw [h]
    have hb := mul_le_mul_of_nonneg_right (golden_layer_marginal_le_inv_pow hp ha) hlq.le
    simpa only [div_mul_cancel₀ _ hlq.ne', inv_pow] using hb

private theorem delta_clock_bound {m q : ℕ} (hm : 0 < m)
    (hX : Real.exp 1 ≤ Real.log (m : ℝ)) (hq : MaximalPrimePower m q) :
    divisorLog m - divisorLog (m / q) ≤
      Real.log (Real.log (m : ℝ)) / Real.log (m : ℝ) := by
  let X := Real.log (m : ℝ)
  let Q : ℝ := (q : ℝ) ^ m.factorization q
  have hp := Nat.prime_of_mem_primeFactors hq.1
  have hQ : 0 < Q := pow_pos (by exact_mod_cast hp.pos) _
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hL : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hb : X ≤ Q * Real.log Q := maximal_clock_bound hm hq
  have hQL : X ≤ Q * Real.log X := by
    rcases le_total X Q with h | h
    · exact h.trans (le_mul_of_one_le_right hQ.le hL)
    · exact hb.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hQ h) hQ.le)
  have hi : Q⁻¹ ≤ Real.log X / X := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hQ hX0).mpr
    simpa only [mul_comm, one_mul] using hQL
  exact (removal_delta hm hq.1).2.2.2.trans hi

theorem divisor_log_le_log {n : ℕ} (hn : 0 < n) :
    divisorLog n ≤ Real.log (n : ℝ) := by
  have hs : 0 < (ArithmeticFunction.sigma 1 n : ℝ) / n :=
    div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn.ne')
      (by exact_mod_cast hn)
  apply Real.log_le_log hs
  apply (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
  exact_mod_cast (by simpa [pow_two] using ArithmeticFunction.sigma_le_pow_succ 1 n)

private theorem height_cancellation {eta X Y E delta : ℝ}
    (heta : 0 < eta) (hY : 1 < Y) (hYX : Y < X)
    (hE : E ≤ 2 / Real.log Y)
    (hslope : 2 * eta * Real.log X ≤ Real.log Y) :
    X ^ eta * (delta + E - (Real.log (Real.log X) - Real.log (Real.log Y))) -
      Y ^ eta * E ≤ X ^ eta * delta := by
  have hY0 : 0 < Y := by linarith
  have hX0 : 0 < X := hY0.trans hYX
  have hl : 0 < Real.log Y := Real.log_pos hY
  have hL : 0 < Real.log X := hl.trans (Real.log_lt_log hY0 hYX)
  let beta := Real.log X - Real.log Y
  have hb : 0 ≤ beta := sub_nonneg.mpr (Real.log_le_log hY0 hYX.le)
  let r := (Y / X) ^ eta
  have hr0 : 0 ≤ r := Real.rpow_nonneg (div_pos hY0 hX0).le _
  have hr1 : r ≤ 1 := Real.rpow_le_one (div_pos hY0 hX0).le
    ((div_le_one hX0).mpr hYX.le) heta.le
  have hdrop : 1 - r ≤ eta * beta := by
    have he := Real.add_one_le_exp (Real.log (Y / X) * eta)
    rw [← Real.rpow_def_of_pos (div_pos hY0 hX0), Real.log_div hY0.ne' hX0.ne'] at he
    dsimp [r, beta]
    nlinarith
  have htangent : beta / Real.log X ≤
      Real.log (Real.log X) - Real.log (Real.log Y) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hl hL)
    rw [Real.log_div hl.ne' hL.ne'] at h
    dsimp [beta]
    have hid : (Real.log X - Real.log Y) / Real.log X =
        1 - Real.log Y / Real.log X := by field_simp
    linarith
  have hcoef : 2 * eta / Real.log Y ≤ 1 / Real.log X := by
    exact (div_le_div_iff₀ hl hL).mpr (by simpa using hslope)
  have hterm : E * (1 - r) ≤ Real.log (Real.log X) - Real.log (Real.log Y) := calc
    _ ≤ (2 / Real.log Y) * (1 - r) :=
      mul_le_mul_of_nonneg_right hE (sub_nonneg.mpr hr1)
    _ ≤ (2 / Real.log Y) * (eta * beta) :=
      mul_le_mul_of_nonneg_left hdrop (by positivity)
    _ = (2 * eta / Real.log Y) * beta := by ring
    _ ≤ (1 / Real.log X) * beta := mul_le_mul_of_nonneg_right hcoef hb
    _ = beta / Real.log X := by ring
    _ ≤ _ := htangent
  have hpow : Y ^ eta = X ^ eta * r := by
    dsimp [r]
    rw [Real.div_rpow hY0.le hX0.le]
    field_simp
  rw [hpow]
  nlinarith [mul_nonneg (Real.rpow_nonneg hX0.le eta)
    (sub_nonneg.mpr hterm)]

private theorem quotient_clock_large (K : ℝ) :
    ∃ A : ℝ, Real.exp 1 ≤ A ∧ ∀ m q : ℕ, 0 < m → A ≤ Real.log (m : ℝ) →
      Real.eulerMascheroniConstant < originalObjective m → MaximalPrimePower m q →
      K ≤ Real.log (m / q : ℕ) := by
  have hratio : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hloglog := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((hratio.eventually_le_const (by norm_num : (0 : ℝ) < 1)).and
      (hloglog.eventually_ge_atTop (K - Real.eulerMascheroniConstant + 1)))
  refine ⟨max B (Real.exp 1), le_max_right _ _, ?_⟩
  intro m q hm hlarge hF hq
  obtain ⟨hsmall, hlog⟩ := hB _ ((le_max_left B _).trans hlarge)
  have hX := (le_max_right B (Real.exp 1)).trans hlarge
  have hd := delta_clock_bound hm hX hq
  have hn := (removal_delta hm hq.1).1
  have hW := divisor_log_le_log hn
  simp only [Function.comp_apply] at hlog
  change Real.eulerMascheroniConstant < divisorLog m -
    Real.log (Real.log (Real.log (m : ℝ))) at hF
  linarith

/-- One threshold works for every actual maximizing occupied prime power. The upper
envelope is applied at the actual quotient, whose size is first proved uniformly. -/
theorem eventual_actual_height_jump {eta : ℝ} (heta : 0 < eta) (hetaHalf : eta < 1 / 2) :
    ∃ A : ℝ, 1 < A ∧ ∀ m : ℕ, 0 < m → A ≤ Real.log (m : ℝ) →
      Real.eulerMascheroniConstant < originalObjective m →
      (∃ q, MaximalPrimePower m q) ∧ ∀ q, MaximalPrimePower m q →
        3 ≤ m / q ∧ 0 < divisorLog m - divisorLog (m / q) ∧
        actualHeight eta m - actualHeight eta (m / q) ≤
          (Real.log (m : ℝ)) ^ eta * (divisorLog m - divisorLog (m / q)) ∧
        (Real.log (m : ℝ)) ^ eta * (divisorLog m - divisorLog (m / q)) ≤
          (Real.log (m : ℝ)) ^ (eta - 1) * Real.log (Real.log (m : ℝ)) := by
  obtain ⟨U, hU, hupper⟩ := eventual_actual_integer_envelope
  let C := (1 + 1 / (2 * eta)) / 2
  have heta2 : 0 < 2 * eta := by positivity
  have hC1 : 1 < C := by
    have : 1 < 1 / (2 * eta) := (one_lt_div heta2).mpr (by linarith)
    dsimp [C]
    linarith
  have hCeta : 2 * eta * C < 1 := by
    dsimp [C]
    have hh : 2 * eta * (1 / (2 * eta)) = 1 := by field_simp
    nlinarith
  have hlogC : 0 < Real.log C := Real.log_pos hC1
  have hsmall : Tendsto (fun y : ℝ => 2 / Real.log y) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop 2
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    (hsmall.eventually_lt_const (show (0 : ℝ) < Real.log C / 2 by positivity))
  obtain ⟨D, hD, hquot⟩ := quotient_clock_large (max U (max B 4))
  have hratio : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (hratio.eventually_lt_const (show (0 : ℝ) < Real.log C / 2 by positivity))
  refine ⟨max D R, ?_, ?_⟩
  · exact (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le
      (hD.trans (le_max_left D R))
  intro m hm hlarge hF
  have hXexp : Real.exp 1 ≤ Real.log (m : ℝ) :=
    hD.trans ((le_max_left D R).trans hlarge)
  have hX1 : 1 < Real.log (m : ℝ) :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hXexp
  have hm1 : 1 < m := by
    by_contra h
    have : m = 1 := by omega
    norm_num [this] at hX1
  refine ⟨maximal_exists hm1, ?_⟩
  intro q hq
  have hY := hquot m q hm ((le_max_left D R).trans hlarge) hF hq
  have hYU : U ≤ Real.log (m / q : ℕ) := (le_max_left U _).trans hY
  have hYB : B ≤ Real.log (m / q : ℕ) :=
    (le_max_left B 4).trans ((le_max_right U _).trans hY)
  have hY4 : 4 ≤ Real.log (m / q : ℕ) :=
    (le_max_right B 4).trans ((le_max_right U _).trans hY)
  obtain ⟨hn, hnm, hdpos, hdbound⟩ := removal_delta hm hq.1
  have hn3 : 3 ≤ m / q := by
    by_contra h
    have hle : Real.log (m / q : ℕ) ≤ Real.log 2 :=
      Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast (by omega : m / q ≤ 2))
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hYX : Real.log (m / q : ℕ) < Real.log (m : ℝ) :=
    Real.log_lt_log (by exact_mod_cast hn) (by exact_mod_cast hnm)
  have hY1 : 1 < Real.log (m / q : ℕ) := by linarith
  have hl : 0 < Real.log (Real.log (m / q : ℕ)) := Real.log_pos hY1
  have hL : 0 < Real.log (Real.log (m : ℝ)) := Real.log_pos hX1
  have hE := hupper (m / q) hn hYU
  have hd := delta_clock_bound hm hXexp hq
  have hsmallY := hB _ hYB
  have hsmallX := hR _ ((le_max_right D R).trans hlarge)
  have hdiff : Real.log (Real.log (Real.log (m : ℝ))) -
      Real.log (Real.log (Real.log (m / q : ℕ))) < Real.log C := by
    unfold originalObjective at hE hF
    unfold divisorLog at hd
    linarith
  have hlogratio : Real.log (Real.log (m : ℝ)) /
      Real.log (Real.log (m / q : ℕ)) < C := by
    apply (Real.log_lt_log_iff (div_pos hL hl) (by linarith : 0 < C)).mp
    rw [Real.log_div hL.ne' hl.ne']
    exact hdiff
  have hslope : 2 * eta * Real.log (Real.log (m : ℝ)) ≤
      Real.log (Real.log (m / q : ℕ)) := by
    have hh := (div_lt_iff₀ hl).mp hlogratio
    have hh' := mul_lt_mul_of_pos_left hh heta2
    nlinarith
  have hcancel := height_cancellation heta hY1 hYX hE hslope
    (delta := divisorLog m - divisorLog (m / q))
  have hid : originalObjective m - Real.eulerMascheroniConstant =
      (divisorLog m - divisorLog (m / q)) +
        (originalObjective (m / q) - Real.eulerMascheroniConstant) -
        (Real.log (Real.log (Real.log (m : ℝ))) -
          Real.log (Real.log (Real.log (m / q : ℕ)))) := by
    unfold originalObjective divisorLog
    ring
  refine ⟨hn3, hdpos, ?_, ?_⟩
  · unfold actualHeight
    rw [hid]
    exact hcancel
  · have hb := mul_le_mul_of_nonneg_left hd
      (Real.rpow_nonneg (by linarith : 0 ≤ Real.log (m : ℝ)) eta)
    rw [Real.rpow_sub_one (by linarith : Real.log (m : ℝ) ≠ 0)]
    convert hb using 1
    ring

#print axioms eventual_actual_height_jump

private theorem jump_error_limit {eta : ℝ} (heta : eta < 1) :
    Tendsto (fun x : ℝ => x ^ (eta - 1) * Real.log x) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (show 0 < 1 - eta by linarith)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [show eta - 1 = -(1 - eta) by ring, Real.rpow_neg hx.le]
  ring

/-- Under the original unbounded-height input, genuine least integer crossings have
vanishing overshoot. Their size tends to infinity, and the explicit error is the one
proved for the actual maximal-prime-power divisor jump. -/
theorem first_crossing_calibration {eta : ℝ} (heta : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hunbounded : ∀ T : ℝ, ∃ m : ℕ, 3 ≤ m ∧ T ≤ actualHeight eta m) :
    ∃ crossing : ℝ → ℕ,
      (∀ T : ℝ, 3 ≤ crossing T ∧ T ≤ actualHeight eta (crossing T) ∧
        ∀ n : ℕ, 3 ≤ n → n < crossing T → actualHeight eta n < T) ∧
      Tendsto crossing atTop atTop ∧
      Tendsto (fun T : ℝ => (Real.log (crossing T : ℝ)) ^ (eta - 1) *
        Real.log (Real.log (crossing T : ℝ))) atTop (𝓝 0) ∧
      (∀ᶠ T : ℝ in atTop, T ≤ actualHeight eta (crossing T) ∧
        actualHeight eta (crossing T) < T +
          (Real.log (crossing T : ℝ)) ^ (eta - 1) * Real.log (Real.log (crossing T : ℝ))) ∧
      Tendsto (fun T : ℝ => actualHeight eta (crossing T) - T) atTop (𝓝 0) := by
  classical
  let crossing := fun T : ℝ => Nat.find (hunbounded T)
  have hspec (T : ℝ) : 3 ≤ crossing T ∧ T ≤ actualHeight eta (crossing T) ∧
      ∀ n : ℕ, 3 ≤ n → n < crossing T → actualHeight eta n < T := by
    refine ⟨(Nat.find_spec (hunbounded T)).1, (Nat.find_spec (hunbounded T)).2, ?_⟩
    intro n hn hlt
    exact lt_of_not_ge (fun h => Nat.find_min (hunbounded T) hlt ⟨hn, h⟩)
  have hcofinal : Tendsto crossing atTop atTop := by
    apply tendsto_atTop.2
    intro N
    obtain ⟨k, hk, hmax⟩ := exists_max_image (range (N + 1)) (actualHeight eta)
      ⟨0, mem_range.mpr (by omega)⟩
    filter_upwards [eventually_gt_atTop (actualHeight eta k)] with T hT
    by_contra h
    have hmem : crossing T ∈ range (N + 1) := mem_range.mpr (by omega)
    have hh := hmax (crossing T) hmem
    linarith [(hspec T).2.1]
  have hclock : Tendsto (fun T : ℝ => Real.log (crossing T : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hcofinal)
  have herror := (jump_error_limit (show eta < 1 by linarith)).comp hclock
  obtain ⟨A, hA, hjump⟩ := eventual_actual_height_jump heta hetaHalf
  have hcalibration : ∀ᶠ T : ℝ in atTop, T ≤ actualHeight eta (crossing T) ∧
      actualHeight eta (crossing T) < T +
        (Real.log (crossing T : ℝ)) ^ (eta - 1) * Real.log (Real.log (crossing T : ℝ)) := by
    filter_upwards [hclock.eventually_ge_atTop A, eventually_gt_atTop (0 : ℝ)] with T hlarge hT
    have hm := (hspec T).1
    have hheight : 0 < actualHeight eta (crossing T) := hT.trans_le (hspec T).2.1
    have hF : Real.eulerMascheroniConstant < originalObjective (crossing T) := by
      have hpow : 0 < (Real.log (crossing T : ℝ)) ^ eta :=
        Real.rpow_pos_of_pos (by linarith [hA.trans_le hlarge]) _
      unfold actualHeight at hheight
      have := (mul_pos_iff_of_pos_left hpow).mp hheight
      linarith
    obtain ⟨⟨q, hq⟩, hall⟩ := hjump (crossing T) (by omega) hlarge hF
    obtain ⟨hn, _, hstep, herr⟩ := hall q hq
    have hproper := (removal_delta (by omega : 0 < crossing T) hq.1).2.1
    have hbefore := (hspec T).2.2 (crossing T / q) hn hproper
    exact ⟨(hspec T).2.1, by linarith⟩
  refine ⟨crossing, hspec, hcofinal, herror, hcalibration, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herror
  · exact Filter.Eventually.of_forall fun T => sub_nonneg.mpr (hspec T).2.1
  · filter_upwards [hcalibration] with T hT
    simp only [Function.comp_apply]
    linarith [hT.2]

#print axioms first_crossing_calibration

end D5.S3.Arith.Robin.ActualIntegerHeightJump
