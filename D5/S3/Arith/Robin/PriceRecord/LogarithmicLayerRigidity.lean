/- GID: D5/S3/Arith/Robin/PriceRecord/LogarithmicLayerRigidity
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/LogarithmicLayerRigidity
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: Shrinking prime windows and logarithmic finite exchanges. -/

import D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity

/-! Prime supply for growing finite exchanges in shrinking relative windows. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity

open Finset Filter Asymptotics
open scoped Topology BigOperators Chebyshev

private theorem theta_error_eight :
    (fun x : ℝ => Chebyshev.theta x - x) =o[atTop]
      (fun x : ℝ => x / Real.log x ^ 8) := by
  obtain ⟨c, hc, hpnt⟩ := MediumPNT
  have hexp : Tendsto
      (fun x : ℝ => Real.log x ^ 8 * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 80 c hc).comp
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
        Real.tendsto_log_atTop)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : 0 ≤ Real.log x := (Real.log_pos hx).le
    simp only [Function.comp_def]
    rw [← Real.rpow_mul hlog]
    norm_num only [show (1 / 10 : ℝ) * 80 = 8 by norm_num]
    norm_num only [← Real.rpow_natCast]
  have hmodel : (fun x : ℝ => x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)))
      =o[atTop] (fun x : ℝ => x / Real.log x ^ 8) := by
    apply isLittleO_of_tendsto'
      ((eventually_gt_atTop (1 : ℝ)).mono fun x hx => by
        exact fun h => False.elim ((div_ne_zero (by linarith : x ≠ 0)
          (pow_ne_zero _ (Real.log_pos hx).ne')) h))
    apply hexp.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    field_simp [show x ≠ 0 by linarith]
  have hlog : Tendsto (fun x : ℝ => Real.log x ^ 8 / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (8 : ℕ) (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hsqrt : Real.sqrt =o[atTop] (fun x : ℝ => x / Real.log x ^ 8) := by
    apply isLittleO_of_tendsto'
      ((eventually_gt_atTop (1 : ℝ)).mono fun x hx => by
        exact fun h => False.elim ((div_ne_zero (by linarith : x ≠ 0)
          (pow_ne_zero _ (Real.log_pos hx).ne')) h))
    apply hlog.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
    field_simp
    rw [Real.sq_sqrt hx0.le]
  have h := (hpnt.trans_isLittleO hmodel).sub
    (Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsqrt)
  apply h.congr_left
  intro x
  simp only [Pi.sub_apply, id_eq]
  ring

private theorem prime_interval_subset {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : 1 < b) (N : ℕ)
    (hmass : (N : ℝ) * Real.log b ≤ Chebyshev.theta b - Chebyshev.theta a) :
    ∃ S : Finset ℕ, S.card = N ∧
      ∀ p ∈ S, p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
  classical
  let A := Nat.primesLE ⌊a⌋₊
  let B := Nat.primesLE ⌊b⌋₊
  have hsub : A ⊆ B := by
    intro p hp
    obtain ⟨hpa, hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpa.trans (Nat.floor_mono hab), hp⟩
  have hmem : ∀ p ∈ B \ A, p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
    intro p hp
    obtain ⟨hpB, hpA⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpb, hprime⟩ := Nat.mem_primesLE.mp hpB
    refine ⟨hprime, ?_, (Nat.le_floor_iff (ha.trans hab)).mp hpb⟩
    by_contra! hpa
    exact hpA (Nat.mem_primesLE.mpr ⟨Nat.le_floor hpa, hprime⟩)
  have hsum : Chebyshev.theta b - Chebyshev.theta a =
      ∑ p ∈ B \ A, Real.log (p : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
    have h := Finset.sum_sdiff hsub (f := fun p : ℕ => Real.log (p : ℝ))
    dsimp [A, B] at h ⊢
    linarith
  have hupper : (∑ p ∈ B \ A, Real.log (p : ℝ)) ≤
      ((B \ A).card : ℝ) * Real.log b := by
    calc
      _ ≤ ∑ _p ∈ B \ A, Real.log b := Finset.sum_le_sum fun p hp =>
        Real.log_le_log (by exact_mod_cast (hmem p hp).1.pos) (hmem p hp).2.2
      _ = _ := by simp
  have hcard : N ≤ (B \ A).card := by
    have h := hmass.trans (hsum ▸ hupper)
    exact_mod_cast (mul_le_mul_iff_left₀ (Real.log_pos hb)).mp h
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨S, hScard, fun p hp => hmem p (hS hp)⟩

/-- Both relative windows of width `x/log(x)^3` supply any requested number
of distinct primes up to a fixed multiple of `log(x)^3`, rounded upwards. -/
theorem shrinking_prime_windows (C : ℝ) (hC : 0 < C) :
    ∃ T : ℝ, 1 < T ∧ ∀ x : ℝ, T ≤ x → ∀ N : ℕ,
      N ≤ ⌈C * Real.log x ^ 3⌉₊ →
      ∃ D U : Finset ℕ, D.card = N ∧ U.card = N ∧
        (∀ p ∈ D, p.Prime ∧ x * (1 - 1 / Real.log x ^ 3) < (p : ℝ) ∧
          (p : ℝ) ≤ x) ∧
        (∀ q ∈ U, q.Prime ∧ x < (q : ℝ) ∧
          (q : ℝ) ≤ x * (1 + 1 / Real.log x ^ 3)) := by
  have herror : ∀ᶠ y : ℝ in atTop,
      |Chebyshev.theta y - y| ≤ y / Real.log y ^ 8 := by
    filter_upwards [theta_error_eight.eventuallyLE, eventually_gt_atTop (1 : ℝ)] with y hy hy1
    simpa only [Real.norm_eq_abs, abs_of_pos
      (div_pos (by linarith : 0 < y) (pow_pos (Real.log_pos hy1) 8))] using hy
  obtain ⟨Y, hY⟩ := eventually_atTop.mp herror
  have hpoly (k : ℕ) : Tendsto (fun x : ℝ => Real.log x ^ k / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop k (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hcapacity : ∀ᶠ x : ℝ in atTop,
      4 * Real.log x ^ 4 * (C * Real.log x ^ 3 + 1) ≤ x := by
    have hlim := ((hpoly 7).const_mul (4 * C)).add ((hpoly 4).const_mul 4)
    simp only [mul_zero, add_zero] at hlim
    have hevent := hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hevent, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have hh : (4 * Real.log x ^ 4 * (C * Real.log x ^ 3 + 1)) / x < 1 := by
      convert hx using 1; ring
    exact ((div_lt_one hx0).mp hh).le
  have hevent : ∀ᶠ x : ℝ in atTop, 4 ≤ x ∧ 2 * Y ≤ x ∧
      8 ≤ Real.log x ∧
      4 * Real.log x ^ 4 * (C * Real.log x ^ 3 + 1) ≤ x := by
    filter_upwards [eventually_ge_atTop (4 : ℝ), eventually_ge_atTop (2 * Y),
      Real.tendsto_log_atTop.eventually_ge_atTop 8, hcapacity] with x hx hY hxlog hcap
    exact ⟨hx, hY, hxlog, hcap⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  refine ⟨max T 4, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro x hx N hN
  obtain ⟨hx4, hYx, hL8, hcap⟩ := hT x ((le_max_left _ _).trans hx)
  let L := Real.log x
  have hx0 : 0 < x := by linarith
  have hL : 0 < L := by dsimp [L]; linarith
  have hL3 : 0 < L ^ 3 := pow_pos hL 3
  have hL4 : 0 < L ^ 4 := pow_pos hL 4
  have hL8pos : 0 < L ^ 8 := pow_pos hL 8
  have hdelta : 1 / L ^ 3 ≤ 1 / 2 := by
    apply (div_le_iff₀ hL3).mpr
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hL8 3
    dsimp [L] at hL3 ⊢
    nlinarith
  have hlocal : ∀ y : ℝ, x / 2 ≤ y → y ≤ 2 * x →
      |Chebyshev.theta y - y| ≤ 512 * x / L ^ 8 := by
    intro y hxy hyx
    have hy0 : 0 < y := by linarith
    have hsqrt : Real.sqrt x ≤ x / 2 := by
      have hs0 := Real.sqrt_nonneg x
      nlinarith [Real.sq_sqrt hx0.le]
    have hlogy : L / 2 ≤ Real.log y := by
      have h := Real.log_le_log (Real.sqrt_pos.mpr hx0) (hsqrt.trans hxy)
      simpa only [Real.log_sqrt hx0.le] using h
    have hlogy0 : 0 < Real.log y := lt_of_lt_of_le (by positivity : 0 < L / 2) hlogy
    have hbnd := hY y (by linarith)
    apply hbnd.trans
    calc
      y / Real.log y ^ 8 ≤ (2 * x) / (L / 2) ^ 8 :=
        div_le_div₀ (by positivity : 0 ≤ 2 * x) hyx (pow_pos (by positivity : 0 < L / 2) 8)
          (pow_le_pow_left₀ (by positivity) hlogy 8)
      _ = _ := by ring
  have herr : 1024 * x / L ^ 8 ≤ x / (2 * L ^ 3) := by
    apply (div_le_div_iff₀ hL8pos (by positivity : 0 < 2 * L ^ 3)).mpr
    have hp : (2048 : ℝ) ≤ L ^ 5 := by
      calc
        _ ≤ (8 : ℝ) ^ 5 := by norm_num
        _ ≤ L ^ 5 := pow_le_pow_left₀ (by norm_num) hL8 5
    have h := mul_le_mul_of_nonneg_left hp (mul_nonneg hx0.le hL3.le)
    nlinarith only [h]
  have hNreal : (N : ℝ) ≤ C * L ^ 3 + 1 := by
    exact (show (N : ℝ) ≤ (⌈C * L ^ 3⌉₊ : ℝ) by exact_mod_cast hN).trans
      (Nat.ceil_lt_add_one (by positivity : 0 ≤ C * L ^ 3)).le
  have hNm : (N : ℝ) * (4 * L ^ 4) ≤ x := by
    exact (mul_le_mul_of_nonneg_right hNreal (by positivity)).trans (by
      simpa only [L, mul_comm] using hcap)
  have choose (a b : ℝ) (ha : x / 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * x)
      (hb1 : 1 < b) (hwidth : x / L ^ 3 ≤ b - a) :
      ∃ S : Finset ℕ, S.card = N ∧
        ∀ p ∈ S, p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
    have hae := abs_le.mp (hlocal a ha (hab.trans hb))
    have hbe := abs_le.mp (hlocal b (ha.trans hab) hb)
    have htheta : x / (2 * L ^ 3) ≤ Chebyshev.theta b - Chebyshev.theta a := by
      have heq : x / L ^ 3 = 2 * (x / (2 * L ^ 3)) := by ring
      have herr' : 2 * (512 * x / L ^ 8) ≤ x / (2 * L ^ 3) := by
        convert herr using 1; ring
      linarith only [hae.2, hbe.1, hwidth, heq, herr']
    have hlogb : Real.log b ≤ 2 * L := by
      have h := Real.log_le_log (by linarith : 0 < b) hb
      have hlog2 : Real.log (2 : ℝ) ≤ L := Real.log_le_log (by norm_num) (by linarith)
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne'] at h
      dsimp [L] at *
      linarith
    apply prime_interval_subset (by linarith) hab hb1 N
    calc
      (N : ℝ) * Real.log b ≤ (N : ℝ) * (2 * L) :=
        mul_le_mul_of_nonneg_left hlogb (Nat.cast_nonneg N)
      _ ≤ x / (2 * L ^ 3) := by
        apply (le_div_iff₀ (by positivity : 0 < 2 * L ^ 3)).mpr
        convert hNm using 1; ring
      _ ≤ _ := htheta
  obtain ⟨D, hDcard, hD⟩ := choose (x * (1 - 1 / L ^ 3)) x
    (by nlinarith [mul_le_mul_of_nonneg_left hdelta hx0.le])
    (by nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hL3.le])
    (by linarith) (by linarith) (by ring_nf; exact le_refl _)
  obtain ⟨U, hUcard, hU⟩ := choose x (x * (1 + 1 / L ^ 3))
    (by linarith) (by nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hL3.le])
    (by nlinarith [mul_le_mul_of_nonneg_left hdelta hx0.le])
    (by nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hL3.le])
    (by ring_nf; exact le_refl _)
  exact ⟨D, U, hDcard, hUcard, hD, hU⟩

end D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
