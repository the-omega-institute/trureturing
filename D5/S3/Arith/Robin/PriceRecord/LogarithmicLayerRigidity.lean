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
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
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

private theorem rounded_counts {z w : ℝ} (hz : 0 < z) (hw : 0 ≤ w) :
    ((⌈z⌉₊ - 1 : ℕ) : ℝ) < z ∧ z - 1 ≤ ((⌈z⌉₊ - 1 : ℕ) : ℝ) ∧
    w < ((⌊w⌋₊ + 1 : ℕ) : ℝ) ∧ ((⌊w⌋₊ + 1 : ℕ) : ℝ) ≤ w + 1 := by
  have hc : 1 ≤ ⌈z⌉₊ := Nat.ceil_pos.mpr hz
  rw [Nat.cast_sub hc, Nat.cast_add, Nat.cast_one]
  exact ⟨by linarith [Nat.ceil_lt_add_one hz.le],
    by linarith [Nat.le_ceil z], Nat.lt_floor_add_one w,
    by linarith [Nat.floor_le hw]⟩

private theorem log_budget_products_lt {D U : Finset ℕ} {r s : ℕ} {V W : ℝ}
    (hDcard : D.card = r) (hUcard : U.card = s) (hV : 0 < V) (hW : 0 < W)
    (hD : ∀ p ∈ D, V ≤ (p : ℝ)) (hU : ∀ q ∈ U, (q : ℝ) ≤ W)
    (hbudget : (s : ℝ) * Real.log W < (r : ℝ) * Real.log V) :
    (∏ q ∈ U, q) < ∏ p ∈ D, p := by
  apply finite_products_lt hDcard hUcard hV hD hU
  apply (div_lt_one (pow_pos hV r)).mpr
  apply (Real.log_lt_log_iff (pow_pos hW s) (pow_pos hV r)).mp
  simpa only [Real.log_pow] using hbudget

private theorem exchange_window_bound {m : ℕ} {lambda V Z W : ℝ} {a b : ℕ}
    (hcert : ExchangeSupply m lambda) (hlambda : 0 < lambda)
    (D U : Finset ℕ) (hdis : Disjoint D U)
    (hD : ∀ p ∈ D, p.Prime ∧ p ∣ m)
    (hU : ∀ q ∈ U, q.Prime)
    (hprod : (∏ q ∈ U, q) < ∏ p ∈ D, p)
    (ha : 1 ≤ a) (hV : 0 < V) (hZ : 1 < Z)
    (hDval : ∀ p ∈ D, a ≤ m.factorization p)
    (hUval : ∀ q ∈ U, m.factorization q + 1 ≤ b)
    (hDV : ∀ p ∈ D, V ≤ (p : ℝ))
    (hUZ : ∀ q ∈ U, Z ≤ (q : ℝ))
    (hUW : ∀ q ∈ U, (q : ℝ) ≤ W) :
    (U.card : ℝ) * ((1 - Z⁻¹) * W⁻¹ ^ b) ≤ (D.card : ℝ) * V⁻¹ ^ a := by
  by_contra! hbad
  apply exchange_forbids_scaled_gain_bounds hcert hlambda (by norm_num : (0 : ℝ) < 1)
    D U hdis hD hU hprod
  · intro p hp
    simpa only [one_mul] using gain_upper_window (hD p hp).1 ha (hDval p hp) hV (hDV p hp)
  · intro q hq
    simpa only [one_mul] using gain_lower_window
      (fun p a hp ha => golden_layer_gain_lower hp ha) (hU q hq)
      (by omega : 1 ≤ m.factorization q + 1) (hUval q hq) hZ (hUZ q hq) (hUW q hq)
  · exact hbad

/-- Simultaneous finite exchanges use their actual scale-dependent windows.
The scalar capacity premises bound the rounded counts, not prime existence. -/
private theorem shrinking_rounded_exchanges (C : ℝ) (hC : 0 < C) :
    ∃ T : ℝ, 1 < T ∧ ∀ (m j : ℕ), 2 ≤ m → 2 ≤ j →
      ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      let P : ℝ := largestPrime m
      let Q : ℝ := layerPrime m j
      let V : ℝ := P * (1 - 1 / Real.log P ^ 3)
      let W : ℝ := Q * (1 + 1 / Real.log Q ^ 3)
      let X : ℝ := Q * (1 - 1 / Real.log Q ^ 3)
      let Y : ℝ := P * (1 + 1 / Real.log P ^ 3)
      let r : ℕ := ⌈Real.log P ^ 3⌉₊
      let s : ℕ := ⌈(r : ℝ) * Real.log V / Real.log W⌉₊ - 1
      let t : ℕ := ⌊(r : ℝ) * Real.log Y / Real.log X⌋₊ + 1
      T ≤ P → T ≤ Q → 1 < V → 1 < X → W < V →
      0 < (r : ℝ) * Real.log V / Real.log W →
      r ≤ ⌈C * Real.log P ^ 3⌉₊ →
      s ≤ ⌈C * Real.log Q ^ 3⌉₊ →
      t ≤ ⌈C * Real.log Q ^ 3⌉₊ →
      (s : ℝ) * ((1 - Q⁻¹) * W⁻¹ ^ j) ≤ (r : ℝ) * V⁻¹ ∧
      (r : ℝ) * ((1 - P⁻¹) * Y⁻¹) ≤ (t : ℝ) * X⁻¹ ^ j := by
  obtain ⟨T, hT, hcapacity⟩ := shrinking_prime_windows C hC
  refine ⟨T, hT, ?_⟩
  intro m j hm hj lambda hlambda hrecord P Q V W X Y r s t hP hQ hV hX hsep hz hr hs ht
  have hP1 : 1 < P := hT.trans_le hP
  have hQ1 : 1 < Q := hT.trans_le hQ
  have hWQ : Q < W := by
    dsimp [W]
    nlinarith [mul_pos (by linarith : 0 < Q)
      (div_pos (by norm_num : (0 : ℝ) < 1) (pow_pos (Real.log_pos hQ1) 3))]
  have hPY : P < Y := by
    dsimp [Y]
    nlinarith [mul_pos (by linarith : 0 < P)
      (div_pos (by norm_num : (0 : ℝ) < 1) (pow_pos (Real.log_pos hP1) 3))]
  have hw : 0 ≤ (r : ℝ) * Real.log Y / Real.log X :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (hP1.trans hPY)).le)
      (Real.log_pos hX).le
  obtain ⟨hslow, _, htup, _⟩ := rounded_counts hz hw
  have hlowerbudget : (s : ℝ) * Real.log W < (r : ℝ) * Real.log V :=
    (lt_div_iff₀ (Real.log_pos (hQ1.trans hWQ))).mp hslow
  have hupperbudget : (r : ℝ) * Real.log Y < (t : ℝ) * Real.log X :=
    (div_lt_iff₀ (Real.log_pos hX)).mp htup
  obtain ⟨DP, UP, hDPcard, hUPcard, hDP, hUP⟩ := hcapacity P hP r hr
  obtain ⟨DQ, UQ, hDQcard, hUQcard, hDQ, hUQ⟩ := hcapacity Q hQ s hs
  obtain ⟨EQ, FQ, hEQcard, _, hEQ, _⟩ := hcapacity Q hQ t ht
  have hstructure := price_record_prime_structure hm hlambda hrecord
  have hsupport (p : ℕ) (hp : p.Prime) (hpP : (p : ℝ) ≤ P) : p ∣ m := by
    apply Nat.dvd_of_mem_primeFactors
    rw [hstructure.2]
    exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast (show (p : ℝ) ≤ (largestPrime m : ℝ) from hpP), hp⟩
  have hcert : ExchangeSupply m lambda := by
    intro D U hdis hD hU hprod
    exact (signed_exchange_certificate lambda (by omega : 0 < m) hrecord D U
      (fun p hp => (hD p hp).1) hU (fun p hp => (hD p hp).2) hdis hprod).2.2
  have hDPdonor : ∀ p ∈ DP, p.Prime ∧ p ∣ m :=
    fun p hp => ⟨(hDP p hp).1, hsupport p (hDP p hp).1 (hDP p hp).2.2⟩
  have hDPval : ∀ p ∈ DP, 1 ≤ m.factorization p := by
    intro p hp
    exact ((hDPdonor p hp).1.dvd_iff_one_le_factorization (by omega : m ≠ 0)).mp
      (hDPdonor p hp).2
  have hUQval : ∀ q ∈ UQ, m.factorization q + 1 ≤ j := by
    intro q hq
    have h := valuation_above_layer_prime (by omega : 0 < m) (by omega : 1 ≤ j)
      (hUQ q hq).1 (by exact_mod_cast (show (layerPrime m j : ℝ) < (q : ℝ) from (hUQ q hq).2.1))
    omega
  have hQnat : 1 < layerPrime m j := by exact_mod_cast (show (1 : ℝ) < (layerPrime m j : ℝ) from hQ1)
  have hQP : Q ≤ P := by
    obtain ⟨hmem, _⟩ := layer_prime_mem hQnat
    rw [hstructure.2] at hmem
    change (layerPrime m j : ℝ) ≤ (largestPrime m : ℝ)
    exact_mod_cast (Nat.mem_primesLE.mp hmem).1
  have hEQval : ∀ p ∈ EQ, j ≤ m.factorization p := by
    intro p hp
    exact valuation_below_layer_prime (hEQ p hp).1 hstructure.1
      (by exact_mod_cast (show (p : ℝ) ≤ (layerPrime m j : ℝ) from (hEQ p hp).2.2))
  have hEQdonor : ∀ p ∈ EQ, p.Prime ∧ p ∣ m := by
    intro p hp
    exact ⟨(hEQ p hp).1, hsupport p (hEQ p hp).1 ((hEQ p hp).2.2.trans hQP)⟩
  have hUPval : ∀ q ∈ UP, m.factorization q + 1 ≤ 1 := by
    intro q hq
    have hndiv : ¬q ∣ m := by
      intro hdiv
      have hmem := (hUP q hq).1.mem_primeFactors hdiv (by omega : m ≠ 0)
      rw [hstructure.2] at hmem
      have hle : (q : ℝ) ≤ P := by
        change (q : ℝ) ≤ (largestPrime m : ℝ)
        exact_mod_cast (Nat.mem_primesLE.mp hmem).1
      exact (hUP q hq).2.1.not_ge hle
    simp [Nat.factorization_eq_zero_of_not_dvd hndiv]
  constructor
  · have hdis : Disjoint DP UQ := Finset.disjoint_left.mpr (by
      intro p hpD hpU
      exact (hDP p hpD).2.1.not_ge ((hUQ p hpU).2.2.trans hsep.le))
    have hprod := log_budget_products_lt hDPcard hUQcard
      (by linarith : 0 < V) (by linarith : 0 < W)
      (fun p hp => (hDP p hp).2.1.le) (fun q hq => (hUQ q hq).2.2) hlowerbudget
    have hbound := exchange_window_bound hcert hlambda DP UQ hdis hDPdonor
      (fun q hq => (hUQ q hq).1) hprod (by norm_num : 1 ≤ 1)
      (by linarith : 0 < V) hQ1 hDPval hUQval
      (fun p hp => (hDP p hp).2.1.le) (fun q hq => (hUQ q hq).2.1.le)
      (fun q hq => (hUQ q hq).2.2)
    simpa only [hDPcard, hUQcard, pow_one] using hbound
  · have hdis : Disjoint EQ UP := Finset.disjoint_left.mpr (by
      intro p hpD hpU
      exact (hUP p hpU).2.1.not_ge ((hEQ p hpD).2.2.trans hQP))
    have hprod := log_budget_products_lt hEQcard hUPcard
      (by linarith : 0 < X) (by linarith : 0 < Y)
      (fun p hp => (hEQ p hp).2.1.le) (fun q hq => (hUP q hq).2.2) hupperbudget
    have hbound := exchange_window_bound hcert hlambda EQ UP hdis hEQdonor
      (fun q hq => (hUP q hq).1) hprod (by omega : 1 ≤ j)
      (by linarith : 0 < X) hP1 hEQval hUPval
      (fun p hp => (hEQ p hp).2.1.le) (fun q hq => (hUP q hq).2.1.le)
      (fun q hq => (hUP q hq).2.2)
    simpa only [hEQcard, hUPcard, pow_one] using hbound

end D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
