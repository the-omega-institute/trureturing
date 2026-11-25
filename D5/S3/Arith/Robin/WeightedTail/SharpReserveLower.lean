/- GID: D5/S3/Arith/Robin/WeightedTail/SharpReserveLower
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/WeightedTail/SharpReserveLower
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Strict all-integer Robin reserve with lower coefficient 2√2 − 2. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Arith.Robin.WeightedTail.PrimeBandReserve
import D5.S3.Arith.Robin.PrimeMinCorrectionLower

/-!
The all-integer lower reserve at the logarithmic clock. Prime powers on
either side of the reserve ledger give a common pointwise lower charge.
Finite prime shells on both sides of the breakpoint at √2 recover
the coefficient 2√2 − 2.
-/

set_option autoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.WeightedTail.SharpReserveLower

open Finset Filter
open scoped BigOperators Topology
open ArithmeticFunction (vonMangoldt_apply_pow vonMangoldt_apply_prime)
open D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel)
open D5.S3.Arith.Robin.EulerLayerRootCorrection (theta_sqrt_scale log_sqrt_scale)
open D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)
open D5.S3.Weil.Mertens.WeightedTailTransport (weightedTail)

/-- The common lower charge for valuations one and at least two. -/
private def sharpPrimeWeight (y : ℝ) (p : ℕ) : ℝ :=
  min (1 / (2 * (p : ℝ) * ((p : ℝ) + 1))) (1 / (2 * y) - 1 / (2 * (p : ℝ) ^ 2))

private theorem sharpPrimeWeight_nonneg {y : ℝ} {p : ℕ}
    (hy : 0 < y) (hp : y < (p : ℝ) ^ 2) : 0 ≤ sharpPrimeWeight y p := by
  apply le_min
  · positivity
  · exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))

section Ledger

open private cutoff rate signedWeight mangoldtWeight mangoldtWeight_prime_pow localEulerGap
  localEulerGap_one_lower localEulerGap_nonneg signedWeight_nonneg
  neg_signedWeight_nonneg robin_slack_eq from
  D5.S3.Arith.Robin.WeightedTail.PrimeBandReserve

private theorem sharpPrimeWeight_le_missing {y : ℝ} {p : ℕ}
    (hy : 2 ≤ y) (hp : p.Prime) (hpY : (p : ℝ) ≤ y / 2) :
    sharpPrimeWeight y p ≤ signedWeight y p := by
  have hy0 : 0 < y := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog := Real.log_le_log hp0 (show (p : ℝ) ≤ y by linarith)
  have hfirst : 1 / (y / 2) ≤ 1 / (p : ℝ) := one_div_le_one_div_of_le hp0 hpY
  have hrate : rate y * ArithmeticFunction.vonMangoldt p ≤ 1 / y := by
    rw [rate, vonMangoldt_apply_prime hp]
    calc
      _ = Real.log p / (y * Real.log y) := by ring
      _ ≤ Real.log y / (y * Real.log y) :=
        div_le_div_of_nonneg_right hlog (mul_pos hy0 hly).le
      _ = 1 / y := by field_simp [hy0.ne', hly.ne']
  have hw : mangoldtWeight p = 1 / (p : ℝ) := by
    simpa [one_div] using mangoldtWeight_prime_pow hp 0
  have hhalf : 1 / (y / 2) = 2 * (1 / y) := by
    field_simp [hy0.ne']
  rw [hhalf] at hfirst
  calc
    _ ≤ 1 / (2 * y) - 1 / (2 * (p : ℝ) ^ 2) := min_le_right _ _
    _ ≤ 1 / y := by
      have h := one_div_le_one_div_of_le hy0 (show y ≤ 2 * y by linarith)
      linarith only [h, show 0 ≤ 1 / (2 * (p : ℝ) ^ 2) by positivity]
    _ ≤ signedWeight y p := by
      rw [signedWeight, hw]
      linarith only [hfirst, hrate]

private theorem sharpPrimeWeight_le_extra_square {y : ℝ} {p : ℕ}
    (hy : 2 ≤ y) (hp : p.Prime) (hpY : y < (p : ℝ) ^ 2) :
    sharpPrimeWeight y p ≤ -signedWeight y (p ^ 2) := by
  have hy0 : 0 < y := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog := Real.log_lt_log hy0 hpY
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hrate : 1 / (2 * y) ≤ rate y * ArithmeticFunction.vonMangoldt (p ^ 2) := by
    rw [rate, vonMangoldt_apply_pow (by decide : (2 : ℕ) ≠ 0), vonMangoldt_apply_prime hp]
    calc
      _ = (Real.log y / 2) / (y * Real.log y) := by
        field_simp [hy0.ne', hly.ne']
      _ ≤ Real.log p / (y * Real.log y) :=
        div_le_div_of_nonneg_right (by linarith only [hlog]) (mul_pos hy0 hly).le
      _ = _ := by ring
  have hw := mangoldtWeight_prime_pow hp 1
  change _ = (p : ℝ)⁻¹ ^ 2 / (2 : ℝ) at hw
  have heq : (p : ℝ)⁻¹ ^ 2 / (2 : ℝ) = 1 / (2 * (p : ℝ) ^ 2) := by
    field_simp [hp0.ne']
  rw [heq] at hw
  calc
    _ ≤ 1 / (2 * y) - 1 / (2 * (p : ℝ) ^ 2) := min_le_right _ _
    _ ≤ -signedWeight y (p ^ 2) := by
      rw [signedWeight, hw]
      linarith only [hrate]

/-- Any finite mask in the indicated interval can be charged once to the exact
ledger. The mask may include primes missing from the factorization of n. -/
private theorem finite_prime_reserve {n : ℕ} {y : ℝ}
    (hclock : y = Real.log (n : ℝ)) (hy : 16 ≤ y) (s : Finset ℕ)
    (hmask : ∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ y / 2 ∧ y < (p : ℝ) ^ 2) :
    (∑ p ∈ s, sharpPrimeWeight y p) ≤
      robinLogMargin n - weightedTail psiErrorKernel y := by
  classical
  have hn : 0 < n := by
    by_contra! h
    have hn0 : n = 0 := by omega
    simp [hn0] at hclock
    linarith
  have hy2 : 2 ≤ y := by linarith
  let m : ℕ → ℕ := fun p => n.factorization p
  let s0 := s.filter (fun p => m p = 0)
  let sp := s.filter (fun p => m p ≠ 0)
  let s1 := sp.filter (fun p => m p = 1)
  let s2 := sp.filter (fun p => m p ≠ 1)
  let v := sharpPrimeWeight y
  have h0 : (∑ p ∈ s0, v p) ≤ ∑ d ∈ cutoff y \ n.divisors, signedWeight y d := by
    apply sum_le_sum_of_injOn id (fun _ _ _ _ he => he)
    · intro d hd
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hd
      obtain ⟨hps, hm⟩ := mem_filter.mp hp
      obtain ⟨hprime, hpy, _⟩ := hmask p hps
      change p ∈ cutoff y \ n.divisors
      apply Finset.mem_sdiff.mpr
      refine ⟨mem_Ioc.mpr ⟨hprime.pos, Nat.le_floor (show (p : ℝ) ≤ y by linarith)⟩, ?_⟩
      intro hd
      have hpos := hprime.factorization_pos_of_dvd hn.ne' (Nat.mem_divisors.mp hd).1
      change n.factorization p = 0 at hm
      omega
    · intro p hp
      obtain ⟨hprime, hpy, _⟩ := hmask p (mem_filter.mp hp).1
      exact sharpPrimeWeight_le_missing hy2 hprime hpy
    · intro d hd _
      exact signedWeight_nonneg hy2 (mem_sdiff.mp hd).1
  have h1 : (∑ p ∈ s1, v p) ≤
      ∑ p ∈ n.primeFactors, localEulerGap p (n.factorization p) := by
    apply sum_le_sum_of_injOn id (fun _ _ _ _ he => he)
    · intro d hd
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hd
      obtain ⟨hps, hm⟩ := mem_filter.mp hp
      obtain ⟨hprime, _, _⟩ := hmask p (mem_filter.mp hps).1
      change p ∈ n.primeFactors
      refine Nat.mem_primeFactors.mpr ⟨hprime, ?_, hn.ne'⟩
      by_contra hnot
      have hz := Nat.factorization_eq_zero_of_not_dvd hnot
      change n.factorization p = 1 at hm
      omega
    · intro p hp
      obtain ⟨hps, hm⟩ := mem_filter.mp hp
      have hprime := (hmask p (mem_filter.mp hps).1).1
      change n.factorization p = 1 at hm
      change sharpPrimeWeight y p ≤ localEulerGap p (n.factorization p)
      rw [hm]
      exact (min_le_left _ _).trans (localEulerGap_one_lower hprime)
    · intro p hp _
      exact localEulerGap_nonneg (Nat.prime_of_mem_primeFactors hp)
  have h2 : (∑ p ∈ s2, v p) ≤ ∑ d ∈ n.divisors \ cutoff y, -signedWeight y d := by
    apply sum_le_sum_of_injOn (fun p : ℕ => p ^ 2)
      (Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)).injOn
    · intro d hd
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hd
      obtain ⟨hpos, hmne1⟩ := mem_filter.mp hp
      obtain ⟨hps, hmne0⟩ := mem_filter.mp hpos
      obtain ⟨hprime, _, hsq⟩ := hmask p hps
      change n.factorization p ≠ 0 at hmne0
      change n.factorization p ≠ 1 at hmne1
      apply Finset.mem_sdiff.mpr
      refine ⟨Nat.mem_divisors.mpr ⟨(hprime.pow_dvd_iff_le_factorization hn.ne').mpr
        (by omega), hn.ne'⟩, ?_⟩
      intro hcut
      have hle := (Nat.le_floor_iff (by linarith : 0 ≤ y)).mp (mem_Ioc.mp hcut).2
      rw [Nat.cast_pow] at hle
      exact (not_le_of_gt hsq) hle
    · intro p hp
      obtain ⟨hprime, _, hsq⟩ := hmask p (mem_filter.mp (mem_filter.mp hp).1).1
      exact sharpPrimeWeight_le_extra_square hy2 hprime hsq
    · intro d hd _
      exact neg_signedWeight_nonneg hy2 (mem_sdiff.mp hd).1 (mem_sdiff.mp hd).2
  have hsplit0 : (∑ p ∈ s0, v p) + (∑ p ∈ sp, v p) = ∑ p ∈ s, v p :=
    sum_filter_add_sum_filter_not s (fun p => m p = 0) v
  have hsplit1 : (∑ p ∈ s1, v p) + (∑ p ∈ s2, v p) = ∑ p ∈ sp, v p :=
    sum_filter_add_sum_filter_not sp (fun p => m p = 1) v
  have hclock2 : 2 ≤ Real.log (n : ℝ) := by
    rw [← hclock]
    exact hy2
  have hslack := robin_slack_eq hn hclock2
  rw [← hclock] at hslack
  change (∑ p ∈ s, v p) ≤ _
  linarith only [h0, h1, h2, hsplit0, hsplit1, hslack]

end Ledger

private def primePrefixAt (c y : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊c * Real.sqrt y⌋₊

private def primeShell (a b y : ℝ) : Finset ℕ :=
  primePrefixAt b y \ primePrefixAt a y

private theorem primePrefixAt_mono (y : ℝ) : Monotone (fun c => primePrefixAt c y) :=
  fun _ _ hab => Nat.primesLE_mono
    (Nat.floor_mono (mul_le_mul_of_nonneg_right hab (Real.sqrt_nonneg y)))

private theorem primeShell_bounds {a b y : ℝ} (hb : 0 ≤ b) {p : ℕ}
    (hp : p ∈ primeShell a b y) :
    p.Prime ∧ a * Real.sqrt y < (p : ℝ) ∧ (p : ℝ) ≤ b * Real.sqrt y := by
  obtain ⟨hu, hl⟩ := mem_sdiff.mp hp
  obtain ⟨hup, hprime⟩ := Nat.mem_primesLE.mp hu
  have hlNat : ⌊a * Real.sqrt y⌋₊ < p := by
    by_contra! h
    exact hl (Nat.mem_primesLE.mpr ⟨h, hprime⟩)
  exact ⟨hprime, Nat.lt_of_floor_lt hlNat,
    (Nat.le_floor_iff (mul_nonneg hb (Real.sqrt_nonneg y))).mp hup⟩

private theorem primeShell_sq_gt {a y : ℝ} {p : ℕ} (ha : 1 ≤ a)
    (hp : a * Real.sqrt y < (p : ℝ)) : y < (p : ℝ) ^ 2 := by
  have h := (le_mul_of_one_le_left (Real.sqrt_nonneg y) ha).trans_lt hp
  exact Real.lt_sq_of_sqrt_lt h

private def shellCoefficient (a b y : ℝ) : ℝ :=
  min (1 / (2 * b * (b + (Real.sqrt y)⁻¹))) (1 / 2 - 1 / (2 * a ^ 2))

private def shellPay (a b y : ℝ) : ℝ :=
  ((primeShell a b y).card : ℝ) * (shellCoefficient a b y / y)

private def shellLimit (a b : ℝ) : ℝ :=
  (b - a) * min (1 / b ^ 2) (1 - 1 / a ^ 2)

private theorem shellCoefficient_div_le_weight {a b y : ℝ}
    (hy : 0 < y) (ha : 1 ≤ a) (hab : a ≤ b) {p : ℕ}
    (hp : p ∈ primeShell a b y) :
    shellCoefficient a b y / y ≤ sharpPrimeWeight y p := by
  have ha0 : 0 < a := by linarith
  have hb0 := ha0.trans_le hab
  have hs := Real.sqrt_pos.mpr hy
  obtain ⟨hprime, hlo, hhi⟩ := primeShell_bounds hb0.le hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hprod : 2 * (p : ℝ) * ((p : ℝ) + 1) ≤
      2 * (b * Real.sqrt y) * (b * Real.sqrt y + 1) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hhi (by norm_num))
      (add_le_add_left hhi 1) (by positivity) (by positivity)
  have hsq : (a * Real.sqrt y) ^ 2 ≤ (p : ℝ) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg ha0.le hs.le) hp0.le).mpr hlo.le
  have hval1 := one_div_le_one_div_of_le
    (show 0 < 2 * (p : ℝ) * ((p : ℝ) + 1) by positivity) hprod
  have hval2 := one_div_le_one_div_of_le
    (show 0 < 2 * (a * Real.sqrt y) ^ 2 by positivity)
    (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2))
  have hfactor : 2 * b * (b + (Real.sqrt y)⁻¹) * y =
      2 * (b * Real.sqrt y) * (b * Real.sqrt y + 1) := by
    calc
      _ = 2 * b * (b + (Real.sqrt y)⁻¹) * (Real.sqrt y) ^ 2 := by
        rw [Real.sq_sqrt hy.le]
      _ = _ := by field_simp [hs.ne'] <;> ring
  have hfactor' : 2 * a ^ 2 * y = 2 * (a * Real.sqrt y) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hy.le]
    exact mul_assoc _ _ _
  apply le_min
  · calc
      _ ≤ (1 / (2 * b * (b + (Real.sqrt y)⁻¹))) / y :=
        div_le_div_of_nonneg_right (min_le_left _ _) hy.le
      _ = 1 / (2 * (b * Real.sqrt y) * (b * Real.sqrt y + 1)) := by
        rw [div_div, hfactor]
      _ ≤ _ := hval1
  · calc
      _ ≤ (1 / 2 - 1 / (2 * a ^ 2)) / y :=
        div_le_div_of_nonneg_right (min_le_right _ _) hy.le
      _ = 1 / (2 * y) - 1 / (2 * (a * Real.sqrt y) ^ 2) := by
        rw [sub_div, div_div, div_div, hfactor']
      _ ≤ _ := sub_le_sub_left hval2 _

private theorem shellPay_le_sum {a b y : ℝ} (hy : 0 < y) (ha : 1 ≤ a) (hab : a ≤ b) :
    shellPay a b y ≤ ∑ p ∈ primeShell a b y, sharpPrimeWeight y p := by
  classical
  calc
    _ = ∑ _p ∈ primeShell a b y, shellCoefficient a b y / y := by
      simp [shellPay, nsmul_eq_mul]
    _ ≤ _ := sum_le_sum (fun _ hp => shellCoefficient_div_le_weight hy ha hab hp)

/-- The Chebyshev weight lies between the two endpoint logs times the count. -/
private theorem primeShell_card_scale {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun y : ℝ => ((primeShell a b y).card : ℝ) * Real.log y / Real.sqrt y)
      atTop (𝓝 (2 * (b - a))) := by
  have hb := ha.trans_le hab
  let H : ℝ → ℝ := fun y =>
    (Chebyshev.theta (b * Real.sqrt y) - Chebyshev.theta (a * Real.sqrt y)) / Real.sqrt y
  have hH : Tendsto H atTop (𝓝 (b - a)) := by
    simpa only [H, sub_div] using (theta_sqrt_scale hb).sub (theta_sqrt_scale ha)
  have hL := hH.div (log_sqrt_scale hb) (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hU := hH.div (log_sqrt_scale ha) (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hval : (b - a) / (1 / 2 : ℝ) = 2 * (b - a) := by ring
  rw [hval] at hL hU
  have hbounds : ∀ᶠ y : ℝ in atTop,
      H y / (Real.log (b * Real.sqrt y) / Real.log y) ≤
        ((primeShell a b y).card : ℝ) * Real.log y / Real.sqrt y ∧
      ((primeShell a b y).card : ℝ) * Real.log y / Real.sqrt y ≤
        H y / (Real.log (a * Real.sqrt y) / Real.log y) := by
    have hg := (Real.tendsto_sqrt_atTop.const_mul_atTop ha).eventually
      (eventually_gt_atTop (1 : ℝ))
    filter_upwards [hg, eventually_gt_atTop (1 : ℝ)] with y hay hy
    have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
    have hly : 0 < Real.log y := Real.log_pos hy
    have haby := mul_le_mul_of_nonneg_right hab hs.le
    have hla := Real.log_pos hay
    have hlb := Real.log_pos (hay.trans_le haby)
    let S := primeShell a b y
    have heq :
        Chebyshev.theta (b * Real.sqrt y) - Chebyshev.theta (a * Real.sqrt y) =
          ∑ p ∈ S, Real.log p := by
      rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
      exact (sum_sdiff_eq_sub (f := fun p : ℕ => Real.log p)
        (primePrefixAt_mono y hab)).symm
    have hlo : (S.card : ℝ) * Real.log (a * Real.sqrt y) ≤ ∑ p ∈ S, Real.log p := by
      calc
        _ = ∑ _p ∈ S, Real.log (a * Real.sqrt y) := by simp [nsmul_eq_mul]
        _ ≤ _ := sum_le_sum (fun p hp => Real.log_le_log (by linarith)
          (primeShell_bounds hb.le hp).2.1.le)
    have hhi : (∑ p ∈ S, Real.log p) ≤ (S.card : ℝ) * Real.log (b * Real.sqrt y) := by
      calc
        _ ≤ ∑ _p ∈ S, Real.log (b * Real.sqrt y) := by
          apply sum_le_sum
          intro p hp
          obtain ⟨hprime, _, hbound⟩ := primeShell_bounds hb.le hp
          exact Real.log_le_log (by exact_mod_cast hprime.pos) hbound
        _ = _ := by simp [nsmul_eq_mul]
    have hfactor (c : ℝ) (hlc : 0 < Real.log (c * Real.sqrt y)) :
        H y / (Real.log (c * Real.sqrt y) / Real.log y) =
          ((∑ p ∈ S, Real.log p) / Real.log (c * Real.sqrt y)) *
            (Real.log y / Real.sqrt y) := by
      dsimp only [H]
      rw [heq]
      field_simp [hs.ne', hly.ne', hlc.ne']
    change _ ≤ (S.card : ℝ) * Real.log y / Real.sqrt y ∧
      (S.card : ℝ) * Real.log y / Real.sqrt y ≤ _
    rw [hfactor b hlb, hfactor a hla]
    simp only [mul_div_assoc]
    constructor
    · exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hlb).mpr hhi)
        (div_nonneg hly.le hs.le)
    · exact mul_le_mul_of_nonneg_right ((le_div_iff₀ hla).mpr hlo)
        (div_nonneg hly.le hs.le)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
    (hbounds.mono (fun _ hy => hy.1)) (hbounds.mono (fun _ hy => hy.2))

private theorem shellPay_scale {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun y : ℝ => shellPay a b y * (Real.sqrt y * Real.log y))
      atTop (𝓝 (shellLimit a b)) := by
  have hb := ha.trans_le hab
  have hs : Tendsto (fun y : ℝ => (Real.sqrt y)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hd : Tendsto (fun y : ℝ => 2 * b * (b + (Real.sqrt y)⁻¹))
      atTop (𝓝 (2 * b * b)) := by
    simpa only [add_zero] using (hs.const_add b).const_mul (2 * b)
  have hleft : Tendsto (fun y : ℝ => 1 / (2 * b * (b + (Real.sqrt y)⁻¹)))
      atTop (𝓝 (1 / (2 * b * b))) :=
    tendsto_const_nhds.div hd (by positivity)
  have hcoef : Tendsto (shellCoefficient a b) atTop
      (𝓝 (min (1 / (2 * b * b)) (1 / 2 - 1 / (2 * a ^ 2)))) :=
    hleft.min tendsto_const_nhds
  have h := (primeShell_card_scale ha hab).mul hcoef
  have hval₁ : 2 * (1 / (2 * b * b)) = 1 / b ^ 2 := by
    field_simp [hb.ne']
  have hval₂ : 2 * (1 / 2 - 1 / (2 * a ^ 2)) = 1 - 1 / a ^ 2 := by
    field_simp [ha.ne']
  have hv :
      2 * (b - a) * min (1 / (2 * b * b)) (1 / 2 - 1 / (2 * a ^ 2)) =
        shellLimit a b := by
    rw [mul_comm (2 : ℝ) (b - a), mul_assoc, mul_min_of_nonneg _ _ (by norm_num),
      hval₁, hval₂, shellLimit]
  rw [hv] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have hs0 := (Real.sqrt_pos.mpr hy).ne'
  have hr : Real.sqrt y / y = 1 / Real.sqrt y := by
    apply (div_eq_div_iff hy.ne' hs0).mpr
    simpa only [one_mul, ← pow_two] using Real.sq_sqrt hy.le
  let c := (primeShell a b y).card
  let w := shellCoefficient a b y
  change (c : ℝ) * Real.log y / Real.sqrt y * w =
    (c : ℝ) * (w / y) * (Real.sqrt y * Real.log y)
  calc
    _ = ((c : ℝ) * Real.log y * w) * (1 / Real.sqrt y) := by
      simp only [div_eq_mul_inv, one_mul]
      ring
    _ = ((c : ℝ) * Real.log y * w) * (Real.sqrt y / y) := by rw [hr]
    _ = _ := by
      simp only [div_eq_mul_inv]
      ring

private def shellSum (A : ℕ → ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ range N, shellPay (A k) (A (k + 1)) y

/-- The differences of the nested prime prefixes telescope over the chain. -/
private theorem shellSum_le_band {A : ℕ → ℝ} (hA : Monotone A) (hA0 : 1 ≤ A 0)
    (N : ℕ) {y : ℝ} (hy : 0 < y) :
    shellSum A N y ≤ ∑ p ∈ primeShell (A 0) (A N) y, sharpPrimeWeight y p := by
  let F : ℕ → ℝ := fun k => ∑ p ∈ primePrefixAt (A k) y, sharpPrimeWeight y p
  have hmono : Monotone (fun k => primePrefixAt (A k) y) :=
    (primePrefixAt_mono y).comp hA
  have hstep (k : ℕ) : shellPay (A k) (A (k + 1)) y ≤ F (k + 1) - F k :=
    (shellPay_le_sum hy (hA0.trans (hA (Nat.zero_le k))) (hA (Nat.le_succ k))).trans_eq
      (sum_sdiff_eq_sub (f := sharpPrimeWeight y) (hmono (Nat.le_succ k)))
  calc
    _ ≤ ∑ k ∈ range N, (F (k + 1) - F k) := sum_le_sum (fun k _ => hstep k)
    _ = F N - F 0 := sum_range_sub F N
    _ = _ := (sum_sdiff_eq_sub (f := sharpPrimeWeight y) (hmono (Nat.zero_le N))).symm

private theorem shellSum_scale {A : ℕ → ℝ} (hA : Monotone A) (hA0 : 0 < A 0) (N : ℕ) :
    Tendsto (fun y : ℝ => shellSum A N y * (Real.sqrt y * Real.log y))
      atTop (𝓝 (∑ k ∈ range N, shellLimit (A k) (A (k + 1)))) := by
  simpa only [shellSum, sum_mul] using
    (tendsto_finsetSum (range N) (fun k _ =>
      shellPay_scale (hA0.trans_le (hA (Nat.zero_le k))) (hA (Nat.le_succ k))))

/-- The breakpoint is sqrt 2. Below it the square mismatch
determines the cell limit. The error of the left endpoint is at most width². -/
private theorem leftCell {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.sqrt 2) :
    (b + 1 / b) - (a + 1 / a) ≤ shellLimit a b + (b - a) ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hb0 := ha0.trans_le hab
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hb2 : b ^ 2 ≤ 2 :=
    ((sq_le_sq₀ hb0.le (Real.sqrt_nonneg 2)).mpr hb).trans_eq hs
  have ha2 : a ^ 2 ≤ 2 := ((sq_le_sq₀ ha0.le hb0.le).mpr hab).trans hb2
  have hA : (1 / 2 : ℝ) ≤ 1 / a ^ 2 := one_div_le_one_div_of_le (by positivity) ha2
  have hB : (1 / 2 : ℝ) ≤ 1 / b ^ 2 := one_div_le_one_div_of_le (by positivity) hb2
  have hmin : 1 - 1 / a ^ 2 ≤ 1 / b ^ 2 := by linarith
  unfold shellLimit
  rw [min_eq_right hmin]
  have hden : 1 ≤ a ^ 2 * b := by
    have hb1 := ha.trans hab
    have haa : 1 ≤ a ^ 2 := one_le_pow₀ ha
    calc
      1 ≤ a ^ 2 := haa
      _ ≤ a ^ 2 * b := le_mul_of_one_le_right (sq_nonneg a) hb1
  have heq : (b + 1 / b) - (a + 1 / a) - (b - a) * (1 - 1 / a ^ 2) =
      (b - a) ^ 2 / (a ^ 2 * b) := by
    field_simp [ha0.ne', hb0.ne']
    ring
  have herr : (b - a) ^ 2 / (a ^ 2 * b) ≤ (b - a) ^ 2 := by
    simpa only [div_one] using
      (div_le_div_of_nonneg_left (sq_nonneg (b - a)) (by norm_num : (0 : ℝ) < 1) hden)
  linarith only [heq, herr]

private theorem rightCell {a b : ℝ} (ha : Real.sqrt 2 ≤ a) (hab : a ≤ b) :
    shellLimit a b = (b - a) / b ^ 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have ha0 : 0 < a := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).trans_le ha
  have hb0 := ha0.trans_le hab
  have ha2 : 2 ≤ a ^ 2 :=
    hs.symm.trans_le ((sq_le_sq₀ (Real.sqrt_nonneg 2) ha0.le).mpr ha)
  have hb2 := ha2.trans ((sq_le_sq₀ ha0.le hb0.le).mpr hab)
  have hA : 1 / a ^ 2 ≤ (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) ha2
  have hB : 1 / b ^ 2 ≤ (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hb2
  have hmin : 1 / b ^ 2 ≤ 1 - 1 / a ^ 2 := by linarith
  rw [shellLimit, min_eq_left hmin, mul_one_div]

private theorem leftShells {δ : ℝ} (hδ : 0 < δ) :
    ∃ (A : ℕ → ℝ) (M : ℕ), Monotone A ∧ A 0 = 1 ∧ A M = Real.sqrt 2 ∧
      Real.sqrt 2 + 1 / Real.sqrt 2 - 2 - δ <
        ∑ k ∈ range M, shellLimit (A k) (A (k + 1)) := by
  let s := Real.sqrt 2
  have hs2 : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 ≤ s := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hslt : s ≤ 2 := by
    calc
      s ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      _ = 2 := by norm_num
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
  have hM0 : 0 < (M : ℝ) := (by positivity : 0 < 1 / δ).trans hM
  let h : ℝ := (s - 1) / (M : ℝ)
  have hh : 0 ≤ h := div_nonneg (sub_nonneg.mpr hs1) hM0.le
  let A : ℕ → ℝ := fun k => 1 + (k : ℝ) * h
  have hA : Monotone A := by
    intro i j hij
    exact add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hh) 1
  have hA0 : A 0 = 1 := by simp [A]
  have hAM : A M = s := by
    dsimp [A, h]
    field_simp [hM0.ne'] <;> ring
  have hcell (k : ℕ) (hk : k ∈ range M) :
      (A (k + 1) + 1 / A (k + 1)) - (A k + 1 / A k) ≤
        shellLimit (A k) (A (k + 1)) + h ^ 2 := by
    have hlow : 1 ≤ A k := hA0.symm.trans_le (hA (Nat.zero_le k))
    have hhigh : A (k + 1) ≤ s := (hA (Nat.succ_le_of_lt (mem_range.mp hk))).trans_eq hAM
    have hw : A (k + 1) - A k = h := by
      simp only [A, Nat.cast_add, Nat.cast_one]
      ring
    simpa only [hw] using leftCell hlow (hA (Nat.le_succ k)) hhigh
  have hsum :
      (∑ k ∈ range M, ((A (k + 1) + 1 / A (k + 1)) - (A k + 1 / A k))) ≤
        ∑ k ∈ range M, (shellLimit (A k) (A (k + 1)) + h ^ 2) :=
    sum_le_sum hcell
  rw [sum_range_sub (fun k => A k + 1 / A k) M, sum_add_distrib] at hsum
  simp only [hA0, hAM, sum_const, card_range, nsmul_eq_mul, div_one] at hsum
  have hmesh : (M : ℝ) * h ^ 2 = (s - 1) ^ 2 / (M : ℝ) := by
    dsimp only [h]
    field_simp [hM0.ne'] <;> ring
  have hbudget : (M : ℝ) * h ^ 2 < δ := by
    rw [hmesh]
    apply (div_lt_iff₀ hM0).mpr
    have hsq : (s - 1) ^ 2 ≤ 1 := by nlinarith only [hs1, hslt, hs2]
    have hlt := (div_lt_iff₀ hδ).mp hM
    exact hsq.trans_lt (by nlinarith only [hlt])
  refine ⟨A, M, hA, hA0, hAM, ?_⟩
  change s + 1 / s - 2 - δ < _
  linarith only [hsum, hbudget]

private theorem two_div_sqrt_two : 2 * (1 / Real.sqrt (2 : ℝ)) = Real.sqrt 2 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  rw [mul_one_div]
  exact (div_eq_iff hs.ne').mpr (by nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])

section GeometricShells

open private shell_parameters from D5.S3.Arith.Robin.PrimeMinCorrectionLower

/-- The existing geometric parameter estimate controls the reciprocal-square
side of the breakpoint. A possible gap from sqrt 2 to the first shell is
already accounted for in that estimate. -/
private theorem rightShells {δ : ℝ} (hδ : 0 < δ) :
    ∃ (B : ℕ → ℝ) (N : ℕ), Monotone B ∧ Real.sqrt 2 ≤ B 0 ∧
      1 / Real.sqrt 2 - δ < ∑ k ∈ range N, shellLimit (B k) (B (k + 1)) := by
  obtain ⟨a, b, r, N, ha, ha2, _, hb, hb2, hr, _, hsum⟩ := shell_parameters hδ
  let s := Real.sqrt 2
  have hs : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs_inv : 2 * (1 / s) = s := two_div_sqrt_two
  have haS : a ≤ s := (sq_le_sq₀ ha.le hs.le).mp (ha2.le.trans_eq hs2.symm)
  have hbS : s ≤ b := (sq_le_sq₀ hs.le hb.le).mp (hs2.trans_le hb2.le)
  let B : ℕ → ℝ := fun k => b * r ^ k
  have hB : Monotone B := fun _ _ hij =>
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr.le hij) hb.le
  have hB0 : s ≤ B 0 := by simpa [B] using hbS
  have hterm (k : ℕ) :
      2 * (B (k + 1) - B k) / (B (k + 1)) ^ 2 =
        2 * shellLimit (B k) (B (k + 1)) := by
    rw [rightCell (hB0.trans (hB (Nat.zero_le k))) (hB (Nat.le_succ k))]
    rw [mul_div_assoc]
  change 2 * s - δ < a + ∑ k ∈ range N,
    2 * (B (k + 1) - B k) / (B (k + 1)) ^ 2 at hsum
  simp_rw [hterm] at hsum
  rw [← mul_sum] at hsum
  refine ⟨B, N, hB, hB0, ?_⟩
  change 1 / s - δ < _
  linarith only [hsum, haS, hs_inv, hδ]

end GeometricShells

private theorem twoShellSums_le_ledger {n : ℕ} {y : ℝ}
    (hclock : y = Real.log (n : ℝ)) (hy : 16 ≤ y)
    {A B : ℕ → ℝ} (hA : Monotone A) (hB : Monotone B) {M N : ℕ}
    (hA0 : A 0 = 1) (hAM : A M = Real.sqrt 2) (hB0 : Real.sqrt 2 ≤ B 0)
    (hcut : B N * Real.sqrt y ≤ y / 2) :
    shellSum A M y + shellSum B N y ≤ robinLogMargin n - weightedTail psiErrorKernel y := by
  classical
  have hy0 : 0 < y := by linarith
  have h01 : 1 ≤ A M := by
    rw [← hA0]
    exact hA (Nat.zero_le M)
  have h12 : A M ≤ B 0 := by simpa only [hAM] using hB0
  have h23 := hB (Nat.zero_le N)
  have h03 := h01.trans (h12.trans h23)
  let L := primePrefixAt 1 y
  let P := primePrefixAt (A M) y
  let Q := primePrefixAt (B 0) y
  let U := primePrefixAt (B N) y
  have hLP : L ⊆ P := primePrefixAt_mono y h01
  have hPQ : P ⊆ Q := primePrefixAt_mono y h12
  have hQU : Q ⊆ U := primePrefixAt_mono y h23
  have hPU : P ⊆ U := hPQ.trans hQU
  have hLU : L ⊆ U := hLP.trans hPU
  let v := sharpPrimeWeight y
  have hleft : shellSum A M y ≤ ∑ p ∈ P \ L, v p := by
    simpa only [hA0, P, L, primeShell, v] using
      shellSum_le_band hA (by rw [hA0]) M hy0
  have hright : shellSum B N y ≤ ∑ p ∈ U \ Q, v p :=
    shellSum_le_band hB (h01.trans h12) N hy0
  have hsubset : U \ Q ⊆ U \ P := by
    intro p hp
    obtain ⟨hpU, hpQ⟩ := mem_sdiff.mp hp
    exact mem_sdiff.mpr ⟨hpU, fun hpP => hpQ (hPQ hpP)⟩
  have hright' : (∑ p ∈ U \ Q, v p) ≤ ∑ p ∈ U \ P, v p := by
    apply sum_le_sum_of_subset_of_nonneg hsubset
    intro p hp _
    have hb : 0 ≤ B N := by linarith only [h03]
    have hlo := (primeShell_bounds hb (show p ∈ primeShell (A M) (B N) y from hp)).2.1
    exact sharpPrimeWeight_nonneg hy0 (primeShell_sq_gt h01 hlo)
  have hmerge : (∑ p ∈ P \ L, v p) + (∑ p ∈ U \ P, v p) = ∑ p ∈ U \ L, v p := by
    rw [sum_sdiff_eq_sub hLP, sum_sdiff_eq_sub hPU, sum_sdiff_eq_sub hLU]
    ring
  have hledger : (∑ p ∈ U \ L, v p) ≤
      robinLogMargin n - weightedTail psiErrorKernel y := by
    apply finite_prime_reserve hclock hy (U \ L)
    intro p hp
    have hb : 0 ≤ B N := by linarith only [h03]
    obtain ⟨hprime, hlo, hhi⟩ :=
      primeShell_bounds hb (show p ∈ primeShell 1 (B N) y from hp)
    exact ⟨hprime, hhi.trans hcut, primeShell_sq_gt le_rfl hlo⟩
  exact ((add_le_add hleft (hright.trans hright')).trans_eq hmerge).trans hledger

/-- Unconditional lower reserve at the logarithmic clock of every natural
number past one threshold. -/
theorem sharp_lower_reserve_all_integers {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℝ, 16 ≤ Y ∧ ∀ n : ℕ, Y ≤ Real.log (n : ℝ) →
      (2 * Real.sqrt 2 - 2 - ε) /
          (Real.sqrt (Real.log (n : ℝ)) * Real.log (Real.log (n : ℝ))) <
        robinLogMargin n - weightedTail psiErrorKernel (Real.log (n : ℝ)) := by
  have hδ : 0 < ε / 4 := div_pos hε (by norm_num)
  obtain ⟨A, M, hA, hA0, hAM, hleft⟩ := leftShells hδ
  obtain ⟨B, N, hB, hB0, hright⟩ := rightShells hδ
  have hApos : 0 < A 0 := by rw [hA0]; norm_num
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs_inv : 2 * (1 / Real.sqrt (2 : ℝ)) = Real.sqrt 2 := two_div_sqrt_two
  have htarget :
      2 * Real.sqrt 2 - 2 - ε <
        (∑ k ∈ range M, shellLimit (A k) (A (k + 1))) +
        (∑ k ∈ range N, shellLimit (B k) (B (k + 1))) := by
    linarith only [hleft, hright, hs_inv, hε]
  have hlimit := (shellSum_scale hA hApos M).add
    (shellSum_scale hB (hs.trans_le hB0) N)
  have hlarge := hlimit.eventually_const_lt htarget
  have hcut := Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (2 * B N))
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlarge.and hcut)
  refine ⟨max T 16, le_max_right _ _, ?_⟩
  intro n hn
  let y := Real.log (n : ℝ)
  change max T 16 ≤ y at hn
  have hy : 16 ≤ y := (le_max_right _ _).trans hn
  have hy0 : 0 ≤ y := by linarith
  obtain ⟨hlarge', hcut'⟩ := hT y ((le_max_left _ _).trans hn)
  have hcut'' : B N * Real.sqrt y ≤ y / 2 := by
    have h := mul_le_mul_of_nonneg_right hcut' (Real.sqrt_nonneg y)
    nlinarith only [h, Real.sq_sqrt hy0]
  have hD : 0 < Real.sqrt y * Real.log y :=
    mul_pos (Real.sqrt_pos.mpr (by linarith)) (Real.log_pos (by linarith))
  have hstrict : (2 * Real.sqrt 2 - 2 - ε) / (Real.sqrt y * Real.log y) <
      shellSum A M y + shellSum B N y := by
    apply (div_lt_iff₀ hD).mpr
    rw [add_mul]
    exact hlarge'
  exact hstrict.trans_le (twoShellSums_le_ledger rfl hy hA hB hA0 hAM hB0 hcut'')

#print axioms sharp_lower_reserve_all_integers

end D5.S3.Arith.Robin.WeightedTail.SharpReserveLower
