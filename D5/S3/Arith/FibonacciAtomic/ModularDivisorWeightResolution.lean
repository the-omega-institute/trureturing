/- GID: D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Factorial congruence domains have a sharp logarithmic divisor-weight resolution. -/

import D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Nat.GCD.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset Filter Asymptotics Real
open scoped BigOperators Topology
open D5.S3.Arith.RobinExponentSwap
open D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
open D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer

namespace D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution

noncomputable def blockSet (m : ℕ) (x : ℝ) : Finset ℕ := (Ioc m ⌊x⌋₊).filter Nat.Prime
noncomputable def primeBlock (m : ℕ) (x : ℝ) : ℕ := ∏ p ∈ blockSet m x, p
noncomputable def lowerCutoff (C : ℝ) (m : ℕ) : ℝ := ((C - 1) / 8) * m * log m
noncomputable def lowerNumber (C : ℝ) (m : ℕ) : ℕ := m.factorial * primeBlock m (lowerCutoff C m)
noncomputable def pairValues (C : ℝ) (m : ℕ) : Set ℝ :=
  {r | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
    (a : ℝ) ≤ (m.factorial : ℝ)^C ∧ (b : ℝ) ≤ (m.factorial : ℝ)^C ∧
    Nat.ModEq m.factorial a b ∧ r = normalizedWeight a / normalizedWeight b}
noncomputable def extremeRatio (C : ℝ) (m : ℕ) : ℝ := sSup (pairValues C m)

/-- The sharp relative resolution, attained by an explicit factorial prime block,
    and the additive divergence of the same congruent pair. -/
theorem result (C : ℝ) (hC : 1 < C) :
    (∀ m : ℕ, (pairValues C m).Finite ∧ (1 : ℝ) ∈ pairValues C m ∧
      extremeRatio C m ∈ pairValues C m ∧ 1 ≤ extremeRatio C m) ∧
    (∀ᶠ m : ℕ in atTop,
      0 < lowerNumber C m ∧
      (lowerNumber C m : ℝ) ≤ (m.factorial : ℝ)^C ∧
      (m.factorial : ℝ) ≤ (m.factorial : ℝ)^C ∧
      Nat.ModEq m.factorial (lowerNumber C m) m.factorial ∧
      Nat.Coprime m.factorial (primeBlock m (lowerCutoff C m)) ∧
      normalizedWeight (lowerNumber C m) / normalizedWeight m.factorial =
        ∏ p ∈ blockSet m (lowerCutoff C m), (1 + (p : ℝ)⁻¹)) ∧
    Tendsto (fun m : ℕ => (extremeRatio C m - 1) *
      (log m / log (log m))) atTop (𝓝 1) ∧
    Tendsto (fun m : ℕ =>
      (normalizedWeight (lowerNumber C m) / normalizedWeight m.factorial - 1) *
      (log m / log (log m))) atTop (𝓝 1) ∧
    Tendsto (fun m : ℕ =>
      (normalizedWeight (lowerNumber C m) - normalizedWeight m.factorial) /
      (exp eulerMascheroniConstant * log (log m))) atTop (𝓝 1) ∧
    Tendsto (fun m : ℕ =>
      normalizedWeight (lowerNumber C m) - normalizedWeight m.factorial) atTop atTop := by
  classical
  have intervalRate : ∀ Y : ℕ → ℝ, (∀ᶠ m : ℕ in atTop, (m : ℝ) ≤ Y m) →
      Tendsto (fun m : ℕ => (log (Y m) - log m) / log (log m)) atTop (𝓝 1) →
      Tendsto (fun m : ℕ => log (primeProduct (Y m) / primeProduct m) *
        (log m / log (log m))) atTop (𝓝 1) := by
    intro Y hYge hdev
    classical
    have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hL := tendsto_log_atTop.comp hnat
    have hQ := tendsto_log_atTop.comp hL
    have hq0 : Tendsto (fun m : ℕ => log (log m) / log m) atTop (𝓝 0) :=
      (isLittleO_log_id_atTop.comp_tendsto hL).tendsto_div_nhds_zero
    have hY : Tendsto Y atTop atTop := tendsto_atTop_mono' atTop hYge hnat
    have hLY := tendsto_log_atTop.comp hY
    have hratio : Tendsto (fun m : ℕ => log (Y m) / log m) atTop (𝓝 1) := by
      have ht := (hdev.mul hq0).add_const 1
      simp only [mul_zero, zero_add] at ht
      apply ht.congr'
      filter_upwards [hL.eventually_gt_atTop 0, hQ.eventually_gt_atTop 0] with m hLm hQm
      change 0 < log (m : ℝ) at hLm
      change 0 < log (log (m : ℝ)) at hQm
      field_simp [hLm.ne', hQm.ne']
      <;> ring
    have logPrime (x : ℝ) (hx : 1 < x) :
        log (primeProduct x) = eulerMascheroniConstant + log (log x) - Mertens.E₃ x := by
      have pos (p : ℕ) (hp : p.Prime) : 0 < 1 - (p : ℝ)⁻¹ :=
        sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))
      rw [primeProduct, log_prod (fun p hp => inv_ne_zero (pos p (mem_filter.mp hp).2).ne')]
      simp_rw [log_inv]
      simp only [Mertens.E₃, one_div, sum_neg_distrib]
      ring
    have error (Z : ℕ → ℝ) (hZ : Tendsto Z atTop atTop)
        (hr : Tendsto (fun m : ℕ => log (Z m) / log m) atTop (𝓝 1)) :
        Tendsto (fun m : ℕ => Mertens.E₃ (Z m) * (log m / log (log m))) atTop (𝓝 0) := by
      have hb := (Mertens.E₃.bound.comp_tendsto hZ).mul
        (isBigO_refl (fun m : ℕ => log m / log (log m)) atTop)
      have hs : Tendsto (fun m : ℕ => (1 / log (Z m)) * (log m / log (log m)))
          atTop (𝓝 0) := by
        have ht := (hr.inv₀ one_ne_zero).mul (hQ.const_div_atTop 1)
        simp only [inv_one, one_mul, mul_zero] at ht
        apply ht.congr'
        filter_upwards [hL.eventually_gt_atTop 0, (tendsto_log_atTop.comp hZ).eventually_gt_atTop 0]
          with m hm hz
        change 0 < log (m : ℝ) at hm
        change 0 < log (Z m) at hz
        try simp only [Function.comp_def, Function.id_def] at *
        field_simp [hm.ne', hz.ne']
        <;> ring
      exact hb.trans_tendsto hs
    have em := error (fun m : ℕ => (m : ℝ)) hnat (by
      have ht : (fun m : ℕ => log m / log m) =ᶠ[atTop] fun _ => (1 : ℝ) := by
        filter_upwards [hL.eventually_gt_atTop 0] with m hm
        exact div_self (ne_of_gt hm)
      exact tendsto_const_nhds.congr' ht.symm)
    have eY := error Y hY hratio
    have hslope : Tendsto (fun m : ℕ => dslope log 1 (log (Y m) / log m)) atTop (𝓝 1) := by
      have hd := hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
      have hc := continuousAt_dslope_same.mpr hd.differentiableAt
      have ht := hc.tendsto.comp hratio
      simpa only [Function.comp_def, dslope_same, hd.deriv, inv_one] using ht
    have hlldiff : Tendsto (fun m : ℕ =>
        (log (log (Y m)) - log (log m)) * (log m / log (log m))) atTop (𝓝 1) := by
      have ht := hslope.mul hdev
      simp only [one_mul] at ht
      apply ht.congr'
      filter_upwards [hL.eventually_gt_atTop 0, hLY.eventually_gt_atTop 0,
        hQ.eventually_gt_atTop 0] with m hm hy hq
      change 0 < log (m : ℝ) at hm
      change 0 < log (Y m) at hy
      change 0 < log (log (m : ℝ)) at hq
      have hh := sub_smul_dslope log (1 : ℝ) (log (Y m) / log m)
      simp only [smul_eq_mul, log_one] at hh
      rw [log_div hy.ne' hm.ne'] at hh
      try simp only [Function.comp_def, Function.id_def]
      field_simp [hm.ne', hq.ne'] at hh ⊢
      nlinarith [hh]
    have ht := (hlldiff.sub eY).add em
    simp only [sub_zero, add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (1 : ℕ), hY.eventually_gt_atTop 1] with m hm hy
    have hmR : (1 : ℝ) < m := by exact_mod_cast hm
    have pp (x : ℝ) : 0 < primeProduct x := by
      exact prod_pos (fun p hp => inv_pos.mpr (sub_pos.mpr
        (inv_lt_one_of_one_lt₀ (by exact_mod_cast (mem_filter.mp hp).2.one_lt))))
    rw [log_div (pp _).ne' (pp _).ne', logPrime _ hy, logPrime _ hmR]
    ring

  have construction : ∀ᶠ m : ℕ in atTop,
      0 < lowerNumber C m ∧
      (lowerNumber C m : ℝ) ≤ (m.factorial : ℝ) ^ C ∧
      (m.factorial : ℝ) ≤ (m.factorial : ℝ) ^ C ∧
      Nat.ModEq m.factorial (lowerNumber C m) m.factorial ∧
      Nat.Coprime m.factorial (primeBlock m (lowerCutoff C m)) ∧
      normalizedWeight (lowerNumber C m) / normalizedWeight m.factorial =
        ∏ p ∈ blockSet m (lowerCutoff C m), (1 + (p : ℝ)⁻¹) := by
    classical
    have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hL := tendsto_log_atTop.comp hnat
    filter_upwards [hL.eventually_gt_atTop 2, eventually_ge_atTop (2 : ℕ)] with m hLm hm
    change 2 < log (m : ℝ) at hLm
    let x := lowerCutoff C m
    let s := blockSet m x
    let q := primeBlock m x
    have prime (p : ℕ) (hp : p ∈ s) : p.Prime := (mem_filter.mp hp).2
    have qpos : 0 < q := prod_pos (fun p hp => (prime p hp).pos)
    have fpos : 0 < m.factorial := Nat.factorial_pos m
    have fposR : 0 < (m.factorial : ℝ) := by exact_mod_cast fpos
    have fone : (1 : ℝ) ≤ m.factorial := by exact_mod_cast Nat.succ_le_of_lt fpos
    have hcop : Nat.Coprime m.factorial q := by
      apply Nat.coprime_prod_right_iff.mpr
      intro p hp
      exact ((prime p hp).coprime_factorial_of_lt (mem_Ioc.mp (mem_filter.mp hp).1).1).symm
    have hqbound : q ≤ primorial ⌊x⌋₊ := by
      apply Finset.prod_le_prod_of_subset_of_one_le
      · intro p hp
        obtain ⟨hpI, hprime⟩ := mem_filter.mp hp
        exact mem_filter.mpr ⟨mem_range.mpr (by have := (mem_Ioc.mp hpI).2; omega), hprime⟩
      · intro p _; exact Nat.zero_le p
      · intro p hp _; exact (mem_filter.mp hp).2.one_lt.le
    have hx0 : 0 ≤ x := by dsimp [x, lowerCutoff]; positivity
    have hqlog : log (q : ℝ) ≤ 4 * x := by
      have h4 : (q : ℝ) ≤ (4 : ℝ) ^ ⌊x⌋₊ := by
        exact_mod_cast hqbound.trans (primorial_le_four_pow _)
      have hlog := log_le_log (by exact_mod_cast qpos) h4
      rw [log_pow] at hlog
      have hlog4 : log (4 : ℝ) ≤ 4 := log_le_self (by norm_num)
      calc
        _ ≤ (⌊x⌋₊ : ℝ) * log 4 := hlog
        _ ≤ (⌊x⌋₊ : ℝ) * 4 := mul_le_mul_of_nonneg_left hlog4 (Nat.cast_nonneg _)
        _ ≤ 4 * x := by nlinarith [Nat.floor_le hx0]
    have hflog : m * log (m : ℝ) - m ≤ log (m.factorial : ℝ) := by
      have hs := Stirling.le_log_factorial_stirling (by omega : m ≠ 0)
      have hpi : 0 ≤ log (2 * Real.pi) := log_nonneg (by nlinarith [Real.two_le_pi])
      nlinarith
    have haH : (lowerNumber C m : ℝ) ≤ (m.factorial : ℝ) ^ C := by
      apply (log_le_log_iff (by dsimp [lowerNumber]; positivity)
        (rpow_pos_of_pos fposR _)).mp
      rw [log_rpow fposR]
      simp only [lowerNumber, Nat.cast_mul]
      change log ((m.factorial : ℝ) * (q : ℝ)) ≤ _
      rw [log_mul fposR.ne' (by exact_mod_cast qpos.ne')]
      have ht : 4 * x ≤ (C - 1) * log (m.factorial : ℝ) := by
        have hhalf : (m : ℝ) * log m / 2 ≤ log (m.factorial : ℝ) := by
          have hmul := mul_le_mul_of_nonneg_left hLm.le (Nat.cast_nonneg m)
          nlinarith
        have hscale := mul_le_mul_of_nonneg_left hhalf (sub_pos.mpr hC).le
        dsimp [x, lowerCutoff]
        nlinarith
      linarith
    have hbH : (m.factorial : ℝ) ≤ (m.factorial : ℝ) ^ C := by
      simpa only [rpow_one] using rpow_le_rpow_of_exponent_le fone hC.le
    have hratio : normalizedWeight (lowerNumber C m) / normalizedWeight m.factorial =
        ∏ p ∈ s, (1 + (p : ℝ)⁻¹) := by
      have hsigma := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop
      have hprod := ArithmeticFunction.IsMultiplicative.map_prod_of_prime
        (ArithmeticFunction.isMultiplicative_sigma (k := 1)) s prime
      have hprimeSig (p : ℕ) (hp : p ∈ s) : ArithmeticFunction.sigma 1 p = p + 1 := by
        simpa [Finset.sum_range_succ, Nat.add_comm] using ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) (prime p hp)
      have hqSig : (ArithmeticFunction.sigma 1 q : ℝ) = ∏ p ∈ s, ((p : ℝ) + 1) := by
        change (ArithmeticFunction.sigma 1 (∏ p ∈ s, p) : ℝ) = _
        rw [hprod, Nat.cast_prod]
        apply prod_congr rfl
        intro p hp
        rw [hprimeSig p hp]
        simp only [Nat.cast_add, Nat.cast_one]
      have hz : normalizedWeight m.factorial ≠ 0 := by
        exact ne_of_gt (div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 _ fpos.ne') fposR)
      have hs : (ArithmeticFunction.sigma 1 m.factorial : ℝ) ≠ 0 := by
        exact_mod_cast (ArithmeticFunction.sigma_pos 1 _ fpos.ne').ne'
      dsimp [normalizedWeight, lowerNumber]
      rw [hsigma]
      simp only [Nat.cast_mul]
      have hr : ((ArithmeticFunction.sigma 1 m.factorial : ℝ) *
          (ArithmeticFunction.sigma 1 q : ℝ) / ((m.factorial : ℝ) * q)) /
          ((ArithmeticFunction.sigma 1 m.factorial : ℝ) / m.factorial) =
          (ArithmeticFunction.sigma 1 q : ℝ) / q := by
        field_simp [hs, fposR.ne', (by exact_mod_cast qpos.ne' : (q : ℝ) ≠ 0)]
      rw [hr, hqSig]
      change (∏ p ∈ s, ((p : ℝ) + 1)) / ((∏ p ∈ s, p : ℕ) : ℝ) = _
      rw [Nat.cast_prod]
      rw [← prod_div_distrib]
      apply prod_congr rfl
      intro p hp
      field_simp [(by exact_mod_cast (prime p hp).ne_zero : (p : ℝ) ≠ 0)]
    refine ⟨by dsimp [lowerNumber]; exact Nat.mul_pos fpos qpos, haH, hbH, ?_, hcop, hratio⟩
    exact Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _) |>.trans
      (Nat.modEq_zero_iff_dvd.mpr dvd_rfl).symm

  have correction (m : ℕ) (hm : 2 ≤ m) (x : ℝ) (hx : (m : ℝ) ≤ x) :
      let s := (Ioc m ⌊x⌋₊).filter Nat.Prime
      let T := ∏ p ∈ s, (1 - ((p : ℝ)⁻¹)^2)
      0 < T ∧ 1 - (m : ℝ)⁻¹ ≤ T ∧ T ≤ 1 ∧
      (∏ p ∈ s, (1 + (p : ℝ)⁻¹)) = T * (primeProduct x / primeProduct m) := by
    classical
    dsimp only
    let s := (Ioc m ⌊x⌋₊).filter Nat.Prime
    let T := ∏ p ∈ s, (1 - ((p : ℝ)⁻¹)^2)
    have mpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hN : m ≤ ⌊x⌋₊ := Nat.le_floor hx
    have invbounds (p : ℕ) (hp : p ∈ s) : 0 ≤ ((p : ℝ)⁻¹)^2 ∧ ((p : ℝ)⁻¹)^2 < 1 := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
      exact ⟨sq_nonneg _, pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hp1) (by norm_num)⟩
    have telescope (N : ℕ) (hNm : m ≤ N) :
        (∑ p ∈ Ioc m N, 1 / ((p : ℝ) * (p - 1))) = (m : ℝ)⁻¹ - (N : ℝ)⁻¹ := by
      induction N, hNm using Nat.le_induction with
      | base => simp
      | succ N hNm ih =>
        rw [sum_Ioc_succ_top hNm, ih]
        have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        push_cast
        field_simp [mpos.ne', hNp.ne']
        ring
    have sumBound : (∑ p ∈ s, ((p : ℝ)⁻¹)^2) ≤ (m : ℝ)⁻¹ := by
      calc
        _ ≤ ∑ p ∈ s, 1 / ((p : ℝ) * (p - 1)) := by
          apply sum_le_sum
          intro p hp
          have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
          rw [inv_pow, one_div]
          apply inv_anti₀ (mul_pos (by positivity) (sub_pos.mpr hp1))
          nlinarith
        _ ≤ ∑ p ∈ Ioc m ⌊x⌋₊, 1 / ((p : ℝ) * (p - 1)) := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro p hp _
          have hp1 : (1 : ℝ) < p := by exact_mod_cast (by have := (mem_Ioc.mp hp).1; omega : 1 < p)
          positivity
        _ = (m : ℝ)⁻¹ - (⌊x⌋₊ : ℝ)⁻¹ := telescope _ hN
        _ ≤ (m : ℝ)⁻¹ := sub_le_self _ (by positivity)
    have Tpos : 0 < T := prod_pos (fun p hp => sub_pos.mpr (invbounds p hp).2)
    have Tup : T ≤ 1 := prod_le_one
      (fun p hp => (sub_pos.mpr (invbounds p hp).2).le)
      (fun p hp => sub_le_self _ (invbounds p hp).1)
    have Tlow : 1 - (m : ℝ)⁻¹ ≤ T := by
      apply (sub_le_sub_left sumBound 1).trans
      dsimp [T]
      rw [prod_one_sub_ordered]
      apply sub_le_sub_left
      apply sum_le_sum
      intro p hp
      apply mul_le_of_le_one_right (invbounds p hp).1
      exact prod_le_one
        (fun j hj => (sub_pos.mpr (invbounds j (mem_filter.mp hj).1).2).le)
        (fun j hj => sub_le_self _ (invbounds j (mem_filter.mp hj).1).1)
    refine ⟨Tpos, Tlow, Tup, ?_⟩
    have quotient : (∏ p ∈ s, (1 - (p : ℝ)⁻¹)⁻¹) = primeProduct x / primeProduct m := by
      have hsplit := prod_filter_mul_prod_filter_not
        ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) (fun p => p ≤ m)
        (fun p => (1 - (p : ℝ)⁻¹)⁻¹)
      have lo : (((Ioc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p => p ≤ m)) =
          (Ioc 0 m).filter Nat.Prime := by
        ext p
        simp only [mem_filter, mem_Ioc]
        constructor
        · rintro ⟨⟨⟨hp0, _⟩, hprime⟩, hpm⟩
          exact ⟨⟨hp0, hpm⟩, hprime⟩
        · rintro ⟨⟨hp0, hpm⟩, hprime⟩
          exact ⟨⟨⟨hp0, hpm.trans hN⟩, hprime⟩, hpm⟩
      have hi : (((Ioc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p => ¬p ≤ m)) = s := by
        ext p
        simp only [mem_filter, mem_Ioc, s, not_le]
        have hpm : m < p → 0 < p := fun h => lt_of_le_of_lt (Nat.zero_le _) h
        tauto
      rw [lo, hi] at hsplit
      have hpos : 0 < ∏ p ∈ (Ioc 0 m).filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹ := by
        exact prod_pos (fun p hp => inv_pos.mpr (sub_pos.mpr
          (inv_lt_one_of_one_lt₀ (by exact_mod_cast (mem_filter.mp hp).2.one_lt))))
      simp only [primeProduct, Nat.floor_natCast]
      apply (eq_div_iff hpos.ne').mpr
      simpa [mul_comm] using hsplit
    rw [← quotient]
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    have hne : 1 - (p : ℝ)⁻¹ ≠ 0 := (sub_pos.mpr
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (mem_filter.mp hp).2.one_lt))).ne'
    field_simp [hne]
    ring

  have cutoffs (k : ℝ) (hk : 0 < k) :
      (∀ᶠ m : ℕ in atTop, (m : ℝ) ≤ k * m * log m) ∧
      Tendsto (fun m : ℕ => (log (k * m * log m) - log m) / log (log m)) atTop (𝓝 1) ∧
      (∀ᶠ m : ℕ in atTop, (m : ℝ) ≤ m * log m * log (log m)) ∧
      Tendsto (fun m : ℕ => (log (m * log m * log (log m)) - log m) / log (log m))
        atTop (𝓝 1) := by
    have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hL := tendsto_log_atTop.comp hnat
    have hQ := tendsto_log_atTop.comp hL
    refine ⟨?_, ?_, ?_, ?_⟩
    · filter_upwards [hL.eventually_ge_atTop (1 / k)] with m hm
      change 1 / k ≤ log (m : ℝ) at hm
      have hs : 1 ≤ k * log (m : ℝ) := by
        have hh := mul_le_mul_of_nonneg_left hm hk.le
        field_simp [hk.ne'] at hh
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    · have ht := (hQ.const_div_atTop (log k)).add_const 1
      simp only [zero_add] at ht
      apply ht.congr'
      filter_upwards [hL.eventually_gt_atTop 0, hQ.eventually_gt_atTop 0,
        eventually_gt_atTop (0 : ℕ)] with m hm hq hm0
      change 0 < log (m : ℝ) at hm
      change 0 < log (log (m : ℝ)) at hq
      rw [log_mul (mul_ne_zero hk.ne' (by exact_mod_cast hm0.ne')) hm.ne',
        log_mul hk.ne' (by exact_mod_cast hm0.ne')]
      try simp only [Function.comp_def, Function.id_def]
      field_simp [hq.ne']
      <;> ring
    · filter_upwards [hL.eventually_ge_atTop 1, hQ.eventually_ge_atTop 1] with m hm hq
      change 1 ≤ log (m : ℝ) at hm
      change 1 ≤ log (log (m : ℝ)) at hq
      have h1 := le_mul_of_one_le_right (Nat.cast_nonneg m) hm
      exact h1.trans (le_mul_of_one_le_right (by positivity) hq)
    · have ht := ((isLittleO_log_id_atTop.comp_tendsto hQ).tendsto_div_nhds_zero).add_const 1
      simp only [zero_add] at ht
      apply ht.congr'
      filter_upwards [hL.eventually_gt_atTop 0, hQ.eventually_gt_atTop 0,
        eventually_gt_atTop (0 : ℕ)] with m hm hq hm0
      change 0 < log (m : ℝ) at hm
      change 0 < log (log (m : ℝ)) at hq
      rw [log_mul (mul_ne_zero (by exact_mod_cast hm0.ne') hm.ne') hq.ne',
        log_mul (by exact_mod_cast hm0.ne') hm.ne']
      try simp only [Function.comp_def, Function.id_def]
      field_simp [hq.ne']
      <;> ring

  have logTransfer (f g : ℕ → ℝ) (hf : Tendsto f atTop (𝓝 1))
      (hb : (fun m => f m - 1) =O[atTop] g)
      (hs : Tendsto (fun m : ℕ => g m * (log m / log (log m))) atTop (𝓝 0)) :
      Tendsto (fun m : ℕ => log (f m) * (log m / log (log m))) atTop (𝓝 0) := by
    have hlog : (fun m => log (f m)) =O[atTop] g := by
      have ht := ((hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).isBigO_sub.comp_tendsto hf).trans hb
      simpa only [Function.comp_def, log_one, sub_zero] using ht
    exact (hlog.mul (isBigO_refl (fun m : ℕ => log m / log (log m)) atTop)).trans_tendsto hs

  have tailLimit : Tendsto (fun m : ℕ => (2 * C / (log m * log (log m))) *
      (log m / log (log m))) atTop (𝓝 0) := by
    have hL := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hQ := tendsto_log_atTop.comp hL
    have ht := ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hQ).const_div_atTop (2 * C)
    apply ht.congr'
    filter_upwards [hL.eventually_gt_atTop 0, hQ.eventually_gt_atTop 0] with m hm hq
    change 0 < log (m : ℝ) at hm
    change 0 < log (log (m : ℝ)) at hq
    try simp only [Function.comp_def, Function.id_def]
    field_simp [hm.ne', hq.ne']
    <;> ring

  have maximum (m : ℕ) :
      (pairValues C m).Finite ∧ (1 : ℝ) ∈ pairValues C m ∧
      extremeRatio C m ∈ pairValues C m ∧ 1 ≤ extremeRatio C m := by
    classical
    let N := ⌊(m.factorial : ℝ)^C⌋₊
    let T := (Icc 1 N).product (Icc 1 N)
    let f : ℕ × ℕ → ℝ := fun ab => normalizedWeight ab.1 / normalizedWeight ab.2
    have subset : pairValues C m ⊆ (T.image f : Set ℝ) := by
      rintro r ⟨a, b, ha, hb, haH, hbH, hab, hr⟩
      apply mem_image.mpr
      refine ⟨(a, b), mem_product.mpr ⟨mem_Icc.mpr ⟨ha, Nat.le_floor haH⟩,
        mem_Icc.mpr ⟨hb, Nat.le_floor hbH⟩⟩, ?_⟩
      exact hr.symm
    have finite : (pairValues C m).Finite := (T.image f).finite_toSet.subset subset
    have height : (1 : ℝ) ≤ (m.factorial : ℝ)^C :=
      one_le_rpow (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos m)) (by linarith)
    have one : (1 : ℝ) ∈ pairValues C m := by
      refine ⟨1, 1, by norm_num, by norm_num, by simpa using height,
        by simpa using height, Nat.ModEq.refl 1, ?_⟩
      norm_num [normalizedWeight, ArithmeticFunction.sigma_one]
    exact ⟨finite, one, Set.Nonempty.csSup_mem ⟨1, one⟩ finite, le_csSup finite.bddAbove one⟩
  have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hL := tendsto_log_atTop.comp hnat
  have hQ := tendsto_log_atTop.comp hL
  let scale : ℕ → ℝ := fun m => log m / log (log m)
  have hq0 : Tendsto (fun m : ℕ => log (log m) / log m) atTop (𝓝 0) :=
    (isLittleO_log_id_atTop.comp_tendsto hL).tendsto_div_nhds_zero
  have dpos (m : ℕ) : 0 < delta m := by
    exact prod_pos (fun p hp => sub_pos.mpr
      (pow_lt_one₀ (inv_nonneg.mpr (Nat.cast_nonneg p))
        (inv_lt_one_of_one_lt₀ (by exact_mod_cast (mem_filter.mp hp).2.one_lt))
        (by omega)))
  have ppos (x : ℝ) : 0 < primeProduct x := by
    exact prod_pos (fun p hp => inv_pos.mpr (sub_pos.mpr
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (mem_filter.mp hp).2.one_lt))))
  have zpos (n : ℕ) (hn : 0 < n) : 0 < normalizedWeight n := by
    exact div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn.ne')
      (by exact_mod_cast hn)
  have invsqrt : Tendsto (fun m : ℕ => (sqrt m)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp hnat)
  have dlimit : Tendsto delta atTop (𝓝 1) := by
    have ht := (ModularDivisorWeightTransfer.result.2.2.trans_tendsto invsqrt).add_const 1
    simpa only [sub_add_cancel, zero_add] using ht
  have sqrtScale : Tendsto (fun m : ℕ => (sqrt m)⁻¹ * scale m) atTop (𝓝 0) := by
    have hr : Tendsto (fun m : ℕ => log m / sqrt m) atTop (𝓝 0) := by
      simpa only [Function.comp_def, sqrt_eq_rpow] using
        ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp_tendsto hnat).tendsto_div_nhds_zero
    simpa only [Function.comp_def, Function.id_def, one_mul, scale, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, mul_zero, zero_mul, one_div] using
      hr.mul (hQ.const_div_atTop 1)
  have dlog : Tendsto (fun m : ℕ => log (delta m) * scale m) atTop (𝓝 0) :=
    logTransfer delta (fun m => (sqrt m)⁻¹) dlimit
      ModularDivisorWeightTransfer.result.2.2 sqrtScale
  have invScale : Tendsto (fun m : ℕ => (m : ℝ)⁻¹ * scale m) atTop (𝓝 0) := by
    have hr := (isLittleO_log_id_atTop.comp_tendsto hnat).tendsto_div_nhds_zero
    simpa only [Function.comp_def, Function.id_def, one_mul, scale, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, mul_zero, zero_mul, one_div] using
      hr.mul (hQ.const_div_atTop 1)
  obtain ⟨hYge, hYdev, hXge, hXdev⟩ := cutoffs ((C-1)/8) (by linarith)
  let Y : ℕ → ℝ := lowerCutoff C
  let X : ℕ → ℝ := fun m => m * log m * log (log m)
  have Yrate := intervalRate Y hYge hYdev
  have Xrate := intervalRate X hXge hXdev
  let T : ℕ → ℝ := fun m => ∏ p ∈ blockSet m (Y m), (1 - ((p : ℝ)⁻¹)^2)
  have Tbounds : ∀ᶠ m : ℕ in atTop, 0 < T m ∧ 1 - (m : ℝ)⁻¹ ≤ T m ∧ T m ≤ 1 ∧
      (∏ p ∈ blockSet m (Y m), (1 + (p : ℝ)⁻¹)) = T m * (primeProduct (Y m) / primeProduct m) := by
    filter_upwards [hYge, eventually_ge_atTop (2 : ℕ)] with m hy hm
    exact correction m hm (Y m) hy
  have Tbig : (fun m => T m - 1) =O[atTop] (fun m : ℕ => (m : ℝ)⁻¹) := by
    refine isBigO_iff.mpr ⟨1, ?_⟩
    filter_upwards [Tbounds] with m ht
    rw [norm_eq_abs, norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr ht.2.2.1),
      abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ)⁻¹ by positivity), one_mul]
    linarith [ht.2.1]
  have Tlimit : Tendsto T atTop (𝓝 1) := by
    have ht := (Tbig.trans_tendsto (tendsto_inv_atTop_zero.comp hnat)).add_const 1
    simpa only [sub_add_cancel, zero_add] using ht
  have Tlog : Tendsto (fun m => log (T m) * scale m) atTop (𝓝 0) :=
    logTransfer T (fun m : ℕ => (m : ℝ)⁻¹) Tlimit Tbig invScale
  let R : ℕ → ℝ := fun m => normalizedWeight (lowerNumber C m) / normalizedWeight m.factorial
  have Rpos (m : ℕ) : 0 < R m := by
    apply div_pos (zpos _ ?_) (zpos _ (Nat.factorial_pos m))
    dsimp [lowerNumber, primeBlock]
    exact Nat.mul_pos (Nat.factorial_pos m) (prod_pos (fun p hp => (mem_filter.mp hp).2.pos))
  have Rrate : Tendsto (fun m => log (R m) * scale m) atTop (𝓝 1) := by
    have ht := Tlog.add Yrate
    simp only [zero_add] at ht
    apply ht.congr'
    filter_upwards [construction, Tbounds] with m hc ht
    dsimp [R]
    rw [hc.2.2.2.2.2, ht.2.2.2, log_mul ht.1.ne' (div_pos (ppos _) (ppos _)).ne']
    ring
  have linearize (f : ℕ → ℝ) (hfpos : ∀ m, 0 < f m)
      (hf : Tendsto (fun m => log (f m) * scale m) atTop (𝓝 1)) :
      Tendsto (fun m => (f m - 1) * scale m) atTop (𝓝 1) := by
    have hlog : Tendsto (fun m => log (f m)) atTop (𝓝 0) := by
      have ht := hf.mul hq0
      simp only [one_mul] at ht
      apply ht.congr'
      filter_upwards [hL.eventually_gt_atTop 0, hQ.eventually_gt_atTop 0] with m hm hq
      change 0 < log (m : ℝ) at hm
      change 0 < log (log (m : ℝ)) at hq
      dsimp [scale]
      try simp only [Function.comp_def, Function.id_def]
      field_simp [hm.ne', hq.ne']
      <;> ring
    have hd := hasDerivAt_exp 0
    have hs := (continuousAt_dslope_same.mpr hd.differentiableAt).tendsto.comp hlog
    simp only [dslope_same, hd.deriv, exp_zero] at hs
    have ht := hs.mul hf
    simp only [one_mul] at ht
    apply ht.congr'
    filter_upwards [] with m
    have he := sub_smul_dslope exp (0 : ℝ) (log (f m))
    simp only [sub_zero, smul_eq_mul, exp_zero, exp_log (hfpos m)] at he
    try simp only [Function.comp_def, Function.id_def]
    rw [← mul_assoc, mul_comm (dslope _ _ _) _, he]
  have relative := linearize R Rpos Rrate

  have split (m n : ℕ) (hn : 0 < n) :
      (ArithmeticFunction.sigma 1 n : ℝ) / n = smallWeight m n * highWeight m n := by
    have hprod : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
      simpa only [Nat.cast_prod, Nat.cast_pow] using
        congrArg (fun k : ℕ => (k : ℝ)) (Nat.prod_primeFactors_pow_factorization hn.ne')
    have hsigma : (ArithmeticFunction.sigma 1 n : ℝ) =
        ∏ p ∈ n.primeFactors, ∑ i ∈ range (n.factorization p + 1), (p : ℝ) ^ i := by
      simpa only [Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, mul_one] using
        congrArg (fun k : ℕ => (k : ℝ))
          (ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
            (k := 1) hn.ne')
    have hgeom (p : ℕ) (hp : p.Prime) (v : ℕ) :
        (∑ i ∈ range (v + 1), (p : ℝ) ^ i) / (p : ℝ) ^ v = reciprocalGeomSum p v := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      dsimp [reciprocalGeomSum]
      rw [geom_sum_inv hp1.ne' hp0]
      rw [geom_sum_eq hp1.ne']
      simp only [inv_pow, pow_succ]
      field_simp [hp0, sub_ne_zero.mpr hp1.ne']
      <;> ring
    rw [hsigma, hprod, ← prod_div_distrib]
    have heq : (∏ p ∈ n.primeFactors,
        (∑ i ∈ range (n.factorization p + 1), (p : ℝ) ^ i) / (p : ℝ) ^ n.factorization p) =
        ∏ p ∈ n.primeFactors, reciprocalGeomSum p (n.factorization p) := by
      exact Finset.prod_congr rfl (fun p hp => hgeom p (Nat.prime_of_mem_primeFactors hp) _)
    rw [heq]
    have hlo : (∏ p ∈ n.primeFactors.filter (fun p => p ≤ m),
        reciprocalGeomSum p (n.factorization p)) = smallWeight m n := by
      apply Finset.prod_subset
      · intro p hp
        exact mem_filter.mpr ⟨mem_Ioc.mpr
          ⟨(Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos, (mem_filter.mp hp).2⟩,
          Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1⟩
      · intro p hp hpnot
        have hd : ¬p ∣ n := by
          intro hd
          apply hpnot
          exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr
            ⟨(mem_filter.mp hp).2, hd, hn.ne'⟩, (mem_Ioc.mp (mem_filter.mp hp).1).2⟩
        simp [Nat.factorization_eq_zero_of_not_dvd hd, reciprocalGeomSum]
    rw [← hlo]
    simpa only [highWeight, not_le] using
      (prod_filter_mul_prod_filter_not n.primeFactors (fun p => p ≤ m)
        (fun p => reciprocalGeomSum p (n.factorization p))).symm
  let U : ℕ → ℝ := fun m => -log (delta m) +
    log (primeProduct (X m) / primeProduct m) + 2 * C / (log m * log (log m))
  have Urate : Tendsto (fun m => U m * scale m) atTop (𝓝 1) := by
    have ht := ((dlog.neg).add Xrate).add tailLimit
    simp only [neg_zero, zero_add, add_zero] at ht
    apply ht.congr'
    exact Eventually.of_forall (fun m => by dsimp [U, scale]; ring)
  have factorone (p v : ℕ) : 1 ≤ reciprocalGeomSum p v := by
    dsimp [reciprocalGeomSum]
    simpa using single_le_sum
      (fun i _ => pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p : (0 : ℝ) ≤ p)) i)
      (mem_range.mpr (by omega : 0 < v + 1))
  have upper (m : ℕ) (hm : 2 ≤ m) (hLm : 1 ≤ log (m : ℝ))
      (hQm : 1 ≤ log (log (m : ℝ))) (hXm : (m : ℝ) ≤ X m)
      (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
      (haH : (a : ℝ) ≤ (m.factorial : ℝ)^C)
      (hab : Nat.ModEq m.factorial a b) :
      log (normalizedWeight a / normalizedWeight b) ≤ U m := by
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hL0 : 0 < log (m : ℝ) := by linarith
    have hQ0 : 0 < log (log (m : ℝ)) := by linarith
    have hX0 : 0 < X m := hm0.trans_le hXm
    have hLX : log m ≤ log (X m) := log_le_log hm0 hXm
    have hLX0 : 0 < log (X m) := hL0.trans_le hLX
    have hloga : log (a : ℝ) ≤ C * m * log m := by
      have hfpos : 0 < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
      have hf := log_le_log hfpos (by exact_mod_cast Nat.factorial_le_pow m :
        (m.factorial : ℝ) ≤ (m : ℝ)^m)
      rw [log_pow] at hf
      have hh := log_le_log (by exact_mod_cast ha) haH
      rw [log_rpow hfpos] at hh
      exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hf (by linarith : 0 ≤ C)])
    have tail : log a / ((X m - 1) * log (X m)) ≤
        2 * C / (log m * log (log m)) := by
      have hX2 : 2 ≤ X m := (by exact_mod_cast hm : (2 : ℝ) ≤ m).trans hXm
      have hXm1 : 0 < X m - 1 := by linarith
      apply (div_le_div_of_nonneg_right hloga (mul_pos hXm1 hLX0).le).trans
      apply (div_le_iff₀ (mul_pos hXm1 hLX0)).mpr
      rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hL0 hQ0)]
      have hhalf : X m ≤ 2 * (X m - 1) := by linarith
      have hden : m * log m * log (log m) * log m ≤
          2 * ((X m - 1) * log (X m)) := by
        calc
          _ = X m * log m := rfl
          _ ≤ 2 * (X m - 1) * log m := mul_le_mul_of_nonneg_right hhalf hL0.le
          _ ≤ 2 * (X m - 1) * log (X m) :=
            mul_le_mul_of_nonneg_left hLX (by linarith)
          _ = _ := by ring
      nlinarith [mul_le_mul_of_nonneg_left hden (by linarith : 0 ≤ C)]
    have lo := (ModularDivisorWeightTransfer.result.1 m a b hm ha hb hab).2
    have hiA := UniformDivisorWeightTransfer.result.1 m a hm ha (X m) hXm
    have hiB := UniformDivisorWeightTransfer.result.1 m b hm hb (X m) hXm
    have highA := hiA.2.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr tail)
      (div_pos (ppos _) (ppos _)).le)
    have hu : normalizedWeight a / normalizedWeight b ≤
        (delta m)⁻¹ * (primeProduct (X m) / primeProduct m *
          exp (2 * C / (log m * log (log m)))) := by
      change ((ArithmeticFunction.sigma 1 a : ℝ) / a) /
        ((ArithmeticFunction.sigma 1 b : ℝ) / b) ≤ _
      rw [split m a ha, split m b hb, mul_div_mul_comm]
      apply mul_le_mul lo ?_
        (div_pos (zero_lt_one.trans_le hiA.1) (zero_lt_one.trans_le hiB.1)).le
        (inv_pos.mpr (dpos m)).le
      exact (div_le_self (zero_lt_one.trans_le hiA.1).le hiB.1).trans highA
    have ht := log_le_log (div_pos (zpos a ha) (zpos b hb)) hu
    rw [log_mul (inv_pos.mpr (dpos m)).ne'
      (mul_pos (div_pos (ppos _) (ppos _)) (exp_pos _)).ne',
      log_inv, log_mul (div_pos (ppos _) (ppos _)).ne' (exp_ne_zero _), log_exp] at ht
    simpa only [U, add_assoc] using ht
  have Erate : Tendsto (fun m => log (extremeRatio C m) * scale m) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' Rrate Urate
    · filter_upwards [construction, hL.eventually_gt_atTop 0,
        hQ.eventually_gt_atTop 0] with m hc hm hq
      change 0 < log (m : ℝ) at hm
      change 0 < log (log (m : ℝ)) at hq
      have hmbr : R m ∈ pairValues C m :=
        ⟨lowerNumber C m, m.factorial, hc.1, Nat.factorial_pos m,
          hc.2.1, hc.2.2.1, hc.2.2.2.1, rfl⟩
      have he := le_csSup (maximum m).1.bddAbove hmbr
      exact mul_le_mul_of_nonneg_right (log_le_log (Rpos m) he) (div_pos hm hq).le
    · filter_upwards [eventually_ge_atTop (2 : ℕ), hL.eventually_ge_atTop 1,
        hQ.eventually_ge_atTop 1, hXge] with m hm hl hq hx
      obtain ⟨a, b, ha, hb, haH, hbH, hab, hr⟩ := (maximum m).2.2.1
      rw [hr]
      exact mul_le_mul_of_nonneg_right (upper m hm hl hq hx a b ha hb haH hab)
        (by dsimp [scale]; positivity)
  have erelative := linearize (extremeRatio C) (fun m => zero_lt_one.trans_le (maximum m).2.2.2) Erate

  have mertens : Tendsto
      (fun x : ℝ => primeProduct x / (exp eulerMascheroniConstant * log x)) atTop (𝓝 1) := by
    have hne : ∀ᶠ x : ℝ in atTop,
        (exp (-eulerMascheroniConstant) / log x)⁻¹ ≠ 0 := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact inv_ne_zero (div_ne_zero (exp_ne_zero _) (log_pos hx).ne')
    have h := (isEquivalent_iff_tendsto_one hne).mp Mertens.E₃.bound''.inv
    change Tendsto (fun x : ℝ =>
      (∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - 1 / (p : ℝ)))⁻¹ /
        (exp (-eulerMascheroniConstant) / log x)⁻¹) atTop (𝓝 1) at h
    simpa only [primeProduct, Pi.div_apply, Pi.inv_apply, inv_div, exp_neg,
      div_inv_eq_mul, prod_inv_distrib, one_div, mul_comm] using h
  have factorialIdentity (m : ℕ) :
      normalizedWeight m.factorial = delta m * primeProduct m := by
    have hi : highWeight m m.factorial = 1 := by
      dsimp [highWeight]
      apply prod_eq_one
      intro p hp
      obtain ⟨hpf, hmp⟩ := mem_filter.mp hp
      have hprime := Nat.prime_of_mem_primeFactors hpf
      have hpm := hprime.dvd_factorial.mp (Nat.dvd_of_mem_primeFactors hpf)
      omega
    have hs := split m m.factorial (Nat.factorial_pos m)
    change normalizedWeight m.factorial = _ at hs
    rw [hi, mul_one] at hs
    rw [hs]
    dsimp [smallWeight, delta, primeProduct]
    rw [Nat.floor_natCast, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    have hq : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀
      (by exact_mod_cast (mem_filter.mp hp).2.one_lt)
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (mem_filter.mp hp).2.ne_zero
    dsimp [reciprocalGeomSum]
    rw [geom_sum_eq hq.ne]
    rw [← neg_sub (1 : ℝ) ((p : ℝ)⁻¹ ^ (m.factorial.factorization p + 1)),
      ← neg_sub (1 : ℝ) (p : ℝ)⁻¹, neg_div_neg_eq, div_eq_mul_inv]
  have factorialLimit : Tendsto (fun m : ℕ =>
      normalizedWeight m.factorial / (exp eulerMascheroniConstant * log m)) atTop (𝓝 1) := by
    have ht := dlimit.mul (mertens.comp hnat)
    simp only [one_mul] at ht
    apply ht.congr'
    exact Eventually.of_forall (fun m => by
      try simp only [Function.comp_def, Function.id_def]
      rw [factorialIdentity]
      ring)
  have additive : Tendsto (fun m : ℕ =>
      (normalizedWeight (lowerNumber C m) - normalizedWeight m.factorial) /
      (exp eulerMascheroniConstant * log (log m))) atTop (𝓝 1) := by
    have ht := factorialLimit.mul relative
    simp only [one_mul] at ht
    apply ht.congr'
    filter_upwards [hL.eventually_gt_atTop 0, hQ.eventually_gt_atTop 0] with m hm hq
    change 0 < log (m : ℝ) at hm
    change 0 < log (log (m : ℝ)) at hq
    dsimp [R, scale]
    field_simp [(zpos m.factorial (Nat.factorial_pos m)).ne', exp_ne_zero, hm.ne', hq.ne']
    <;> ring
  have divergent : Tendsto (fun m : ℕ =>
      normalizedWeight (lowerNumber C m) - normalizedWeight m.factorial) atTop atTop := by
    have ht : Tendsto (fun m : ℕ => (exp eulerMascheroniConstant / 2) * log (log m))
        atTop atTop := hQ.const_mul_atTop (by positivity)
    apply tendsto_atTop_mono' atTop ?_ ht
    filter_upwards [additive.eventually_const_lt (by norm_num : (1/2 : ℝ) < 1),
      hQ.eventually_gt_atTop 0] with m hm hq
    change 0 < log (log (m : ℝ)) at hq
    have hh := (le_div_iff₀ (mul_pos (exp_pos _) hq)).mp hm.le
    nlinarith
  exact ⟨maximum, construction, erelative, relative, additive, divergent⟩

#print axioms result
end D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution
