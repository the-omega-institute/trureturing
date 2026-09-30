/- GID: D5/S3/Arith/FibonacciAtomic/UniformDivisorWeightTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/UniformDivisorWeightTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: High-prime divisor factors obey a uniform cutoff envelope. -/

import D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer
import D5.S3.Weil.GronwallUpperEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Filter Asymptotics Real
open scoped BigOperators Topology
open D5.S3.Arith.RobinExponentSwap
open D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer

namespace D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer

noncomputable def highWeight (m n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors with m < p, reciprocalGeomSum p (n.factorization p)

noncomputable def primeProduct (x : ℝ) : ℝ :=
  ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (p : ℝ)⁻¹)⁻¹

/-- The sum of divisors divided by its positive integer argument. -/
noncomputable def normalizedWeight (n : ℕ) : ℝ := (ArithmeticFunction.sigma 1 n : ℝ) / n

/-- The supremum of relative errors on one factorial congruence domain. -/
noncomputable def uniformError (C : ℝ) (m : ℕ) : ℝ := sSup
  {r : ℝ | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
    (a : ℝ) ≤ exp (C * m * log m) ∧ (b : ℝ) ≤ exp (C * m * log m) ∧
    Nat.ModEq m.factorial a b ∧ r = |normalizedWeight a / normalizedWeight b - 1|}

/-- A uniform cutoff estimate and factorial-congruence transfer on bounded heights. -/
theorem result :
    (∀ m n : ℕ, 2 ≤ m → 0 < n → ∀ X : ℝ, (m : ℝ) ≤ X →
      1 ≤ highWeight m n ∧ highWeight m n ≤
        primeProduct X / primeProduct m * exp (log n / ((X - 1) * log X))) ∧
    (∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      ∀ a b : ℕ, 0 < a → 0 < b →
        (a : ℝ) ≤ exp (C * m * log m) → (b : ℝ) ≤ exp (C * m * log m) →
        Nat.ModEq m.factorial a b →
        |normalizedWeight a / normalizedWeight b - 1| < ε) ∧
    (∀ C : ℝ, 0 < C → Tendsto (fun m : ℕ => uniformError C m) atTop (𝓝 0)) := by
  have cutoff (m n : ℕ) (hm : 2 ≤ m) (hn : 0 < n)
      (X : ℝ) (hX : (m : ℝ) ≤ X) :
      1 ≤ highWeight m n ∧ highWeight m n ≤
        primeProduct X / primeProduct m * exp (log n / ((X - 1) * log X)) := by
    classical
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hX2 : 2 ≤ X := hmR.trans hX
    have factor (p : ℕ) (hp : p.Prime) (v : ℕ) :
        1 ≤ reciprocalGeomSum p v ∧
          reciprocalGeomSum p v ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      have hq0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
      have hq1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
      constructor
      · dsimp [reciprocalGeomSum]
        simpa using (Finset.single_le_sum
          (fun i _ => pow_nonneg hq0 i) (mem_range.mpr (by omega : 0 < v + 1)))
      · dsimp [reciprocalGeomSum]
        rw [geom_sum_eq hq1.ne]
        rw [← neg_sub (1 : ℝ) ((p : ℝ)⁻¹ ^ (v + 1)),
          ← neg_sub (1 : ℝ) (p : ℝ)⁻¹, neg_div_neg_eq]
        simpa only [one_div] using div_le_div_of_nonneg_right
          (sub_le_self (1 : ℝ) (pow_nonneg hq0 (v + 1))) (sub_pos.mpr hq1).le
    have eulerpos (p : ℕ) (hp : p.Prime) : 0 < (1 - (p : ℝ)⁻¹)⁻¹ := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      exact inv_pos.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1))
    have eulerone (p : ℕ) (hp : p.Prime) : 1 ≤ (1 - (p : ℝ)⁻¹)⁻¹ :=
      (factor p hp 0).1.trans (factor p hp 0).2
    let s := n.primeFactors.filter (fun p => m < p)
    let t := s.filter (fun p : ℕ => (p : ℝ) ≤ X)
    let u := (Ioc 0 ⌊X⌋₊).filter (fun p => p.Prime ∧ m < p)
    have hsub : t ⊆ u := by
      intro p hp
      obtain ⟨hp, hpx⟩ := mem_filter.mp hp
      obtain ⟨hpn, hmp⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr
        ⟨(Nat.prime_of_mem_primeFactors hpn).pos, Nat.le_floor hpx⟩,
        Nat.prime_of_mem_primeFactors hpn, hmp⟩
    have padded : (∏ p ∈ t, (1 - (p : ℝ)⁻¹)⁻¹) ≤
        ∏ p ∈ u, (1 - (p : ℝ)⁻¹)⁻¹ := by
      exact Finset.prod_le_prod_of_subset_of_one_le hsub
        (fun p hp => (eulerpos p (Nat.prime_of_mem_primeFactors
          (mem_filter.mp (mem_filter.mp hp).1).1)).le)
        (fun p hp _ => eulerone p (mem_filter.mp hp).2.1)
    have quotient : (∏ p ∈ u, (1 - (p : ℝ)⁻¹)⁻¹) =
        primeProduct X / primeProduct m := by
      have hfloor : m ≤ ⌊X⌋₊ := Nat.le_floor hX
      have hsplit := Finset.prod_filter_mul_prod_filter_not
        ((Ioc 0 ⌊X⌋₊).filter Nat.Prime) (fun p => p ≤ m)
        (fun p => (1 - (p : ℝ)⁻¹)⁻¹)
      have lo : (((Ioc 0 ⌊X⌋₊).filter Nat.Prime).filter (fun p => p ≤ m)) =
          (Ioc 0 m).filter Nat.Prime := by
        ext p
        simp only [mem_filter, mem_Ioc]
        constructor
        · rintro ⟨⟨⟨hp0, _⟩, hprime⟩, hpm⟩
          exact ⟨⟨hp0, hpm⟩, hprime⟩
        · rintro ⟨⟨hp0, hpm⟩, hprime⟩
          exact ⟨⟨⟨hp0, hpm.trans hfloor⟩, hprime⟩, hpm⟩
      have hi : (((Ioc 0 ⌊X⌋₊).filter Nat.Prime).filter (fun p => ¬p ≤ m)) = u := by
        ext p
        simp only [mem_filter, mem_Ioc, u, not_le]
        tauto
      rw [lo, hi] at hsplit
      have hpos : 0 < primeProduct m := by
        dsimp [primeProduct]
        exact Finset.prod_pos (fun p hp => eulerpos p (mem_filter.mp hp).2)
      have hpos' : 0 < ∏ p ∈ (Ioc 0 m).filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹ := by
        simpa only [primeProduct, Nat.floor_natCast] using hpos
      simp only [primeProduct, Nat.floor_natCast]
      apply (eq_div_iff hpos'.ne').mpr
      simpa [mul_comm] using hsplit
    have hiSet : s.filter (fun p : ℕ => ¬(p : ℝ) ≤ X) =
        D5.S3.Weil.GronwallUpperEnvelope.largePrimes n X := by
      ext p
      simp only [s, D5.S3.Weil.GronwallUpperEnvelope.largePrimes, mem_filter, not_le]
      constructor
      · rintro ⟨⟨hpn, _⟩, hxp⟩; exact ⟨hpn, hxp⟩
      · rintro ⟨hpn, hxp⟩
        have hmp : m < p := by exact_mod_cast (hX.trans_lt hxp)
        exact ⟨⟨hpn, hmp⟩, hxp⟩
    have hlarge : (∏ p ∈ D5.S3.Weil.GronwallUpperEnvelope.largePrimes n X,
        (1 - (p : ℝ)⁻¹)⁻¹) ≤ exp (log n / ((X - 1) * log X)) := by
      let l := D5.S3.Weil.GronwallUpperEnvelope.largePrimes n X
      have hXm1 : 0 < X - 1 := by linarith
      have hlogX : 0 < log X := log_pos (by linarith)
      have hlprime (p : ℕ) (hp : p ∈ l) : p.Prime :=
        Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
      have point (p : ℕ) (hp : p ∈ l) : log ((1 - (p : ℝ)⁻¹)⁻¹) ≤ 1 / (X - 1) := by
        have hp1 : (1 : ℝ) < p := by exact_mod_cast (hlprime p hp).one_lt
        have hp0 : 0 < (p : ℝ) := by linarith
        have hpm : 0 < (p : ℝ) - 1 := by linarith
        have hxp : X < (p : ℝ) := (mem_filter.mp hp).2
        rw [← one_div (p : ℝ), one_sub_div hp0.ne', inv_div]
        calc
          log ((p : ℝ) / (p - 1)) ≤ (p : ℝ) / (p - 1) - 1 :=
            log_le_sub_one_of_pos (div_pos hp0 hpm)
          _ = 1 / ((p : ℝ) - 1) := by rw [div_sub_one hpm.ne', sub_sub_cancel]
          _ ≤ 1 / (X - 1) := div_le_div_of_nonneg_left zero_le_one hXm1 (by linarith)
      apply (log_le_iff_le_exp (Finset.prod_pos
        (fun p hp => eulerpos p (hlprime p hp)))).mp
      rw [log_prod (fun p hp => (eulerpos p (hlprime p hp)).ne')]
      calc
        _ ≤ (l.card : ℝ) * (1 / (X - 1)) := by
          simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum point
        _ ≤ (log n / log X) * (1 / (X - 1)) :=
          mul_le_mul_of_nonneg_right
            (D5.S3.Weil.GronwallUpperEnvelope.large_prime_count_le hn hX2) (by positivity)
        _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
    dsimp [highWeight]
    refine ⟨Finset.one_le_prod (fun p hp => (factor p
      (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1) _).1), ?_⟩
    calc
      _ ≤ ∏ p ∈ s, (1 - (p : ℝ)⁻¹)⁻¹ := Finset.prod_le_prod
        (fun p hp => zero_le_one.trans (factor p
          (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1) _).1)
        (fun p hp => (factor p (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1) _).2)
      _ = (∏ p ∈ t, (1 - (p : ℝ)⁻¹)⁻¹) *
          ∏ p ∈ D5.S3.Weil.GronwallUpperEnvelope.largePrimes n X, (1 - (p : ℝ)⁻¹)⁻¹ := by
        simpa only [t, hiSet] using
          (Finset.prod_filter_mul_prod_filter_not s (fun p : ℕ => (p : ℝ) ≤ X)
            (fun p => (1 - (p : ℝ)⁻¹)⁻¹)).symm
      _ ≤ (∏ p ∈ u, (1 - (p : ℝ)⁻¹)⁻¹) * exp (log n / ((X - 1) * log X)) :=
        mul_le_mul padded hlarge
          (Finset.prod_nonneg (fun p hp => (eulerpos p
            (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)).le))
          (Finset.prod_nonneg (fun p hp => (eulerpos p (mem_filter.mp hp).2.1).le))
      _ = _ := by rw [quotient]
  have uniform : ∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      ∀ a b : ℕ, 0 < a → 0 < b →
        (a : ℝ) ≤ exp (C * m * log m) → (b : ℝ) ≤ exp (C * m * log m) →
        Nat.ModEq m.factorial a b →
        |normalizedWeight a / normalizedWeight b - 1| < ε := by
    intro C hC ε hε
    dsimp only [normalizedWeight]
    classical
    have factorone (p v : ℕ) : 1 ≤ reciprocalGeomSum p v := by
      dsimp [reciprocalGeomSum]
      simpa using Finset.single_le_sum
        (fun i _ => pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p : (0 : ℝ) ≤ p)) i)
        (mem_range.mpr (by omega : 0 < v + 1))
    have smallpos (m n : ℕ) : 0 < smallWeight m n := by
      exact Finset.prod_pos (fun p _ => zero_lt_one.trans_le (factorone p _))
    have dpos (m : ℕ) : 0 < delta m := by
      exact Finset.prod_pos (fun p hp => sub_pos.mpr
        (pow_lt_one₀ (inv_nonneg.mpr (Nat.cast_nonneg p))
          (inv_lt_one_of_one_lt₀ (by exact_mod_cast (mem_filter.mp hp).2.one_lt))
          (by omega)))
    have ppos (x : ℝ) : 0 < primeProduct x := by
      exact Finset.prod_pos (fun p hp => inv_pos.mpr (sub_pos.mpr
        (inv_lt_one_of_one_lt₀ (by exact_mod_cast (mem_filter.mp hp).2.one_lt))))
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
    have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hlog : Tendsto (fun m : ℕ => log (m : ℝ)) atTop atTop := tendsto_log_atTop.comp hnat
    let X : ℕ → ℝ := fun m => m * (log m)^2
    have hXge : ∀ᶠ m : ℕ in atTop, (m : ℝ) ≤ X m := by
      filter_upwards [hlog.eventually_ge_atTop 1] with m hm
      dsimp [X]
      exact le_mul_of_one_le_right (Nat.cast_nonneg m) (by nlinarith)
    have hX : Tendsto X atTop atTop := tendsto_atTop_mono' atTop hXge hnat
    have hlogratio : Tendsto (fun m : ℕ => log (X m) / log m) atTop (𝓝 1) := by
      have hs := (isLittleO_log_id_atTop.comp_tendsto hlog).tendsto_div_nhds_zero
      have ht : Tendsto (fun m : ℕ => 1 + 2 * (log (log m) / log m)) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hs)
      apply ht.congr'
      filter_upwards [hlog.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)] with m hm hm0
      dsimp [X]
      rw [log_mul (by positivity) (by positivity), log_pow]
      field_simp [ne_of_gt hm]
      <;> ring
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
    have pratio : Tendsto (fun m : ℕ => primeProduct (X m) / primeProduct m) atTop (𝓝 1) := by
      have h := ((mertens.comp hX).div (mertens.comp hnat) one_ne_zero).mul hlogratio
      simp only [div_self one_ne_zero, one_mul] at h
      apply h.congr'
      filter_upwards [hlog.eventually_gt_atTop 0, (tendsto_log_atTop.comp hX).eventually_gt_atTop 0]
        with m hm hx
      change 0 < log (X m) at hx
      simp only [Function.comp_apply, Pi.div_apply]
      field_simp [ne_of_gt (ppos m), ne_of_gt hm, ne_of_gt hx, exp_ne_zero]
      <;> ring
    have dlimit : Tendsto delta atTop (𝓝 1) := by
      have hi : Tendsto (fun m : ℕ => (sqrt m)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp hnat)
      have h := ModularDivisorWeightTransfer.result.2.2.trans_tendsto hi
      have ht := h.add_const 1
      simpa only [sub_add_cancel, zero_add] using ht
    let B : ℕ → ℝ := fun m => (delta m)⁻¹ *
      (primeProduct (X m) / primeProduct m * exp (2 * C / (log m)^2))
    have hB : Tendsto B atTop (𝓝 1) := by
      have ht : Tendsto (fun m : ℕ => 2 * C / (log m)^2) atTop (𝓝 0) :=
        ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlog).const_div_atTop _
      simpa only [B, inv_one, exp_zero, one_mul, mul_one] using
        (dlimit.inv₀ one_ne_zero).mul (pratio.mul ht.rexp)
    have hBinv : Tendsto (fun m => (B m)⁻¹) atTop (𝓝 1) := by
      simpa only [inv_one] using hB.inv₀ one_ne_zero
    have upper (m : ℕ) (hm : 2 ≤ m) (hLm : 1 ≤ log (m : ℝ))
        (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
        (haH : (a : ℝ) ≤ exp (C * m * log m))
        (hab : Nat.ModEq m.factorial a b) :
        ((ArithmeticFunction.sigma 1 a : ℝ) / a) /
          ((ArithmeticFunction.sigma 1 b : ℝ) / b) ≤ B m := by
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hL0 : 0 < log (m : ℝ) := by linarith
      have hXm : (m : ℝ) ≤ X m := by dsimp [X]; exact le_mul_of_one_le_right hm0.le (by nlinarith)
      have hX0 : 0 < X m := hm0.trans_le hXm
      have hLX : log m ≤ log (X m) := log_le_log hm0 hXm
      have hLX0 : 0 < log (X m) := hL0.trans_le hLX
      have hloga : log (a : ℝ) ≤ C * m * log m := by
        simpa only [log_exp] using log_le_log (by positivity) haH
      have tail : log a / ((X m - 1) * log (X m)) ≤ 2 * C / (log m)^2 := by
        have hX2 : 2 ≤ X m := (by exact_mod_cast hm : (2 : ℝ) ≤ m).trans hXm
        have hXm1 : 0 < X m - 1 := by linarith
        apply (div_le_div_of_nonneg_right hloga (mul_pos hXm1 hLX0).le).trans
        apply (div_le_iff₀ (mul_pos hXm1 hLX0)).mpr
        rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hL0)]
        have hhalf : m * (log m)^2 ≤ 2 * (m * (log m)^2 - 1) := by
          dsimp [X] at hX2
          linarith
        have hden : m * (log m)^2 * log m ≤ 2 * ((X m - 1) * log (X m)) := by
          dsimp [X] at *
          calc
            _ ≤ 2 * (m * (log m)^2 - 1) * log m :=
              mul_le_mul_of_nonneg_right hhalf hL0.le
            _ ≤ 2 * (m * (log m)^2 - 1) * log (m * (log m)^2) :=
              mul_le_mul_of_nonneg_left hLX (by nlinarith)
            _ = _ := by ring
        nlinarith [mul_le_mul_of_nonneg_left hden hC.le]
      have hlow := (ModularDivisorWeightTransfer.result.1 m a b hm ha hb hab).2
      have hhighA := (cutoff m a hm ha (X m) hXm).2
      have hhighB := (cutoff m b hm hb (X m) hXm).1
      have hu := hhighA.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr tail)
        (div_pos (ppos _) (ppos _)).le)
      rw [split m a ha, split m b hb, mul_div_mul_comm]
      apply (mul_le_mul hlow ?_ (div_pos (zero_lt_one.trans_le (cutoff m a hm ha _ hXm).1)
        (zero_lt_one.trans_le hhighB)).le (inv_pos.mpr (dpos m)).le)
      exact (div_le_self (zero_lt_one.trans_le (cutoff m a hm ha _ hXm).1).le hhighB).trans hu
    filter_upwards [eventually_ge_atTop (2 : ℕ), hlog.eventually_ge_atTop 1,
      hB.eventually_lt_const (by linarith : (1 : ℝ) < 1 + ε),
      hBinv.eventually_const_lt (by linarith : 1 - ε < (1 : ℝ))] with m hm hLm hBu hBd
    intro a b ha hb haH hbH hab
    have hU := upper m hm hLm a b ha hb haH hab
    have hV := upper m hm hLm b a hb ha hbH hab.symm
    have hXm : (m : ℝ) ≤ X m := by dsimp [X]; exact le_mul_of_one_le_right (Nat.cast_nonneg m) (by nlinarith)
    have za : 0 < (ArithmeticFunction.sigma 1 a : ℝ) / a := by
      rw [split m a ha]
      exact mul_pos (smallpos _ _) (zero_lt_one.trans_le (cutoff m a hm ha _ hXm).1)
    have zb : 0 < (ArithmeticFunction.sigma 1 b : ℝ) / b := by
      rw [split m b hb]
      exact mul_pos (smallpos _ _) (zero_lt_one.trans_le (cutoff m b hm hb _ hXm).1)
    have ratio : 0 < ((ArithmeticFunction.sigma 1 a : ℝ) / a) /
        ((ArithmeticFunction.sigma 1 b : ℝ) / b) := div_pos za zb
    have lower : (B m)⁻¹ ≤ ((ArithmeticFunction.sigma 1 a : ℝ) / a) /
        ((ArithmeticFunction.sigma 1 b : ℝ) / b) := by
      rw [← inv_div]
      exact (inv_le_inv₀ (lt_of_lt_of_le (div_pos zb za) hV) (div_pos zb za)).mpr hV
    rw [abs_lt]
    constructor <;> linarith
  refine ⟨cutoff, uniform, ?_⟩
  intro C hC
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [uniform C hC (ε / 2) (by linarith), eventually_ge_atTop (2 : ℕ)]
    with m hu hm
  classical
  let S : Set ℝ := {r : ℝ | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
    (a : ℝ) ≤ exp (C * m * log m) ∧ (b : ℝ) ≤ exp (C * m * log m) ∧
    Nat.ModEq m.factorial a b ∧ r = |normalizedWeight a / normalizedWeight b - 1|}
  have hheight : (1 : ℝ) ≤ exp (C * m * log m) := by
    apply one_le_exp_iff.mpr
    have hlog : 0 ≤ log (m : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    positivity
  have hz : (0 : ℝ) ∈ S := by
    refine ⟨1, 1, by norm_num, by norm_num, by simpa using hheight, by simpa using hheight, Nat.ModEq.refl 1, ?_⟩
    norm_num [normalizedWeight, ArithmeticFunction.sigma_one]
  have hb : ∀ r ∈ S, r ≤ ε / 2 := by
    rintro r ⟨a, b, ha, hbb, haH, hbH, hab, hr⟩
    rw [hr]
    exact (hu a b ha hbb haH hbH hab).le
  have hbd : BddAbove S := ⟨ε / 2, hb⟩
  have hlow : 0 ≤ sSup S := le_csSup hbd hz
  have hhigh : sSup S ≤ ε / 2 := csSup_le ⟨0, hz⟩ hb
  change dist (sSup S) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlow]
  linarith

#print axioms result
end D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
