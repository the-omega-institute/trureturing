/- GID: D5/S3/Weil/Analytic/NymanPrimeDilations
   generality: I
   mirror-B: none(waiver:nyman-signed-prime-support)
   mirror-E: none(waiver:nyman-signed-prime)
   anchors: []
   utility: none
   digest: Möbius inversion centers prime dilations and bounds the contribution of higher prime powers. -/

import D5.S3.Weil.Analytic.NymanFixedRationalScalar
import D5.S3.Weil.Mertens.Estimates
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! Finite dilation identities and bounds for the fixed Nyman kernel. -/

set_option autoImplicit false

noncomputable section

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace NymanPrimeDilations

open NymanFixedRationalKernel (A A_pos one_lt_A b b_zero_right)

/-- The right endpoint of the support of the repository kernel. -/
abbrev B : ℝ := A ^ 4

def primesUpTo (z : ℝ) : Finset ℕ :=
  (Ioc 0 ⌊z⌋₊).filter Nat.Prime

/-- Including exponents 1 and 2 uniformly makes both splittings valid at small cutoffs. -/
def powerLimit (z : ℝ) : ℕ :=
  max 2 ⌊Real.log z / Real.log 2⌋₊

def shell (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊B * x⌋₊, (μ n : ℝ) * b ((n : ℝ) / x)

def logCorrection (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊B * x⌋₊, (μ n : ℝ) * b ((n : ℝ) / x) * Real.log ((n : ℝ) / x)

def primeDilations (x : ℝ) : ℝ :=
  ∑ p ∈ primesUpTo (B * x), Real.log (p : ℝ) * shell (x / (p : ℝ))

def higherPowerDilations (x : ℝ) : ℝ :=
  ∑ k ∈ Icc 2 (powerLimit (B * x)),
    ∑ p ∈ primesUpTo ((B * x) ^ ((1 : ℝ) / k)),
      Real.log (p : ℝ) * shell (x / ((p ^ k : ℕ) : ℝ))

theorem shell_eq_zero_below {x : ℝ} (hx : 0 < x) (h : B * x ≤ 1) : shell x = 0 := by
  unfold shell
  apply sum_eq_zero
  intro n hn
  have hn₁ : (1 : ℝ) ≤ n := by
    exact_mod_cast (mem_Ioc.mp hn).1
  have hb : B ≤ (n : ℝ) / x := (le_div_iff₀ hx).mpr (h.trans hn₁)
  rw [b_zero_right hb, mul_zero]

theorem shell_nat_eq_scalar {N : ℕ} (hN : 0 < N) :
    shell (N : ℝ) = (NymanFixedRationalScalar.scalar N : ℝ) := by
  have h₀ : (0 : ℝ) < N := by exact_mod_cast hN
  unfold shell NymanFixedRationalScalar.scalar
  push_cast
  simp only [NymanFixedRationalKernel.bRat_cast, Rat.cast_div, Rat.cast_natCast]
  let s := Ioc 0 ⌊B * (N : ℝ)⌋₊
  let t := Ioc N (2 * N)
  let f : ℕ → ℝ := fun n => (μ n : ℝ) * b ((n : ℝ) / (N : ℝ))
  change (∑ n ∈ s, f n) = ∑ n ∈ t, f n
  calc
    _ = ∑ n ∈ s ∪ t, f n := by
      apply sum_subset subset_union_left
      intro n hst hn
      have hnt : n ∈ t := (mem_union.mp hst).resolve_left hn
      have hn₀ : 0 < n := Nat.zero_lt_of_lt (mem_Ioc.mp hnt).1
      have hn' : ⌊B * (N : ℝ)⌋₊ < n := by
        by_contra! h
        exact hn (mem_Ioc.mpr ⟨hn₀, h⟩)
      have hn'' : B * (N : ℝ) ≤ n := (Nat.lt_of_floor_lt hn').le
      simp [f, b_zero_right ((le_div_iff₀ h₀).mpr hn'')]
    _ = ∑ n ∈ t, f n := by
      symm
      apply sum_subset subset_union_right
      intro n _ hnt
      by_cases hle : n ≤ N
      · have hn₀ : (n : ℝ) ≤ N := by exact_mod_cast hle
        simp [f, NymanFixedRationalKernel.b_zero_left ((div_le_one h₀).mpr hn₀)]
      · have hn₂ : 2 * N < n := by
          by_contra! hh
          exact hnt (mem_Ioc.mpr ⟨lt_of_not_ge hle, hh⟩)
        have h₂ : (2 : ℝ) * N ≤ n := by exact_mod_cast hn₂.le
        have hB : B ≤ (n : ℝ) / N := (le_div_iff₀ h₀).mpr
          ((mul_le_mul_of_nonneg_right NymanFixedRationalKernel.A4_lt_two.le h₀.le).trans h₂)
        simp [f, b_zero_right hB]

private def logWeightedMoebius : ArithmeticFunction ℝ :=
  ⟨fun n => (μ n : ℝ) * Real.log n, by simp⟩

-- The arithmetic identity is also used privately in LinearOrder/MoebiusPrefixes.lean.
private theorem logWeightedMoebius_eq :
    logWeightedMoebius = -(ArithmeticFunction.vonMangoldt * (μ : ArithmeticFunction ℝ)) := by
  have h : logWeightedMoebius * (ζ : ArithmeticFunction ℝ) = -ArithmeticFunction.vonMangoldt := by
    ext n
    rw [coe_mul_zeta_apply]
    simpa only [logWeightedMoebius, coe_mk, ArithmeticFunction.neg_apply, ArithmeticFunction.log_apply]
      using (sum_moebius_mul_log_eq (n := n))
  have ht := congrArg (fun f : ArithmeticFunction ℝ => f * (μ : ArithmeticFunction ℝ)) h
  calc
    _ = (-ArithmeticFunction.vonMangoldt) * (μ : ArithmeticFunction ℝ) := by
      simpa only [mul_assoc, coe_zeta_mul_coe_moebius, mul_one] using ht
    _ = _ := by
      ext n
      simp only [mul_apply, ArithmeticFunction.neg_apply, _root_.neg_mul, sum_neg_distrib]

/-- Finite Dirichlet convolution against an arbitrary weight on the product. -/
private theorem sum_weighted_convolution (f g : ArithmeticFunction ℝ) (N : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ Ioc 0 N, (f * g) n * w n) =
      ∑ d ∈ Ioc 0 N, f d * ∑ m ∈ Ioc 0 (N / d), g m * w (d * m) := by
  let s := Ioc 0 N
  calc
    _ = ∑ n ∈ s, ∑ a ∈ (s ×ˢ s).filter (fun a => a.1 * a.2 = n),
          (f a.1 * g a.2) * w (a.1 * a.2) := by
      apply sum_congr rfl
      intro n hn
      obtain ⟨hn₀, hnN⟩ := mem_Ioc.mp hn
      rw [ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_eq_prod_filter_of_le
        hn₀.ne' hnN, Finset.sum_mul]
      exact sum_congr rfl fun a ha => by rw [(mem_filter.mp ha).2]
    _ = ∑ a ∈ (s ×ˢ s).filter (fun a => a.1 * a.2 ≤ N),
          (f a.1 * g a.2) * w (a.1 * a.2) := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro a ha
      obtain ⟨hd, hm⟩ := mem_product.mp ha
      have hpos := Nat.mul_pos (mem_Ioc.mp hd).1 (mem_Ioc.mp hm).1
      simp only [Finset.sum_ite_eq, s, mem_Ioc, hpos, true_and]
    _ = _ := by
      rw [Finset.sum_filter, Finset.sum_product]
      apply sum_congr rfl
      intro d hd
      have hd₀ : 0 < d := (mem_Ioc.mp hd).1
      have hf : s.filter (fun m => d * m ≤ N) = Ioc 0 (N / d) := by
        ext m
        have hdiv : d * m ≤ N ↔ m ≤ N / d := by
          rw [Nat.le_div_iff_mul_le hd₀, Nat.mul_comm m d]
        simp only [s, mem_filter, mem_Ioc, hdiv]
        exact ⟨fun h => ⟨h.1.1, h.2⟩,
          fun h => ⟨⟨h.1, h.2.trans (Nat.div_le_self _ _)⟩, h.2⟩⟩
      rw [← Finset.sum_filter, hf, Finset.mul_sum]
      exact sum_congr rfl fun m _ => mul_assoc _ _ _

private theorem sum_dilations_eq_sum_convolution (f : ArithmeticFunction ℝ) (x : ℝ) :
    (∑ d ∈ Ioc 0 ⌊B * x⌋₊, f d * shell (x / (d : ℝ))) =
      ∑ n ∈ Ioc 0 ⌊B * x⌋₊, (f * (μ : ArithmeticFunction ℝ)) n * b ((n : ℝ) / x) := by
  rw [sum_weighted_convolution]
  refine sum_congr rfl fun d _ => congrArg (fun u : ℝ => f d * u) ?_
  unfold shell
  rw [← mul_div_assoc, Nat.floor_div_natCast]
  refine sum_congr rfl fun m _ => congrArg (fun u : ℝ => (μ m : ℝ) * b u) ?_
  push_cast
  rw [div_div_eq_mul_div, mul_comm (m : ℝ)]

/-- The constant counting weight convolved with the Möbius coefficient is the
Dirichlet convolution unit. -/
theorem sum_integerDilations_eq_kernel {x : ℝ} (hx : 0 < x) :
    (∑ d ∈ Ioc 0 ⌊B * x⌋₊, shell (x / (d : ℝ))) = b (1 / x) := by
  calc
    _ = ∑ d ∈ Ioc 0 ⌊B * x⌋₊, (ζ : ArithmeticFunction ℝ) d * shell (x / (d : ℝ)) := by
      apply sum_congr rfl
      intro d hd
      rw [ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply_ne (mem_Ioc.mp hd).1.ne', Nat.cast_one, one_mul]
    _ = ∑ n ∈ Ioc 0 ⌊B * x⌋₊, (1 : ArithmeticFunction ℝ) n * b ((n : ℝ) / x) := by
      rw [sum_dilations_eq_sum_convolution, coe_zeta_mul_coe_moebius]
    _ = b (1 / x) := by
      by_cases hcut : 1 ≤ ⌊B * x⌋₊
      · rw [Finset.sum_eq_single_of_mem 1 (mem_Ioc.mpr ⟨by decide, hcut⟩)]
        · simp
        · intro n _ hn
          rw [ArithmeticFunction.one_apply_ne hn, zero_mul]
      · have hcut₀ : ⌊B * x⌋₊ = 0 := by omega
        have hxlt : B * x < 1 := by
          simpa only [hcut₀, Nat.cast_zero, zero_add] using Nat.lt_floor_add_one (B * x)
        have hb : b (1 / x) = 0 := b_zero_right ((le_div_iff₀ hx).mpr hxlt.le)
        rw [hb]
        simp [hcut₀]

/-- Centering the prime weight by integer counting leaves precisely the kernel
value from the Dirichlet unit. -/
theorem primeDilations_add_shell_eq_centered_with_boundary {x : ℝ} (hx : 0 < x) :
    primeDilations x + shell x = b (1 / x) +
      ∑ d ∈ Ioc 1 ⌊B * x⌋₊,
        ((if d.Prime then Real.log (d : ℝ) else 0) - 1) * shell (x / (d : ℝ)) := by
  have hprime : primeDilations x = ∑ d ∈ Ioc 0 ⌊B * x⌋₊,
      (if d.Prime then Real.log (d : ℝ) else 0) * shell (x / (d : ℝ)) := by
    unfold primeDilations primesUpTo
    rw [Finset.sum_filter]
    exact sum_congr rfl fun d _ => by split_ifs <;> simp
  have hcenter : (∑ d ∈ Ioc 0 ⌊B * x⌋₊,
      ((if d.Prime then Real.log (d : ℝ) else 0) - 1) * shell (x / (d : ℝ))) =
      primeDilations x - b (1 / x) := by
    simp_rw [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib, ← hprime, sum_integerDilations_eq_kernel hx]
  by_cases hcut : 1 ≤ ⌊B * x⌋₊
  · have hsplit : Ioc 0 ⌊B * x⌋₊ = insert 1 (Ioc 1 ⌊B * x⌋₊) := by
      ext d
      simp only [mem_Ioc, mem_insert]
      omega
    rw [hsplit, Finset.sum_insert (by simp)] at hcenter
    simp only [Nat.not_prime_one, ite_false, zero_sub, Nat.cast_one, div_one, neg_mul,
      one_mul] at hcenter
    linarith only [hcenter]
  · have hcut₀ : ⌊B * x⌋₊ = 0 := by omega
    have hxlt : B * x < 1 := by
      simpa only [hcut₀, Nat.cast_zero, zero_add] using Nat.lt_floor_add_one (B * x)
    have hb : b (1 / x) = 0 := b_zero_right ((le_div_iff₀ hx).mpr hxlt.le)
    have hs : shell x = 0 := shell_eq_zero_below hx hxlt.le
    rw [hb]
    simp [primeDilations, primesUpTo, hcut₀, hs]

/-- Prime dilations paired with the integer counting weight at smaller scales. -/
def centeredPrimeDilations (x : ℝ) : ℝ :=
  ∑ d ∈ Ioc 1 ⌊B * x⌋₊,
    ((if d.Prime then Real.log (d : ℝ) else 0) - 1) * shell (x / (d : ℝ))

/-- The Dirichlet coefficient of the prime weight centered by integer counting. -/
def centeredPrimeCoefficient : ArithmeticFunction ℝ :=
  ⟨fun n => if 1 < n then (if n.Prime then Real.log (n : ℝ) else 0) - 1 else 0,
    by simp⟩

theorem centeredPrimeDilations_eq_convolution (x : ℝ) :
    centeredPrimeDilations x =
      ∑ n ∈ Ioc 0 ⌊B * x⌋₊,
        (centeredPrimeCoefficient * (μ : ArithmeticFunction ℝ)) n * b ((n : ℝ) / x) := by
  rw [← sum_dilations_eq_sum_convolution]
  unfold centeredPrimeDilations
  calc
    _ = ∑ d ∈ Ioc 1 ⌊B * x⌋₊, centeredPrimeCoefficient d * shell (x / (d : ℝ)) := by
      apply sum_congr rfl
      intro d hd
      simp [centeredPrimeCoefficient, (mem_Ioc.mp hd).1]
    _ = _ := by
      apply sum_subset (fun d hd => mem_Ioc.mpr
        ⟨zero_lt_one.trans (mem_Ioc.mp hd).1, (mem_Ioc.mp hd).2⟩)
      intro d hmem hnot
      have hd : ¬ 1 < d := fun h => hnot (mem_Ioc.mpr ⟨h, (mem_Ioc.mp hmem).2⟩)
      simp [centeredPrimeCoefficient, hd]

theorem centeredPrimeDilations_eq_zero_of_le_one {x : ℝ} (hx : x ≤ 1) :
    centeredPrimeDilations x = 0 := by
  have hB : 0 ≤ B := pow_nonneg A_pos.le _
  have hcut : ⌊B * x⌋₊ < 2 := by
    apply (Nat.floor_lt' (by norm_num : (2 : ℕ) ≠ 0)).mpr
    exact (by simpa using mul_le_mul_of_nonneg_left hx hB :
      B * x ≤ B).trans_lt NymanFixedRationalKernel.A4_lt_two
  have hempty : Ioc 1 ⌊B * x⌋₊ = (∅ : Finset ℕ) := by
    apply eq_empty_iff_forall_notMem.mpr
    intro n hn
    have h := mem_Ioc.mp hn
    omega
  simp [centeredPrimeDilations, hempty]

theorem primeDilations_add_shell_eq_centered {x : ℝ} (hx : 1 ≤ x) :
    primeDilations x + shell x = centeredPrimeDilations x := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  rw [primeDilations_add_shell_eq_centered_with_boundary hx₀,
    NymanFixedRationalKernel.b_zero_left ((div_le_one hx₀).mpr hx), zero_add]
  rfl

private theorem sum_mangoldt_dilations {x : ℝ} (hx : 0 ≤ B * x) :
    (∑ d ∈ Ioc 0 ⌊B * x⌋₊, ArithmeticFunction.vonMangoldt d * shell (x / (d : ℝ))) =
      primeDilations x + higherPowerDilations x := by
  have hlimit : 1 ≤ powerLimit (B * x) :=
    (by decide : 1 ≤ 2).trans (le_max_left _ _)
  calc
    _ = ∑ d ∈ (Ioc 0 ⌊B * x⌋₊).filter IsPrimePow,
        Real.log (d.minFac : ℝ) * shell (x / (d : ℝ)) := by
      rw [Finset.sum_filter]
      apply sum_congr rfl
      intro d _
      rw [vonMangoldt_apply]
      split_ifs <;> simp
    _ = ∑ k ∈ Icc 1 (powerLimit (B * x)),
        ∑ p ∈ primesUpTo ((B * x) ^ ((1 : ℝ) / k)),
          Real.log ((p ^ k).minFac : ℝ) * shell (x / ((p ^ k : ℕ) : ℝ)) :=
      Chebyshev.sum_PrimePow_eq_sum_sum' _ hx (le_max_right _ _)
    _ = _ := by
      rw [← add_sum_Ioc_eq_sum_Icc hlimit, ← Icc_add_one_left_eq_Ioc]
      unfold primeDilations higherPowerDilations
      congr 1
      · simp only [Nat.cast_one, div_one, Real.rpow_one, pow_one]
        exact sum_congr rfl fun p hp => by
          rw [(mem_filter.mp hp).2.minFac_eq]
      · refine sum_congr rfl fun k hk => sum_congr rfl fun p hp => ?_
        rw [Nat.Prime.pow_minFac (mem_filter.mp hp).2 (by have := (mem_Icc.mp hk).1; omega)]

/-- The exact finite Möbius log identity, with the log of the kernel argument explicit. -/
theorem moebius_log_split {x : ℝ} (hx : 0 < x) :
    Real.log x * shell x + logCorrection x = -(primeDilations x + higherPowerDilations x) := by
  have hlog :
      Real.log x * shell x + logCorrection x =
        ∑ n ∈ Ioc 0 ⌊B * x⌋₊, logWeightedMoebius n * b ((n : ℝ) / x) := by
    unfold shell logCorrection
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (mem_Ioc.mp hn).1
    rw [Real.log_div hn₀.ne' hx.ne']
    change _ = ((μ n : ℝ) * Real.log (n : ℝ)) * b ((n : ℝ) / x)
    ring
  rw [hlog, logWeightedMoebius_eq]
  simp only [ArithmeticFunction.neg_apply, _root_.neg_mul, sum_neg_distrib, neg_inj]
  rw [← sum_dilations_eq_sum_convolution,
    sum_mangoldt_dilations (mul_nonneg (pow_nonneg A_pos.le _) hx.le)]

/-- The coefficient of the absolute feedback on a power envelope of exponent `β`. -/
def higherPowerWeight (z β : ℝ) : ℝ :=
  ∑ k ∈ Icc 2 (powerLimit z), ∑ p ∈ primesUpTo (z ^ ((1 : ℝ) / k)),
    Real.log (p : ℝ) / ((p : ℝ) ^ k) ^ β

private theorem prime_of_mem {z : ℝ} {p : ℕ} (hp : p ∈ primesUpTo z) : p.Prime :=
  (mem_filter.mp hp).2

private theorem primes_root_subset {z : ℝ} (hz : 1 ≤ z) {k : ℕ} (hk : 1 ≤ k) :
    primesUpTo (z ^ ((1 : ℝ) / k)) ⊆ primesUpTo z := by
  intro p hp
  obtain ⟨hp', hprime⟩ := mem_filter.mp hp
  refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hp').1, ?_⟩, hprime⟩
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hroot := Real.rpow_le_self_of_one_le hz
    ((div_le_one₀ (show (0 : ℝ) < k by linarith)).mpr hk')
  exact (mem_Ioc.mp hp').2.trans (Nat.floor_mono hroot)

private theorem pow_rpow_half (p k : ℕ) :
    ((p : ℝ) ^ k) ^ (1 / 2 : ℝ) = (Real.sqrt (p : ℝ)) ^ k := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Nat.cast_nonneg p),
    ← Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_comm (k : ℝ)]

private theorem prime_geometric_tail {p : ℕ} (hp : p.Prime) (K : ℕ) :
    (∑ k ∈ Icc 3 K, Real.log (p : ℝ) / (Real.sqrt (p : ℝ)) ^ k) ≤
      16 / (p : ℝ) ^ (5 / 4 : ℝ) := by
  let r : ℝ := Real.sqrt (p : ℝ)
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp₀ : (0 : ℝ) < p := by linarith
  have hr : 0 < r := Real.sqrt_pos_of_pos hp₀
  have hrlo : 4 / 3 ≤ r := Real.le_sqrt_of_sq_le (by linarith)
  have hinv : r⁻¹ ≤ (3 / 4 : ℝ) := by
    rw [inv_eq_one_div, div_le_iff₀ hr]
    linarith
  have hgeom (L : ℕ) : (∑ j ∈ range L, (3 / 4 : ℝ) ^ j) ≤ 4 := by
    have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)
    calc
      _ ≤ ∑' j : ℕ, (3 / 4 : ℝ) ^ j := hs.sum_le_tsum _ (fun j _ => by positivity)
      _ = 4 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have hindices : Icc 3 K = Ico 3 (K + 1) := by
    ext k
    simp only [mem_Icc, mem_Ico]
    omega
  change (∑ k ∈ Icc 3 K, Real.log (p : ℝ) / r ^ k) ≤ _
  rw [hindices, sum_Ico_eq_sum_range]
  calc
    _ ≤ ∑ j ∈ range (K + 1 - 3), (Real.log (p : ℝ) / r ^ 3) * (3 / 4 : ℝ) ^ j := by
      apply sum_le_sum
      intro j _
      rw [pow_add, div_mul_eq_div_div, div_eq_mul_inv (Real.log (p : ℝ) / r ^ 3),
        ← inv_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv j)
        (div_nonneg (Real.log_natCast_nonneg p) (by positivity))
    _ ≤ (Real.log (p : ℝ) / r ^ 3) * 4 := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hgeom _) (div_nonneg (Real.log_natCast_nonneg p) (by positivity))
    _ ≤ 16 / (p : ℝ) ^ (5 / 4 : ℝ) := by
      have hlog := Real.log_le_rpow_div hp₀.le (by norm_num : (0 : ℝ) < 1 / 4)
      have hrpow : r ^ (3 : ℕ) = (p : ℝ) ^ (3 / 2 : ℝ) := by
        dsimp [r]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hp₀.le]
        norm_num
      have hratio : (p : ℝ) ^ (1 / 4 : ℝ) / (p : ℝ) ^ (3 / 2 : ℝ) =
          ((p : ℝ) ^ (5 / 4 : ℝ))⁻¹ := by
        rw [← Real.rpow_sub hp₀, show (1 / 4 : ℝ) - 3 / 2 = -(5 / 4) by norm_num, Real.rpow_neg hp₀.le]
      rw [hrpow]
      calc
        _ ≤ (((p : ℝ) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ)) / (p : ℝ) ^ (3 / 2 : ℝ)) * 4 :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right hlog (by positivity)) (by norm_num)
        _ = 16 * ((p : ℝ) ^ (1 / 4 : ℝ) / (p : ℝ) ^ (3 / 2 : ℝ)) := by ring
        _ = _ := by simpa only [div_eq_mul_inv] using congrArg (16 * ·) hratio

private def tailConstant : ℝ := ∑' n : ℕ, 16 / (n : ℝ) ^ (5 / 4 : ℝ)

private theorem tailConstant_nonneg : 0 ≤ tailConstant :=
  tsum_nonneg fun _ => by positivity

private theorem higherPower_tail_le {z : ℝ} (hz : 1 ≤ z) :
    (∑ k ∈ Icc 3 (powerLimit z),
      ∑ p ∈ primesUpTo (z ^ ((1 : ℝ) / k)),
        Real.log (p : ℝ) / (Real.sqrt (p : ℝ)) ^ k) ≤ tailConstant := by
  calc
    _ ≤ ∑ k ∈ Icc 3 (powerLimit z), ∑ p ∈ primesUpTo z,
          Real.log (p : ℝ) / (Real.sqrt (p : ℝ)) ^ k := by
      apply sum_le_sum
      intro k hk
      apply sum_le_sum_of_subset_of_nonneg (primes_root_subset hz (by have := (mem_Icc.mp hk).1; omega))
      exact fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (by positivity)
    _ = ∑ p ∈ primesUpTo z, ∑ k ∈ Icc 3 (powerLimit z),
          Real.log (p : ℝ) / (Real.sqrt (p : ℝ)) ^ k := Finset.sum_comm
    _ ≤ ∑ p ∈ primesUpTo z, 16 / (p : ℝ) ^ (5 / 4 : ℝ) :=
      sum_le_sum fun p hp => prime_geometric_tail (prime_of_mem hp) _
    _ ≤ tailConstant := by
      have hsum : Summable (fun n : ℕ => 16 / (n : ℝ) ^ (5 / 4 : ℝ)) :=
        (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 5 / 4)).const_div 16
      exact hsum.sum_le_tsum _ fun _ _ => by positivity

/-- At exponent one half the squares account for the logarithm, with bounded remainder. -/
theorem abs_higherPowerWeight_sub_half_log_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ≥ (1 : ℝ),
      |higherPowerWeight z (1 / 2) - Real.log z / 2| ≤ C := by
  refine ⟨Real.log 4 + 4 + tailConstant,
    add_nonneg (by positivity) tailConstant_nonneg, fun z hz => ?_⟩
  let T : ℝ := ∑ k ∈ Icc 3 (powerLimit z),
    ∑ p ∈ primesUpTo (z ^ ((1 : ℝ) / k)),
      Real.log (p : ℝ) / (Real.sqrt (p : ℝ)) ^ k
  have hT : 0 ≤ T := sum_nonneg fun _ _ => sum_nonneg fun p _ =>
    div_nonneg (Real.log_natCast_nonneg p) (by positivity)
  have hT' : T ≤ tailConstant := higherPower_tail_le hz
  have hsplit : higherPowerWeight z (1 / 2) =
      (∑ p ∈ primesUpTo (Real.sqrt z), Real.log (p : ℝ) / p) + T := by
    unfold higherPowerWeight
    simp_rw [pow_rpow_half]
    rw [← add_sum_Ioc_eq_sum_Icc (show 2 ≤ powerLimit z from le_max_left _ _),
      ← Icc_add_one_left_eq_Ioc]
    change (∑ p ∈ primesUpTo (z ^ ((1 : ℝ) / (2 : ℕ))),
      Real.log (p : ℝ) / (Real.sqrt (p : ℝ)) ^ (2 : ℕ)) + T = _
    simp only [Nat.cast_ofNat, ← Real.sqrt_eq_rpow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hm := Mertens.sum_log_prime_div_eq_log (Real.one_le_sqrt.mpr hz)
  change |(∑ p ∈ primesUpTo (Real.sqrt z), Real.log (p : ℝ) / p) -
    Real.log (Real.sqrt z)| ≤ Real.log 4 + 4 at hm
  rw [Real.log_sqrt (zero_le_one.trans hz)] at hm
  rw [hsplit, abs_le]
  have hm' := abs_le.mp hm
  exact ⟨by linarith [hm'.1, tailConstant_nonneg], by linarith [hm'.2]⟩

theorem higherPowerWeight_le_half_log_add :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ≥ (1 : ℝ), ∀ β ≥ (1 / 2 : ℝ),
      higherPowerWeight z β ≤ Real.log z / 2 + C := by
  obtain ⟨C, hC, hcrit⟩ := abs_higherPowerWeight_sub_half_log_le
  refine ⟨C, hC, fun z hz β hβ => ?_⟩
  have hmono : higherPowerWeight z β ≤ higherPowerWeight z (1 / 2) := by
    unfold higherPowerWeight
    refine sum_le_sum fun k _ => sum_le_sum fun p hp => ?_
    have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem hp).one_le
    have hbase : (1 : ℝ) ≤ (p : ℝ) ^ k := one_le_pow₀ hp₁
    exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p)
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hbase) _)
      (Real.rpow_le_rpow_of_exponent_le hbase hβ)
  linarith only [hmono, (abs_le.mp (hcrit z hz)).2]

/-- The estimate only needs an envelope on the smaller scales sampled at `x`. -/
theorem abs_higherPowerDilations_le_weight {x β M : ℝ} (hx : 0 < x)
    (hM : ∀ y : ℝ, 0 < y → y ≤ x → |shell y| ≤ M * y ^ β) :
    |higherPowerDilations x| ≤ M * x ^ β * higherPowerWeight (B * x) β := by
  unfold higherPowerDilations higherPowerWeight
  simp_rw [Finset.mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hp => ?_)
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem hp).one_le
  have hbase : (1 : ℝ) ≤ (p : ℝ) ^ k := one_le_pow₀ hp₁
  have hpos : 0 < (p : ℝ) ^ k := zero_lt_one.trans_le hbase
  push_cast
  rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg p)]
  calc
    _ ≤ Real.log (p : ℝ) * (M * (x / (p : ℝ) ^ k) ^ β) :=
      mul_le_mul_of_nonneg_left
        (hM _ (div_pos hx hpos) ((div_le_iff₀ hpos).mpr (by
          simpa using mul_le_mul_of_nonneg_left hbase hx.le))) (Real.log_natCast_nonneg p)
    _ = _ := by rw [Real.div_rpow hx.le hpos.le]; ring

theorem abs_higherPowerDilations_le_half_log_add :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ (1 : ℝ), ∀ β ≥ (1 / 2 : ℝ), ∀ M ≥ (0 : ℝ),
      (∀ y : ℝ, 0 < y → y ≤ x → |shell y| ≤ M * y ^ β) →
      |higherPowerDilations x| ≤ M * x ^ β * (Real.log x / 2 + C) := by
  obtain ⟨C, hC, hW⟩ := higherPowerWeight_le_half_log_add
  have hB₁ : (1 : ℝ) ≤ B := one_le_pow₀ one_lt_A.le
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB₁
  refine ⟨C + Real.log B / 2, by linarith, fun x hx β hβ M hM hS => ?_⟩
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hBx : 1 ≤ B * x := one_le_mul_of_one_le_of_one_le hB₁ hx
  have hw := hW (B * x) hBx β hβ
  rw [Real.log_mul (pow_ne_zero _ A_pos.ne') hx₀.ne'] at hw
  exact (abs_higherPowerDilations_le_weight hx₀ hS).trans
    (mul_le_mul_of_nonneg_left (by linarith only [hw])
      (mul_nonneg hM (Real.rpow_nonneg hx₀.le _)))

open MeasureTheory

/-- The half-open convention gives an exact partition by backward translations. -/
def logBox (h j t : ℝ) : ℝ :=
  (Set.Ioc 0 h).indicator (fun u => Real.exp (j * u)) t

def oneSidedExp (j t : ℝ) : ℝ :=
  (Set.Ioi 0).indicator (fun u => Real.exp (j * u)) t

theorem logBox_eq_oneSidedExp_sub {h j t : ℝ} (hh : 0 < h) :
    logBox h j t = oneSidedExp j t - Real.exp (j * h) * oneSidedExp j (t - h) := by
  by_cases ht : t ≤ h
  · by_cases ht₀ : 0 < t
    · simp [logBox, oneSidedExp, Set.indicator_apply, ht, ht₀, show ¬0 < t - h by linarith]
    · simp [logBox, oneSidedExp, Set.indicator_apply, ht₀,
        show ¬0 < t - h by linarith [le_of_not_gt ht₀]]
  · have hht : h < t := lt_of_not_ge ht
    have ht₀ : 0 < t := hh.trans hht
    have hshift : 0 < t - h := sub_pos.mpr hht
    simp only [logBox, oneSidedExp, Set.indicator_apply, Set.mem_Ioc, Set.mem_Ioi,
      ht₀, ht, and_false, ite_false, ite_true]
    rw [if_pos hshift, ← Real.exp_add, show j * h + j * (t - h) = j * t by ring, sub_self]

private theorem weighted_logBox_shift (h j t v : ℝ) :
    Real.exp (-j * v) * logBox h j (t + v) =
      if t + v ∈ Set.Ioc 0 h then Real.exp (j * t) else 0 := by
  unfold logBox
  rw [Set.indicator_apply]
  split_ifs
  · rw [← Real.exp_add]
    congr 1
    ring
  · rw [mul_zero]

private theorem integral_weighted_logBox_shift (h j t : ℝ) :
    (∫ v in Set.Ioi (0 : ℝ), Real.exp (-j * v) * logBox h j (t + v)) =
      max 0 (h - t - max 0 (-t)) * Real.exp (j * t) := by
  let a := max 0 (-t)
  let d := h - t
  have ha : 0 ≤ a := le_max_left _ _
  have hsub : Set.Ioc a d ⊆ Set.Ioi (0 : ℝ) :=
    fun v hv => ha.trans_lt hv.1
  calc
    _ = ∫ v in Set.Ioi (0 : ℝ), (Set.Ioc a d).indicator (fun _ => Real.exp (j * t)) v := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      have hv₀ : 0 < v := hv
      have hmem : t + v ∈ Set.Ioc 0 h ↔ v ∈ Set.Ioc a d := by
        simp only [Set.mem_Ioc, a, d, max_lt_iff, hv₀, true_and]
        constructor <;> intro hv' <;> constructor <;> linarith [hv'.1, hv'.2]
      change Real.exp (-j * v) * logBox h j (t + v) = _
      rw [weighted_logBox_shift]
      by_cases ht : t + v ∈ Set.Ioc (0 : ℝ) h
      · rw [if_pos ht, Set.indicator_of_mem (hmem.mp ht)]
      · have hv : v ∉ Set.Ioc a d := fun hv => ht (hmem.mpr hv)
        rw [if_neg ht, Set.indicator_of_notMem hv]
    _ = ∫ _ in Set.Ioc a d, Real.exp (j * t) := by
      rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr hsub]
    _ = _ := by
      by_cases had : a ≤ d
      · rw [← intervalIntegral.integral_of_le had, intervalIntegral.integral_const,
          smul_eq_mul, max_eq_right (sub_nonneg.mpr had)]
      · have hempty : Set.Ioc a d = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro v hv
          exact had (hv.1.le.trans hv.2)
        rw [hempty, setIntegral_empty, max_eq_left (sub_nonpos.mpr (le_of_not_ge had)), zero_mul]

/-- In the positive shifts, `k + 1` ranges over the integers at least one. -/
theorem logBox_mul_argument {h : ℝ} (hh : 0 < h) (j t : ℝ) :
    t * logBox h j t =
      h * logBox h j t +
        h * (∑' k : ℕ, Real.exp (-j * (((k + 1 : ℕ) : ℝ) * h)) *
          logBox h j (t + ((k + 1 : ℕ) : ℝ) * h)) -
        ∫ v in Set.Ioi (0 : ℝ), Real.exp (-j * v) * logBox h j (t + v) := by
  rw [integral_weighted_logBox_shift]
  simp_rw [weighted_logBox_shift]
  by_cases ht : 0 < t
  · have hzero (k : ℕ) : ¬t + ((k + 1 : ℕ) : ℝ) * h ∈ Set.Ioc 0 h := by
      intro hk
      have hk₁ : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ k + 1 by omega)
      have hkh := mul_le_mul_of_nonneg_right hk₁ hh.le
      have hk₂ := hk.2
      linarith
    simp only [hzero, ite_false, tsum_zero, mul_zero, add_zero, max_eq_left (neg_nonpos.mpr ht.le),
      sub_zero]
    by_cases hth : t ≤ h
    · simp only [logBox, Set.indicator_apply, Set.mem_Ioc, ht, hth, and_self, ite_true,
        max_eq_right (sub_nonneg.mpr hth)]
      ring
    · simp [logBox, Set.indicator_apply, hth, max_eq_left (sub_nonpos.mpr (le_of_not_ge hth))]
  · have ht₀ : t ≤ 0 := le_of_not_gt ht
    let k₀ := ⌊-t / h⌋₊
    have hlo : (k₀ : ℝ) * h ≤ -t :=
      (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg (neg_nonneg.mpr ht₀) hh.le))
    have hhi : -t < ((k₀ : ℝ) + 1) * h :=
      (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one _)
    have hmem : t + ((k₀ + 1 : ℕ) : ℝ) * h ∈ Set.Ioc 0 h := by
      simp only [Nat.cast_add, Nat.cast_one, Set.mem_Ioc]
      constructor <;> linarith [hlo, hhi, show ((k₀ : ℝ) + 1) * h = (k₀ : ℝ) * h + h by ring]
    have hzero (k : ℕ) (hk : k ≠ k₀) :
        ¬t + ((k + 1 : ℕ) : ℝ) * h ∈ Set.Ioc 0 h := by
      intro hkv
      have hkv₁ := hkv.1
      have hkv₂ := hkv.2
      push_cast at hkv₁ hkv₂
      rcases lt_or_gt_of_ne hk with hlt | hgt
      · have hk' : (k : ℝ) + 1 ≤ k₀ := by exact_mod_cast (show k + 1 ≤ k₀ by omega)
        linarith [mul_le_mul_of_nonneg_right hk' hh.le]
      · have hk' : (k₀ : ℝ) + 1 ≤ k := by exact_mod_cast (show k₀ + 1 ≤ k by omega)
        have hm := mul_le_mul_of_nonneg_right hk' hh.le
        nlinarith only [hhi, hm, hkv₂]
    rw [tsum_eq_single k₀ (fun k hk => if_neg (hzero k hk)), if_pos hmem]
    have hlen : h - t - max 0 (-t) = h := by rw [max_eq_right (neg_nonneg.mpr ht₀)]; ring
    simp [logBox, Set.indicator_apply, ht, hlen, max_eq_right hh.le]

/-- Scalar additive convolution with Lebesgue measure. -/
def logConvolution (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ v : ℝ, f v * g (t - v)

theorem logConvolution_mul_argument {f g : ℝ → ℝ} {t : ℝ}
    (hf : Integrable (fun v => (v * f v) * g (t - v)))
    (hg : Integrable (fun v => f v * ((t - v) * g (t - v)))) :
    t * logConvolution f g t =
      logConvolution (fun v => v * f v) g t +
        logConvolution f (fun v => v * g v) t := by
  unfold logConvolution
  rw [← integral_const_mul, ← integral_add hf hg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by ring

/-!
Open analytic steps for h = Real.log A:

* For the left-associated convolution F_r of oneSidedExp j for j = 0,...,r,
  prove F_r(t) = (Real.exp t - 1)^r / r.factorial for t > 0 and zero for t < 0.
  In the step with j = r + 1 use u = Real.exp (t - v), where v is the old kernel's
  argument. After cancellation the integrand is (Real.exp t - u)^r / r.factorial.
* Prove that the left-associated fourfold convolution of logBox h j for j = 0,...,3
  equals b (Real.exp t) pointwise. Expanding logBox_eq_oneSidedExp_sub gives the
  coefficient polynomial from NymanFixedRationalKernel.coefficient_product.
* Justify the integral exchanges for the weighted boxes, then prove for all x > 0
  that logCorrection x equals 4*h*shell x plus
    ∑ j : Fin 4, (h * ∑' k : ℕ, Real.exp (-(j.val : ℝ) * ((k+1 : ℕ) : ℝ) * h) *
        shell (x * Real.exp (-((k+1 : ℕ) : ℝ) * h)) -
      ∫ v in Set.Ioi (0 : ℝ), Real.exp (-(j.val : ℝ) * v) * shell (x * Real.exp (-v))).
  The shell cutoff gives a finite dilation range at each x.
-/

end NymanPrimeDilations
