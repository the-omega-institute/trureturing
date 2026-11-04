/- GID: D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The literal factorial and complete von Mangoldt dilation sum has exact finite smoothing, continuous compensation and an identified restricted-ae derivative with global bounds. -/

import D5.S3.Arith.Robin.ActualFactorialRobinHighDerivative
import D5.S3.Weil.Mertens.Estimates
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
Integrated from the immutable arithmetic source candidate with the pinned supplier
source admission 01b573fd9b691a4be3a8b0ecbb41b3311eda19b5; Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679 and Lean 4.35.0. The owner and its
public contract are checked by the scoped Lean/report workflow; registration
binding remains a separate unfinished audit.

The arithmetic objects below are the actual factorial residual and the complete
von Mangoldt function. The finite smoothing is proved by regrouping the complete
divisor triangle, including the real-floor boundary. No arithmetic identity or
analytic estimate is an extra hypothesis of a public theorem.

The factorial identity and envelope are reused from their public owners. Their
Terence Tao / Apache-2.0 attribution remains at LogConvolutionMassExpansion;
none of its private scalar proofs is copied here. Abel summation, harmonic
limits, and improper-integral facts are reused from pinned public Mathlib.

The original signed inverse cancellation, centered prime-power quadratic,
exponential boundary form, complete Mobius tail, and sublinear sufficient
moment order are not conclusions of this source.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
open scoped BigOperators Topology ArithmeticFunction

namespace D5.S3.Arith.Robin.ActualContinuousFactorialCompensation

abbrev gamma : ℝ := Real.eulerMascheroniConstant
def L : ℝ := Real.log (2 * Real.pi)
abbrev eta := ActualFactorialRobinHighDerivative.eta

/-- A right-closed prefixSum, retaining the zero coefficient for Abel summation. -/
def prefixSum (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n

def H (x : ℝ) : ℝ := prefixSum (fun n => (n : ℝ)⁻¹) x
def J (x : ℝ) : ℝ := prefixSum (fun n => Real.log n / n) x

/-- The term at one vanishes; every prime power at least two is retained. -/
def B (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 2 ⌊x⌋₊,
    ArithmeticFunction.vonMangoldt n * (1 - Int.fract (x / n))) - gamma * x

def h (x : ℝ) : ℝ := eta x - L - B x
def h1 : ℝ := 1 + gamma - L
def Z_h (x : ℝ) : ℝ := ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, h (x / k)
def ceta : ℝ := ∫ y in Ioi (1 : ℝ), eta y / y ^ 2
def alpha : ℝ := gamma ^ 2 + 2 * ceta - 2
def G (x : ℝ) : ℝ := Z_h x - h1 * ⌊x⌋₊ - alpha * (x - 1)
def epsilon (x : ℝ) : ℝ := H x - Real.log x - gamma
def epsilonDensity (x : ℝ) : ℝ := epsilon x / x
def T_epsilon (x : ℝ) : ℝ := ∫ t in Ioi x, epsilonDensity t
def slope (x : ℝ) : ℝ := (gamma - Real.log x) * H x + 2 * J x - alpha

private lemma prefixSum_eq_Ioc (c : ℕ → ℝ) (hc : c 0 = 0) (x : ℝ) :
    prefixSum c x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, c n := by
  rw [prefixSum, Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, hc, zero_add]

private lemma sum_Ioc_eq_range (c : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, c n) = ∑ i ∈ Finset.range N, c (i + 1) := by
  symm
  refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_Ioc.mpr ⟨by omega, by have := Finset.mem_range.mp hi; omega⟩
  · intro i _ j _ hij
    omega
  · intro n hn
    obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hn
    exact ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i _
    rfl

lemma H_harmonic (x : ℝ) : H x = (harmonic ⌊x⌋₊ : ℝ) := by
  rw [H, prefixSum_eq_Ioc (fun n => (n : ℝ)⁻¹) (by simp), sum_Ioc_eq_range]
  simp [harmonic, Rat.cast_sum]

private lemma log_prefixSum (x : ℝ) :
    prefixSum (fun n => Real.log n) x = Real.log (⌊x⌋₊.factorial : ℝ) := by
  rw [prefixSum_eq_Ioc (fun n => Real.log n) (by simp)]
  exact D5.S3.Arith.LogConvolutionMassExpansion.sum_log_eq_log_factorial _

private lemma eta_formula (x : ℝ) :
    eta x = Real.log (⌊x⌋₊.factorial : ℝ) - (x * Real.log x - x) :=
  ActualFactorialRobinHighDerivative.result.1 x

private lemma eta_bound {x : ℝ} (hx : 1 ≤ x) : |eta x| ≤ 1 + Real.log x := by
  simpa only [ActualFactorialRobinHighDerivative.eta,
    ActualFactorialRobinHighDerivative.kernelData, one_mul] using
    ActualFactorialRobinHighDerivative.kernelData.residual_high x hx

private lemma eta_measurable : Measurable eta :=
  QuotientIntegralBudget.measurable_residual (fun n : ℕ => Real.log n) 1 1

private lemma prefixSum_measurable (c : ℕ → ℝ) : Measurable (prefixSum c) := by
  exact (measurable_of_countable (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N, c n)).comp
    Nat.measurable_floor

/-- Regroup an arbitrary weight on the finite divisor triangle, without
separability or a prime-only restriction. This helper is consumed by smoothing. -/
private lemma divisor_triangle (x : ℝ) (W : ℕ × ℕ → ℝ) :
    (∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, ∑ n ∈ Finset.Ioc 0 ⌊x / k⌋₊, W (k, n)) =
      ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, ∑ p ∈ m.divisorsAntidiagonal, W p := by
  classical
  let N := ⌊x⌋₊
  have hinner (k : ℕ) (hk : k ∈ Finset.Ioc 0 N) :
      (∑ n ∈ Finset.Ioc 0 (N / k), W (k, n)) =
        ∑ n ∈ Finset.Ioc 0 N, if k * n ≤ N then W (k, n) else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_filter]
    have hk0 := (Finset.mem_Ioc.mp hk).1
    constructor
    · rintro ⟨hn0, hn⟩
      refine ⟨⟨hn0, hn.trans (Nat.div_le_self _ _)⟩, ?_⟩
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hk0).mp hn
    · rintro ⟨⟨hn0, _⟩, hkn⟩
      exact ⟨hn0, (Nat.le_div_iff_mul_le hk0).mpr (by simpa [Nat.mul_comm] using hkn)⟩
  have hprod :
      (∑ k ∈ Finset.Ioc 0 N, ∑ n ∈ Finset.Ioc 0 (N / k), W (k, n)) =
        ∑ p ∈ Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N with p.1 * p.2 ≤ N, W p := by
    simp_rw [Finset.sum_filter, Finset.sum_product]
    exact Finset.sum_congr rfl hinner
  have hregroup :
      (∑ m ∈ Finset.Ioc 0 N, ∑ p ∈ m.divisorsAntidiagonal, W p) =
        ∑ p ∈ Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N with p.1 * p.2 ≤ N, W p := by
    calc
      _ = ∑ m ∈ Finset.Ioc 0 N,
          ∑ p ∈ Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N with p.1 * p.2 = m, W p := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le
          (Finset.mem_Ioc.mp hm).1.ne' (Finset.mem_Ioc.mp hm).2]
      _ = _ := by
        simp_rw [Finset.sum_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p hp
        have hp0 := Finset.mem_product.mp hp
        have hpos : 0 < p.1 * p.2 := Nat.mul_pos
          (Finset.mem_Ioc.mp hp0.1).1 (Finset.mem_Ioc.mp hp0.2).1
        by_cases hle : p.1 * p.2 ≤ N
        · rw [if_pos hle]
          rw [Finset.sum_eq_single (p.1 * p.2)]
          · simp
          · intro b _ hb
            simp [Ne.symm hb]
          · intro hnot
            exact (hnot (Finset.mem_Ioc.mpr ⟨hpos, hle⟩)).elim
        · rw [if_neg hle]
          apply Finset.sum_eq_zero
          intro m hm
          have hmN := (Finset.mem_Ioc.mp hm).2
          have hne : p.1 * p.2 ≠ m := by intro he; exact hle (he ▸ hmN)
          simp [hne]
  simpa only [Nat.floor_div_natCast] using hprod.trans hregroup.symm

private lemma mangoldt_ramp (x : ℝ) :
    (∑ k ∈ Finset.Ioc 0 ⌊x⌋₊,
      ∑ n ∈ Finset.Ioc 0 ⌊x / k⌋₊,
        ArithmeticFunction.vonMangoldt n * (x / ((k : ℝ) * n) - 1)) =
      ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, Real.log m * (x / m - 1) := by
  rw [divisor_triangle x (fun p =>
    ArithmeticFunction.vonMangoldt p.2 * (x / ((p.1 : ℝ) * p.2) - 1))]
  apply Finset.sum_congr rfl
  intro m hm
  calc
    _ = ∑ p ∈ m.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt p.2 * (x / m - 1) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := (Nat.mem_divisorsAntidiagonal.mp hp).1
      rw [← Nat.cast_mul, hp']
    _ = (∑ p ∈ m.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt p.2) * (x / m - 1) := by rw [Finset.sum_mul]
    _ = _ := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ n => ArithmeticFunction.vonMangoldt n),
        ArithmeticFunction.vonMangoldt_sum]

private lemma h_expansion {x : ℝ} (hx : 1 ≤ x) :
    h x = x * (1 + gamma - Real.log x) - L +
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt n * (x / n - 1) := by
  have hfrac (n : ℕ) :
      ArithmeticFunction.vonMangoldt n * (1 - Int.fract (x / n)) =
        ArithmeticFunction.vonMangoldt n * (⌊x / n⌋₊ : ℝ) -
          ArithmeticFunction.vonMangoldt n * (x / n - 1) := by
    rw [Int.fract, ← natCast_floor_eq_intCast_floor
      (div_nonneg (by linarith) (Nat.cast_nonneg n))]
    ring
  have hb :
      (∑ n ∈ Finset.Icc 2 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt n * (1 - Int.fract (x / n))) =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt n * (1 - Int.fract (x / n)) := by
    change (∑ n ∈ Finset.Ioc 1 ⌊x⌋₊, _) = _
    exact Mertens.sum_Ioc_one_eq_sum_Ioc_zero
      ((Nat.one_le_floor_iff x).mpr hx) (by simp)
  rw [h, B, hb, eta_formula]
  simp_rw [hfrac]
  rw [Finset.sum_sub_distrib, ← Mertens.sum_log_eq_sum_mangoldt,
    D5.S3.Arith.LogConvolutionMassExpansion.sum_log_eq_log_factorial]
  ring

/-- Full all-real finite smoothing. The factorial and the real-floor endpoint
are literal; the finite von Mangoldt rearrangement is proved above. -/
theorem finite_smoothing {x : ℝ} (hx : 1 ≤ x) :
    Z_h x = x * ((1 + gamma - Real.log x) * H x + 2 * J x) -
      Real.log (⌊x⌋₊.factorial : ℝ) - L * ⌊x⌋₊ := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hkpos (k : ℕ) (hk : k ∈ Finset.Ioc 0 ⌊x⌋₊) : 0 < (k : ℝ) := by
    exact_mod_cast (Finset.mem_Ioc.mp hk).1
  have hkx (k : ℕ) (hk : k ∈ Finset.Ioc 0 ⌊x⌋₊) : (k : ℝ) ≤ x :=
    (Nat.le_floor_iff hx0.le).mp (Finset.mem_Ioc.mp hk).2
  have hsplit : Z_h x =
      Finset.sum (Finset.Ioc 0 ⌊x⌋₊) (fun k =>
        (x / k) * (1 + gamma - Real.log (x / k)) - L) +
      Finset.sum (Finset.Ioc 0 ⌊x⌋₊) (fun k =>
        Finset.sum (Finset.Ioc 0 ⌊x / k⌋₊) (fun n =>
          ArithmeticFunction.vonMangoldt n * (x / ((k : ℝ) * n) - 1))) := by
    calc
      Z_h x = Finset.sum (Finset.Ioc 0 ⌊x⌋₊) (fun k =>
          ((x / k) * (1 + gamma - Real.log (x / k)) - L) +
            Finset.sum (Finset.Ioc 0 ⌊x / k⌋₊) (fun n =>
              ArithmeticFunction.vonMangoldt n * (x / ((k : ℝ) * n) - 1))) := by
        unfold Z_h
        apply Finset.sum_congr rfl
        intro k hk
        rw [h_expansion ((one_le_div (hkpos k hk)).mpr (hkx k hk))]
        simp only [div_div]
      _ = _ := by simpa only [Finset.sum_add_distrib]
  rw [hsplit, mangoldt_ramp]
  have hbase :
      Finset.sum (Finset.Ioc 0 ⌊x⌋₊) (fun k =>
        (x / k) * (1 + gamma - Real.log (x / k)) - L) =
        x * ((1 + gamma - Real.log x) * H x + J x) - L * ⌊x⌋₊ := by
    have hexpand :
        Finset.sum (Finset.Ioc 0 ⌊x⌋₊) (fun k =>
          (x / k) * (1 + gamma - Real.log (x / k)) - L) =
        Finset.sum (Finset.Ioc 0 ⌊x⌋₊) (fun k =>
          (x / k) * (1 + gamma - (Real.log x - Real.log k)) - L) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [Real.log_div hx0.ne' (hkpos k hk).ne']
    rw [hexpand]
    have he (k : ℕ) :
        (x / k) * (1 + gamma - (Real.log x - Real.log k)) - L =
          x * (1 + gamma - Real.log x) * (k : ℝ)⁻¹ +
            x * (Real.log k / k) - L := by ring
    simp_rw [he]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    rw [H, J, prefixSum_eq_Ioc (fun n => (n : ℝ)⁻¹) (by simp),
      prefixSum_eq_Ioc (fun n => Real.log n / n) (by simp)]
    have hcard : (Finset.Ioc 0 ⌊x⌋₊).card = ⌊x⌋₊ := by
      simpa using (Nat.card_Ioc 0 ⌊x⌋₊)
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hcard]
    ring
  have hramp :
      (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, Real.log m * (x / m - 1)) =
        x * J x - Real.log (⌊x⌋₊.factorial : ℝ) := by
    simp_rw [mul_sub, mul_one, show ∀ m : ℕ,
      Real.log m * (x / m) = x * (Real.log m / m) from fun m => by ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← prefixSum_eq_Ioc (fun n => Real.log n / n) (by simp),
      ← prefixSum_eq_Ioc (fun n => Real.log n) (by simp), log_prefixSum]
    rfl
  rw [hbase, hramp]
  ring

lemma G_formula {x : ℝ} (hx : 1 ≤ x) :
    G x = x * ((1 + gamma - Real.log x) * H x + 2 * J x) -
      Real.log (⌊x⌋₊.factorial : ℝ) - (1 + gamma) * ⌊x⌋₊ - alpha * (x - 1) := by
  rw [G, finite_smoothing hx, h1]
  ring

private lemma gamma_pos : 0 < gamma := by
  have := Real.one_half_lt_eulerMascheroniConstant
  linarith

/-- The real-floor harmonic error is bounded on the entire half-line,
using the two public harmonic sequences at N and N+1. -/
private lemma epsilon_bound {x : ℝ} (hx : 1 ≤ x) : |epsilon x| ≤ 1 / x := by
  let N := ⌊x⌋₊
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hlo := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant N
  have hhi := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' (N + 1)
  simp only [Real.eulerMascheroniSeq] at hlo
  simp only [Real.eulerMascheroniSeq', Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, if_false, harmonic_succ, Rat.cast_add, Rat.cast_inv,
    Rat.cast_natCast, Nat.cast_add, Nat.cast_one] at hhi
  have hlog := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0 < (N : ℝ) + 1) hx0)
  rw [Real.log_div (by positivity : (N : ℝ) + 1 ≠ 0) hx0.ne'] at hlog
  have hu : Real.log ((N : ℝ) + 1) - Real.log x ≤ 1 / x := by
    calc
      _ ≤ ((N : ℝ) + 1) / x - 1 := hlog
      _ ≤ 1 / x := by rw [div_sub_one hx0.ne']; gcongr; linarith
  have hl : Real.log x ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log hx0 hxN.le
  have hi : 1 / ((N : ℝ) + 1) ≤ 1 / x := one_div_le_one_div_of_le hx0 hxN.le
  rw [epsilon, H_harmonic, abs_le]
  change -(1 / x) ≤ (harmonic N : ℝ) - Real.log x - gamma ∧
    (harmonic N : ℝ) - Real.log x - gamma ≤ 1 / x
  have hhi' : gamma < (harmonic N : ℝ) + 1 / ((N : ℝ) + 1) -
      Real.log ((N : ℝ) + 1) := by
    simpa [gamma, one_div, Nat.cast_add] using hhi
  constructor
  · linarith
  · linarith

private lemma prefixSum_mul_interval (c : ℕ → ℝ) {x : ℝ} (hx : 1 ≤ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 1 x)) :
    IntervalIntegrable (fun t => g t * prefixSum c t) volume 1 x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  exact integrableOn_mul_sum_Icc c (by norm_num) (hg.integrableOn_Icc)

private lemma prefixSum_interval (c : ℕ → ℝ) {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable (prefixSum c) volume 1 x := by
  simpa only [one_mul] using
    (prefixSum_mul_interval c hx (g := fun _ => 1) continuousOn_const)

/-- Public Abel summation, with the actual zero coefficient and actual floor.
Only used as an auxiliary in the three genuine compositions below. -/
private lemma abel (c : ℕ → ℝ) (hc : c 0 = 0) {f f' : ℝ → ℝ}
    {x : ℝ} (hx : 1 ≤ x)
    (hd : ∀ t ∈ Icc (1 : ℝ) x, HasDerivAt f (f' t) t)
    (hi : IntegrableOn f' (Icc (1 : ℝ) x)) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n * c n) =
      f x * prefixSum c x - ∫ t in (1 : ℝ)..x, f' t * prefixSum c t := by
  have hid : IntegrableOn (deriv f) (Icc (1 : ℝ) x) :=
    hi.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have ha := sum_mul_eq_sub_integral_mul₀ c hc x
    (fun t ht => (hd t ht).differentiableAt) hid
  have hs :
      (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n * c n) =
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n * c n := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
    simp only [hc, mul_zero, zero_add]
  have he :
      (∫ t in Ioc (1 : ℝ) x, deriv f t * prefixSum c t) =
        ∫ t in (1 : ℝ)..x, f' t * prefixSum c t := by
    rw [intervalIntegral.integral_of_le hx]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change deriv f t * prefixSum c t = f' t * prefixSum c t
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv]
  change (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n * c n) =
    f x * prefixSum c x - ∫ t in Ioc (1 : ℝ) x, deriv f t * prefixSum c t at ha
  rw [hs, he] at ha
  exact ha

private lemma log_continuousOn {x : ℝ} : ContinuousOn Real.log (Icc (1 : ℝ) x) :=
  Real.continuousOn_log.mono (fun t ht => ne_of_gt (zero_lt_one.trans_le ht.1))

private lemma slope_interval {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable slope volume 1 x := by
  have hiH : IntervalIntegrable H volume 1 x := by
    change IntervalIntegrable (prefixSum (fun n => (n : ℝ)⁻¹)) volume 1 x
    exact prefixSum_interval _ hx
  have hiJ : IntervalIntegrable J volume 1 x := by
    change IntervalIntegrable (prefixSum (fun n => Real.log n / n)) volume 1 x
    exact prefixSum_interval _ hx
  have hiLH : IntervalIntegrable (fun t => Real.log t * H t) volume 1 x := by
    simpa [H, mul_comm, mul_left_comm, mul_assoc] using
      (prefixSum_mul_interval (fun n => (n : ℝ)⁻¹) hx log_continuousOn)
  convert (((hiH.const_mul gamma).sub hiLH).add (hiJ.const_mul 2)).sub
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => alpha) volume 1 x)
    using 1 <;> ext t <;> dsimp [slope] <;> ring

private lemma H_first_moment {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, H t) = x * H x - ⌊x⌋₊ := by
  have ha := abel (fun n => (n : ℝ)⁻¹) (by simp) hx
    (f := id) (f' := fun _ => 1) (fun t _ => hasDerivAt_id t)
    (continuousOn_const.integrableOn_Icc)
  have hs :
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (n : ℝ) * (n : ℝ)⁻¹) = (⌊x⌋₊ : ℝ) := by
    calc
      _ = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact mul_inv_cancel₀ (by exact_mod_cast (Finset.mem_Ioc.mp hn).1.ne')
      _ = _ := by simp
  simp only [id_eq, one_mul] at ha
  rw [hs] at ha
  have ha' : (⌊x⌋₊ : ℝ) = x * H x - ∫ t in (1 : ℝ)..x, H t := by
    simpa [H] using ha
  linarith

private lemma H_log_moment {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, Real.log t * H t) =
      (x * Real.log x - x) * H x - Real.log (⌊x⌋₊.factorial : ℝ) + ⌊x⌋₊ := by
  have hd (t : ℝ) (ht : t ∈ Icc (1 : ℝ) x) :
      HasDerivAt (fun u : ℝ => u * Real.log u - u) (Real.log t) t := by
    have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans_le ht.1)
    convert ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)).sub
      (hasDerivAt_id t) using 1
    · ext u
      simp [id_eq]
    · simp [id_eq]
      field_simp [ht0]
      ring
  have ha := abel (fun n => (n : ℝ)⁻¹) (by simp) hx hd
    log_continuousOn.integrableOn_Icc
  have hs :
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ((n : ℝ) * Real.log n - n) * (n : ℝ)⁻¹) =
        Real.log (⌊x⌋₊.factorial : ℝ) - ⌊x⌋₊ := by
    calc
      _ = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Real.log n - 1) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Finset.mem_Ioc.mp hn).1.ne'
        field_simp [hn0]
        <;> ring
      _ = _ := by
        rw [Finset.sum_sub_distrib,
          D5.S3.Arith.LogConvolutionMassExpansion.sum_log_eq_log_factorial]
        simp
  rw [hs] at ha
  change _ = _ * H x - ∫ t in (1 : ℝ)..x, Real.log t * H t at ha
  linarith

private lemma J_first_moment {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, J t) = x * J x - Real.log (⌊x⌋₊.factorial : ℝ) := by
  have ha := abel (fun n => Real.log n / n) (by simp) hx
    (f := id) (f' := fun _ => 1) (fun t _ => hasDerivAt_id t)
    (continuousOn_const.integrableOn_Icc)
  have hs :
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (n : ℝ) * (Real.log n / n)) =
        Real.log (⌊x⌋₊.factorial : ℝ) := by
    rw [← D5.S3.Arith.LogConvolutionMassExpansion.sum_log_eq_log_factorial]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Finset.mem_Ioc.mp hn).1.ne'
    field_simp [hn0]
    <;> ring
  simp only [id_eq, one_mul] at ha
  rw [hs] at ha
  have ha' : Real.log (⌊x⌋₊.factorial : ℝ) =
      x * J x - ∫ t in (1 : ℝ)..x, J t := by
    simpa [J] using ha
  linarith

/-- The exact integral representation pays continuity and absolute continuity
without discarding the integer cutoffs. -/
lemma G_eq_integral {x : ℝ} (hx : 1 ≤ x) :
    G x = ∫ t in (1 : ℝ)..x, slope t := by
  have hH : IntervalIntegrable H volume 1 x := by
    change IntervalIntegrable (prefixSum (fun n => (n : ℝ)⁻¹)) volume 1 x
    exact prefixSum_interval _ hx
  have hJ : IntervalIntegrable J volume 1 x := by
    change IntervalIntegrable (prefixSum (fun n => Real.log n / n)) volume 1 x
    exact prefixSum_interval _ hx
  have hLH : IntervalIntegrable (fun t => Real.log t * H t) volume 1 x := by
    simpa [H, mul_comm, mul_left_comm, mul_assoc] using
      (prefixSum_mul_interval (fun n => (n : ℝ)⁻¹) hx log_continuousOn)
  have he : slope = fun t => gamma * H t - Real.log t * H t + 2 * J t - alpha := by
    funext t
    dsimp [slope]
    ring
  rw [he, intervalIntegral.integral_sub
    (((hH.const_mul gamma).sub hLH).add (hJ.const_mul 2)) intervalIntegrable_const,
    intervalIntegral.integral_add ((hH.const_mul gamma).sub hLH) (hJ.const_mul 2),
    intervalIntegral.integral_sub (hH.const_mul gamma) hLH,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul,
    H_first_moment hx, H_log_moment hx, J_first_moment hx, G_formula hx]
  ring

private lemma G_ac {x : ℝ} (hx : 1 ≤ x) : AbsolutelyContinuousOnInterval G 1 x := by
  apply ((slope_interval hx).absolutelyContinuousOnInterval_intervalIntegral
    (c := 1) (by simp)).congr
  intro y hy
  rw [uIcc_of_le hx] at hy
  exact (G_eq_integral hy.1).symm

private lemma G_continuous : ContinuousOn G (Ici (1 : ℝ)) := by
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := hx
  have hX : 1 ≤ x + 1 := by linarith
  have hc := (G_ac hX).continuousOn
  rw [uIcc_of_le hX] at hc
  apply (hc x ⟨hx, by linarith⟩).mono_of_mem_nhdsWithin
  have hm₁ : Ici (1 : ℝ) ∈ 𝓝[Ici (1 : ℝ)] x := self_mem_nhdsWithin
  have hm₂ : Iio (x + 1) ∈ 𝓝[Ici (1 : ℝ)] x :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith))
  filter_upwards [hm₁, hm₂] with y hy₁ hy₂
  exact ⟨hy₁, hy₂.le⟩

private lemma eta_density_integrable :
    IntegrableOn (fun y => eta y / y ^ 2) (Ioi (1 : ℝ)) := by
  apply (QuotientIntegralBudget.integrableOn_log_tail (by norm_num : (1 : ℝ) ≤ 1)).mono'
    (eta_measurable.div (measurable_id.pow_const 2)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change ‖eta y / y ^ 2‖ ≤ (1 + Real.log y) / y ^ 2
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg y)]
  exact div_le_div_of_nonneg_right (eta_bound hy.le) (sq_nonneg y)

lemma inv_sq_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Ioi a) := by
  convert integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) ha using 1
  ext t
  simp [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast, inv_pow]

lemma inv_sq_integral {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi a, (1 : ℝ) / t ^ 2) = 1 / a := by
  have he : (fun t : ℝ => 1 / t ^ 2) = fun t : ℝ => t ^ (-2 : ℝ) := by
    ext t
    simp [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast, inv_pow]
  rw [he, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha]
  norm_num [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]

private lemma epsilonDensity_measurable : Measurable epsilonDensity := by
  exact (((prefixSum_measurable _).sub Real.measurable_log).sub measurable_const).div measurable_id

private lemma epsilonDensity_bound {x : ℝ} (hx : 1 ≤ x) :
    |epsilonDensity x| ≤ 1 / x ^ 2 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  rw [epsilonDensity, abs_div, abs_of_pos hx0]
  calc
    _ ≤ (1 / x) / x := div_le_div_of_nonneg_right (epsilon_bound hx) hx0.le
    _ = _ := by ring

lemma epsilonDensity_integrable : IntegrableOn epsilonDensity (Ioi (1 : ℝ)) := by
  apply (inv_sq_integrable (by norm_num : (0 : ℝ) < 1)).mono'
    epsilonDensity_measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [Real.norm_eq_abs] using epsilonDensity_bound hx.le

private lemma T_epsilon_bound {x : ℝ} (hx : 1 ≤ x) : |T_epsilon x| ≤ 1 / x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hi := epsilonDensity_integrable.mono_set (Ioi_subset_Ioi hx)
  calc
    _ ≤ ∫ t in Ioi x, |epsilonDensity t| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioi x, (1 : ℝ) / t ^ 2 := by
      apply setIntegral_mono_on hi.abs (inv_sq_integrable hx0) measurableSet_Ioi
      intro t ht
      exact epsilonDensity_bound (hx.trans ht.le)
    _ = _ := inv_sq_integral hx0

private lemma inv_continuousOn {x : ℝ} :
    ContinuousOn (fun t : ℝ => t⁻¹) (Icc (1 : ℝ) x) :=
  continuousOn_id.inv₀ (fun t ht => ne_of_gt (zero_lt_one.trans_le ht.1))

private lemma log_div_interval {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ => Real.log t / t) volume 1 x := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hx]
  exact log_continuousOn.div continuousOn_id
    (fun t ht => ne_of_gt (zero_lt_one.trans_le ht.1))

private lemma log_div_integral {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, Real.log t / t) = (Real.log x) ^ 2 / 2 := by
  have hd (t : ℝ) (ht : t ∈ uIcc (1 : ℝ) x) :
      HasDerivAt (fun u : ℝ => (Real.log u) ^ 2 / 2) (Real.log t / t) t := by
    rw [uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans_le ht.1)
    convert ((Real.hasDerivAt_log ht0).pow 2).div_const 2 using 1 <;> ring
  have ha := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (log_div_interval hx)
  simpa using ha

private lemma inv_integral {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, (1 : ℝ) / t) = Real.log x := by
  simpa only [one_div, div_one] using integral_inv_of_pos (by norm_num : (0 : ℝ) < 1)
    (zero_lt_one.trans_le hx)

private lemma J_finite_harmonic {x : ℝ} (hx : 1 ≤ x) :
    J x = (Real.log x) ^ 2 / 2 + Real.log x * epsilon x -
      ∫ t in (1 : ℝ)..x, epsilonDensity t := by
  have hiH := prefixSum_mul_interval (fun n => (n : ℝ)⁻¹) hx
    (g := fun t => t⁻¹) inv_continuousOn
  have hiH' : IntervalIntegrable (fun t => H t / t) volume 1 x := by
    simpa only [H, div_eq_mul_inv, mul_comm] using hiH
  have hiLog := log_div_interval hx
  have hiInv : IntervalIntegrable (fun t : ℝ => 1 / t) volume 1 x := by
    simpa only [one_div] using
      (ContinuousOn.intervalIntegrable (show ContinuousOn (fun t : ℝ => t⁻¹) (uIcc 1 x) by
        rw [uIcc_of_le hx]; exact inv_continuousOn))
  have ha := abel (fun n => (n : ℝ)⁻¹) (by simp) hx
    (f := Real.log) (f' := fun t => 1 / t)
    (fun t ht => by simpa only [one_div] using
      Real.hasDerivAt_log (ne_of_gt (zero_lt_one.trans_le ht.1)))
    (by simpa only [one_div] using inv_continuousOn.integrableOn_Icc)
  have hs :
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Real.log n * (n : ℝ)⁻¹) = J x := by
    rw [J, prefixSum_eq_Ioc (fun n => Real.log n / n) (by simp)]
    simp only [div_eq_mul_inv]
  have hh : (∫ t in (1 : ℝ)..x, H t / t) = Real.log x * H x - J x := by
    rw [hs] at ha
    have he : (fun t : ℝ => 1 / t * prefixSum (fun n => (n : ℝ)⁻¹) t) =
        fun t => H t / t := by funext t; simp [H, div_eq_mul_inv, mul_comm]
    rw [he] at ha
    change J x = Real.log x * H x - ∫ t in (1 : ℝ)..x, H t / t at ha
    linarith
  have he : epsilonDensity = fun t => H t / t - Real.log t / t - gamma * (1 / t) := by
    funext t
    dsimp [epsilonDensity, epsilon]
    ring
  have hi : (∫ t in (1 : ℝ)..x, epsilonDensity t) =
      Real.log x * H x - J x - (Real.log x) ^ 2 / 2 - gamma * Real.log x := by
    rw [he, intervalIntegral.integral_sub (hiH'.sub hiLog) (hiInv.const_mul gamma),
      intervalIntegral.integral_sub hiH' hiLog, intervalIntegral.integral_const_mul,
      hh, log_div_integral hx, inv_integral hx]
  rw [epsilon]
  linarith

private lemma J_finite_factorial {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, eta t / t ^ 2) =
      1 - eta x / x + J x - (Real.log x) ^ 2 / 2 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hd (t : ℝ) (ht : t ∈ Icc (1 : ℝ) x) :
      HasDerivAt (fun u : ℝ => u⁻¹) (-(1 / t ^ 2)) t := by
    have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans_le ht.1)
    convert (hasDerivAt_id t).inv ht0 using 1
    · ext u
      simp [id_eq]
    · simp [id_eq]
      field_simp [ht0]
  have hci : ContinuousOn (fun t : ℝ => -(1 / t ^ 2)) (Icc (1 : ℝ) x) := by
    exact (continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero _ (ne_of_gt (zero_lt_one.trans_le ht.1)))).neg
  have ha := abel (fun n => Real.log n) (by simp) hx hd hci.integrableOn_Icc
  have hs :
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (n : ℝ)⁻¹ * Real.log n) = J x := by
    rw [J, prefixSum_eq_Ioc (fun n => Real.log n / n) (by simp)]
    simp [div_eq_mul_inv, mul_comm]
  have hiP := prefixSum_mul_interval (fun n => Real.log n) hx
    (g := fun t => 1 / t ^ 2)
    (continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero _ (ne_of_gt (zero_lt_one.trans_le ht.1))))
  have hiP' : IntervalIntegrable
      (fun t => Real.log (⌊t⌋₊.factorial : ℝ) / t ^ 2) volume 1 x := by
    simpa only [log_prefixSum, div_eq_mul_inv, one_mul, mul_comm, mul_left_comm,
      mul_assoc] using hiP
  have hiLog := log_div_interval hx
  have hiInv : IntervalIntegrable (fun t : ℝ => 1 / t) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx]
    exact continuousOn_const.div continuousOn_id
      (fun t ht => ne_of_gt (zero_lt_one.trans_le ht.1))
  have hp : (∫ t in (1 : ℝ)..x, Real.log (⌊t⌋₊.factorial : ℝ) / t ^ 2) =
      J x - Real.log (⌊x⌋₊.factorial : ℝ) / x := by
    rw [hs, log_prefixSum] at ha
    have he : (fun t : ℝ => -(1 / t ^ 2) * prefixSum (fun n => Real.log n) t) =
        fun t => -(Real.log (⌊t⌋₊.factorial : ℝ) / t ^ 2) := by
      funext t
      rw [log_prefixSum]
      ring
    rw [he, intervalIntegral.integral_neg] at ha
    simp only [div_eq_mul_inv, mul_comm] at ha ⊢
    linarith
  have he : (∫ t in (1 : ℝ)..x, eta t / t ^ 2) =
      (∫ t in (1 : ℝ)..x, Real.log (⌊t⌋₊.factorial : ℝ) / t ^ 2) -
        (∫ t in (1 : ℝ)..x, Real.log t / t) + ∫ t in (1 : ℝ)..x, 1 / t := by
    rw [← intervalIntegral.integral_sub hiP' hiLog,
      ← intervalIntegral.integral_add (hiP'.sub hiLog) hiInv]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx] at ht
    change eta t / t ^ 2 =
      Real.log (⌊t⌋₊.factorial : ℝ) / t ^ 2 - Real.log t / t + 1 / t
    rw [eta_formula]
    have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans_le ht.1)
    field_simp
    <;> ring
  rw [he, hp, log_div_integral hx, inv_integral hx, eta_formula]
  field_simp [hx0.ne']
  <;> ring

private lemma quotient_limits :
    Tendsto (fun x : ℝ => eta x / x) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => Real.log x * epsilon x) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have henv : Tendsto (fun x : ℝ => (1 + Real.log x) / x) atTop (𝓝 0) := by
    convert tendsto_inv_atTop_zero.add hlog using 1 <;> simp [add_div, one_div]
  constructor
  · apply squeeze_zero_norm' _ henv
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (zero_lt_one.trans_le hx)]
    exact div_le_div_of_nonneg_right (eta_bound hx) (by linarith)
  · apply squeeze_zero_norm' _ hlog
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.log_nonneg hx)]
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left (epsilon_bound hx) (Real.log_nonneg hx)

/-- Identification of the actual factorial constant, rather than an assumed
constant equating two asymptotic expansions. -/
private lemma constant_identity :
    ceta - 1 = -(∫ t in Ioi (1 : ℝ), epsilonDensity t) := by
  have hη := intervalIntegral_tendsto_integral_Ioi 1 eta_density_integrable tendsto_id
  have hε := intervalIntegral_tendsto_integral_Ioi 1 epsilonDensity_integrable tendsto_id
  have hf : ∀ᶠ x : ℝ in atTop,
      (∫ t in (1 : ℝ)..x, eta t / t ^ 2) +
        (∫ t in (1 : ℝ)..x, epsilonDensity t) =
          1 - eta x / x + Real.log x * epsilon x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [J_finite_factorial hx, J_finite_harmonic hx]
    ring
  have heq : ∀ᶠ x : ℝ in atTop,
      (∫ t in (1 : ℝ)..x, eta t / t ^ 2) +
          (∫ t in (1 : ℝ)..x, epsilonDensity t) =
        1 - eta x / x + Real.log x * epsilon x := by
    filter_upwards [hf] with x hx
    exact hx
  have hsum : Tendsto
      (fun x : ℝ =>
        (∫ t in (1 : ℝ)..x, eta t / t ^ 2) +
          (∫ t in (1 : ℝ)..x, epsilonDensity t)) atTop
      (𝓝 (ceta + ∫ t in Ioi (1 : ℝ), epsilonDensity t)) := by
    simpa only [id_eq, ceta] using hη.add hε
  have htarget := hsum.congr' heq
  have hlimit : Tendsto (fun x : ℝ => 1 - eta x / x + Real.log x * epsilon x)
      atTop (𝓝 (1 - 0 + 0)) := by
    simpa only [sub_zero, add_zero] using
      ((tendsto_const_nhds.sub quotient_limits.1).add quotient_limits.2)
  have he := tendsto_nhds_unique htarget hlimit
  change ceta + (∫ t in Ioi (1 : ℝ), epsilonDensity t) = 1 - 0 + 0 at he
  linarith

private lemma epsilon_split {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in Ioi (1 : ℝ), epsilonDensity t) =
      (∫ t in (1 : ℝ)..x, epsilonDensity t) + T_epsilon x := by
  have hi := epsilonDensity_integrable
  rw [← Ioc_union_Ioi_eq_Ioi hx]
  rw [setIntegral_union (Set.disjoint_left.mpr (by
    intro y hy hy'; exact (not_lt_of_ge hy.2) hy')) measurableSet_Ioi
      (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi hx))]
  rw [intervalIntegral.integral_of_le hx]
  rfl

private lemma J_tail_identity {x : ℝ} (hx : 1 ≤ x) :
    J x = (Real.log x) ^ 2 / 2 + (ceta - 1) +
      Real.log x * epsilon x + T_epsilon x := by
  have hj := J_finite_harmonic hx
  have hc := constant_identity
  rw [epsilon_split hx] at hc
  linarith

private lemma slope_identity {x : ℝ} (hx : 1 ≤ x) :
    slope x = (gamma + Real.log x) * epsilon x + 2 * T_epsilon x := by
  rw [slope, J_tail_identity hx, epsilon, alpha]
  ring

private lemma slope_bound {x : ℝ} (hx : 1 ≤ x) :
    |slope x| ≤ (gamma + 2 + Real.log x) / x := by
  have hc : 0 ≤ gamma + Real.log x := add_nonneg gamma_pos.le (Real.log_nonneg hx)
  rw [slope_identity hx]
  calc
    _ ≤ |(gamma + Real.log x) * epsilon x| + |2 * T_epsilon x| := abs_add_le _ _
    _ = (gamma + Real.log x) * |epsilon x| + 2 * |T_epsilon x| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (gamma + Real.log x) * (1 / x) + 2 * (1 / x) := by
      gcongr
      · exact epsilon_bound hx
      · exact T_epsilon_bound hx
    _ = _ := by ring

private lemma global_G_bound {x : ℝ} (hx : 1 ≤ x) :
    |G x| ≤ (gamma + 2) * Real.log x + (Real.log x) ^ 2 / 2 := by
  let b : ℝ → ℝ := fun t => (gamma + 2 + Real.log t) / t
  have hb : IntervalIntegrable b volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx]
    exact (continuousOn_const.add log_continuousOn).div continuousOn_id
      (fun t ht => ne_of_gt (zero_lt_one.trans_le ht.1))
  have hbd : ∀ t ∈ uIcc (1 : ℝ) x,
      HasDerivAt (fun u : ℝ => (gamma + 2) * Real.log u + (Real.log u) ^ 2 / 2)
        (b t) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 := ne_of_gt (zero_lt_one.trans_le ht.1)
    convert ((Real.hasDerivAt_log ht0).const_mul (gamma + 2)).add
      (((Real.hasDerivAt_log ht0).pow 2).div_const 2) using 1 <;> dsimp [b] <;> ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hbd hb
  simp only [Real.log_one, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_div, add_zero, sub_zero] at he
  rw [G_eq_integral hx]
  calc
    _ ≤ ∫ t in (1 : ℝ)..x, b t := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_of_norm_le (f := slope) (g := b) hx
          (by
            filter_upwards with t ht
            simpa only [Real.norm_eq_abs] using slope_bound ht.1.le) hb)
    _ = _ := he

lemma slope_measurable : Measurable slope := by
  exact (((measurable_const.sub Real.measurable_log).mul (prefixSum_measurable _)).add
    ((prefixSum_measurable _).const_mul 2)).sub measurable_const

/-- The countable interval FTC identifies the derivative of the literal G.
The endpoint one is excluded only as a volume-null singleton; no pointwise
ordinary derivative at all integer cutoffs is asserted. -/
private lemma G_hasDerivAt_ae :
    ∀ᵐ x : ℝ ∂volume.restrict (Ici (1 : ℝ)), HasDerivAt G (slope x) x := by
  have hFTC (n : ℕ) :
      ∀ᵐ x : ℝ, x ∈ Icc (1 : ℝ) ((n : ℝ) + 2) →
        HasDerivAt (fun y => ∫ t in (1 : ℝ)..y, slope t) (slope x) x := by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    filter_upwards [(slope_interval hn).ae_hasDerivAt_integral] with x hx hxn
    exact hx (by simpa only [uIcc_of_le hn] using hxn) 1
      (by rw [uIcc_of_le hn]; exact ⟨le_rfl, hn⟩)
  have hall : ∀ᵐ x : ℝ, ∀ n : ℕ, x ∈ Icc (1 : ℝ) ((n : ℝ) + 2) →
      HasDerivAt (fun y => ∫ t in (1 : ℝ)..y, slope t) (slope x) x :=
    ae_all_iff.mpr hFTC
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by simp [ae_iff, measure_singleton]
  apply (ae_restrict_iff' measurableSet_Ici).mpr
  filter_upwards [hall, hne] with x hx hxne hx1
  have hxgt : (1 : ℝ) < x := lt_of_le_of_ne hx1 (Ne.symm hxne)
  obtain ⟨n, hn⟩ := exists_nat_gt x
  have hxI : x ∈ Icc (1 : ℝ) ((n : ℝ) + 2) := ⟨hx1, by linarith⟩
  apply (hx n hxI).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hxgt] with y hy
  exact G_eq_integral hy.le

/-- The complete arithmetic compensation is locally absolutely continuous,
vanishes at one, and obeys the full global logarithmic bound. Its actual
almost-everywhere derivative on the complete half-line equals slope and obeys
the stated density bound. No supplier assumption replaces the finite
identity, the harmonic tail, or the derivative identification. -/
theorem compensation :
    G 1 = 0 ∧
    ContinuousOn G (Ici (1 : ℝ)) ∧
    (∀ X : ℝ, 1 ≤ X → AbsolutelyContinuousOnInterval G 1 X) ∧
    (∀ x : ℝ, 1 ≤ x → |G x| ≤
      (gamma + 2) * Real.log x + (Real.log x) ^ 2 / 2) ∧
    (∀ t : ℝ, 0 ≤ t → |G (Real.exp t)| ≤ (gamma + 2) * t + t ^ 2 / 2) ∧
    (∀ x : ℝ, 1 ≤ x → slope x =
      (gamma + Real.log x) * epsilon x + 2 * T_epsilon x ∧
      |slope x| ≤ (gamma + 2 + Real.log x) / x) ∧
    (∀ᵐ x : ℝ ∂volume.restrict (Ici (1 : ℝ)),
      HasDerivAt G (slope x) x ∧
      |deriv G x| ≤ (gamma + 2 + Real.log x) / x) := by
  refine ⟨?_, G_continuous, fun _ hX => G_ac hX, fun _ hx => global_G_bound hx,
    ?_, ?_, ?_⟩
  · rw [G_eq_integral (by norm_num : (1 : ℝ) ≤ 1)]
    simp
  · intro t ht
    simpa only [Real.log_exp] using global_G_bound (Real.one_le_exp_iff.mpr ht)
  · intro x hx
    exact ⟨slope_identity hx, slope_bound hx⟩
  · filter_upwards [G_hasDerivAt_ae, ae_restrict_mem measurableSet_Ici] with x hd hx
    exact ⟨hd, by rw [hd.deriv]; exact slope_bound hx⟩

end D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
