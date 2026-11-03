/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real correlation and resolvent identities for the complete actual kernel. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentMixture
import Mathlib.Algebra.Group.ForwardDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open D5.S3.Arith.Robin.CompleteMertensPeak

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate

variable {I : Type u} [Fintype I]

def correlation (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℝ :=
  (∫ v : ℝ, star («prefix» x a (v + t)) * «prefix» x a v).re

def continuum (D : ℝ) (x : I → ℝ) (a : I → ℂ) : ℝ :=
  2 * ∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * correlation x a t

/-- Real-space resolvent on the complete correlation support. The finite
reconstruction realizes fullR by this convolution. The actual causal-square
and translated-polarization proof below supplies positivity and shift control. -/
def S (D : ℝ) (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℝ :=
  (1 / 4) * ∫ s in Icc (-D) D, Real.exp (-|t - s| / 2) * correlation x a s

def W (D : ℝ) (x : I → ℝ) (a : I → ℂ) : ℝ := S D x a 0
def Z (D : ℝ) (x : I → ℝ) (a : I → ℂ) : ℝ := 4 * M D * S D x a D

/-- All original V terms, including the inclusive upper-cutoff boundary. -/
def V (D : ℝ) (x : I → ℝ) (a : I → ℂ) : ℝ :=
  2 * (∑ n ∈ primes D, ArithmeticFunction.vonMangoldt n / Real.sqrt n * S D x a (Real.log n)) -
    2 * (∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * S D x a t) - b D / 2 * Z D x a

/-- The explicit finite expression in the original Pro answer. Its
identification with an independently defined signed-J integral is NOT
asserted by this source payload. -/
def signedJExpression (D : ℝ) (x : I → ℝ) (a : I → ℂ) : ℝ :=
  -2 * Real.eulerMascheroniConstant * (energy x a - W D x a) -
    primeQuadratic D x a + continuum D x a + V D x a

lemma correlation_continuous (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) : Continuous (correlation x a) := by
  have he (s : ℝ) : correlation x a s =
      -(quadratic x a (fun t => max (t - s) 0)).re := by
    have h := congrArg Complex.re (shifted_hinge_prefix_energy x a ha s).2.2.1
    dsimp [correlation, quadratic] at *
    linarith only [h]
  have heq : correlation x a =
      fun s => -(quadratic x a (fun t => max (t - s) 0)).re := funext he
  rw [heq]
  dsimp [quadratic]
  fun_prop

/-- Only the REAL correlation is even; no symmetry of an auxiliary spectral
measure is asserted. This is direct translation of the actual complex prefix. -/
private lemma correlation_neg (x : I → ℝ) (a : I → ℂ) (s : ℝ) :
    correlation x a (-s) = correlation x a s := by
  let f : ℝ → ℂ := fun v =>
    star («prefix» x a (v - s)) * «prefix» x a v
  have ht := integral_add_right_eq_self (μ := (volume : Measure ℝ)) f s
  have he (v : ℝ) : f (v + s) =
      star (star («prefix» x a (v + s)) * «prefix» x a v) := by
    dsimp [f]
    rw [show v + s - s = v by ring]
    change star («prefix» x a v) * «prefix» x a (v + s) =
      star (star («prefix» x a (v + s)) * «prefix» x a v)
    rw [star_mul, star_star]
  simp_rw [he] at ht
  have hc : (∫ v : ℝ, star (star («prefix» x a (v + s)) * «prefix» x a v)) =
      star (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v) := by
    simpa only [Complex.star_def] using integral_conj
      (f := fun v : ℝ => star («prefix» x a (v + s)) * «prefix» x a v)
  rw [hc] at ht
  have hr := congrArg Complex.re ht
  simpa only [correlation, f, sub_eq_add_neg, Complex.star_def, Complex.conj_re] using hr.symm

def pairedResolvent (t s : ℝ) : ℝ :=
  Real.exp (-|t - s| / 2) + Real.exp (-|t + s| / 2)

private lemma pairedResolvent_comm (t s : ℝ) :
    pairedResolvent t s = pairedResolvent s t := by
  dsimp [pairedResolvent]
  rw [abs_sub_comm t s, add_comm t s]

/-- Split the actual convolution at zero, with the actual real correlation.
All functions in this finite-window change of variables are continuous. -/
lemma S_half_window (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0) (t : ℝ) :
    S D x a t = (1 / 4) *
      ∫ s in Icc (0 : ℝ) D, pairedResolvent t s * correlation x a s := by
  let f : ℝ → ℝ := fun s => Real.exp (-|t - s| / 2) * correlation x a s
  have hf : Continuous f := by
    exact (by fun_prop : Continuous (fun s : ℝ => Real.exp (-|t - s| / 2))).mul
      (correlation_continuous x a ha)
  have hw (l r : ℝ) (hlr : l ≤ r) :
      (∫ s in Icc l r, f s) = ∫ s in l..r, f s := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hlr]
  have hn : (∫ s in (-D)..0, f s) = ∫ s in (0 : ℝ)..D, f (-s) := by
    simpa only [neg_zero, neg_neg] using
      (intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := D)).symm
  have he (s : ℝ) : f (-s) + f s =
      pairedResolvent t s * correlation x a s := by
    dsimp [f, pairedResolvent]
    rw [correlation_neg, sub_neg_eq_add]
    ring
  dsimp only [S]
  congr 1
  rw [hw (-D) D (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (-D) 0) (hf.intervalIntegrable 0 D), hn]
  have hadd := intervalIntegral.integral_add (μ := (volume : Measure ℝ))
    ((hf.comp continuous_neg).intervalIntegrable 0 D) (hf.intervalIntegrable 0 D)
  dsimp only [Function.comp_def] at hadd
  rw [← hadd]
  simp_rw [he]
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hD]

private lemma fullR_cumulative (t : ℝ) (ht : 0 ≤ t) :
    fullR t = Real.exp (t / 2) * (1 + Real.eulerMascheroniConstant - t + F t) -
      Real.exp (-t / 2) * (Chebyshev.psi (Real.exp t) + Real.log (2 * Real.pi)) := by
  have he : Real.exp (-t / 2) * Real.exp t = Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [fullR, abs_of_nonneg ht, U, ← F_eq_Ioc, Real.log_exp]
  calc
    _ = (Real.exp (-t / 2) * Real.exp t) *
        (1 + Real.eulerMascheroniConstant - t + F t) -
      Real.exp (-t / 2) * (Chebyshev.psi (Real.exp t) + Real.log (2 * Real.pi)) := by ring
    _ = _ := by rw [he]

/-- Ordinary integration of the growing exponential against the reflected
resolvent pair. The split is at t itself, not at prime-power entry points. -/
private lemma pairedResolvent_exp_integral (D t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) :
    (∫ s in Icc (0 : ℝ) D, Real.exp (s / 2) * pairedResolvent t s) =
      Real.exp (t / 2) * (D - t + 1) + (D - 1) * Real.exp (-t / 2) := by
  let f : ℝ → ℝ := fun s => Real.exp (s / 2) * pairedResolvent t s
  have hf : Continuous f := by dsimp [f, pairedResolvent]; fun_prop
  have hl (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :
      f s = Real.exp (-t / 2) * Real.exp s + Real.exp (-t / 2) := by
    dsimp [f, pairedResolvent]
    rw [abs_of_nonneg (by linarith [hs.2] : 0 ≤ t - s),
      abs_of_nonneg (by linarith [ht.1, hs.1] : 0 ≤ t + s), mul_add,
      ← Real.exp_add, ← Real.exp_add]
    have h1 : s / 2 + -(t - s) / 2 = -t / 2 + s := by ring
    have h2 : s / 2 + -(t + s) / 2 = -t / 2 := by ring
    rw [h1, h2, Real.exp_add]
  have hr (s : ℝ) (hs : s ∈ Icc t D) :
      f s = Real.exp (t / 2) + Real.exp (-t / 2) := by
    dsimp [f, pairedResolvent]
    rw [abs_of_nonpos (by linarith [hs.1] : t - s ≤ 0),
      abs_of_nonneg (by linarith [ht.1, hs.1] : 0 ≤ t + s), mul_add,
      ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  have hli : (∫ s in (0 : ℝ)..t, f s) =
      Real.exp (-t / 2) * (Real.exp t - 1) + t * Real.exp (-t / 2) := by
    calc
      _ = ∫ s in (0 : ℝ)..t,
          Real.exp (-t / 2) * Real.exp s + Real.exp (-t / 2) := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact hl s (by simpa only [uIcc_of_le ht.1] using hs)
      _ = _ := by
        rw [intervalIntegral.integral_add
          ((Real.continuous_exp.const_mul _).intervalIntegrable 0 t)
          (continuous_const.intervalIntegrable 0 t), intervalIntegral.integral_const_mul,
          integral_exp, intervalIntegral.integral_const]
        simp
  have hri : (∫ s in t..D, f s) =
      (D - t) * (Real.exp (t / 2) + Real.exp (-t / 2)) := by
    calc
      _ = ∫ s in t..D, Real.exp (t / 2) + Real.exp (-t / 2) := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact hr s (by simpa only [uIcc_of_le ht.2] using hs)
      _ = _ := by simp <;> ring
  have he : Real.exp (-t / 2) * Real.exp t = Real.exp (t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (ht.1.trans ht.2),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable 0 t) (hf.intervalIntegrable t D), hli, hri]
  nlinarith only [he]

private lemma paired_weight (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (hn : 2 ≤ n) :
    weight n * pairedResolvent t (Real.log n) =
      ArithmeticFunction.vonMangoldt n / n *
        (Real.exp (t / 2) + Real.exp (-t / 2)) +
      if Real.log (n : ℝ) ≤ t then
        ArithmeticFunction.vonMangoldt n * Real.exp (-t / 2) -
          ArithmeticFunction.vonMangoldt n / n * Real.exp (t / 2) else 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hexp : Real.exp (-Real.log (n : ℝ)) = (n : ℝ)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hn0]
  have he (r : ℝ) : Real.exp (-Real.log (n : ℝ) + r) = (n : ℝ)⁻¹ * Real.exp r := by
    rw [Real.exp_add, hexp]
  dsimp only [weight, pairedResolvent]
  rw [abs_of_nonneg (by linarith : 0 ≤ t + Real.log (n : ℝ))]
  by_cases h : Real.log (n : ℝ) ≤ t
  · rw [if_pos h, abs_of_nonneg (by linarith : 0 ≤ t - Real.log (n : ℝ))]
    have h1 : -Real.log (n : ℝ) / 2 + -(t - Real.log n) / 2 = -t / 2 := by ring
    have h2 : -Real.log (n : ℝ) / 2 + -(t + Real.log n) / 2 =
        -Real.log n + -t / 2 := by ring
    calc
      _ = ArithmeticFunction.vonMangoldt n *
          (Real.exp (-Real.log (n : ℝ) / 2 + -(t - Real.log n) / 2) +
            Real.exp (-Real.log (n : ℝ) / 2 + -(t + Real.log n) / 2)) := by
        rw [Real.exp_add, Real.exp_add]; ring
      _ = _ := by rw [h1, h2, he]; ring
  · rw [if_neg h, abs_of_nonpos (by linarith : t - Real.log (n : ℝ) ≤ 0)]
    have h1 : -Real.log (n : ℝ) / 2 + -(-(t - Real.log n)) / 2 =
        -Real.log n + t / 2 := by ring
    have h2 : -Real.log (n : ℝ) / 2 + -(t + Real.log n) / 2 =
        -Real.log n + -t / 2 := by ring
    calc
      _ = ArithmeticFunction.vonMangoldt n *
          (Real.exp (-Real.log (n : ℝ) / 2 + -(-(t - Real.log n)) / 2) +
            Real.exp (-Real.log (n : ℝ) / 2 + -(t + Real.log n) / 2)) := by
        rw [Real.exp_add, Real.exp_add]; ring
      _ = _ := by rw [h1, h2, he, he]; ring

/-- Exact finite reflected-resolvent realization of the ACTUAL fullR.
The upper b(D) term survives the reconstruction, including equality at
every prime-power entry. No differential or spectral bridge is assumed. -/
private lemma fullR_resolvent_reconstruction (D t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) :
    fullR t = -d0 * Real.exp (-t / 2) -
      (∑ n ∈ primes D, weight n * pairedResolvent t (Real.log n)) +
      (∫ s in Icc (0 : ℝ) D, Real.exp (s / 2) * pairedResolvent t s) +
        b D * M D * pairedResolvent t D := by
  classical
  have hs : (∑ n ∈ primes D, weight n * pairedResolvent t (Real.log n)) =
      F D * (Real.exp (t / 2) + Real.exp (-t / 2)) +
        Chebyshev.psi (Real.exp t) * Real.exp (-t / 2) - F t * Real.exp (t / 2) := by
    rw [Finset.sum_congr (s₁ := primes D) rfl (fun n hn =>
      paired_weight t ht.1 n (Finset.mem_Icc.mp hn).1)]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_filter,
      indices D t ht.2, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      cumulative]
    dsimp only [F]
    ring
  have hb : M D * pairedResolvent t D = Real.exp (t / 2) + Real.exp (-t / 2) := by
    dsimp [M, pairedResolvent]
    rw [abs_of_nonpos (by linarith [ht.2] : t - D ≤ 0),
      abs_of_nonneg (by linarith [ht.1, ht.2] : 0 ≤ t + D), mul_add,
      ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  rw [fullR_cumulative t ht.1, hs, pairedResolvent_exp_integral D t ht]
  rw [mul_assoc (b D) (M D), hb]
  dsimp [b, d0]
  ring

/-- Integrate the explicit reconstruction against the ORIGINAL correlation.
Compact-square continuity supplies Fubini. In particular this is not an
assumed analytic supplier and does not redefine fullR by a Green equation. -/
theorem actual_fullR_resolvent_identity (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0) :
    -(1 / 2) * (∫ t in Icc (0 : ℝ) D, fullR t * correlation x a t) =
      d0 * W D x a + V D x a := by
  classical
  let c : ℝ → ℝ := correlation x a
  let L : ℝ → ℝ → ℝ := pairedResolvent
  let f : ℝ → ℝ → ℝ := fun t s => Real.exp (s / 2) * L t s * c t
  have hc : Continuous c := correlation_continuous x a ha
  have hkernel (s : ℝ) : Continuous (fun t : ℝ => L t s * c t) := by
    exact (by dsimp [L, pairedResolvent]; fun_prop : Continuous (fun t : ℝ => L t s)).mul hc
  have hjoint : Continuous (Function.uncurry f) := by
    dsimp [Function.uncurry, f, L, pairedResolvent]
    exact (by fun_prop : Continuous (fun z : ℝ × ℝ =>
      Real.exp (z.2 / 2) *
        (Real.exp (-|z.1 - z.2| / 2) + Real.exp (-|z.1 + z.2| / 2)))).mul
      (hc.comp continuous_fst)
  have hprod : Integrable (Function.uncurry f)
      ((volume.restrict (Icc (0 : ℝ) D)).prod (volume.restrict (Icc (0 : ℝ) D))) := by
    rw [Measure.prod_restrict]
    exact hjoint.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hfour (s : ℝ) : (∫ t in Icc (0 : ℝ) D, L t s * c t) = 4 * S D x a s := by
    have h := S_half_window D hD x a ha s
    have he : (∫ t in Icc (0 : ℝ) D, L t s * c t) =
        ∫ t in Icc (0 : ℝ) D, pairedResolvent s t * correlation x a t := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t _
      dsimp [L, c]
      rw [pairedResolvent_comm]
    rw [he]
    linarith only [h]
  have hzero : (∫ t in Icc (0 : ℝ) D, Real.exp (-t / 2) * c t) = 2 * W D x a := by
    have h := hfour 0
    have he : (∫ t in Icc (0 : ℝ) D, L t 0 * c t) =
        2 * ∫ t in Icc (0 : ℝ) D, Real.exp (-t / 2) * c t := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp [L, pairedResolvent]
      rw [sub_zero, add_zero, abs_of_nonneg ht.1]
      ring
    rw [he] at h
    change _ = 2 * S D x a 0
    linarith only [h]
  have hprime : (∫ t in Icc (0 : ℝ) D,
      (∑ n ∈ primes D, weight n * L t (Real.log n)) * c t) =
        4 * ∑ n ∈ primes D, weight n * S D x a (Real.log n) := by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ (fun (n : ℕ) _ =>
      (((hkernel (Real.log n)).const_mul (weight n)).congr
        (fun t => by ring)).integrableOn_Icc)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [show (fun t : ℝ => weight n * L t (Real.log n) * c t) =
      (fun t => weight n * (L t (Real.log n) * c t)) by ext t; ring,
      integral_const_mul, hfour]
    ring
  have hcont : (∫ t in Icc (0 : ℝ) D,
      (∫ s in Icc (0 : ℝ) D, Real.exp (s / 2) * L t s) * c t) =
        4 * ∫ s in Icc (0 : ℝ) D, Real.exp (s / 2) * S D x a s := by
    calc
      _ = ∫ t in Icc (0 : ℝ) D, ∫ s in Icc (0 : ℝ) D, f t s := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t _
        dsimp [f]
        rw [integral_mul_const]
      _ = ∫ s in Icc (0 : ℝ) D, ∫ t in Icc (0 : ℝ) D, f t s :=
        integral_integral_swap hprod
      _ = _ := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Icc
        intro s _
        dsimp [f]
        simp_rw [mul_assoc]
        rw [integral_const_mul, hfour]
        ring
  have hboundary : (∫ t in Icc (0 : ℝ) D, b D * M D * L t D * c t) =
      b D * Z D x a := by
    simp_rw [show ∀ t : ℝ, b D * M D * L t D * c t =
      (b D * M D) * (L t D * c t) by intro t; ring]
    rw [integral_const_mul, hfour]
    dsimp [Z]
    ring
  have hsplit : (∫ t in Icc (0 : ℝ) D, fullR t * c t) =
      -d0 * (2 * W D x a) -
        4 * (∑ n ∈ primes D, weight n * S D x a (Real.log n)) +
        4 * (∫ s in Icc (0 : ℝ) D, Real.exp (s / 2) * S D x a s) +
          b D * Z D x a := by
    have hi0 : IntegrableOn (fun t => -d0 * Real.exp (-t / 2) * c t) (Icc 0 D) :=
      ((by fun_prop : Continuous (fun t : ℝ => -d0 * Real.exp (-t / 2))).mul hc).integrableOn_Icc
    have hip : IntegrableOn (fun t =>
        (∑ n ∈ primes D, weight n * L t (Real.log n)) * c t) (Icc 0 D) := by
      apply Continuous.integrableOn_Icc
      exact (continuous_finsetSum _ (fun n _ => by dsimp [L, pairedResolvent]; fun_prop)).mul hc
    have hic : IntegrableOn (fun t =>
        (∫ s in Icc (0 : ℝ) D, Real.exp (s / 2) * L t s) * c t) (Icc 0 D) := by
      have h := hprod.integral_prod_left
      apply h.congr
      filter_upwards [] with t
      dsimp only [Function.uncurry, f]
      rw [integral_mul_const]
    have hib : IntegrableOn (fun t => b D * M D * L t D * c t) (Icc 0 D) := by
      have hbcont : Continuous (fun t => b D * M D * L t D * c t) :=
        ((hkernel D).const_mul (b D * M D)).congr (fun t => by ring)
      exact hbcont.integrableOn_Icc
    calc
      _ = ∫ t in Icc (0 : ℝ) D,
          -d0 * Real.exp (-t / 2) * c t -
            (∑ n ∈ primes D, weight n * L t (Real.log n)) * c t +
            (∫ s in Icc (0 : ℝ) D, Real.exp (s / 2) * L t s) * c t +
              b D * M D * L t D * c t := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        dsimp only
        rw [fullR_resolvent_reconstruction D t ht]
        dsimp [L]
        ring
      _ = _ := by
        have ha3 := integral_add ((hi0.sub hip).add hic) hib
        have ha2 := integral_add (hi0.sub hip) hic
        have hs1 := integral_sub hi0 hip
        simp only [Pi.add_apply, Pi.sub_apply] at ha3 ha2 hs1
        rw [ha3, ha2, hs1, hprime, hcont, hboundary]
        rw [show (fun t : ℝ => -d0 * Real.exp (-t / 2) * c t) =
          (fun t => -d0 * (Real.exp (-t / 2) * c t)) by ext t; ring,
          integral_const_mul, hzero]
  have hweights : (∑ n ∈ primes D, weight n * S D x a (Real.log n)) =
      ∑ n ∈ primes D, ArithmeticFunction.vonMangoldt n / Real.sqrt n * S D x a (Real.log n) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [weight_eq_sqrt n (Finset.mem_Icc.mp hn).1]
  change -(1 / 2) * (∫ t in Icc (0 : ℝ) D, fullR t * c t) = _
  rw [hsplit, hweights]
  dsimp [V]
  ring

/-- Normalization check against the retained exact exponential prefix
identity: the present W is E-Re Q_exp(1/2), without any spectral premise. -/
private lemma W_eq_exponential_deficit (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) :
    W D x a = energy x a -
      (quadratic x a (fun t => Real.exp (-|t| / 2))).re := by
  have hdiam (i j : I) : |x i - x j| ≤ D := by
    apply abs_le.mpr
    constructor <;> linarith [(hx i).1, (hx i).2, (hx j).1, (hx j).2]
  have h := exponential_prefix_energy x a ha (1 / 2) D (by norm_num) hD hdiam
  have hi := h.2.2.2.1
  have hc : (quadratic x a (fun t => Real.exp (-(1 / 2) * |t|))) =
      ((2 * (1 / 2 : ℝ) * energy x a : ℝ) : ℂ) -
        (((1 / 2 : ℝ) ^ 2 : ℝ) : ℂ) *
          (∫ s in Icc (-D) D, (Real.exp (-(1 / 2) * |s|) : ℂ) *
            (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v)) := by
    simpa only [quadratic, energy, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_ofNat] using h.2.2.2.2
  have he := congrArg Complex.re hc
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at he
  have hre := integral_re hi
  simp only [RCLike.re_to_complex] at hre
  rw [← hre] at he
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at he
  have hh (s : ℝ) : -(1 / 2 : ℝ) * |s| = -|s| / 2 := by ring
  simp_rw [hh] at he
  change (quadratic x a (fun t => Real.exp (-|t| / 2))).re =
    2 * (1 / 2 : ℝ) * energy x a - (1 / 2 : ℝ) ^ 2 *
      (∫ s in Icc (-D) D, Real.exp (-|s| / 2) * correlation x a s) at he
  have hz : W D x a = (1 / 4) *
      ∫ s in Icc (-D) D, Real.exp (-|s| / 2) * correlation x a s := by
    dsimp [W, S]
    simp only [zero_sub, abs_neg]
  linarith only [he, hz]

private lemma W_moment_upper (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    W D x a ≤ (D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))) * energy x a / 4 := by
  have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
  have h := D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.moment_exponential_prefix_coercivity
    D hD q hq (1 / 2) (by norm_num) x a hx hm
  rw [W_eq_exponential_deficit D hD.le x a hx ha]
  have hh (t : ℝ) : -(1 / 2 : ℝ) * |t| = -|t| / 2 := by ring
  simp_rw [hh] at h
  dsimp only [energy, quadratic] at *
  ring_nf at h ⊢
  nlinarith only [h]

lemma original_K_split (t : ℝ) : ActualKernelLocalPositivity.K t = P t + fullR t := by
  dsimp [ActualKernelLocalPositivity.K, P, fullR]
  ring

lemma actual_fullR_correlation (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) :
    (quadratic x a fullR).re = -d0 * energy x a - primeQuadratic D x a +
      continuum D x a - (1 / 2) * ∫ t in Icc (0 : ℝ) D, fullR t * correlation x a t := by
  let N : ℕ := ⌈Real.exp D⌉₊ + 1
  have hN : Real.exp D < (N : ℝ) := by
    have h := Nat.le_ceil (Real.exp D)
    dsimp [N]
    push_cast
    linarith
  have h := ActualKernelPrefixPerturbation.actual_remainder_correlation_identity
    D hD N hN x a hx ha
  have hR (t : ℝ) : ActualKernelLocalPositivity.K t -
      Real.exp (-|t| / 2) * trivialT |t| = fullR t := by
    rw [original_K_split]
    dsimp [P]
    ring
  simp_rw [hR] at h
  have hp : (∑ n ∈ primes D,
      (ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
        correlation x a (Real.log n)) =
      ∑ n ∈ primes D, ArithmeticFunction.vonMangoldt n / Real.sqrt n * correlation x a (Real.log n) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [← weight_eq_sqrt n (Finset.mem_Icc.mp hn).1]
    rfl
  change (quadratic x a fullR).re = -d0 * energy x a -
    2 * (∑ n ∈ primes D,
      (ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) * correlation x a (Real.log n)) +
      continuum D x a - (1 / 2) * ∫ t in Icc (0 : ℝ) D, fullR t * correlation x a t at h
  rw [hp] at h
  exact h

/-- Source-only intermediate balance for the ORIGINAL actual K. The fullR
correlation integral is realized as d0*W+V with its literal cutoff boundary.
The continuum and the size of V remain unpaid, so this is explicitly NOT
the requested coercivity certificate. The second conjunct pays the moment
upper bound on the actual W, using the retained exponential theorem. -/
theorem actual_kernel_moment_balance (p : PNTConstants)
    (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q) (hr : 8 ≤ (q : ℝ) / D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    ((Real.log ((q : ℝ) / D) - 1 - d0 - beta p D) * energy x a + continuum D x a +
      d0 * W D x a + V D x a ≤ (quadratic x a ActualKernelLocalPositivity.K).re) ∧
    W D x a ≤ (D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))) * energy x a / 4 := by
  have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
  have hP := complete_positive_mixture_logarithmic D hD q hq hr x a hx hm
  have hT := actual_weighted_mangoldt_translation_bound p D x a hx ha
  have hR := actual_fullR_correlation D hD.le x a hx ha
  have hV := actual_fullR_resolvent_identity D hD.le x a ha
  have hsplit : (quadratic x a ActualKernelLocalPositivity.K).re =
      (quadratic x a P).re + (quadratic x a fullR).re := by
    simp only [quadratic, original_K_split, Complex.ofReal_add, mul_add,
      Finset.sum_add_distrib, Complex.add_re]
  refine ⟨?_, W_moment_upper D hD q hq x a hx hm⟩
  linarith only [hP, hT, hR, hV, hsplit]


private lemma correlation_support (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) (t : ℝ) (ht : t ∉ Icc (-D) D) :
    correlation x a t = 0 := by
  have he (v : ℝ) : star («prefix» x a (v + t)) * «prefix» x a v = 0 := by
    by_cases hv : v ∈ Icc (0 : ℝ) D
    · have hvt : v + t ∉ Icc (0 : ℝ) D := by
        intro h
        exact ht ⟨by linarith [hv.2, h.1], by linarith [hv.1, h.2]⟩
      rw [prefix_support D x a hx ha (v + t) hvt, star_zero, zero_mul]
    · rw [prefix_support D x a hx ha v hv, mul_zero]
  simp only [correlation, he, integral_zero, Complex.zero_re]

private lemma correlation_kernel_integrable (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) (t : ℝ) :
    Integrable (fun s : ℝ => Real.exp (-|t - s| / 2) * correlation x a s) := by
  have hc : Continuous (fun s => Real.exp (-|t - s| / 2) * correlation x a s) :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (-|t - s| / 2))).mul
      (correlation_continuous x a ha)
  apply (integrableOn_iff_integrable_of_support_subset (s := Icc (-D) D) ?_).mp
    hc.integrableOn_Icc
  intro s hs
  by_contra h
  exact hs (by
    dsimp only
    rw [correlation_support D hD x a hx ha s h, mul_zero])

private lemma S_global (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) (t : ℝ) :
    S D x a t = (1 / 4) *
      ∫ s : ℝ, Real.exp (-|t - s| / 2) * correlation x a s := by
  dsimp only [S]
  congr 1
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun s hs => by
    rw [correlation_support D hD x a hx ha s hs, mul_zero])

lemma W_nonneg (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) : 0 ≤ W D x a := by
  rw [W_eq_exponential_deficit D hD x a hx ha]
  exact D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_deficit_nonneg
    D hD x a hx ha

/- Polarization of the literal causal square. The two shifted copies are
kept as a Sum index type; no grouping, ordering or nonempty premise occurs.
The argument is the real translated Cauchy inequality obtained by expanding
the squares of the sum and difference of the two causal responses. -/
private def shiftedNodes (x : I → ℝ) (t : ℝ) : I ⊕ I → ℝ
  | .inl i => x i + max t 0
  | .inr i => x i + max (-t) 0

private def shiftedCoeffs (a : I → ℂ) (r : ℝ) : I ⊕ I → ℂ
  | .inl i => a i
  | .inr i => (r : ℂ) * a i

private lemma shifted_prefix (x : I → ℝ) (a : I → ℂ) (t r v : ℝ) :
    «prefix» (shiftedNodes x t) (shiftedCoeffs a r) v =
      «prefix» x a (v - max t 0) + (r : ℂ) * «prefix» x a (v - max (-t) 0) := by
  classical
  simp only [«prefix», Fintype.sum_sum_type, shiftedNodes, shiftedCoeffs,
    Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp only [← le_sub_iff_add_le]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [← le_sub_iff_add_le]
    split_ifs <;> simp

private lemma real_cross_translation (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) (l r : ℝ) :
    Integrable (fun v : ℝ => (star («prefix» x a (v + l)) * «prefix» x a (v + r)).re) ∧
    (∫ v : ℝ, (star («prefix» x a (v + l)) * «prefix» x a (v + r)).re) =
      correlation x a (l - r) := by
  have hi := ((shifted_hinge_prefix_energy x a ha (l - r)).1.comp_add_right r).re
  have he (v : ℝ) : v + r + (l - r) = v + l := by ring
  simp_rw [he] at hi
  refine ⟨hi, ?_⟩
  have ht := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun v : ℝ => (star («prefix» x a (v + (l - r))) * «prefix» x a v).re) r
  simp_rw [he] at ht
  rw [ht]
  have hre := integral_re (shifted_hinge_prefix_energy x a ha (l - r)).1
  simpa only [RCLike.re_to_complex, correlation] using hre

private lemma shifted_correlation (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) (t r s : ℝ) (hr : r ^ 2 = 1) :
    correlation (shiftedNodes x t) (shiftedCoeffs a r) s =
      2 * correlation x a s + r *
        (correlation x a (s + t) + correlation x a (s - t)) := by
  have hdelta : max t 0 - max (-t) 0 = t := by
    rcases le_total 0 t with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -t ≤ 0)]
      ring
    · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -t)]
      ring
  have hterm (v : ℝ) :
      (star («prefix» (shiftedNodes x t) (shiftedCoeffs a r) (v + s)) *
        «prefix» (shiftedNodes x t) (shiftedCoeffs a r) v).re =
      (star («prefix» x a (v + (s - max t 0))) * «prefix» x a (v - max t 0)).re +
      r * (star («prefix» x a (v + (s - max t 0))) * «prefix» x a (v - max (-t) 0)).re +
      r * (star («prefix» x a (v + (s - max (-t) 0))) * «prefix» x a (v - max t 0)).re +
      (star («prefix» x a (v + (s - max (-t) 0))) * «prefix» x a (v - max (-t) 0)).re := by
    simp only [shifted_prefix, star_add, star_mul, Complex.star_def,
      Complex.conj_ofReal, add_mul, mul_add, Complex.add_re,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]
    simp only [show ∀ u : ℝ, v + s - u = v + (s - u) by intro u; ring]
    linear_combination ((«prefix» x a (v + (s - max (-t) 0))).re *
      («prefix» x a (v - max (-t) 0)).re +
      («prefix» x a (v + (s - max (-t) 0))).im *
      («prefix» x a (v - max (-t) 0)).im) * hr
  have h1 := real_cross_translation x a ha (s - max t 0) (-max t 0)
  have h2 := real_cross_translation x a ha (s - max t 0) (-max (-t) 0)
  have h3 := real_cross_translation x a ha (s - max (-t) 0) (-max t 0)
  have h4 := real_cross_translation x a ha (s - max (-t) 0) (-max (-t) 0)
  have ha' : ∑ i, shiftedCoeffs a r i = 0 := by
    simp [shiftedCoeffs, Fintype.sum_sum_type, ← Finset.mul_sum, ha]
  have hre := integral_re (shifted_hinge_prefix_energy
    (shiftedNodes x t) (shiftedCoeffs a r) ha' s).1
  simp only [RCLike.re_to_complex] at hre
  change (∫ v : ℝ, star («prefix» (shiftedNodes x t) (shiftedCoeffs a r) (v + s)) *
    «prefix» (shiftedNodes x t) (shiftedCoeffs a r) v).re = _
  rw [← hre]
  simp_rw [hterm, sub_eq_add_neg]
  simp only [sub_eq_add_neg] at h1 h2 h3 h4
  have ha3 := integral_add ((h1.1.add (h2.1.const_mul r)).add (h3.1.const_mul r)) h4.1
  have ha2 := integral_add (h1.1.add (h2.1.const_mul r)) (h3.1.const_mul r)
  have ha1 := integral_add h1.1 (h2.1.const_mul r)
  simp only [Pi.add_apply] at ha3 ha2 ha1
  rw [ha3, ha2, ha1, integral_const_mul, integral_const_mul]
  have he1 : s - max t 0 - -max t 0 = s := by ring
  have he2 : s - max t 0 - -max (-t) 0 = s - t := by linarith only [hdelta]
  have he3 : s - max (-t) 0 - -max t 0 = s + t := by linarith only [hdelta]
  have he4 : s - max (-t) 0 - -max (-t) 0 = s := by ring
  simp only [sub_eq_add_neg] at he1 he2 he3 he4
  rw [h1.2, h2.2, h3.2, h4.2, he1, he2, he3, he4]
  ring


private lemma S_even (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0) (t : ℝ) :
    S D x a (-t) = S D x a t := by
  rw [S_half_window D hD x a ha, S_half_window D hD x a ha]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro s _
  dsimp [pairedResolvent]
  rw [show -t - s = -(t + s) by ring, show -t + s = -(t - s) by ring,
    abs_neg, abs_neg]
  ring

private lemma shifted_W (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) (t r : ℝ) (hr : r ^ 2 = 1) :
    W (D + |t|) (shiftedNodes x t) (shiftedCoeffs a r) =
      2 * W D x a + 2 * r * S D x a t := by
  have hx' : ∀ i, shiftedNodes x t i ∈ Icc (0 : ℝ) (D + |t|) := by
    intro i
    cases i with
    | inl i => exact ⟨by exact add_nonneg (hx i).1 (le_max_right _ _),
        by dsimp [shiftedNodes]; linarith [(hx i).2, le_abs_self t, neg_le_abs t,
          show max t 0 ≤ |t| from max_le (le_abs_self t) (abs_nonneg t)]⟩
    | inr i => exact ⟨by exact add_nonneg (hx i).1 (le_max_right _ _),
        by dsimp [shiftedNodes]; linarith [(hx i).2,
          show max (-t) 0 ≤ |t| from max_le (neg_le_abs t) (abs_nonneg t)]⟩
  have ha' : ∑ i, shiftedCoeffs a r i = 0 := by
    simp [shiftedCoeffs, Fintype.sum_sum_type, ← Finset.mul_sum, ha]
  have hbase := correlation_kernel_integrable D hD x a hx ha 0
  have hshift (z : ℝ) :
      Integrable (fun s : ℝ => Real.exp (-|s| / 2) * correlation x a (s + z)) := by
    have hi := (correlation_kernel_integrable D hD x a hx ha z).comp_add_right z
    convert hi using 1
    ext s
    congr 2
    rw [show z - (s + z) = -s by ring, abs_neg]
  have hs (z : ℝ) :
      (∫ s : ℝ, Real.exp (-|s| / 2) * correlation x a (s + z)) =
        4 * S D x a z := by
    rw [S_global D hD x a hx ha z]
    have ht := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun s : ℝ => Real.exp (-|z - s| / 2) * correlation x a s) z
    have he (s : ℝ) : |z - (s + z)| = |s| := by
      rw [show z - (s + z) = -s by ring, abs_neg]
    simp_rw [he] at ht
    linarith only [ht]
  have hz : (∫ s : ℝ, Real.exp (-|s| / 2) * correlation x a s) = 4 * W D x a := by
    simpa only [add_zero, W] using hs 0
  rw [W, S_global (D + |t|) (by positivity) _ _ hx' ha' 0]
  simp_rw [zero_sub, abs_neg, shifted_correlation x a ha t r _ hr]
  have hbase' : Integrable (fun s => Real.exp (-|s| / 2) * correlation x a s) := by
    simpa using hbase
  have he (s : ℝ) : Real.exp (-|s| / 2) * (2 * correlation x a s +
      r * (correlation x a (s + t) + correlation x a (s - t))) =
      2 * (Real.exp (-|s| / 2) * correlation x a s) +
      r * (Real.exp (-|s| / 2) * correlation x a (s + t)) +
      r * (Real.exp (-|s| / 2) * correlation x a (s + -t)) := by
    rw [sub_eq_add_neg]; ring
  simp_rw [he]
  have ha2 := integral_add ((hbase'.const_mul 2).add ((hshift t).const_mul r))
    ((hshift (-t)).const_mul r)
  have ha1 := integral_add (hbase'.const_mul 2) ((hshift t).const_mul r)
  simp only [Pi.add_apply] at ha2 ha1
  rw [ha2, ha1,
    integral_const_mul, integral_const_mul, integral_const_mul, hz, hs t, hs (-t),
    S_even D hD x a ha]
  dsimp only [W]
  ring

lemma S_abs_le_W (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) (t : ℝ) : |S D x a t| ≤ W D x a := by
  have hx' : ∀ i, shiftedNodes x t i ∈ Icc (0 : ℝ) (D + |t|) := by
    intro i
    cases i with
    | inl i =>
      exact ⟨add_nonneg (hx i).1 (le_max_right _ _),
        add_le_add (hx i).2 (max_le (le_abs_self t) (abs_nonneg t))⟩
    | inr i =>
      exact ⟨add_nonneg (hx i).1 (le_max_right _ _),
        add_le_add (hx i).2 (max_le (neg_le_abs t) (abs_nonneg t))⟩
  have hz (r : ℝ) : ∑ i, shiftedCoeffs a r i = 0 := by
    simp [shiftedCoeffs, Fintype.sum_sum_type, ← Finset.mul_sum, ha]
  have hp := W_nonneg (D + |t|) (by positivity) _ _ hx' (hz 1)
  have hm := W_nonneg (D + |t|) (by positivity) _ _ hx' (hz (-1))
  rw [shifted_W D hD x a hx ha t 1 (by norm_num)] at hp
  rw [shifted_W D hD x a hx ha t (-1) (by norm_num)] at hm
  exact abs_le.mpr ⟨by linarith only [hp], by linarith only [hm]⟩


private lemma literal_correlation_zero (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) : correlation x a 0 = energy x a := by
  have hre := integral_re (shifted_hinge_prefix_energy x a ha 0).1
  simp only [RCLike.re_to_complex] at hre
  rw [correlation, ← hre]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [add_zero]
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private def literalExpPair (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℝ :=
  (∑ i, ∑ j, star (a i) * a j * (Real.exp (-|t + x i - x j| / 2) : ℂ)).re

private lemma literalExpPair_neg (x : I → ℝ) (a : I → ℂ) (t : ℝ) :
    literalExpPair x a (-t) = literalExpPair x a t := by
  classical
  simp only [literalExpPair, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : |-t + x j - x i| = |t + x i - x j| := by
    rw [show -t + x j - x i = -(t + x i - x j) by ring, abs_neg]
  rw [he]
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private lemma literalExpPair_shift (x : I → ℝ) (a : I → ℂ) (t : ℝ) :
    (quadratic (shiftedNodes x t) (shiftedCoeffs a 1)
      (fun s => Real.exp (-|s| / 2))).re =
      2 * literalExpPair x a 0 + 2 * literalExpPair x a t := by
  classical
  have hd : max t 0 - max (-t) 0 = t := by
    rcases le_total 0 t with ht | ht
    · rw [max_eq_left ht, max_eq_right (by linarith : -t ≤ 0)]; ring
    · rw [max_eq_right ht, max_eq_left (by linarith : 0 ≤ -t)]; ring
  have he₁ (i j : I) : x i + max t 0 - (x j + max t 0) = x i - x j := by ring
  have he₂ (i j : I) : x i + max (-t) 0 - (x j + max (-t) 0) = x i - x j := by ring
  have he₃ (i j : I) : x i + max t 0 - (x j + max (-t) 0) = t + x i - x j := by
    linarith only [hd]
  have he₄ (i j : I) : x i + max (-t) 0 - (x j + max t 0) = -t + x i - x j := by
    linarith only [hd]
  simp only [quadratic, Fintype.sum_sum_type, shiftedNodes, shiftedCoeffs,
    Complex.ofReal_one, one_mul, he₁, he₂, he₃, he₄, Finset.sum_add_distrib,
    Complex.add_re]
  have heq : literalExpPair x a 0 + literalExpPair x a (-t) +
      (literalExpPair x a t + literalExpPair x a 0) =
      2 * literalExpPair x a 0 + 2 * literalExpPair x a t := by
    rw [literalExpPair_neg]
    ring
  simpa only [literalExpPair, zero_add] using heq

/-- Finite polarization of the actual resolvent, with support-safe shifts. -/
private lemma literal_S_finite (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) (t : ℝ) :
    S D x a t = correlation x a t - literalExpPair x a t := by
  have hx' : ∀ i, shiftedNodes x t i ∈ Icc (0 : ℝ) (D + |t|) := by
    intro i
    cases i with
    | inl i => exact ⟨add_nonneg (hx i).1 (le_max_right _ _),
        add_le_add (hx i).2 (max_le (le_abs_self t) (abs_nonneg t))⟩
    | inr i => exact ⟨add_nonneg (hx i).1 (le_max_right _ _),
        add_le_add (hx i).2 (max_le (neg_le_abs t) (abs_nonneg t))⟩
  have ha' : ∑ i, shiftedCoeffs a 1 i = 0 := by
    simp [shiftedCoeffs, Fintype.sum_sum_type, ← Finset.mul_sum, ha]
  have hp := shifted_W D hD x a hx ha t 1 (by norm_num)
  have hd := W_eq_exponential_deficit (D + |t|) (by positivity) _ _ hx' ha'
  have he := shifted_correlation x a ha t 1 0 (by norm_num)
  rw [literal_correlation_zero _ _ ha', literal_correlation_zero _ _ ha,
    zero_add, zero_sub, correlation_neg] at he
  rw [W_eq_exponential_deficit D hD x a hx ha] at hp
  rw [literalExpPair_shift] at hd
  have hq : (quadratic x a (fun s => Real.exp (-|s| / 2))).re =
      literalExpPair x a 0 := by simp [literalExpPair, quadratic]
  rw [hq] at hp
  linarith only [hp, hd, he]

private def literalNuNodes (ell : ℝ) : Fin 3 → ℝ := ![0, ell / 2, ell]
private def literalNuCoeffs (ell : ℝ) : Fin 3 → ℝ :=
  ![1, -(1 + Real.exp (-ell / 4)), Real.exp (-ell / 4)]
private def literalStep (q : ℕ) : ℝ := 1 / (16 * (q : ℝ))
private def literalNodes (q : ℕ) (i : Fin q × Fin 3 × Bool) : ℝ :=
  (i.1 : ℝ) * literalStep q + literalNuNodes (literalStep q) i.2.1 +
    if i.2.2 then Real.log 2 else 0
private def literalCoeffs (q : ℕ) (i : Fin q × Fin 3 × Bool) : ℂ :=
  (((-1 : ℝ) ^ (i.1 : ℕ) * ((q - 1).choose (i.1 : ℕ) : ℝ) *
    literalNuCoeffs (literalStep q) i.2.1 * if i.2.2 then -1 else 1) : ℝ)

private lemma literalCoeffs_ofReal_re (q : ℕ) (i : Fin q × Fin 3 × Bool) :
    ((literalCoeffs q i).re : ℂ) = literalCoeffs q i := rfl

private lemma literal_step_bounds (q : ℕ) (hq : 1 ≤ q) :
    0 < literalStep q ∧ literalStep q ≤ 1 / 16 ∧
      (q : ℝ) * literalStep q = 1 / 16 := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  dsimp [literalStep]
  constructor
  · positivity
  constructor
  · apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * q) (by norm_num : (0 : ℝ) < 16)).mpr
    nlinarith
  · field_simp

private lemma literal_support (q : ℕ) (hq : 1 ≤ q) (i : Fin q × Fin 3 × Bool) :
    literalNodes q i ∈ Icc (0 : ℝ) (1 / 16) ∪
      Icc (Real.log 2) (Real.log 2 + 1 / 16) := by
  have hl := literal_step_bounds q hq
  have hj : (i.1 : ℝ) + 1 ≤ q := by exact_mod_cast i.1.isLt
  have hk : 0 ≤ literalNuNodes (literalStep q) i.2.1 ∧
      literalNuNodes (literalStep q) i.2.1 ≤ literalStep q := by
    rcases i.2.1 with ⟨k, hk⟩
    interval_cases k <;> simp [literalNuNodes] <;> (try constructor) <;> linarith [hl.1]
  have hb : 0 ≤ (i.1 : ℝ) * literalStep q + literalNuNodes (literalStep q) i.2.1 ∧
      (i.1 : ℝ) * literalStep q + literalNuNodes (literalStep q) i.2.1 ≤ 1 / 16 := by
    constructor
    · exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hl.1.le) hk.1
    · nlinarith [mul_le_mul_of_nonneg_right hj hl.1.le, hl.2.2]
  cases hb' : i.2.2
  · exact Or.inl (by simpa [literalNodes, hb'] using hb)
  · exact Or.inr (by simp only [literalNodes, hb', ite_true, mem_Icc]; constructor <;> linarith [hb.1, hb.2])

private lemma literalNu_mass (ell : ℝ) : ∑ k, (literalNuCoeffs ell k : ℂ) = 0 := by
  simp [literalNuCoeffs, Fin.sum_univ_succ]

private lemma literalNu_exp (ell : ℝ) :
    ∑ k, (literalNuCoeffs ell k : ℂ) * (Real.exp (literalNuNodes ell k / 2) : ℂ) = 0 := by
  have h₁ : Real.exp (-ell / 4) * Real.exp (ell / 4) = 1 := by
    rw [← Real.exp_add]; convert Real.exp_zero using 2 <;> ring
  have h₂ : Real.exp (-ell / 4) * Real.exp (ell / 2) = Real.exp (ell / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have hreal : ∑ k, literalNuCoeffs ell k * Real.exp (literalNuNodes ell k / 2) = 0 := by
    simp [literalNuNodes, literalNuCoeffs, Fin.sum_univ_succ,
      show ell / 2 / 2 = ell / 4 by ring]
    nlinarith only [h₁, h₂]
  exact_mod_cast hreal

private lemma literal_exp_cubic (z : ℝ) (hz : 0 ≤ z) :
    z ^ 3 / 6 ≤ (z - 2) * Real.exp z + z + 2 := by
  let f : ℝ → ℝ := fun t => (t - 1) * Real.exp t + 1 - t ^ 2 / 2
  have hf' (t : ℝ) : HasDerivAt f (t * (Real.exp t - 1)) t := by
    dsimp [f]
    convert (((hasDerivAt_id t).sub_const 1).mul (Real.hasDerivAt_exp t)).add_const 1 |>.sub
      (((hasDerivAt_id t).pow 2).div_const 2) using 1 <;> (try funext u) <;> dsimp <;> ring
  have hf : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (by dsimp [f]; fun_prop)
      (fun t _ => (hf' t).hasDerivWithinAt)
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht : t ∈ Ici (0 : ℝ))
    exact mul_nonneg ht0 (sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht0))
  have hf0 (t : ℝ) (ht : 0 ≤ t) : 0 ≤ f t := by
    have h := hf (by simp) ht ht
    simpa [f] using h
  let g : ℝ → ℝ := fun t => (t - 2) * Real.exp t + t + 2 - t ^ 3 / 6
  have hg' (t : ℝ) : HasDerivAt g (f t) t := by
    dsimp [g, f]
    convert (((((hasDerivAt_id t).sub_const 2).mul (Real.hasDerivAt_exp t)).add
      (hasDerivAt_id t)).add_const 2).sub (((hasDerivAt_id t).pow 3).div_const 6) using 1 <;> (try funext u) <;> dsimp <;> ring
  have hg : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (by dsimp [g]; fun_prop) (fun t _ => (hg' t).hasDerivWithinAt)
    intro t ht
    exact hf0 t (interior_subset ht)
  have h := hg (by simp) hz hz
  dsimp [g] at h
  norm_num at h
  linarith


private lemma literal_correlation_hinge (x : I → ℝ) (a : I → ℝ)
    (ha : ∑ i, (a i : ℂ) = 0) (t : ℝ) :
    correlation x (fun i => (a i : ℂ)) t =
      -(∑ i, ∑ j, a i * a j * max (x i - x j - t) 0) := by
  have h := congrArg Complex.re (shifted_hinge_prefix_energy x (fun i => (a i : ℂ)) ha t).2.2.1
  simp only [Complex.re_sum, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.neg_re] at h
  change _ = -correlation x (fun i => (a i : ℂ)) t at h
  linarith only [h]

private lemma literal_S_tail (D H : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hxH : ∀ i, x i ∈ Icc (0 : ℝ) H) (ha : ∑ i, a i = 0)
    (hexp : ∑ i, a i * (Real.exp (x i / 2) : ℂ) = 0)
    (t : ℝ) (ht : H ≤ |t|) : S D x a t = 0 := by
  have hpos (s : ℝ) (hs : H ≤ s) : S D x a s = 0 := by
    have hc : correlation x a s = 0 := by
      have hh := congrArg Complex.re (shifted_hinge_prefix_energy x a ha s).2.2.1
      have hz (i j : I) : max (x i - x j - s) 0 = 0 :=
        max_eq_right (by linarith [(hxH i).2, (hxH j).1])
      simp only [hz, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero,
        Complex.zero_re, Complex.neg_re] at hh
      change 0 = -correlation x a s at hh
      linarith only [hh]
    have he (i j : I) : Real.exp (-|s + x i - x j| / 2) =
        Real.exp (-s / 2) * Real.exp (-x i / 2) * Real.exp (x j / 2) := by
      rw [abs_of_nonneg (by linarith [(hxH i).1, (hxH j).2]),
        ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hq : literalExpPair x a s = 0 := by
      dsimp only [literalExpPair]
      have hz (i : I) : (∑ j, star (a i) * a j * (Real.exp (-|s + x i - x j| / 2) : ℂ)) = 0 := by
        simp_rw [he, Complex.ofReal_mul]
        calc
          _ = (star (a i) * (Real.exp (-s / 2) : ℂ) *
              (Real.exp (-x i / 2) : ℂ)) *
              ∑ j, a j * (Real.exp (x j / 2) : ℂ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = 0 := by rw [hexp, mul_zero]
      simp only [hz, Finset.sum_const_zero, Complex.zero_re]
    rw [literal_S_finite D hD x a hx ha s, hc, hq, sub_self]
  rcases le_total 0 t with ht0 | ht0
  · exact hpos t (by simpa only [abs_of_nonneg ht0] using ht)
  · rw [← S_even D hD x a ha t]
    exact hpos (-t) (by simpa only [abs_of_nonpos ht0] using ht)

private lemma literalNu_support (ell : ℝ) (hl : 0 ≤ ell) (k : Fin 3) :
    literalNuNodes ell k ∈ Icc (0 : ℝ) ell := by
  rcases k with ⟨k, hk⟩
  interval_cases k <;> simp [literalNuNodes] <;> (try constructor) <;> linarith

private lemma literalNu_energy (ell : ℝ) (hl : 0 ≤ ell) :
    energy (literalNuNodes ell) (fun k => (literalNuCoeffs ell k : ℂ)) =
      ell * (1 + Real.exp (-ell / 4) ^ 2) / 2 := by
  rw [← literal_correlation_zero _ _ (literalNu_mass ell),
    literal_correlation_hinge _ _ (literalNu_mass ell)]
  have hh : 0 ≤ ell / 2 := by linarith
  have hn : -(ell / 2) ≤ 0 := by linarith
  have hn' : -ell ≤ 0 := by linarith
  simp [literalNuNodes, literalNuCoeffs, Fin.sum_univ_succ,
    max_eq_left hl, max_eq_left hh, max_eq_right hn, max_eq_right hn',
    show ell / 2 - ell = -(ell / 2) by ring,
    show ell - ell / 2 = ell / 2 by ring]
  ring

private lemma literal_quadratic_real (x : I → ℝ) (a : I → ℝ) (f : ℝ → ℝ) :
    (quadratic x (fun i => (a i : ℂ)) f).re =
      ∑ i, ∑ j, a i * a j * f (x i - x j) := by
  simp only [quadratic, Complex.re_sum, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, Complex.ofReal_re]

private lemma literalNu_W (D ell : ℝ) (hD : 0 ≤ D) (hl : 0 ≤ ell)
    (hlD : ell ≤ D) :
    W D (literalNuNodes ell) (fun k => (literalNuCoeffs ell k : ℂ)) =
      ell * (1 + Real.exp (-ell / 4) ^ 2) / 2 - 2 * (1 - Real.exp (-ell / 4) ^ 2) := by
  rw [W_eq_exponential_deficit D hD _ _
    (fun k => ⟨(literalNu_support ell hl k).1,
      (literalNu_support ell hl k).2.trans hlD⟩) (literalNu_mass ell), literalNu_energy ell hl]
  rw [literal_quadratic_real]
  have he : Real.exp (-ell / 2) = Real.exp (-ell / 4) ^ 2 := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hh : 0 ≤ ell / 2 := by linarith
  simp [literalNuNodes, literalNuCoeffs, Fin.sum_univ_succ,
    abs_of_nonneg hl, abs_of_nonneg hh, abs_of_nonpos (neg_nonpos.mpr hl),
    abs_of_nonpos (neg_nonpos.mpr hh),
    show ell / 2 - ell = -(ell / 2) by ring,
    show ell - ell / 2 = ell / 2 by ring,
    he, show -(ell / 2) / 2 = -ell / 4 by ring]
  ring

private lemma literalNu_W_lower (D ell : ℝ) (hD : 0 ≤ D) (hl : 0 ≤ ell)
    (hlD : ell ≤ D) :
    Real.exp (-ell / 4) ^ 2 * ell ^ 3 / 48 ≤
      W D (literalNuNodes ell) (fun k => (literalNuCoeffs ell k : ℂ)) := by
  rw [literalNu_W D ell hD hl hlD]
  have he : Real.exp (-ell / 4) ^ 2 = Real.exp (-(ell / 2)) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hinv : Real.exp (ell / 2) * Real.exp (-(ell / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have h := mul_le_mul_of_nonneg_left (literal_exp_cubic (ell / 2) (by linarith))
    (Real.exp_pos (-(ell / 2))).le
  rw [he]
  have heq : Real.exp (-(ell / 2)) *
      ((ell / 2 - 2) * Real.exp (ell / 2) + ell / 2 + 2) =
      ell * (1 + Real.exp (-(ell / 2))) / 2 - 2 * (1 - Real.exp (-(ell / 2))) := by
    calc
      _ = (ell / 2 - 2) * (Real.exp (ell / 2) * Real.exp (-(ell / 2))) +
          Real.exp (-(ell / 2)) * (ell / 2 + 2) := by ring
      _ = _ := by rw [hinv]; ring
  rw [heq] at h
  convert h using 1 <;> ring


private def literalMixed : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | h :: hs, f => literalMixed hs (fwdDiff h f)

private lemma literalMixed_mul (hs : List ℝ) (c : ℝ) (f : ℝ → ℝ) :
    literalMixed hs (fun t => c * f t) = fun t => c * literalMixed hs f t := by
  induction hs generalizing f with
  | nil => rfl
  | cons h hs ih =>
    have he : fwdDiff h (fun t => c * f t) = fun t => c * fwdDiff h f t := by
      ext t; simp only [fwdDiff]; ring
    simp only [literalMixed, he, ih]

private lemma literalMixed_sum {J : Type*} (s : Finset J) (hs : List ℝ) (f : J → ℝ → ℝ) :
    literalMixed hs (fun t => ∑ j ∈ s, f j t) = fun t => ∑ j ∈ s, literalMixed hs (f j) t := by
  induction hs generalizing f with
  | nil => rfl
  | cons h hs ih =>
    have he : fwdDiff h (fun t => ∑ j ∈ s, f j t) = fun t => ∑ j ∈ s, fwdDiff h (f j) t := by
      ext t; simp only [fwdDiff, Finset.sum_sub_distrib]
    simp only [literalMixed, he, ih]

private lemma literal_pow_difference (h : ℝ) (m : ℕ) :
    fwdDiff h (fun t : ℝ => t ^ m) =
      fun t => ∑ k ∈ Finset.range m, ((m.choose k : ℝ) * h ^ (m - k)) * t ^ k := by
  ext t
  simp only [fwdDiff, add_pow, Finset.sum_range_succ, Nat.sub_self,
    pow_zero, Nat.choose_self, Nat.cast_one, mul_one, add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma literalMixed_power (hs : List ℝ) (m : ℕ) (hm : m ≤ hs.length) (y : ℝ) :
    literalMixed hs (fun t => t ^ m) y =
      if m < hs.length then 0 else (m.factorial : ℝ) * hs.prod := by
  induction hs generalizing m y with
  | nil =>
    have hm0 : m = 0 := by simpa using hm
    subst m
    simp [literalMixed]
  | cons h hs ih =>
    have he : literalMixed (h :: hs) (fun t => t ^ m) y =
        ∑ k ∈ Finset.range m, ((m.choose k : ℝ) * h ^ (m - k)) *
          literalMixed hs (fun t => t ^ k) y := by
      simp only [literalMixed, literal_pow_difference, literalMixed_sum, literalMixed_mul]
    rw [he]
    by_cases hlt : m < (h :: hs).length
    · rw [if_pos hlt]
      apply Finset.sum_eq_zero
      intro k hk
      have hk0 : k < hs.length := by
        have := Finset.mem_range.mp hk
        simp only [List.length_cons] at hlt
        omega
      rw [ih k hk0.le y, if_pos hk0, mul_zero]
    · have hm0 : m = hs.length + 1 := by simp only [List.length_cons] at hm hlt; omega
      subst m
      rw [if_neg hlt, Finset.sum_range_succ]
      have hz : (∑ k ∈ Finset.range hs.length,
          ((hs.length + 1).choose k : ℝ) * h ^ (hs.length + 1 - k) *
            literalMixed hs (fun t => t ^ k) y) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hk0 := Finset.mem_range.mp hk
        rw [ih k hk0.le y, if_pos hk0, mul_zero]
      rw [hz, zero_add, ih hs.length le_rfl y, if_neg (lt_irrefl _),
        Nat.add_sub_cancel_left, pow_one, Nat.choose_succ_self_right,
        Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, List.prod_cons]
      ring

private lemma literalMixed_shift (hs : List ℝ) (f : ℝ → ℝ) (c : ℝ) :
    literalMixed hs (fun t => f (t + c)) = fun t => literalMixed hs f (t + c) := by
  induction hs generalizing f with
  | nil => rfl
  | cons h hs ih =>
    have he : fwdDiff h (fun t => f (t + c)) = fun t => fwdDiff h f (t + c) := by
      ext t; simp [fwdDiff, add_right_comm]
    simp only [literalMixed, he, ih]

private lemma literalMixed_sub (hs : List ℝ) (f g : ℝ → ℝ) :
    literalMixed hs (fun t => f t - g t) = fun t => literalMixed hs f t - literalMixed hs g t := by
  induction hs generalizing f g with
  | nil => rfl
  | cons h hs ih =>
    have he : fwdDiff h (fun t => f t - g t) = fun t => fwdDiff h f t - fwdDiff h g t := by
      ext t; simp only [fwdDiff]; ring
    simp only [literalMixed, he, ih]

private lemma literalMixed_commute (hs : List ℝ) (h : ℝ) (f : ℝ → ℝ) :
    literalMixed hs (fwdDiff h f) = fwdDiff h (literalMixed hs f) := by
  induction hs generalizing f with
  | nil => rfl
  | cons k hs ih =>
    have he : fwdDiff k (fwdDiff h f) = fwdDiff h (fwdDiff k f) := by
      ext t; simp [fwdDiff, add_right_comm]; ring
    simp only [literalMixed, he, ih]

private lemma literalMixed_replicate (n : ℕ) (h : ℝ) (f : ℝ → ℝ) :
    literalMixed (List.replicate n h) f = (fwdDiff h)^[n] f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, literalMixed, ih, Function.iterate_succ_apply]

private lemma literalMixed_append (hs ks : List ℝ) (f : ℝ → ℝ) :
    literalMixed (hs ++ ks) f = literalMixed ks (literalMixed hs f) := by
  induction hs generalizing f with
  | nil => rfl
  | cons h hs ih => simp only [List.cons_append, literalMixed, ih]

private lemma literal_binomial_difference (n : ℕ) (ell y : ℝ) (f : ℝ → ℝ) :
    (∑ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℝ) *
      f (y + (j : ℝ) * ell)) = (-1 : ℝ) ^ n * (fwdDiff ell)^[n] f y := by
  rw [fwdDiff_iter_eq_sum_shift, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (j : ℕ) ≤ n := by omega
  have he : (-1 : ℝ) ^ n * (-1 : ℝ) ^ (n - (j : ℕ)) = (-1 : ℝ) ^ (j : ℕ) := by
    rw [← pow_add, show n + (n - (j : ℕ)) = 2 * (n - (j : ℕ)) + (j : ℕ) by omega,
      pow_add, pow_mul]
    norm_num
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, nsmul_eq_mul]
  rw [← he]
  ring

private lemma literal_stencil (n : ℕ) (f : ℝ → ℝ) :
    (∑ i : Fin (n + 1) × Fin 3 × Bool,
      (literalCoeffs (n + 1) i).re * f (literalNodes (n + 1) i)) =
    (-1 : ℝ) ^ n *
      (literalMixed (List.replicate n (literalStep (n + 1)) ++
          [Real.log 2, literalStep (n + 1) / 2]) f 0 -
        Real.exp (-literalStep (n + 1) / 4) *
          literalMixed (List.replicate n (literalStep (n + 1)) ++
            [Real.log 2, literalStep (n + 1) / 2]) f (literalStep (n + 1) / 2)) := by
  let ell := literalStep (n + 1)
  let r := Real.exp (-ell / 4)
  let g : ℝ → ℝ := fun t =>
    f t - (1 + r) * f (t + ell / 2) + r * f (t + ell) -
      (f (t + Real.log 2) - (1 + r) * f (t + Real.log 2 + ell / 2) +
        r * f (t + Real.log 2 + ell))
  have hsum : (∑ i : Fin (n + 1) × Fin 3 × Bool,
      (literalCoeffs (n + 1) i).re * f (literalNodes (n + 1) i)) =
      ∑ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℝ) *
        g (0 + (j : ℝ) * ell) := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    simp [literalNodes, literalCoeffs, literalNuNodes, literalNuCoeffs,
      Fin.sum_univ_succ, Fintype.sum_bool, g, ell, r]
    ring
  have hg : g = fun t => fwdDiff (ell / 2) (fwdDiff (Real.log 2) f) t -
      r * fwdDiff (ell / 2) (fwdDiff (Real.log 2) f) (t + ell / 2) := by
    ext t
    dsimp [g, fwdDiff]
    simp only [show t + ell / 2 + Real.log 2 = t + Real.log 2 + ell / 2 by ring,
      show t + ell / 2 + ell / 2 = t + ell by ring,
      show t + ell / 2 + ell / 2 + Real.log 2 = t + Real.log 2 + ell by ring]
    ring
  rw [hsum, literal_binomial_difference n ell 0 g, ← literalMixed_replicate, hg,
    literalMixed_sub, literalMixed_mul, literalMixed_shift,
    literalMixed_commute, literalMixed_commute]
  simp only [literalMixed_append, literalMixed, zero_add]
  rfl

private lemma literal_moments (q : ℕ) (hq : 1 ≤ q) (m : ℕ) (hm : m ≤ q) :
    ∑ i : Fin q × Fin 3 × Bool, literalCoeffs q i * (literalNodes q i : ℂ) ^ m = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have he := literal_stencil n (fun t => t ^ m)
  have hlen : m < (List.replicate n (literalStep (n + 1)) ++
      [Real.log 2, literalStep (n + 1) / 2]).length := by simp; omega
  rw [literalMixed_power _ m hlen.le, if_pos hlen,
    literalMixed_power _ m hlen.le, if_pos hlen] at he
  simp only [mul_zero, sub_self] at he
  have hc : ∑ i : Fin (n + 1) × Fin 3 × Bool,
      (((literalCoeffs (n + 1) i).re * literalNodes (n + 1) i ^ m : ℝ) : ℂ) = 0 := by
    exact_mod_cast he
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, literalCoeffs_ofReal_re] using hc

private lemma literal_moment_residual (q : ℕ) (hq : 1 ≤ q) :
    (∑ i : Fin q × Fin 3 × Bool, literalCoeffs q i * (literalNodes q i : ℂ) ^ (q + 1)) =
      (((-1 : ℝ) ^ (q + 1) * ((q + 1).factorial : ℝ) * Real.log 2 *
        literalStep q ^ q * (1 - Real.exp (-literalStep q / 4)) / 2 : ℝ) : ℂ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have he := literal_stencil n (fun t => t ^ (n + 1 + 1))
  have hlen : (List.replicate n (literalStep (n + 1)) ++
      [Real.log 2, literalStep (n + 1) / 2]).length = n + 1 + 1 := by simp
  simp only [literalMixed_power _ _ (by omega : n + 1 + 1 ≤
    (List.replicate n (literalStep (n + 1)) ++ [Real.log 2, literalStep (n + 1) / 2]).length),
    hlen, lt_self_iff_false, if_false, List.prod_append, List.prod_replicate,
    List.prod_cons, List.prod_nil, mul_one] at he
  have hr : (-1 : ℝ) ^ (n + 1 + 1) = (-1 : ℝ) ^ n := by rw [show n + 1 + 1 = n + 2 by omega, pow_add]; norm_num
  have he' : (∑ i : Fin (n + 1) × Fin 3 × Bool,
      (literalCoeffs (n + 1) i).re * literalNodes (n + 1) i ^ (n + 1 + 1)) =
      (-1 : ℝ) ^ (n + 1 + 1) * ((n + 1 + 1).factorial : ℝ) * Real.log 2 *
        literalStep (n + 1) ^ (n + 1) * (1 - Real.exp (-literalStep (n + 1) / 4)) / 2 := by
    rw [he, hr, pow_succ]
    ring
  have hc := congrArg (fun z : ℝ => (z : ℂ)) he'
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    literalCoeffs_ofReal_re] using hc


private lemma literalNu_exp_real (ell : ℝ) :
    ∑ k, literalNuCoeffs ell k * Real.exp (literalNuNodes ell k / 2) = 0 := by
  have h := congrArg Complex.re (literalNu_exp ell)
  simpa only [Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.zero_re] using h

private lemma literal_exp_translate (x : I → ℝ) (a : I → ℝ) (c : ℝ) :
    (∑ i, a i * Real.exp ((c + x i) / 2)) =
      Real.exp (c / 2) * ∑ i, a i * Real.exp (x i / 2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (c + x i) / 2 = c / 2 + x i / 2 by ring, Real.exp_add]
  ring

private lemma literal_exp_translate_weighted (x : I → ℝ) (a : I → ℝ)
    (ha : ∑ i, a i * Real.exp (x i / 2) = 0) (c : ℝ) :
    (∑ i, a i * (c + x i) * Real.exp ((c + x i) / 2)) =
      Real.exp (c / 2) * ∑ i, a i * x i * Real.exp (x i / 2) := by
  calc
    _ = Real.exp (c / 2) * (c * (∑ i, a i * Real.exp (x i / 2)) +
        ∑ i, a i * x i * Real.exp (x i / 2)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [show (c + x i) / 2 = c / 2 + x i / 2 by ring, Real.exp_add]
      ring
    _ = _ := by rw [ha, mul_zero, zero_add]

private lemma literalNu_exp_weighted (ell : ℝ) :
    (∑ k, literalNuCoeffs ell k * literalNuNodes ell k *
      Real.exp (literalNuNodes ell k / 2)) =
        (ell / 2) * (Real.exp (ell / 4) - 1) := by
  have h₁ : Real.exp (-ell / 4) * Real.exp (ell / 4) = 1 := by
    rw [← Real.exp_add]; convert Real.exp_zero using 2 <;> ring
  have h₂ : Real.exp (-ell / 4) * Real.exp (ell / 2) = Real.exp (ell / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  simp [literalNuNodes, literalNuCoeffs, Fin.sum_univ_succ,
    show ell / 2 / 2 = ell / 4 by ring]
  linear_combination (ell / 2) * (-h₁) + ell * h₂

private lemma literal_binomial_exp (n : ℕ) (ell : ℝ) :
    (∑ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℝ) *
      Real.exp ((j : ℝ) * ell / 2)) = (1 - Real.exp (ell / 2)) ^ n := by
  have he (j : ℕ) : Real.exp ((j : ℝ) * ell / 2) = Real.exp (ell / 2) ^ j := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [show 1 - Real.exp (ell / 2) = -Real.exp (ell / 2) + 1 by ring,
    add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [he]
  rw [neg_pow]
  simp only [one_pow, mul_one]
  ring

private lemma literal_exp_null (q : ℕ) :
    ∑ i : Fin q × Fin 3 × Bool, literalCoeffs q i *
      (Real.exp (literalNodes q i / 2) : ℂ) = 0 := by
  have hr : (∑ i : Fin q × Fin 3 × Bool, (literalCoeffs q i).re *
      Real.exp (literalNodes q i / 2)) = 0 := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro j _
    let beta : ℝ := (-1 : ℝ) ^ (j : ℕ) * ((q - 1).choose (j : ℕ) : ℝ)
    have he : (∑ k : Fin 3, ∑ b : Bool,
        (literalCoeffs q (j, k, b)).re * Real.exp (literalNodes q (j, k, b) / 2)) =
        beta * ((∑ k, literalNuCoeffs (literalStep q) k *
          Real.exp (((j : ℝ) * literalStep q + literalNuNodes (literalStep q) k) / 2)) -
        ∑ k, literalNuCoeffs (literalStep q) k *
          Real.exp (((j : ℝ) * literalStep q + Real.log 2 + literalNuNodes (literalStep q) k) / 2)) := by
      simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib,
        Fintype.sum_bool, literalCoeffs, literalNodes, Complex.ofReal_re]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [beta]
      simp only [Bool.false_eq_true, ite_false, ite_true, add_zero]
      rw [show (j : ℝ) * literalStep q + literalNuNodes (literalStep q) k + Real.log 2 =
        (j : ℝ) * literalStep q + Real.log 2 + literalNuNodes (literalStep q) k by ring]
      ring
    rw [he, literal_exp_translate, literal_exp_translate, literalNu_exp_real]
    simp only [mul_zero, sub_self]
  have hc := congrArg (fun z : ℝ => (z : ℂ)) hr
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, literalCoeffs_ofReal_re, Complex.ofReal_zero] using hc

private lemma literal_exp_residual (q : ℕ) (hq : 1 ≤ q) :
    (∑ i : Fin q × Fin 3 × Bool, literalCoeffs q i * (literalNodes q i : ℂ) *
      (Real.exp (literalNodes q i / 2) : ℂ)) =
      (((literalStep q / 2) * (1 - Real.exp (Real.log 2 / 2)) *
        (1 - Real.exp (literalStep q / 2)) ^ (q - 1) *
        (Real.exp (literalStep q / 4) - 1) : ℝ) : ℂ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  let ell := literalStep (n + 1)
  let R := (ell / 2) * (Real.exp (ell / 4) - 1)
  have hrow (j : Fin (n + 1)) :
      (∑ k : Fin 3, ∑ b : Bool,
        (literalCoeffs (n + 1) (j, k, b)).re * literalNodes (n + 1) (j, k, b) *
          Real.exp (literalNodes (n + 1) (j, k, b) / 2)) =
      (-1 : ℝ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℝ) *
        Real.exp ((j : ℝ) * ell / 2) * (1 - Real.exp (Real.log 2 / 2)) * R := by
    have he : (∑ k : Fin 3, ∑ b : Bool,
        (literalCoeffs (n + 1) (j, k, b)).re * literalNodes (n + 1) (j, k, b) *
          Real.exp (literalNodes (n + 1) (j, k, b) / 2)) =
      (-1 : ℝ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℝ) *
      ((∑ k, literalNuCoeffs ell k * ((j : ℝ) * ell + literalNuNodes ell k) *
          Real.exp (((j : ℝ) * ell + literalNuNodes ell k) / 2)) -
      ∑ k, literalNuCoeffs ell k * ((j : ℝ) * ell + Real.log 2 + literalNuNodes ell k) *
          Real.exp (((j : ℝ) * ell + Real.log 2 + literalNuNodes ell k) / 2)) := by
      simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib,
        Fintype.sum_bool, literalCoeffs, literalNodes, Complex.ofReal_re,
        Nat.add_sub_cancel_right]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [ell]
      simp only [Bool.false_eq_true, ite_false, ite_true, add_zero]
      rw [show (j : ℝ) * literalStep (n + 1) + literalNuNodes (literalStep (n + 1)) k + Real.log 2 =
        (j : ℝ) * literalStep (n + 1) + Real.log 2 + literalNuNodes (literalStep (n + 1)) k by ring]
      ring
    rw [he, literal_exp_translate_weighted _ _ (literalNu_exp_real ell),
      literal_exp_translate_weighted _ _ (literalNu_exp_real ell), literalNu_exp_weighted]
    rw [show ((j : ℝ) * ell + Real.log 2) / 2 =
      (j : ℝ) * ell / 2 + Real.log 2 / 2 by ring, Real.exp_add]
    dsimp [R]
    ring
  have hr : (∑ i : Fin (n + 1) × Fin 3 × Bool,
      (literalCoeffs (n + 1) i).re * literalNodes (n + 1) i *
        Real.exp (literalNodes (n + 1) i / 2)) =
      (ell / 2) * (1 - Real.exp (Real.log 2 / 2)) *
        (1 - Real.exp (ell / 2)) ^ n * (Real.exp (ell / 4) - 1) := by
    simp only [Fintype.sum_prod_type, hrow]
    rw [← Finset.sum_mul, ← Finset.sum_mul, literal_binomial_exp]
    dsimp [R]
    ring
  have hc := congrArg (fun z : ℝ => (z : ℂ)) hr
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, literalCoeffs_ofReal_re,
    Nat.add_sub_cancel_right, Nat.succ_sub_one, ell] using hc


private def literalPair (x : I → ℝ) (a : I → ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, a i * a j * f (t + x i - x j)

private lemma literal_correlation_pair (x : I → ℝ) (a : I → ℝ)
    (ha : ∑ i, (a i : ℂ) = 0) (t : ℝ) :
    correlation x (fun i => (a i : ℂ)) t = -literalPair x a (fun s => max s 0) t := by
  rw [← correlation_neg x (fun i => (a i : ℂ)) t, literal_correlation_hinge x a ha]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show x i - x j - -t = t + x i - x j by ring]

private lemma literal_S_pair (D : ℝ) (hD : 0 ≤ D) (x : I → ℝ) (a : I → ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, (a i : ℂ) = 0) (t : ℝ) :
    S D x (fun i => (a i : ℂ)) t =
      -literalPair x a (fun s => max s 0 + Real.exp (-|s| / 2)) t := by
  rw [literal_S_finite D hD _ _ hx ha t, literal_correlation_pair x a ha t]
  have he : literalExpPair x (fun i => (a i : ℂ)) t =
      literalPair x a (fun s => Real.exp (-|s| / 2)) t := by
    simp only [literalExpPair, literalPair, Complex.re_sum, Complex.star_def,
      Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [he]
  simp only [literalPair, mul_add, Finset.sum_add_distrib]
  ring

private lemma literalPair_translates {J : Type*} [Fintype J]
    (x : I → ℝ) (a : I → ℝ) (s b : J → ℝ) (f : ℝ → ℝ) (t : ℝ) :
    literalPair (fun i : J × I => s i.1 + x i.2)
      (fun i => b i.1 * a i.2) f t =
    ∑ j, ∑ k, b j * b k * literalPair x a f (t + s j - s k) := by
  classical
  simp only [literalPair, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  rw [show t + (s j + x i) - (s k + x l) = t + s j - s k + x i - x l by ring]
  ring

private lemma literalPair_two (x : I → ℝ) (a : I → ℝ) (L t : ℝ) (f : ℝ → ℝ) :
    literalPair (fun i : I × Bool => x i.1 + if i.2 then L else 0)
      (fun i => a i.1 * if i.2 then -1 else 1) f t =
      2 * literalPair x a f t - literalPair x a f (t + L) - literalPair x a f (t - L) := by
  classical
  have he (i j : I) :
      (∑ b : Bool, ∑ c : Bool,
        (a i * if b then -1 else 1) * (a j * if c then -1 else 1) *
          f (t + (x i + if b then L else 0) - (x j + if c then L else 0))) =
      2 * (a i * a j * f (t + x i - x j)) -
        a i * a j * f (t + L + x i - x j) -
        a i * a j * f (t - L + x i - x j) := by
    simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false, add_zero]
    rw [show t + (x i + L) - (x j + L) = t + x i - x j by ring,
      show t + (x i + L) - x j = t + L + x i - x j by ring,
      show t + x i - (x j + L) = t - L + x i - x j by ring]
    ring
  unfold literalPair
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ i, ∑ j, ∑ b : Bool, ∑ c : Bool,
        (a i * if b then -1 else 1) * (a j * if c then -1 else 1) *
          f (t + (x i + if b then L else 0) - (x j + if c then L else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by simp only [he, Finset.sum_sub_distrib, Finset.mul_sum]

private def literalBeta (q : ℕ) (j : Fin q) : ℝ :=
  (-1 : ℝ) ^ (j : ℕ) * ((q - 1).choose (j : ℕ) : ℝ)
private def literalEtaNodes (q : ℕ) (i : Fin q × Fin 3) : ℝ :=
  (i.1 : ℝ) * literalStep q + literalNuNodes (literalStep q) i.2
private def literalEtaCoeffs (q : ℕ) (i : Fin q × Fin 3) : ℝ :=
  literalBeta q i.1 * literalNuCoeffs (literalStep q) i.2
private def literalN (q : ℕ) : ℝ := ∑ j : Fin q, literalBeta q j ^ 2

private lemma literal_eta_mass (q : ℕ) :
    ∑ i, (literalEtaCoeffs q i : ℂ) = 0 := by
  simp only [literalEtaCoeffs, Fintype.sum_prod_type, Complex.ofReal_mul,
    ← Finset.mul_sum, literalNu_mass, mul_zero, Finset.sum_const_zero]

private lemma literal_eta_exp (q : ℕ) :
    ∑ i, (literalEtaCoeffs q i : ℂ) * (Real.exp (literalEtaNodes q i / 2) : ℂ) = 0 := by
  have hr : ∑ i, literalEtaCoeffs q i * Real.exp (literalEtaNodes q i / 2) = 0 := by
    simp only [literalEtaCoeffs, literalEtaNodes, Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro j _
    simp only [mul_assoc]
    rw [← Finset.mul_sum, literal_exp_translate, literalNu_exp_real, mul_zero, mul_zero]
  exact_mod_cast hr

private lemma literal_eta_support (q : ℕ) (hq : 1 ≤ q) (i : Fin q × Fin 3) :
    literalEtaNodes q i ∈ Icc (0 : ℝ) (1 / 16) := by
  have hl := literal_step_bounds q hq
  have hk := literalNu_support (literalStep q) hl.1.le i.2
  have hj : (i.1 : ℝ) + 1 ≤ q := by exact_mod_cast i.1.isLt
  constructor
  · exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hl.1.le) hk.1
  · dsimp [literalEtaNodes]
    nlinarith [mul_le_mul_of_nonneg_right hj hl.1.le, hl.2.2, hk.2]

private lemma literal_N_pos (q : ℕ) (hq : 1 ≤ q) : 0 < literalN q := by
  have hq0 : 0 < q := by omega
  apply Finset.sum_pos'
  · intro j _; exact sq_nonneg _
  · refine ⟨⟨0, hq0⟩, Finset.mem_univ _, ?_⟩
    simp [literalBeta]

private lemma literal_eta_correlation (q : ℕ) (t : ℝ) :
    correlation (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) t =
      ∑ j : Fin q, ∑ k : Fin q, literalBeta q j * literalBeta q k *
        correlation (literalNuNodes (literalStep q))
          (fun i => (literalNuCoeffs (literalStep q) i : ℂ))
          (t + (j : ℝ) * literalStep q - (k : ℝ) * literalStep q) := by
  rw [literal_correlation_pair _ _ (literal_eta_mass q)]
  change -literalPair (fun i : Fin q × Fin 3 => (i.1 : ℝ) * literalStep q +
      literalNuNodes (literalStep q) i.2)
    (fun i => literalBeta q i.1 * literalNuCoeffs (literalStep q) i.2) _ _ = _
  rw [literalPair_translates (literalNuNodes (literalStep q)) (literalNuCoeffs (literalStep q))
    (fun j : Fin q => (j : ℝ) * literalStep q) (literalBeta q)]
  simp only [literal_correlation_pair _ _ (literalNu_mass (literalStep q)), mul_neg,
    Finset.sum_neg_distrib]

private lemma literal_eta_S (q : ℕ) (hq : 1 ≤ q) (D : ℝ) (hD : 1 / 16 ≤ D) (t : ℝ) :
    S D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) t =
      ∑ j : Fin q, ∑ k : Fin q, literalBeta q j * literalBeta q k *
        S D (literalNuNodes (literalStep q))
          (fun i => (literalNuCoeffs (literalStep q) i : ℂ))
          (t + (j : ℝ) * literalStep q - (k : ℝ) * literalStep q) := by
  have hl := literal_step_bounds q hq
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  rw [literal_S_pair D hD0 _ _ (fun i => ⟨(literal_eta_support q hq i).1,
    (literal_eta_support q hq i).2.trans hD⟩) (literal_eta_mass q)]
  change -literalPair (fun i : Fin q × Fin 3 => (i.1 : ℝ) * literalStep q +
      literalNuNodes (literalStep q) i.2)
    (fun i => literalBeta q i.1 * literalNuCoeffs (literalStep q) i.2) _ _ = _
  rw [literalPair_translates (literalNuNodes (literalStep q)) (literalNuCoeffs (literalStep q))
    (fun j : Fin q => (j : ℝ) * literalStep q) (literalBeta q)]
  simp only [literal_S_pair D hD0 _ _ (fun i => ⟨(literalNu_support _ hl.1.le i).1,
    (literalNu_support _ hl.1.le i).2.trans (hl.2.1.trans hD)⟩)
      (literalNu_mass (literalStep q)), mul_neg, Finset.sum_neg_distrib]


private lemma literal_correlation_tail (H : ℝ) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) H) (ha : ∑ i, a i = 0)
    (t : ℝ) (ht : H ≤ |t|) : correlation x a t = 0 := by
  have hp (s : ℝ) (hs : H ≤ s) : correlation x a s = 0 := by
    have hh := congrArg Complex.re (shifted_hinge_prefix_energy x a ha s).2.2.1
    have hz (i j : I) : max (x i - x j - s) 0 = 0 :=
      max_eq_right (by linarith [(hx i).2, (hx j).1])
    simp only [hz, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero,
      Complex.zero_re, Complex.neg_re] at hh
    change 0 = -correlation x a s at hh
    linarith only [hh]
  rcases le_total 0 t with ht0 | ht0
  · exact hp t (by simpa only [abs_of_nonneg ht0] using ht)
  · rw [← correlation_neg x a t]
    exact hp (-t) (by simpa only [abs_of_nonpos ht0] using ht)

private lemma literal_spacing (q : ℕ) (hq : 1 ≤ q) (j k : Fin q) (hjk : j ≠ k) :
    literalStep q ≤ |(j : ℝ) * literalStep q - (k : ℝ) * literalStep q| := by
  have hl := (literal_step_bounds q hq).1
  have hv : (j : ℕ) ≠ (k : ℕ) := fun h => hjk (Fin.ext h)
  rcases lt_or_gt_of_ne hv with h | h
  · have hr : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
    rw [abs_of_nonpos (by nlinarith : (j : ℝ) * literalStep q - (k : ℝ) * literalStep q ≤ 0)]
    nlinarith
  · have hr : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
    rw [abs_of_nonneg (by nlinarith : 0 ≤ (j : ℝ) * literalStep q - (k : ℝ) * literalStep q)]
    nlinarith

private lemma literal_diagonal {J : Type*} [Fintype J] (b s : J → ℝ) (F : ℝ → ℝ)
    (hf : ∀ j k, j ≠ k → F (s j - s k) = 0) :
    (∑ j, ∑ k, b j * b k * F (0 + s j - s k)) = (∑ j, b j ^ 2) * F 0 := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single j]
  · simp only [zero_add, sub_self, pow_two]
  · intro k _ hkj
    rw [zero_add, hf j k (Ne.symm hkj), mul_zero]
  · simp

private lemma literal_eta_energy (q : ℕ) (hq : 1 ≤ q) :
    energy (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) =
      literalN q * (literalStep q * (1 + Real.exp (-literalStep q / 4) ^ 2) / 2) := by
  rw [← literal_correlation_zero _ _ (literal_eta_mass q), literal_eta_correlation]
  have hz (j k : Fin q) (hjk : j ≠ k) :
      correlation (literalNuNodes (literalStep q))
        (fun i => (literalNuCoeffs (literalStep q) i : ℂ))
        ((j : ℝ) * literalStep q - (k : ℝ) * literalStep q) = 0 :=
    literal_correlation_tail _ _ _ (literalNu_support _ (literal_step_bounds q hq).1.le)
      (literalNu_mass _) _ (literal_spacing q hq j k hjk)
  rw [literal_diagonal _ _ _ hz, literal_correlation_zero _ _ (literalNu_mass _),
    literalNu_energy _ (literal_step_bounds q hq).1.le]
  rfl

private lemma literal_eta_W (q : ℕ) (hq : 1 ≤ q) (D : ℝ) (hD : 1 / 16 ≤ D) :
    W D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) =
      literalN q * W D (literalNuNodes (literalStep q))
        (fun i => (literalNuCoeffs (literalStep q) i : ℂ)) := by
  have hl := literal_step_bounds q hq
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  rw [W, literal_eta_S q hq D hD]
  have hz (j k : Fin q) (hjk : j ≠ k) :
      S D (literalNuNodes (literalStep q))
        (fun i => (literalNuCoeffs (literalStep q) i : ℂ))
        ((j : ℝ) * literalStep q - (k : ℝ) * literalStep q) = 0 :=
    literal_S_tail D (literalStep q) hD0 _ _
      (fun i => ⟨(literalNu_support _ hl.1.le i).1,
        (literalNu_support _ hl.1.le i).2.trans (hl.2.1.trans hD)⟩)
      (literalNu_support _ hl.1.le) (literalNu_mass _) (literalNu_exp _) _
      (literal_spacing q hq j k hjk)
  rw [literal_diagonal _ _ _ hz]
  rfl

private lemma literal_two_pair (q : ℕ) (f : ℝ → ℝ) (t : ℝ) :
    literalPair (literalNodes q) (fun i => (literalCoeffs q i).re) f t =
      2 * literalPair (literalEtaNodes q) (literalEtaCoeffs q) f t -
        literalPair (literalEtaNodes q) (literalEtaCoeffs q) f (t + Real.log 2) -
        literalPair (literalEtaNodes q) (literalEtaCoeffs q) f (t - Real.log 2) := by
  have h := literalPair_two (literalEtaNodes q) (literalEtaCoeffs q) (Real.log 2) t f
  simpa only [literalPair, Fintype.sum_prod_type, literalNodes, literalCoeffs,
    literalEtaNodes, literalEtaCoeffs, literalBeta, Complex.ofReal_re, mul_assoc] using h

private lemma literal_mass (q : ℕ) (hq : 1 ≤ q) :
    ∑ i, literalCoeffs q i = 0 := by
  simpa only [pow_zero, mul_one] using literal_moments q hq 0 (Nat.zero_le _)

private lemma literal_support_D (q : ℕ) (hq : 1 ≤ q) (D : ℝ)
    (hD : Real.log 2 + 1 / 16 ≤ D) (i : Fin q × Fin 3 × Bool) :
    literalNodes q i ∈ Icc (0 : ℝ) D := by
  rcases literal_support q hq i with h | h
  · exact ⟨h.1, by linarith [h.2, Real.log_pos (by norm_num : (1 : ℝ) < 2)]⟩
  · exact ⟨le_trans (Real.log_pos (by norm_num)).le h.1, h.2.trans hD⟩

private lemma literal_two_S (q : ℕ) (hq : 1 ≤ q) (D : ℝ)
    (hD : Real.log 2 + 1 / 16 ≤ D) (t : ℝ) :
    S D (literalNodes q) (literalCoeffs q) t =
      2 * S D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) t -
        S D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) (t + Real.log 2) -
        S D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) (t - Real.log 2) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD0 : 0 ≤ D := by linarith
  have hx := literal_support_D q hq D hD
  have hxe : ∀ i, literalEtaNodes q i ∈ Icc (0 : ℝ) D :=
    fun i => ⟨(literal_eta_support q hq i).1, by linarith [(literal_eta_support q hq i).2]⟩
  have hreal : (fun i => ((literalCoeffs q i).re : ℂ)) = literalCoeffs q :=
    funext (literalCoeffs_ofReal_re q)
  rw [← hreal, literal_S_pair D hD0 _ _ hx (by simpa only [hreal] using literal_mass q hq),
    literal_two_pair]
  simp only [literal_S_pair D hD0 _ _ hxe (literal_eta_mass q)]
  ring

private lemma literal_energy_double (q : ℕ) (hq : 1 ≤ q) :
    energy (literalNodes q) (literalCoeffs q) =
      2 * literalN q * (literalStep q * (1 + Real.exp (-literalStep q / 4) ^ 2) / 2) := by
  have hL : 1 / 16 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hr : (fun i => ((literalCoeffs q i).re : ℂ)) = literalCoeffs q :=
    funext (literalCoeffs_ofReal_re q)
  rw [← literal_correlation_zero _ _ (literal_mass q hq), ← hr,
    literal_correlation_pair _ _ (by simpa only [hr] using literal_mass q hq), literal_two_pair]
  have he (s : ℝ) : -literalPair (literalEtaNodes q) (literalEtaCoeffs q)
      (fun z => max z 0) s =
      correlation (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) s :=
    (literal_correlation_pair _ _ (literal_eta_mass q) s).symm
  have hz (s : ℝ) (hs : 1 / 16 ≤ |s|) :
      correlation (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) s = 0 :=
    literal_correlation_tail _ _ _ (literal_eta_support q hq) (literal_eta_mass q) s hs
  have hp := hz (Real.log 2) (by rwa [abs_of_nonneg (by linarith)])
  have hn := hz (-Real.log 2) (by rwa [abs_neg, abs_of_nonneg (by linarith)])
  have h0 := he 0
  have h1 := he (Real.log 2)
  have h2 := he (-Real.log 2)
  rw [literal_correlation_zero _ _ (literal_eta_mass q), literal_eta_energy q hq] at h0
  simp only [zero_add, zero_sub] at *
  linarith only [hp, hn, h0, h1, h2]

private lemma literal_continuum_identity (h L D : ℝ) (hh : 0 ≤ h) (hL : h ≤ L)
    (hD : L + h ≤ D) (F : ℝ → ℝ) (hc : Continuous F)
    (he : ∀ t, F (-t) = F t) (hs : ∀ t, h ≤ |t| → F t = 0) :
    (2 * ∫ t in (0 : ℝ)..D,
      Real.exp (t / 2) * (2 * F t - F (t + L) - F (t - L))) =
    4 * ∫ t in (0 : ℝ)..h,
      (Real.exp (t / 2) - Real.exp (L / 2) *
        (Real.exp (t / 2) + Real.exp (-t / 2)) / 2) * F t := by
  let J : ℝ → ℝ := fun t => Real.exp (t / 2) * F t
  have hJ : Continuous J := (by fun_prop : Continuous (fun t : ℝ => Real.exp (t / 2))).mul hc
  have hD0 : 0 ≤ D := by linarith
  have hcut : (∫ t in (0 : ℝ)..D, J t) = ∫ t in (0 : ℝ)..h, J t := by
    have hz : (∫ t in h..D, J t) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards [] with t ht
      have ht := uIoc_subset_uIcc ht
      rw [uIcc_of_le (by linarith : h ≤ D)] at ht
      dsimp [J]
      rw [hs t (by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.1), mul_zero]
    have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hJ.intervalIntegrable 0 h) (hJ.intervalIntegrable h D)
    linarith only [hadj, hz]
  have hplus : (∫ t in (0 : ℝ)..D, Real.exp (t / 2) * F (t + L)) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with t ht
    have ht := uIoc_subset_uIcc ht
    rw [uIcc_of_le hD0] at ht
    rw [hs (t + L) (by rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.1]), mul_zero]
  have hleft : (∫ t in (-L)..(-h), J t) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with t ht
    have ht := uIoc_subset_uIcc ht
    rw [uIcc_of_le (by linarith : -L ≤ -h)] at ht
    dsimp [J]
    rw [hs t (by rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.2]), mul_zero]
  have hright : (∫ t in h..(D - L), J t) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with t ht
    have ht := uIoc_subset_uIcc ht
    rw [uIcc_of_le (by linarith : h ≤ D - L)] at ht
    dsimp [J]
    rw [hs t (by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.1), mul_zero]
  have hwindow : (∫ t in (-L)..(D - L), J t) = ∫ t in (-h)..h, J t := by
    have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hJ.intervalIntegrable (-L) (-h)) (hJ.intervalIntegrable (-h) (D - L))
    have hb := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hJ.intervalIntegrable (-h) h) (hJ.intervalIntegrable h (D - L))
    linarith only [ha, hb, hleft, hright]
  have hminus : (∫ t in (0 : ℝ)..D, Real.exp (t / 2) * F (t - L)) =
      Real.exp (L / 2) * ∫ t in (-h)..h, J t := by
    have heq (t : ℝ) : Real.exp (t / 2) * F (t - L) = Real.exp (L / 2) * J (t - L) := by
      dsimp [J]
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    simp_rw [heq]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right,
      zero_sub, hwindow]
  have hreflect : (∫ t in (-h)..0, J t) =
      ∫ t in (0 : ℝ)..h, Real.exp (-t / 2) * F t := by
    have ht := intervalIntegral.integral_comp_neg
      (f := J) (a := (0 : ℝ)) (b := h)
    simp only [neg_zero] at ht
    have heq : (fun t => J (-t)) = fun t => Real.exp (-t / 2) * F t := by
      ext t
      simp only [J, he]
    rw [heq] at ht
    exact ht.symm
  have heven : (∫ t in (-h)..h, J t) =
      ∫ t in (0 : ℝ)..h, (Real.exp (t / 2) + Real.exp (-t / 2)) * F t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hJ.intervalIntegrable (-h) 0) (hJ.intervalIntegrable 0 h), hreflect]
    have hnint : IntervalIntegrable (fun t : ℝ => Real.exp (-t / 2) * F t) volume 0 h :=
      (by fun_prop : Continuous (fun t : ℝ => Real.exp (-t / 2) * F t)).intervalIntegrable 0 h
    rw [← intervalIntegral.integral_add hnint (hJ.intervalIntegrable 0 h)]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [J]
    ring
  have hsplit : (∫ t in (0 : ℝ)..D,
      Real.exp (t / 2) * (2 * F t - F (t + L) - F (t - L))) =
      2 * (∫ t in (0 : ℝ)..D, J t) -
      (∫ t in (0 : ℝ)..D, Real.exp (t / 2) * F (t + L)) -
      (∫ t in (0 : ℝ)..D, Real.exp (t / 2) * F (t - L)) := by
    have heq (t : ℝ) : Real.exp (t / 2) * (2 * F t - F (t + L) - F (t - L)) =
        2 * J t - Real.exp (t / 2) * F (t + L) - Real.exp (t / 2) * F (t - L) := by
      dsimp [J]; ring
    simp_rw [heq]
    have hp : Continuous (fun t : ℝ => Real.exp (t / 2) * F (t + L)) := by fun_prop
    have hm : Continuous (fun t : ℝ => Real.exp (t / 2) * F (t - L)) := by fun_prop
    have h2J : Continuous (fun t => 2 * J t) := hJ.const_mul 2
    have hfirst : IntervalIntegrable
        (fun t => 2 * J t - Real.exp (t / 2) * F (t + L)) volume 0 D :=
      (h2J.sub hp).intervalIntegrable 0 D
    rw [intervalIntegral.integral_sub (μ := volume) hfirst (hm.intervalIntegrable 0 D),
      intervalIntegral.integral_sub (μ := volume) (h2J.intervalIntegrable 0 D)
        (hp.intervalIntegrable 0 D), intervalIntegral.integral_const_mul]
  have hbracket : (∫ t in (0 : ℝ)..h,
      (Real.exp (t / 2) - Real.exp (L / 2) *
        (Real.exp (t / 2) + Real.exp (-t / 2)) / 2) * F t) =
      (∫ t in (0 : ℝ)..h, J t) - Real.exp (L / 2) / 2 *
        (∫ t in (0 : ℝ)..h, (Real.exp (t / 2) + Real.exp (-t / 2)) * F t) := by
    have heq (t : ℝ) : (Real.exp (t / 2) - Real.exp (L / 2) *
        (Real.exp (t / 2) + Real.exp (-t / 2)) / 2) * F t =
        J t - Real.exp (L / 2) / 2 * ((Real.exp (t / 2) + Real.exp (-t / 2)) * F t) := by
      dsimp [J]; ring
    simp_rw [heq]
    have hbcont : Continuous (fun t : ℝ => Real.exp (L / 2) / 2 *
        ((Real.exp (t / 2) + Real.exp (-t / 2)) * F t)) := by fun_prop
    rw [intervalIntegral.integral_sub (μ := volume)
      (hJ.intervalIntegrable 0 h) (hbcont.intervalIntegrable 0 h),
      intervalIntegral.integral_const_mul]
  rw [hsplit, hcut, hplus, hminus, heven, hbracket]
  ring


private lemma literal_continuum_bound (h L D B : ℝ) (hh : 0 ≤ h) (hL : h ≤ L)
    (hD : L + h ≤ D) (hB : 0 ≤ B) (F : ℝ → ℝ) (hc : Continuous F)
    (he : ∀ t, F (-t) = F t) (hs : ∀ t, h ≤ |t| → F t = 0)
    (hb : ∀ t, |F t| ≤ B) :
    |2 * ∫ t in (0 : ℝ)..D,
      Real.exp (t / 2) * (2 * F t - F (t + L) - F (t - L))| ≤
      4 * h * Real.exp ((L + h) / 2) * B := by
  rw [literal_continuum_identity h L D hh hL hD F hc he hs, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := h) (C := Real.exp ((L + h) / 2) * B)
    (f := fun t => (Real.exp (t / 2) - Real.exp (L / 2) *
        (Real.exp (t / 2) + Real.exp (-t / 2)) / 2) * F t) (fun t ht => by
      rw [uIoc_of_le hh] at ht
      have hA : Real.exp (t / 2) ≤ Real.exp ((L + h) / 2) :=
        Real.exp_le_exp.mpr (by linarith [ht.2])
      have h₁ : Real.exp (L / 2) * Real.exp (t / 2) ≤ Real.exp ((L + h) / 2) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [ht.2])
      have h₂ : Real.exp (L / 2) * Real.exp (-t / 2) ≤ Real.exp ((L + h) / 2) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [ht.1])
      have hB' : 0 ≤ Real.exp (L / 2) * (Real.exp (t / 2) + Real.exp (-t / 2)) / 2 := by positivity
      have hd : |Real.exp (t / 2) - Real.exp (L / 2) *
          (Real.exp (t / 2) + Real.exp (-t / 2)) / 2| ≤ Real.exp ((L + h) / 2) := by
        apply abs_le.mpr
        constructor <;> nlinarith [Real.exp_pos (t / 2)]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul hd (hb t) (abs_nonneg _) (Real.exp_pos _).le)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hh] at hn
  nlinarith only [hn]

private lemma literal_numeric_margin :
    (1 / 2 : ℝ) < Real.sqrt 2 * Real.log 2 -
      4 * (1 / 16) * Real.exp ((Real.log 2 + 1 / 16) / 2) := by
  have hs : (7 / 5 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have he : Real.exp (1 / 32 : ℝ) ≤ 32 / 31 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 32) (by norm_num : (1 / 32 : ℝ) < 1)
    norm_num at h ⊢
    exact h
  have hsqrt : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [show (Real.log 2 + 1 / 16) / 2 = Real.log 2 / 2 + 1 / 32 by ring,
    Real.exp_add, hsqrt]
  have hlog : (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hfactor : (1 / 2 : ℝ) < Real.sqrt 2 * (Real.log 2 - Real.exp (1 / 32) / 4) := by
    have hpos : (0 : ℝ) < Real.log 2 - Real.exp (1 / 32) / 4 := by linarith
    nlinarith [mul_pos (sub_pos.mpr hs) hpos]
  nlinarith only [hfactor]

private lemma literal_ratio_constant (q : ℕ) (hq : 1 ≤ q) (N Eg Wg Vv E : ℝ)
    (hN : 0 < N) (hEg : 0 < Eg) (hEg' : Eg ≤ literalStep q)
    (hW : Real.exp (-literalStep q / 4) ^ 2 * literalStep q ^ 3 / 48 ≤ Wg)
    (hV : Vv ≤ -(N * Wg) / 2) (hE : E = 2 * N * Eg) :
    0 < E ∧ Vv / E ≤ -1 / (65536 * (q : ℝ) ^ 2) := by
  have hl := literal_step_bounds q hq
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hr : (3 / 4 : ℝ) ≤ Real.exp (-literalStep q / 4) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    have ha := Real.add_one_le_exp (-literalStep q / 2)
    rw [show -literalStep q / 4 + -literalStep q / 4 = -literalStep q / 2 by ring]
    linarith [hl.2.1]
  have hw : literalStep q ^ 2 * Eg / 64 ≤ Wg := by
    have hp := mul_nonneg (sub_nonneg.mpr hr) (pow_nonneg hl.1.le 3)
    have hp' := mul_nonneg (sub_nonneg.mpr hEg') (sq_nonneg (literalStep q))
    nlinarith only [hW, hp, hp']
  have hE0 : 0 < E := by rw [hE]; positivity
  have hvE : Vv ≤ -(literalStep q ^ 2 / 256) * E := by
    calc
      Vv ≤ -(N / 2) * Wg := by linarith only [hV]
      _ ≤ -(N / 2) * (literalStep q ^ 2 * Eg / 64) :=
        mul_le_mul_of_nonpos_left hw (by linarith)
      _ = _ := by rw [hE]; ring
  have hel : literalStep q ^ 2 / 256 = 1 / (65536 * (q : ℝ) ^ 2) := by
    dsimp [literalStep]
    field_simp
    <;> ring
  refine ⟨hE0, (div_le_iff₀ hE0).mpr ?_⟩
  rw [hel] at hvE
  simpa only [neg_div, one_mul] using hvE


private lemma literal_V_upper (q : ℕ) (hq : 1 ≤ q) (D : ℝ)
    (hD : Real.log 2 + 1 / 16 ≤ D) :
    V D (literalNodes q) (literalCoeffs q) ≤
      -(literalN q * W D (literalNuNodes (literalStep q))
        (fun i => (literalNuCoeffs (literalStep q) i : ℂ))) / 2 := by
  let F : ℝ → ℝ := S D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ))
  let B := W D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ))
  have hL : 1 / 16 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hD0 : 0 ≤ D := by linarith
  have hDh : 1 / 16 ≤ D := by linarith
  have hx := literal_support_D q hq D hD
  have hxe : ∀ i, literalEtaNodes q i ∈ Icc (0 : ℝ) D := fun i =>
    ⟨(literal_eta_support q hq i).1, (literal_eta_support q hq i).2.trans hDh⟩
  have hFcont : Continuous F := by
    have heq : F = fun t => -literalPair (literalEtaNodes q) (literalEtaCoeffs q)
        (fun s => max s 0 + Real.exp (-|s| / 2)) t :=
      funext (literal_S_pair D hD0 _ _ hxe (literal_eta_mass q))
    rw [heq]
    dsimp [literalPair]
    fun_prop
  have hFeven (t : ℝ) : F (-t) = F t := S_even D hD0 _ _ (literal_eta_mass q) t
  have hFtail (t : ℝ) (ht : 1 / 16 ≤ |t|) : F t = 0 :=
    literal_S_tail D (1 / 16) hD0 _ _ hxe (literal_eta_support q hq)
      (literal_eta_mass q) (literal_eta_exp q) t ht
  have hFbound (t : ℝ) : |F t| ≤ B := S_abs_le_W D hD0 _ _ hxe (literal_eta_mass q) t
  have hB : 0 ≤ B := W_nonneg D hD0 _ _ hxe (literal_eta_mass q)
  have htwo (t : ℝ) : S D (literalNodes q) (literalCoeffs q) t =
      2 * F t - F (t + Real.log 2) - F (t - Real.log 2) := literal_two_S q hq D hD t
  have htail (t : ℝ) (ht : Real.log 2 + 1 / 16 ≤ t) :
      S D (literalNodes q) (literalCoeffs q) t = 0 := by
    rw [htwo, hFtail t (by rw [abs_of_nonneg (by linarith)]; linarith),
      hFtail (t + Real.log 2) (by rw [abs_of_nonneg (by linarith)]; linarith),
      hFtail (t - Real.log 2) (by rw [abs_of_nonneg (by linarith)]; linarith)]
    ring
  have hSL : S D (literalNodes q) (literalCoeffs q) (Real.log 2) = -B := by
    rw [htwo, hFtail (Real.log 2) (by rwa [abs_of_nonneg (by linarith)]),
      hFtail (Real.log 2 + Real.log 2) (by rw [abs_of_nonneg (by linarith)]; linarith), sub_self]
    change 2 * 0 - 0 - B = -B
    ring
  have hZ : Z D (literalNodes q) (literalCoeffs q) = 0 := by
    rw [Z, htail D hD, mul_zero]
  have hExpD0 : Real.exp (Real.log 2 + 1 / 16) < 3 := by
    have he := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num : (1 / 16 : ℝ) < 1)
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num at he
    linarith
  have hlog3 : Real.log 2 + 1 / 16 < Real.log 3 := by
    apply Real.exp_lt_exp.mp
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have h2 : 2 ∈ primes D := by
    apply Finset.mem_Icc.mpr
    refine ⟨le_rfl, (log_cut_iff 2 (by norm_num) D).mp ?_⟩
    norm_num only [Nat.cast_ofNat]
    linarith
  have hsqrt : 2 / Real.sqrt (2 : ℝ) = Real.sqrt 2 := by
    apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))).mpr
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have harith : 2 * (∑ n ∈ primes D, ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      S D (literalNodes q) (literalCoeffs q) (Real.log n)) =
      -Real.sqrt 2 * Real.log 2 * B := by
    rw [Finset.sum_eq_single 2]
    · rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      norm_num only [Nat.cast_ofNat]
      rw [hSL]
      calc
        _ = -(2 / Real.sqrt (2 : ℝ)) * Real.log 2 * B := by ring
        _ = _ := by rw [hsqrt]
    · intro n hn hn2
      have hn3 : 3 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
      have hlogn : Real.log 3 ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn3)
      rw [htail _ (by linarith), mul_zero]
    · exact fun hn => (hn h2).elim
  have hC : |2 * ∫ t in Icc (0 : ℝ) D,
      Real.exp (t / 2) * S D (literalNodes q) (literalCoeffs q) t| ≤
      4 * (1 / 16) * Real.exp ((Real.log 2 + 1 / 16) / 2) * B := by
    have h := literal_continuum_bound (1 / 16) (Real.log 2) D B (by norm_num)
      hL hD hB F hFcont hFeven hFtail hFbound
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hD0]
    simpa only [htwo] using h
  have hV : V D (literalNodes q) (literalCoeffs q) =
      -Real.sqrt 2 * Real.log 2 * B -
        2 * ∫ t in Icc (0 : ℝ) D,
          Real.exp (t / 2) * S D (literalNodes q) (literalCoeffs q) t := by
    rw [V, harith, hZ, mul_zero, sub_zero]
  have hv : V D (literalNodes q) (literalCoeffs q) ≤ -B / 2 := by
    have hmargin := mul_nonneg (sub_nonneg.mpr literal_numeric_margin.le) hB
    rw [hV]
    have hc := (abs_le.mp hC).1
    nlinarith only [hmargin, hc]
  simpa only [B, literal_eta_W q hq D hDh] using hv

/-- The explicit six-q atom family retains the inclusive literal Mangoldt V,
vanishes through exactly the requested polynomial order and at the positive
exponential moment, and has a strictly negative energy-normalized value. -/
theorem literal_V_energy_moment_obstruction (q : ℕ) (hq : 1 ≤ q) (D : ℝ)
    (hD : Real.log 2 + 1 / 16 ≤ D) :
    ∃ (x : Fin q × Fin 3 × Bool → ℝ) (a : Fin q × Fin 3 × Bool → ℂ),
      (∀ i, x i ∈ Icc (0 : ℝ) (1 / 16) ∪ Icc (Real.log 2) (Real.log 2 + 1 / 16)) ∧
      (∀ i, x i ∈ Icc (0 : ℝ) D) ∧
      (∀ m : ℕ, m ≤ q → ∑ i, a i * (x i : ℂ) ^ m = 0) ∧
      (∑ i, a i * (Real.exp (x i / 2) : ℂ) = 0) ∧
      (∑ i, a i * (x i : ℂ) ^ (q + 1)) ≠ 0 ∧
      (∑ i, a i * (x i : ℂ) * (Real.exp (x i / 2) : ℂ)) ≠ 0 ∧
      0 < energy x a ∧ V D x a / energy x a ≤ -1 / (65536 * (q : ℝ) ^ 2) := by
  have hl := literal_step_bounds q hq
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : 0 < 1 - Real.exp (-literalStep q / 4) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [hl.1]))
  have hR : (-1 : ℝ) ^ (q + 1) * ((q + 1).factorial : ℝ) * Real.log 2 *
      literalStep q ^ q * (1 - Real.exp (-literalStep q / 4)) / 2 ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))) hL.ne')
      (pow_ne_zero _ hl.1.ne')) hr.ne') (by norm_num)
  have hM : (∑ i, literalCoeffs q i * (literalNodes q i : ℂ) ^ (q + 1)) ≠ 0 := by
    rw [literal_moment_residual q hq]
    exact_mod_cast hR
  have hLexp : 1 < Real.exp (Real.log 2 / 2) := Real.one_lt_exp_iff.mpr (by linarith)
  have hlexp : 1 < Real.exp (literalStep q / 2) := Real.one_lt_exp_iff.mpr (by linarith [hl.1])
  have hqexp : 1 < Real.exp (literalStep q / 4) := Real.one_lt_exp_iff.mpr (by linarith [hl.1])
  have hRexp : (literalStep q / 2) * (1 - Real.exp (Real.log 2 / 2)) *
      (1 - Real.exp (literalStep q / 2)) ^ (q - 1) *
      (Real.exp (literalStep q / 4) - 1) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt (by linarith : 0 < literalStep q / 2))
      (ne_of_lt (by linarith : 1 - Real.exp (Real.log 2 / 2) < 0)))
      (pow_ne_zero _ (ne_of_lt (by linarith : 1 - Real.exp (literalStep q / 2) < 0))))
      (ne_of_gt (by linarith : 0 < Real.exp (literalStep q / 4) - 1))
  have hMexp : (∑ i, literalCoeffs q i * (literalNodes q i : ℂ) *
      (Real.exp (literalNodes q i / 2) : ℂ)) ≠ 0 := by
    rw [literal_exp_residual q hq]
    exact_mod_cast hRexp
  let Eg := literalStep q * (1 + Real.exp (-literalStep q / 4) ^ 2) / 2
  have hEg : 0 < Eg := by
    exact div_pos (mul_pos hl.1 (by positivity)) (by norm_num)
  have hEg' : Eg ≤ literalStep q := by
    have he : Real.exp (-literalStep q / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hl.1])
    have hp := Real.exp_pos (-literalStep q / 4)
    have hsq : Real.exp (-literalStep q / 4) ^ 2 ≤ 1 := by nlinarith
    have ht := mul_nonneg hl.1.le (sub_nonneg.mpr hsq)
    dsimp [Eg]
    nlinarith only [ht]
  have hD0 : 0 ≤ D := by linarith
  have hlD : literalStep q ≤ D := by linarith [hl.2.1]
  have hout := literal_ratio_constant q hq (literalN q) Eg
    (W D (literalNuNodes (literalStep q)) (fun i => (literalNuCoeffs (literalStep q) i : ℂ)))
    (V D (literalNodes q) (literalCoeffs q)) (energy (literalNodes q) (literalCoeffs q))
    (literal_N_pos q hq) hEg hEg' (literalNu_W_lower D _ hD0 hl.1.le hlD)
    (literal_V_upper q hq D hD) (by simpa only [Eg, mul_assoc] using literal_energy_double q hq)
  exact ⟨literalNodes q, literalCoeffs q, literal_support q hq, literal_support_D q hq D hD,
    literal_moments q hq, literal_exp_null q, hM, hMexp, hout.1, hout.2⟩

/-- Concrete S/Gamma resolvent control. The lower and shift bounds come
from the actual finite causal squares and their translated polarization;
the upper bound consumes the retained moment-exponential theorem. -/
theorem actual_resolvent_control (D : ℝ) (hD : 0 < D)
    (q : ℕ) (hq : 1 ≤ q) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    0 ≤ W D x a ∧ (∀ t : ℝ, |S D x a t| ≤ W D x a) ∧
      W D x a ≤ D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) * energy x a / 4 ∧
        |Z D x a| ≤ 4 * M D * W D x a := by
  have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
  refine ⟨W_nonneg D hD.le x a hx ha, S_abs_le_W D hD.le x a hx ha,
    W_moment_upper D hD q hq x a hx hm, ?_⟩
  dsimp only [Z]
  rw [abs_mul, abs_of_nonneg (by dsimp [M]; positivity : 0 ≤ 4 * M D)]
  exact mul_le_mul_of_nonneg_left (S_abs_le_W D hD.le x a hx ha D)
    (by dsimp [M]; positivity)

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
