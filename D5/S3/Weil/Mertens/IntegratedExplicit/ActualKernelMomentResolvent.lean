/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real correlation and resolvent identities for the complete actual kernel. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentMixture

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
lemma correlation_neg (x : I → ℝ) (a : I → ℂ) (s : ℝ) :
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
lemma W_eq_exponential_deficit (D : ℝ) (hD : 0 ≤ D)
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

lemma S_global (D : ℝ) (hD : 0 ≤ D)
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
def shiftedNodes (x : I → ℝ) (t : ℝ) : I ⊕ I → ℝ
  | .inl i => x i + max t 0
  | .inr i => x i + max (-t) 0

def shiftedCoeffs (a : I → ℂ) (r : ℝ) : I ⊕ I → ℂ
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

lemma shifted_correlation (x : I → ℝ) (a : I → ℂ)
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


lemma S_even (D : ℝ) (hD : 0 ≤ D)
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

lemma shifted_W (D : ℝ) (hD : 0 ≤ D)
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
