/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentPayments
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentPayments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Inclusive cutoff and continuum moment payments for the complete actual kernel. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentResolvent

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

/-- Inclusive Abel identity in the logarithmic variable. It is obtained
by integrating each of the finitely many Mangoldt atoms, including the
atom at the upper endpoint (whose tail integral is zero). -/
private lemma inclusive_abel_half (D : ℝ) (hD : 0 ≤ D) :
    (∑ n ∈ primes D, weight n) =
      Real.exp (-D / 2) * Chebyshev.psi (Real.exp D) +
        (1 / 2) * ∫ t in Icc (0 : ℝ) D,
          Real.exp (-t / 2) * Chebyshev.psi (Real.exp t) := by
  classical
  let f (n : ℕ) (t : ℝ) :=
    (Icc (Real.log n) D).indicator
      (fun t => ArithmeticFunction.vonMangoldt n * Real.exp (-t / 2)) t
  have hi (n : ℕ) : IntegrableOn (f n) (Icc 0 D) :=
    ((by fun_prop : Continuous (fun t : ℝ =>
      ArithmeticFunction.vonMangoldt n * Real.exp (-t / 2))).integrableOn_Icc).indicator
        measurableSet_Icc
  have hnlog (n : ℕ) (hn : n ∈ primes D) :
      Real.log (n : ℝ) ∈ Icc (0 : ℝ) D := by
    rcases Finset.mem_Icc.mp hn with ⟨hn2, hnD⟩
    exact ⟨Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)),
      (log_cut_iff n hn2 D).mpr hnD⟩
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) :
      (∑ n ∈ primes D, f n t) =
        Real.exp (-t / 2) * Chebyshev.psi (Real.exp t) := by
    have he (n : ℕ) : f n t =
        if Real.log (n : ℝ) ≤ t then ArithmeticFunction.vonMangoldt n * Real.exp (-t / 2) else 0 := by
      simp [f, Set.indicator, ht.2]
    simp_rw [he]
    rw [← Finset.sum_filter, indices D t ht.2, ← Finset.sum_mul, cumulative]
    ring
  have hint (n : ℕ) (hn : n ∈ primes D) :
      (∫ t in Icc (0 : ℝ) D, f n t) =
        2 * (weight n - ArithmeticFunction.vonMangoldt n * Real.exp (-D / 2)) := by
    have hl := hnlog n hn
    dsimp only [f]
    rw [setIntegral_indicator measurableSet_Icc,
      show (Icc (0 : ℝ) D) ∩ Icc (Real.log (n : ℝ)) D =
        Icc (Real.log (n : ℝ)) D from
      inter_eq_right.mpr (Icc_subset_Icc_left hl.1)]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hl.2]
    have hd (t : ℝ) : HasDerivAt (fun t => -2 * Real.exp (-t / 2))
        (Real.exp (-t / 2)) t := by
      convert (((hasDerivAt_id t).neg.div_const 2).exp.const_mul (-2)) using 1 <;> (try funext y) <;> (try dsimp only [id, Pi.neg_apply]) <;> ring
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := Real.log (n : ℝ)) (b := D) (fun t _ => hd t)
      ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-t / 2))).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul, he]
    dsimp [weight]
    ring
  have htotal : (∫ t in Icc (0 : ℝ) D,
      Real.exp (-t / 2) * Chebyshev.psi (Real.exp t)) =
      2 * ((∑ n ∈ primes D, weight n) -
        Real.exp (-D / 2) * Chebyshev.psi (Real.exp D)) := by
    calc
      _ = ∫ t in Icc (0 : ℝ) D, ∑ n ∈ primes D, f n t :=
        setIntegral_congr_fun measurableSet_Icc (fun t ht => (hf t ht).symm)
      _ = ∑ n ∈ primes D, ∫ t in Icc (0 : ℝ) D, f n t :=
        integral_finsetSum _ (fun n _ => hi n)
      _ = _ := by
        rw [Finset.sum_congr rfl hint, ← Finset.mul_sum, Finset.sum_sub_distrib,
          ← Finset.sum_mul, cumulative]
        ring
  linarith only [htotal]

private lemma psi_global_upper (p : PNTConstants) (t : ℝ) (ht : 0 ≤ t) :
    Chebyshev.psi (Real.exp t) ≤ (1 + p.C) * Real.exp t := by
  have h := (abs_le.mp (relativeError_le p ht)).2
  have he := mul_le_mul_of_nonneg_left h (Real.exp_nonneg t)
  dsimp only [relativeError] at he
  have hexp : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  rw [mul_sub, ← mul_assoc, hexp, one_mul, mul_one] at he
  linarith only [he]

private lemma inclusive_weight_bound (p : PNTConstants) (D : ℝ) (hD : 0 ≤ D) :
    (∑ n ∈ primes D, ArithmeticFunction.vonMangoldt n / Real.sqrt n) ≤
      2 * (1 + p.C) * M D := by
  classical
  have hident := inclusive_abel_half D hD
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) :
      Real.exp (-t / 2) * Chebyshev.psi (Real.exp t) ≤
        (1 + p.C) * Real.exp (t / 2) := by
    have h := mul_le_mul_of_nonneg_left (psi_global_upper p t ht.1)
      (Real.exp_nonneg (-t / 2))
    have he : Real.exp (-t / 2) * Real.exp t = Real.exp (t / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ ≤ Real.exp (-t / 2) * ((1 + p.C) * Real.exp t) := h
      _ = (1 + p.C) * (Real.exp (-t / 2) * Real.exp t) := by ring
      _ = _ := by rw [he]
  have hi : IntegrableOn (fun t => Real.exp (-t / 2) * Chebyshev.psi (Real.exp t))
      (Icc 0 D) := by
    let f (n : ℕ) (t : ℝ) :=
      (Icc (Real.log n) D).indicator
        (fun t => ArithmeticFunction.vonMangoldt n * Real.exp (-t / 2)) t
    have hf (n : ℕ) : IntegrableOn (f n) (Icc 0 D) :=
      ((by fun_prop : Continuous (fun t : ℝ =>
        ArithmeticFunction.vonMangoldt n * Real.exp (-t / 2))).integrableOn_Icc).indicator
          measurableSet_Icc
    apply (integrable_finsetSum (primes D) (fun n _ => hf n)).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have he : (∑ n ∈ primes D, f n t) =
        (∑ n ∈ (primes D).filter (fun (n : ℕ) => Real.log (n : ℝ) ≤ t),
          ArithmeticFunction.vonMangoldt n) * Real.exp (-t / 2) := by
      simp only [f, Set.indicator, Set.mem_Icc, ht.2, and_true, ← Finset.sum_filter, Finset.sum_mul]
    rw [he, indices D t ht.2, cumulative]
    ring
  have hI := setIntegral_mono_on hi
    ((by fun_prop : Continuous (fun t : ℝ => (1 + p.C) * Real.exp (t / 2))).integrableOn_Icc)
    measurableSet_Icc hpoint
  have he (t : ℝ) : HasDerivAt (fun t => 2 * Real.exp (t / 2)) (Real.exp (t / 2)) t := by
    convert (((hasDerivAt_id t).div_const 2).exp.const_mul 2) using 1 <;> (try funext y) <;> (try dsimp only [id, Pi.neg_apply]) <;> ring
  have hexp : (∫ t in Icc (0 : ℝ) D, Real.exp (t / 2)) = 2 * (M D - 1) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hD,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => he t)
        ((by fun_prop : Continuous (fun t : ℝ => Real.exp (t / 2))).intervalIntegrable 0 D)]
    simp [M]
    ring
  rw [integral_const_mul, hexp] at hI
  have hDpsi := hpoint D ⟨hD, le_rfl⟩
  have hsum : (∑ n ∈ primes D, ArithmeticFunction.vonMangoldt n / Real.sqrt n) =
      ∑ n ∈ primes D, weight n :=
    Finset.sum_congr rfl (fun n hn => (weight_eq_sqrt n (Finset.mem_Icc.mp hn).1).symm)
  rw [hsum, hident]
  dsimp only [M] at *
  nlinarith only [hI, hDpsi, p.one_le_C]

/-- Every cutoff term is paid, including the continuum resolvent integral
and the signed b(D)Z/2 boundary. The arithmetic sum is the actual inclusive
complete Mangoldt sum; no squarefree or prime-only replacement occurs. -/
theorem actual_cutoff_resolvent_payment (p : PNTConstants)
    (D : ℝ) (hD : 0 < D) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0) :
    |V D x a| ≤ (8 + 4 * p.C + 2 * B p) * M D * W D x a := by
  have hW := W_nonneg D hD.le x a hx ha
  have hS := S_abs_le_W D hD.le x a hx ha
  have hZ : |Z D x a| ≤ 4 * M D * W D x a := by
    dsimp only [Z]
    rw [abs_mul, abs_of_nonneg (by dsimp [M]; positivity : 0 ≤ 4 * M D)]
    exact mul_le_mul_of_nonneg_left (hS D) (by dsimp [M]; positivity)
  have hp : |∑ n ∈ primes D,
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * S D x a (Real.log n)| ≤
        2 * (1 + p.C) * M D * W D x a := by
    calc
      _ ≤ ∑ n ∈ primes D,
          |ArithmeticFunction.vonMangoldt n / Real.sqrt n * S D x a (Real.log n)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ (∑ n ∈ primes D, ArithmeticFunction.vonMangoldt n / Real.sqrt n) * W D x a := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro n hn
        rw [abs_mul, abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.sqrt_nonneg _))]
        exact mul_le_mul_of_nonneg_left (hS _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (inclusive_weight_bound p D hD.le) hW
  have hSi : IntegrableOn (fun t => Real.exp (t / 2) * S D x a t) (Icc 0 D) := by
    have hs : Continuous (S D x a) := by
      rw [show S D x a = fun t => (1 / 4) *
          ∫ s in Icc (0 : ℝ) D, pairedResolvent t s * correlation x a s from
        funext (S_half_window D hD.le x a ha)]
      apply continuous_const.mul
      apply continuous_parametric_integral_of_continuous _ isCompact_Icc
      dsimp [pairedResolvent]
      exact (by dsimp [pairedResolvent]; fun_prop : Continuous (fun z : ℝ × ℝ => pairedResolvent z.1 z.2)).mul
        ((correlation_continuous x a ha).comp continuous_snd)
    exact ((by fun_prop : Continuous (fun t : ℝ => Real.exp (t / 2))).mul hs).integrableOn_Icc
  have hc : |∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * S D x a t| ≤
      2 * (M D - 1) * W D x a := by
    have he (t : ℝ) : HasDerivAt (fun t => 2 * Real.exp (t / 2)) (Real.exp (t / 2)) t := by
      convert (((hasDerivAt_id t).div_const 2).exp.const_mul 2) using 1 <;> (try funext y) <;> (try dsimp only [id, Pi.neg_apply]) <;> ring
    calc
      _ ≤ ∫ t in Icc (0 : ℝ) D, |Real.exp (t / 2) * S D x a t| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * W D x a := by
        apply setIntegral_mono_on hSi.abs ((by fun_prop : Continuous (fun t : ℝ => Real.exp (t / 2) * W D x a)).integrableOn_Icc)
          measurableSet_Icc
        intro t ht
        rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hS t) (Real.exp_nonneg _)
      _ = _ := by
        rw [integral_mul_const, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le hD.le,
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => he t)
            ((by fun_prop : Continuous (fun t : ℝ => Real.exp (t / 2))).intervalIntegrable 0 D)]
        simp only [M, zero_div, Real.exp_zero, smul_eq_mul]
        ring
  have hb : |b D / 2 * Z D x a| ≤ 2 * B p * M D * W D x a := by
    rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hdiv : |b D| / 2 ≤ B p / 2 :=
      div_le_div_of_nonneg_right (b_bound p D hD.le) (by norm_num : (0 : ℝ) ≤ 2)
    have h := mul_le_mul hdiv hZ (abs_nonneg (Z D x a))
      (by have := B_ge_C p; linarith [p.one_le_C] : 0 ≤ B p / 2)
    nlinarith only [h]
  have htri := (abs_sub
    (2 * (∑ n ∈ primes D,
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * S D x a (Real.log n)) -
      2 * ∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * S D x a t)
    (b D / 2 * Z D x a)).trans
    (add_le_add (abs_sub (2 * (∑ n ∈ primes D,
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * S D x a (Real.log n)))
      (2 * ∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * S D x a t)) (le_refl _))
  dsimp only [V]
  calc
    _ ≤ 2 * |∑ n ∈ primes D,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n * S D x a (Real.log n)| +
        2 * |∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * S D x a t| + |b D / 2 * Z D x a| := by
      simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using htri
    _ ≤ 2 * (2 * (1 + p.C) * M D * W D x a) +
        2 * (2 * (M D - 1) * W D x a) + 2 * B p * M D * W D x a := by
      linarith only [hp, hc, hb]
    _ ≤ _ := by nlinarith only [hW]


def G (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..t, «prefix» x a u

private def primitiveRamp (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℂ :=
  ∑ i, a i * (max (t - x i) 0 : ℝ)

private lemma G_eq_ramp (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, 0 ≤ x i) (t : ℝ) (ht : 0 ≤ t) :
    G x a t = primitiveRamp x a t :=
  D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.actual_prefix_primitive_realization
    x a hx t ht

private def growingForm (D : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ u in Icc (0 : ℝ) D, ∫ v in Icc (0 : ℝ) D,
    Real.exp (|u - v| / 2) * (star (f u) * f v).re

/-- Actual compact-square Fubini, with only the diagonal singleton removed
in each slice. It identifies the growing quadratic with its causal triangle. -/
private lemma growingForm_causal (D : ℝ) (hD : 0 ≤ D)
    (f : ℝ → ℂ) (hf : Continuous f) :
    growingForm D f = 2 * ∫ u in Icc (0 : ℝ) D,
      (star (f u) * (∫ v in (0 : ℝ)..u,
        (Real.exp ((u - v) / 2) : ℂ) * f v)).re := by
  let K : ℝ → ℝ → ℝ := fun u v =>
    Real.exp (|u - v| / 2) * (star (f u) * f v).re
  let L : ℝ → ℝ → ℝ := fun u v => if v ≤ u then K u v else 0
  have hK : Continuous (Function.uncurry K) := by
    exact (by fun_prop : Continuous (fun z : ℝ × ℝ => Real.exp (|z.1 - z.2| / 2))).mul (Complex.continuous_re.comp ((hf.comp continuous_fst).star.mul
      (hf.comp continuous_snd)))
  have hsymm (u v : ℝ) : K u v = K v u := by
    dsimp [K]
    rw [abs_sub_comm]
    congr 1
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hKi : Integrable (Function.uncurry K)
      ((volume.restrict (Icc (0 : ℝ) D)).prod (volume.restrict (Icc (0 : ℝ) D))) := by
    rw [Measure.prod_restrict]
    exact hK.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hLi : Integrable (Function.uncurry L)
      ((volume.restrict (Icc (0 : ℝ) D)).prod (volume.restrict (Icc (0 : ℝ) D))) := by
    have he : Function.uncurry L =
        {z : ℝ × ℝ | z.2 ≤ z.1}.indicator (Function.uncurry K) := by rfl
    rw [he]
    exact hKi.indicator (isClosed_le continuous_snd continuous_fst).measurableSet
  have hslice (u : ℝ) : (∫ v in Icc (0 : ℝ) D, K u v) =
      (∫ v in Icc (0 : ℝ) D, L u v) + ∫ v in Icc (0 : ℝ) D, L v u := by
    have h1 : IntegrableOn (L u) (Icc 0 D) :=
      ((hK.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc).indicator
        measurableSet_Iic
    have h2 : IntegrableOn (fun v => L v u) (Icc 0 D) :=
      ((hK.comp (continuous_id.prodMk continuous_const)).integrableOn_Icc).indicator
        measurableSet_Ici
    rw [← integral_add h1 h2]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae ((volume : Measure ℝ).ae_ne u)] with v hv
    dsimp only [L]
    rcases lt_or_gt_of_ne hv with hv | hv
    · rw [if_pos hv.le, if_neg (not_le.mpr hv)]
      ring
    · rw [if_neg (not_le.mpr hv), if_pos hv.le, hsymm]
      ring
  have htri (u : ℝ) (hu : u ∈ Icc (0 : ℝ) D) :
      (∫ v in Icc (0 : ℝ) D, L u v) =
        (star (f u) * (∫ v in (0 : ℝ)..u,
          (Real.exp ((u - v) / 2) : ℂ) * f v)).re := by
    have he : L u = (Iic u).indicator (K u) := by rfl
    have hinter : Icc (0 : ℝ) D ∩ Iic u = Icc 0 u := by
      ext v
      constructor
      · rintro ⟨⟨hv0, hvD⟩, hvu⟩
        exact ⟨hv0, hvu⟩
      · rintro ⟨hv0, hvu⟩
        exact ⟨⟨hv0, hvu.trans hu.2⟩, hvu⟩
    have hi : IntegrableOn (fun v : ℝ => star (f u) *
        ((Real.exp ((u - v) / 2) : ℂ) * f v)) (Icc (0 : ℝ) u) :=
      (continuous_const.mul ((by fun_prop : Continuous (fun v : ℝ => (Real.exp ((u - v) / 2) : ℂ))).mul hf)).integrableOn_Icc
    rw [he, setIntegral_indicator measurableSet_Iic, hinter,
      intervalIntegral.integral_of_le hu.1, ← integral_Icc_eq_integral_Ioc,
      ← integral_const_mul]
    have hre := integral_re hi
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    dsimp [K]
    rw [abs_of_nonneg (by linarith [hv.2] : 0 ≤ u - v)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_im]
    ring
  have he : growingForm D f =
      2 * ∫ u in Icc (0 : ℝ) D, ∫ v in Icc (0 : ℝ) D, L u v := by
    dsimp only [growingForm]
    change (∫ u in Icc (0 : ℝ) D, ∫ v in Icc (0 : ℝ) D, K u v) = _
    simp_rw [hslice]
    have hadd := integral_add hLi.integral_prod_left hLi.integral_prod_right
    dsimp only [Function.uncurry] at hadd
    rw [hadd, ← integral_integral_swap hLi]
    ring
  rw [he]
  congr 1
  exact setIntegral_congr_fun measurableSet_Icc htri

private lemma growing_weight_row (D u : ℝ) (hu : u ∈ Icc (0 : ℝ) D) :
    (∫ v in Icc (0 : ℝ) D, Real.exp (|u - v| / 2) * g D v) =
      (M D - 1) * g D u + u * Real.exp (u / 2) +
        (D - u) * Real.exp ((D - u) / 2) := by
  let f : ℝ → ℝ := fun v => Real.exp (|u - v| / 2) * g D v
  have hf : Continuous f := by dsimp [f, g]; fun_prop
  have hl (v : ℝ) (hv : v ∈ Icc (0 : ℝ) u) :
      f v = Real.exp (u / 2) + Real.exp ((D + u) / 2) * Real.exp (-v) := by
    dsimp [f, g]
    rw [abs_of_nonneg (by linarith [hv.2] : 0 ≤ u - v), mul_add,
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  have hr (v : ℝ) (hv : v ∈ Icc u D) :
      f v = Real.exp (-u / 2) * Real.exp v + Real.exp ((D - u) / 2) := by
    dsimp [f, g]
    rw [abs_of_nonpos (by linarith [hv.1] : u - v ≤ 0), mul_add,
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  have hli : (∫ v in (0 : ℝ)..u, f v) =
      u * Real.exp (u / 2) + Real.exp ((D + u) / 2) * (1 - Real.exp (-u)) := by
    calc
      _ = ∫ v in (0 : ℝ)..u, Real.exp (u / 2) +
          Real.exp ((D + u) / 2) * Real.exp (-v) := by
        apply intervalIntegral.integral_congr
        intro v hv
        exact hl v (by simpa only [uIcc_of_le hu.1] using hv)
      _ = _ := by
        rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
          ((by fun_prop : Continuous (fun v : ℝ => Real.exp ((D + u) / 2) * Real.exp (-v))).intervalIntegrable _ _), intervalIntegral.integral_const,
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_comp_neg, integral_exp]
        simp
  have hri : (∫ v in u..D, f v) =
      Real.exp (-u / 2) * (Real.exp D - Real.exp u) +
        (D - u) * Real.exp ((D - u) / 2) := by
    calc
      _ = ∫ v in u..D, Real.exp (-u / 2) * Real.exp v +
          Real.exp ((D - u) / 2) := by
        apply intervalIntegral.integral_congr
        intro v hv
        exact hr v (by simpa only [uIcc_of_le hu.2] using hv)
      _ = _ := by
        rw [intervalIntegral.integral_add ((by fun_prop : Continuous (fun v : ℝ => Real.exp (-u / 2) * Real.exp v)).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
          integral_exp, intervalIntegral.integral_const]
        rfl
  have he1 : Real.exp ((D + u) / 2) = M D * Real.exp (u / 2) := by
    rw [M, ← Real.exp_add]; congr 1; ring
  have he2 : Real.exp ((D + u) / 2) * Real.exp (-u) = Real.exp ((D - u) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have he3 : Real.exp (-u / 2) * Real.exp D = M D * Real.exp ((D - u) / 2) := by
    rw [M, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have he4 : Real.exp (-u / 2) * Real.exp u = Real.exp (u / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hu.1.trans hu.2),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable 0 u) (hf.intervalIntegrable u D), hli, hri]
  dsimp [g]
  nlinarith only [he1, he2, he3, he4]

private lemma growingForm_upper (D : ℝ) (hD : 0 ≤ D)
    (f : ℝ → ℂ) (hf : Continuous f) :
    growingForm D f ≤ (M D + D - 1) *
      ∫ u in Icc (0 : ℝ) D, ‖f u‖ ^ 2 := by
  let k (u v : ℝ) : ℝ := Real.exp (|u - v| / 2)
  let F (u v : ℝ) : ℝ := k u v * (g D v / g D u * ‖f u‖ ^ 2)
  have hF : Continuous (Function.uncurry F) := by
    apply Continuous.mul (by dsimp [k]; fun_prop)
    exact ((by dsimp [g]; fun_prop : Continuous (fun z : ℝ × ℝ => g D z.2)).div
      (by dsimp [g]; fun_prop : Continuous (fun z : ℝ × ℝ => g D z.1))
      (fun z => (g_pos D z.1).ne')).mul ((hf.comp continuous_fst).norm.pow 2)
  have hFi : Integrable (Function.uncurry F)
      ((volume.restrict (Icc (0 : ℝ) D)).prod (volume.restrict (Icc (0 : ℝ) D))) := by
    rw [Measure.prod_restrict]
    exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hlocal (u v : ℝ) :
      2 * (k u v * (star (f u) * f v).re) ≤ F u v + F v u := by
    have h := mul_le_mul_of_nonneg_left
      (weighted_complex_pair (g D v) (g D u) (g_pos D v) (g_pos D u) (f u) (f v))
      (Real.exp_nonneg (|u - v| / 2))
    dsimp only [F, k]
    rw [abs_sub_comm v u]
    linarith only [h]
  have hK : Continuous (fun z : ℝ × ℝ =>
      2 * (k z.1 z.2 * (star (f z.1) * f z.2).re)) := by
    dsimp [k]
    fun_prop
  have hKi : Integrable (fun z : ℝ × ℝ =>
      2 * (k z.1 z.2 * (star (f z.1) * f z.2).re))
      ((volume.restrict (Icc (0 : ℝ) D)).prod (volume.restrict (Icc (0 : ℝ) D))) := by
    rw [Measure.prod_restrict]
    exact hK.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hmono := integral_mono hKi (hFi.add hFi.swap)
    (fun z => hlocal z.1 z.2)
  simp only [Pi.add_apply] at hmono
  rw [integral_add hFi hFi.swap, integral_prod _ hKi, integral_prod _ hFi,
    integral_prod _ hFi.swap] at hmono
  dsimp only [Function.uncurry, Function.comp_def, Prod.swap] at hmono
  rw [← integral_integral_swap hFi] at hmono
  have hleft : (∫ u in Icc (0 : ℝ) D, ∫ v in Icc (0 : ℝ) D,
      2 * (k u v * (star (f u) * f v).re)) = 2 * growingForm D f := by
    simp only [integral_const_mul, growingForm, k]
  rw [hleft] at hmono
  have hrow : (∫ u in Icc (0 : ℝ) D, ∫ v in Icc (0 : ℝ) D, F u v) ≤
      (M D + D - 1) * ∫ u in Icc (0 : ℝ) D, ‖f u‖ ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hFi.integral_prod_left
      (((hf.norm.pow 2).const_mul _).integrableOn_Icc) measurableSet_Icc
    intro u hu
    have hinner : (∫ v in Icc (0 : ℝ) D, F u v) =
        ((∫ v in Icc (0 : ℝ) D, k u v * g D v) / g D u) * ‖f u‖ ^ 2 := by
      dsimp only [F]
      simp_rw [div_eq_mul_inv]
      rw [← integral_mul_const, ← integral_mul_const]
      congr 1
      funext v
      ring
    dsimp only [Function.uncurry, Pi.pow_apply]
    rw [hinner]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply (div_le_iff₀ (g_pos D u)).mpr
    rw [show (∫ v in Icc (0 : ℝ) D, k u v * g D v) =
      (M D - 1) * g D u + u * Real.exp (u / 2) +
        (D - u) * Real.exp ((D - u) / 2) from growing_weight_row D u hu]
    dsimp only [g]
    nlinarith [mul_le_mul_of_nonneg_right hu.2 (Real.exp_nonneg (u / 2)),
      mul_le_mul_of_nonneg_right (show D - u ≤ D by linarith [hu.1])
        (Real.exp_nonneg ((D - u) / 2))]
  linarith only [hmono, hrow]

/-- Literal continuum identity and moment payment. G is the actual
integral primitive, and its two zero endpoints follow from the original
mass and first moment. No continuum bridge is an input. -/
theorem actual_continuum_moment_payment (D : ℝ) (hD : 0 < D)
    (q : ℕ) (hq : 1 ≤ q) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    -((M D + D + 3) / 4) *
      (D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))) * energy x a ≤ continuum D x a := by
  have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
  have hfirst : ∑ i, a i * (x i : ℂ) = 0 := by simpa using hm 1 hq
  let R := primitiveRamp x a
  have hR : Continuous R := by
    change Continuous (fun t : ℝ => ∑ i, a i * (max (t - x i) 0 : ℝ))
    fun_prop
  have hG (t : ℝ) (ht : 0 ≤ t) : G x a t = R t :=
    G_eq_ramp x a (fun i => (hx i).1) t ht
  have hid := D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.growing_primitive_identity
    D hD.le x a hx ha hfirst
  have hactual := ActualKernelPrefixPerturbation.growing_exponential_correlation_identity
    D hD.le x a hx ha
  have htriangle := growingForm_causal D hD.le R hR
  have hrewrite : (2 * ∫ t in Icc (0 : ℝ) D,
      (star (G x a t) * (∫ u in (0 : ℝ)..t,
        (Real.exp ((t - u) / 2) : ℂ) * G x a u)).re) = growingForm D R := by
    rw [htriangle]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [hG t ht.1]
    congr 2
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    dsimp only
    rw [hG u hu.1]
  have hEG : (∫ t in Icc (0 : ℝ) D, ‖G x a t‖ ^ 2) =
      ∫ t in Icc (0 : ℝ) D, ‖R t‖ ^ 2 :=
    setIntegral_congr_fun measurableSet_Icc (fun t ht => by rw [hG t ht.1])
  change G x a 0 = 0 ∧ G x a D = 0 ∧ _ at hid
  have hidentity : continuum D x a =
      -(∫ t in Icc (0 : ℝ) D, ‖R t‖ ^ 2) - growingForm D R / 4 := by
    have hi := hid.2.2
    change _ = -energy x a + (1 / 4) *
      (∫ t in Icc (0 : ℝ) D, ‖G x a t‖ ^ 2) + (1 / 16) *
        (2 * ∫ t in Icc (0 : ℝ) D,
          (star (G x a t) * (∫ u in (0 : ℝ)..t,
            (Real.exp ((t - u) / 2) : ℂ) * G x a u)).re) at hi
    rw [hEG, hrewrite] at hi
    change _ = -energy x a - (1 / 2) *
      ∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * correlation x a t at hactual
    dsimp only [continuum]
    linarith only [hi, hactual]
  have hrow := growingForm_upper D hD.le R hR
  have hgap := D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.actual_prefix_primitive_gap
    D hD q hq x a hx hm
  change (∫ t in Icc (0 : ℝ) D, ‖R t‖ ^ 2) ≤
    D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) * energy x a at hgap
  have hcoef : 0 ≤ (M D + D + 3) / 4 := by dsimp [M]; positivity
  have hpay := mul_le_mul_of_nonneg_left hgap hcoef
  rw [hidentity]
  nlinarith only [hrow, hpay]

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
