/- GID: D5/S3/Analytic/MomentOrthogonalPrimitiveGap
   generality: G
   mirror-B: D5/B/S3/Analytic/MomentOrthogonalPrimitiveGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.ShiftedLegendre, mathlib/module/Mathlib.MeasureTheory.Function.ContinuousMapDense, mathlib/module/Mathlib.Topology.ContinuousMap.Weierstrass]
   utility: none
   digest: Moment cancellation gives a quantitative complex L2 primitive gap. -/

import D5.S3.Analytic.LegendrePrimitiveGap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Complex L2 moment-orthogonal primitive energy

The finite inverse Sturm estimate in `LegendrePrimitiveGap` extends to
arbitrary complex L2 functions by corrected polynomial approximation.
The correction removes the first q Legendre coordinates and does not
increase the approximation error. A bounded linear map on the actual
L2 quotient represents the interval primitive. Passing to the limit and
then dilating the interval gives the quantitative constant D²/(4q(q+1)).
-/

noncomputable section

open Polynomial MeasureTheory Set Filter
open scoped Interval ComplexConjugate Topology ENNReal

namespace D5.S3.Analytic.MomentOrthogonalPrimitiveGap

private abbrev μ (D : ℝ) : Measure ℝ := volume.restrict (Icc 0 D)
private abbrev pv (p : ℂ[X]) (x : ℝ) : ℂ := p.eval (x : ℂ)
private abbrev E (D : ℝ) (f : ℝ → ℂ) : ℝ := ∫ x in Icc 0 D, ‖f x‖ ^ 2
private abbrev primitive (f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t in 0..x, f t

private lemma setIntegral_eq_intervalIntegral {D : ℝ} (hD : 0 ≤ D)
    (f : ℝ → ℂ) : (∫ x in Icc 0 D, f x) = ∫ x in 0..D, f x := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hD]

private lemma energy_eq_intervalIntegral {D : ℝ} (hD : 0 ≤ D)
    (f : ℝ → ℂ) : E D f = ∫ x in 0..D, ‖f x‖ ^ 2 := by
  rw [E, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hD]

private lemma polynomial_memLp (D : ℝ) (p : ℂ[X]) : MemLp (pv p) 2 (μ D) := by
  apply (memLp_two_iff_integrable_sq_norm
    (p.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable).mpr
  exact ((p.continuous.comp Complex.continuous_ofReal).norm.pow 2).integrableOn_Icc

private lemma energy_eq_norm_sq {D : ℝ} {f : ℝ → ℂ} (hf : MemLp f 2 (μ D)) :
    E D f = ‖hf.toLp f‖ ^ 2 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (hf.toLp f)
  rw [L2.inner_def] at h
  have he : ((E D f : ℝ) : ℂ) = (‖hf.toLp f‖ : ℂ) ^ 2 := by
    calc
      ((E D f : ℝ) : ℂ) = ∫ x, ((‖f x‖ ^ 2 : ℝ) : ℂ) ∂μ D :=
        (integral_ofReal (f := fun x => ‖f x‖ ^ 2)).symm
      _ = ∫ x, inner ℂ (hf.toLp f x) (hf.toLp f x) ∂μ D := by
        apply integral_congr_ae
        filter_upwards [hf.coeFn_toLp] with x hx
        rw [hx, inner_self_eq_norm_sq_to_K]
        norm_cast
      _ = _ := by convert h using 1
  exact_mod_cast he

private lemma complex_polynomial_uniform_approximation (g : ℝ → ℂ)
    (hg : ContinuousOn g (Icc (0 : ℝ) 1)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ x ∈ Icc (0 : ℝ) 1, ‖pv p x - g x‖ < ε := by
  obtain ⟨pr, hpr⟩ := exists_polynomial_near_of_continuousOn 0 1
    (fun x => (g x).re) (Complex.continuous_re.comp_continuousOn hg) (ε / 2) (by positivity)
  obtain ⟨pi, hpi⟩ := exists_polynomial_near_of_continuousOn 0 1
    (fun x => (g x).im) (Complex.continuous_im.comp_continuousOn hg) (ε / 2) (by positivity)
  let p : ℂ[X] := pr.map Complex.ofRealHom + C Complex.I * pi.map Complex.ofRealHom
  refine ⟨p, ?_⟩
  intro x hx
  have he (r : ℝ[X]) : pv (r.map Complex.ofRealHom) x = ((r.eval x : ℝ) : ℂ) := by
    simpa only [pv, Complex.ofRealHom_eq_coe] using Polynomial.eval_map_apply (p := r) Complex.ofRealHom x
  have hval : pv p x = ((pr.eval x : ℝ) : ℂ) + Complex.I * ((pi.eval x : ℝ) : ℂ) := by
    dsimp only [p, pv]
    rw [eval_add, eval_mul, eval_C]
    exact congrArg₂ (fun z w : ℂ => z + Complex.I * w) (he pr) (he pi)
  have hre : (pv p x - g x).re = pr.eval x - (g x).re := by rw [hval]; simp
  have him : (pv p x - g x).im = pi.eval x - (g x).im := by rw [hval]; simp
  have h := Complex.norm_le_abs_re_add_abs_im (pv p x - g x)
  rw [hre, him] at h
  linarith [hpr x hx, hpi x hx]

/-- Raw complex polynomial density, using real and imaginary Weierstrass
approximation only after the genuine L2-to-continuous approximation. -/
private lemma raw_polynomial_L2_approximation (A : ℝ → ℂ) (hA : MemLp A 2 (μ 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], E 1 (fun x => A x - pv p x) ≤ ε := by
  have hA' : MemLp A (ENNReal.ofReal (2 : ℝ)) (μ 1) := by simpa using hA
  obtain ⟨g, hg, hgMem⟩ := hA'.exists_boundedContinuous_integral_rpow_sub_le
    (by norm_num : (0 : ℝ) < 2) (show 0 < ε / 4 by positivity)
  have hgE : E 1 (fun x => A x - g x) ≤ ε / 4 := by
    simpa only [E, Real.rpow_two] using hg
  have hgMem' : MemLp (fun x => g x) 2 (μ 1) := by simpa using hgMem
  obtain ⟨p, hp⟩ := complex_polynomial_uniform_approximation g g.continuous.continuousOn
    (Real.sqrt ε / 2) (by positivity)
  have hgp := hgMem'.sub (polynomial_memLp 1 p)
  have hag := hA.sub hgMem'
  have hap := hA.sub (polynomial_memLp 1 p)
  have hgpInt := (memLp_two_iff_integrable_sq_norm hgp.aestronglyMeasurable).mp hgp
  have hagInt := (memLp_two_iff_integrable_sq_norm hag.aestronglyMeasurable).mp hag
  have hapInt := (memLp_two_iff_integrable_sq_norm hap.aestronglyMeasurable).mp hap
  have hgpE : E 1 (fun x => g x - pv p x) ≤ ε / 4 := by
    calc
      E 1 (fun x => g x - pv p x) ≤ ∫ _x, ε / 4 ∂μ 1 := by
        apply integral_mono_ae hgpInt (integrable_const _)
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        have hb := (hp x hx).le
        rw [norm_sub_rev] at hb
        have hs := Real.sq_sqrt hε.le
        have hsq := (sq_le_sq₀ (norm_nonneg (g x - pv p x))
          (show 0 ≤ Real.sqrt ε / 2 by positivity)).mpr hb
        change ‖g x - pv p x‖ ^ 2 ≤ ε / 4
        nlinarith
      _ = ε / 4 := by
        change (∫ _x in Icc (0 : ℝ) 1, ε / 4) = ε / 4
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
        simp
  refine ⟨p, ?_⟩
  calc
    E 1 (fun x => A x - pv p x) ≤
        2 * E 1 (fun x => A x - g x) + 2 * E 1 (fun x => g x - pv p x) := by
      change (∫ x, ‖(A - pv p) x‖ ^ 2 ∂μ 1) ≤
        2 * (∫ x, ‖(A - fun x => g x) x‖ ^ 2 ∂μ 1) +
        2 * (∫ x, ‖((fun x => g x) - pv p) x‖ ^ 2 ∂μ 1)
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add (hagInt.const_mul 2) (hgpInt.const_mul 2)]
      apply integral_mono_ae hapInt ((hagInt.const_mul 2).add (hgpInt.const_mul 2))
      filter_upwards with x
      have ht : ‖A x - pv p x‖ ≤ ‖A x - g x‖ + ‖g x - pv p x‖ := by
        calc
          ‖A x - pv p x‖ = ‖(A x - g x) + (g x - pv p x)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have hs := (sq_le_sq₀ (norm_nonneg (A x - pv p x))
        (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr ht
      change ‖A x - pv p x‖ ^ 2 ≤ 2 * ‖A x - g x‖ ^ 2 + 2 * ‖g x - pv p x‖ ^ 2
      nlinarith [sq_nonneg (‖A x - g x‖ - ‖g x - pv p x‖)]
    _ ≤ ε := by linarith

private abbrev polyLp (p : ℂ[X]) : Lp ℂ 2 (μ 1) := (polynomial_memLp 1 p).toLp (pv p)

private lemma poly_inner (p r : ℂ[X]) :
    inner ℂ (polyLp p) (polyLp r) =
      PolynomialL2Derivative.moment r (p.map (starRingEnd ℂ)) := by
  rw [L2.inner_def, PolynomialL2Derivative.moment,
    ← setIntegral_eq_intervalIntegral (by norm_num)]
  apply integral_congr_ae
  filter_upwards [(polynomial_memLp 1 p).coeFn_toLp,
    (polynomial_memLp 1 r).coeFn_toLp] with x hp hr
  rw [hp, hr, RCLike.inner_apply]
  simp only [pv, ← Polynomial.eval_map_apply (starRingEnd ℂ), Complex.conj_ofReal]

private lemma low_polynomial_inner_zero (q : ℕ) (A : ℝ → ℂ)
    (hA : MemLp A 2 (μ 1))
    (hm : ∀ r : ℕ, r < q → ∫ x in Icc (0 : ℝ) 1, (x : ℂ) ^ r * A x = 0)
    (p : ℂ[X]) (hp : p.degree < (q : WithBot ℕ)) :
    inner ℂ (polyLp p) (hA.toLp A) = 0 := by
  have hp' : (p.map (starRingEnd ℂ)).degree < (q : WithBot ℕ) :=
    Polynomial.degree_map_le.trans_lt hp
  let r := p.map (starRingEnd ℂ)
  have hmInt (n : ℕ) : Integrable (fun x : ℝ => (x : ℂ) ^ n * A x) (μ 1) :=
    IntegrableOn.continuousOn_mul
      (Complex.continuous_ofReal.pow n).continuousOn
      (hA.integrable (by norm_num)) isCompact_Icc
  calc
    inner ℂ (polyLp p) (hA.toLp A) = ∫ x, pv r x * A x ∂μ 1 := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(polynomial_memLp 1 p).coeFn_toLp, hA.coeFn_toLp] with x he hf
      rw [he, hf, RCLike.inner_apply']
      simp only [r, pv, ← Polynomial.eval_map_apply (starRingEnd ℂ), Complex.conj_ofReal]
    _ = ∫ x, ∑ n ∈ Finset.range (r.natDegree + 1),
        r.coeff n * ((x : ℂ) ^ n * A x) ∂μ 1 := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [pv, Polynomial.eval_eq_sum_range, Finset.sum_mul, mul_assoc]
    _ = ∑ n ∈ Finset.range (r.natDegree + 1),
        ∫ x, r.coeff n * ((x : ℂ) ^ n * A x) ∂μ 1 :=
      integral_finsetSum _ (fun n _ => (hmInt n).const_mul _)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      by_cases hnq : n < q
      · rw [integral_const_mul, hm n hnq, mul_zero]
      · have hc : r.coeff n = 0 :=
          (Polynomial.degree_lt_iff_coeff_zero r q).mp hp' n (by omega)
        simp [hc]

private def low (q : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ := if n < q then a n else 0
private def high (q : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ := if n < q then 0 else a n

private lemma low_degree (d q : ℕ) (a : ℕ → ℂ) :
    (PolynomialL2Derivative.expansion d (low q a)).degree < (q : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro k hk
  simp only [PolynomialL2Derivative.expansion, Polynomial.finsetSum_coeff, coeff_C_mul]
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hnq : n < q
  · have hc : (PolynomialL2Derivative.legendreC n).coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt (by
        rw [PolynomialL2Derivative.legendreC, Polynomial.degree_map_eq_of_injective
          (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective),
          Polynomial.degree_shiftedLegendre]
        exact_mod_cast (lt_of_lt_of_le hnq hk))
    rw [hc, mul_zero]
  · simp [low, hnq]

private lemma correction_nonexpansive (d q : ℕ) (a : ℕ → ℂ) (A : ℝ → ℂ)
    (hA : MemLp A 2 (μ 1))
    (hm : ∀ r : ℕ, r < q → ∫ x in Icc (0 : ℝ) 1, (x : ℂ) ^ r * A x = 0) :
    E 1 (fun x => A x - pv (PolynomialL2Derivative.expansion d (high q a)) x) ≤
      E 1 (fun x => A x - pv (PolynomialL2Derivative.expansion d a) x) := by
  let p := PolynomialL2Derivative.expansion d a
  let u := PolynomialL2Derivative.expansion d (low q a)
  let v := PolynomialL2Derivative.expansion d (high q a)
  have he : p = u + v := by
    unfold p u v PolynomialL2Derivative.expansion
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : n < q <;> simp [low, high, h]
  have heLp : polyLp p = polyLp u + polyLp v := by
    apply Lp.ext
    filter_upwards [(polynomial_memLp 1 p).coeFn_toLp,
      (polynomial_memLp 1 u).coeFn_toLp, (polynomial_memLp 1 v).coeFn_toLp,
      Lp.coeFn_add (polyLp u) (polyLp v)] with x hp hu hv huv
    rw [hp, huv]
    change pv p x = polyLp u x + polyLp v x
    rw [hu, hv]
    simp only [pv, he, eval_add]
  have huv : inner ℂ (polyLp u) (polyLp v) = 0 := by
    rw [poly_inner, LegendrePrimitiveGap.mixed_expansion]
    apply Finset.sum_eq_zero
    intro n hn
    by_cases h : n < q <;> simp [low, high, h]
  have huA : inner ℂ (polyLp u) (hA.toLp A) = 0 :=
    low_polynomial_inner_zero q A hA hm u (low_degree d q a)
  have horth : inner ℂ (polyLp u) (polyLp v - hA.toLp A) = 0 := by
    rw [inner_sub_right, huv, huA, sub_self]
  have hpy := @norm_add_sq ℂ (Lp ℂ 2 (μ 1)) _ _ _ (polyLp u) (polyLp v - hA.toLp A)
  rw [horth] at hpy
  have hs : polyLp u + (polyLp v - hA.toLp A) = polyLp p - hA.toLp A := by
    rw [heLp]
    abel
  rw [hs] at hpy
  change E 1 (A - pv v) ≤ E 1 (A - pv p)
  rw [energy_eq_norm_sq (hA.sub (polynomial_memLp 1 v)),
    energy_eq_norm_sq (hA.sub (polynomial_memLp 1 p)),
    MemLp.toLp_sub hA (polynomial_memLp 1 v), MemLp.toLp_sub hA (polynomial_memLp 1 p)]
  have hh : ‖polyLp v - hA.toLp A‖ ^ 2 ≤ ‖polyLp p - hA.toLp A‖ ^ 2 := by
    simp only [map_zero, mul_zero, add_zero] at hpy
    nlinarith [sq_nonneg ‖polyLp u‖]
  simpa only [norm_sub_rev] using hh

/-- Polynomial L2 density after subtracting exactly the first q Legendre
coefficients. The limit is in the actual Lp quotient, not pointwise. -/
private lemma corrected_polynomial_approximation (q : ℕ) (hq : 1 ≤ q)
    (A : ℝ → ℂ) (hA : MemLp A 2 (μ 1))
    (hm : ∀ r : ℕ, r < q → ∫ x in Icc (0 : ℝ) 1, (x : ℂ) ^ r * A x = 0) :
    ∃ (d : ℕ → ℕ) (a : ℕ → ℕ → ℂ),
      (∀ j n, n < q → a j n = 0) ∧
      Tendsto (fun j => (polynomial_memLp 1 (PolynomialL2Derivative.expansion (d j) (a j))).toLp
        (pv (PolynomialL2Derivative.expansion (d j) (a j)))) atTop (𝓝 (hA.toLp A)) := by
  classical
  have hexp (p : ℂ[X]) : ∃ a : ℕ → ℂ,
      PolynomialL2Derivative.expansion (max q (p.natDegree + 1)) a = p := by
    apply PolynomialL2Derivative.exists_expansion
    exact Polynomial.degree_le_natDegree.trans_lt
      (by exact_mod_cast (Nat.lt_of_lt_of_le (Nat.lt_succ_self p.natDegree)
        (le_max_right q (p.natDegree + 1))))
  have hraw (j : ℕ) : ∃ p : ℂ[X],
      E 1 (fun x => A x - pv p x) ≤ (1 / ((j : ℝ) + 1)) ^ 2 :=
    raw_polynomial_L2_approximation A hA _ (by positivity)
  choose p hp using hraw
  choose a ha using fun j => hexp (p j)
  let d (j : ℕ) := max q ((p j).natDegree + 1)
  refine ⟨d, fun j => high q (a j), ?_, ?_⟩
  · intro j n hn
    simp [high, hn]
  · rw [tendsto_iff_dist_tendsto_zero]
    have hbound (j : ℕ) :
        dist (polyLp (PolynomialL2Derivative.expansion (d j) (high q (a j))))
          (hA.toLp A) ≤ 1 / ((j : ℝ) + 1) := by
      have h := (correction_nonexpansive (d j) q (a j) A hA hm).trans (by
        simpa only [d, ha j] using hp j)
      change E 1 (A - pv (PolynomialL2Derivative.expansion (d j) (high q (a j)))) ≤ _ at h
      rw [energy_eq_norm_sq (hA.sub (polynomial_memLp 1 _)),
        MemLp.toLp_sub hA (polynomial_memLp 1 _)] at h
      rw [dist_eq_norm, norm_sub_rev]
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h
    exact squeeze_zero (fun j => dist_nonneg) hbound
      tendsto_one_div_add_atTop_nhds_zero_nat

/-- Boundedness of the actual indefinite integral on L2([0,1]).
The primitive is defined for all real x; only its restriction is measured. -/
private lemma primitive_L2_continuity :
    ∃ T : Lp ℂ 2 (μ 1) →L[ℂ] Lp ℂ 2 (μ 1),
      ∀ (f : ℝ → ℂ) (hf : MemLp f 2 (μ 1)),
        ∃ hV : MemLp (primitive f) 2 (μ 1),
          T (hf.toLp f) = hV.toLp (primitive f) := by
  classical
  have hsub {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : Ioc (0 : ℝ) x ⊆ Icc (0 : ℝ) 1 :=
    fun t ht => ⟨ht.1.le, ht.2.trans hx.2⟩
  have hcongr {f g : ℝ → ℂ} (hfg : f =ᵐ[μ 1] g) {x : ℝ}
      (hx : x ∈ Icc (0 : ℝ) 1) : primitive f x = primitive g x := by
    simp only [primitive, intervalIntegral.integral_of_le hx.1]
    exact integral_congr_ae (hfg.filter_mono (ae_mono (Measure.restrict_mono (hsub hx) le_rfl)))
  have hint (f : Lp ℂ 2 (μ 1)) : IntervalIntegrable (fun x => f x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr
      ((Lp.memLp f).integrable (by norm_num))
  have hcont (f : Lp ℂ 2 (μ 1)) : ContinuousOn (primitive (fun x => f x)) (Icc (0 : ℝ) 1) := by
    have hi : IntegrableOn (fun x => f x) (uIcc (0 : ℝ) 1) := by
      change Integrable (fun x : ℝ => f x) (volume.restrict (uIcc (0 : ℝ) 1))
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact (Lp.memLp f).integrable (by norm_num)
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), primitive] using
      intervalIntegral.continuousOn_primitive_interval hi
  have hbound (f : Lp ℂ 2 (μ 1)) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
      ‖primitive (fun x => f x) x‖ ≤ ‖f‖ := by
    let I : Lp ℂ 2 (μ 1) := indicatorConstLp (s := Ioc (0 : ℝ) x) 2 measurableSet_Ioc (by finiteness) (1 : ℂ)
    have hI : (inner ℂ I f) = primitive (fun x => f x) x := by
      rw [L2.inner_indicatorConstLp_one]
      change (∫ t, f t ∂(volume.restrict (Icc (0 : ℝ) 1)).restrict (Ioc 0 x)) = _
      rw [Measure.restrict_restrict_of_subset (hsub hx)]
      exact (intervalIntegral.integral_of_le hx.1).symm
    have hμx : (μ 1).real (Ioc 0 x) = x := by
      simp only [μ, Measure.real, Measure.restrict_apply measurableSet_Ioc,
        inter_eq_left.mpr (hsub hx), Real.volume_Ioc, sub_zero,
        ENNReal.toReal_ofReal hx.1]
    have hIn : ‖I‖ ≤ 1 := by
      change ‖indicatorConstLp (s := Ioc (0 : ℝ) x) 2 measurableSet_Ioc (by finiteness) (1 : ℂ)‖ ≤ 1
      rw [norm_indicatorConstLp (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞), hμx]
      simpa only [norm_one, one_mul, ENNReal.toReal_ofNat] using
        (Real.rpow_le_one hx.1 hx.2 (by norm_num : (0 : ℝ) ≤ 1 / 2))
    rw [← hI]
    exact (norm_inner_le_norm I f).trans (by nlinarith [norm_nonneg f])
  have hmem (f : Lp ℂ 2 (μ 1)) : MemLp (primitive (fun x => f x)) 2 (μ 1) := by
    apply MemLp.of_bound ((hcont f).aestronglyMeasurable measurableSet_Icc) ‖f‖
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hbound f hx
  let T₀ : Lp ℂ 2 (μ 1) →ₗ[ℂ] Lp ℂ 2 (μ 1) := {
    toFun := fun f => (hmem f).toLp (primitive (fun x => f x))
    map_add' := by
      intro f g
      apply Lp.ext
      filter_upwards [(hmem (f + g)).coeFn_toLp,
        Lp.coeFn_add ((hmem f).toLp _) ((hmem g).toLp _),
        (hmem f).coeFn_toLp, (hmem g).coeFn_toLp,
        ae_restrict_mem measurableSet_Icc] with x hfg hadd hf hg hx
      rw [hfg, hadd]
      change primitive (fun t => (f + g) t) x =
        (hmem f).toLp _ x + (hmem g).toLp _ x
      rw [hf, hg]
      calc
        primitive (fun t => (f + g) t) x = primitive (fun t => f t + g t) x :=
          hcongr (Lp.coeFn_add f g) hx
        _ = _ := by
          apply intervalIntegral.integral_add
          · exact (hint f).mono_set (by
              rw [uIcc_of_le hx.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
              exact Icc_subset_Icc le_rfl hx.2)
          · exact (hint g).mono_set (by
              rw [uIcc_of_le hx.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
              exact Icc_subset_Icc le_rfl hx.2)
    map_smul' := by
      intro c f
      apply Lp.ext
      filter_upwards [(hmem (c • f)).coeFn_toLp,
        Lp.coeFn_smul c ((hmem f).toLp _), (hmem f).coeFn_toLp,
        ae_restrict_mem measurableSet_Icc] with x hcf hsmul hf hx
      rw [hcf]
      change primitive (fun t => (c • f) t) x = (c • (hmem f).toLp _) x
      rw [hsmul]
      change primitive (fun t => (c • f) t) x = c • ((hmem f).toLp _ x)
      rw [hf]
      calc
        primitive (fun t => (c • f) t) x = primitive (fun t => c • f t) x :=
          hcongr (Lp.coeFn_smul c f) hx
        _ = _ := intervalIntegral.integral_smul c _ }
  have hnorm (f : Lp ℂ 2 (μ 1)) : ‖T₀ f‖ ≤ 1 * ‖f‖ := by
    have h := Lp.norm_le_of_ae_bound (f := T₀ f) (norm_nonneg f) (by
      filter_upwards [(hmem f).coeFn_toLp, ae_restrict_mem measurableSet_Icc] with x he hx
      rw [show T₀ f x = primitive (fun t => f t) x from he]
      exact hbound f hx)
    simpa only [μ, measureUnivNNReal, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      ENNReal.toNNReal_one, NNReal.coe_one, Real.one_rpow] using h
  let T := T₀.mkContinuous 1 hnorm
  refine ⟨T, ?_⟩
  intro f hf
  have he : primitive (fun t => hf.toLp f t) =ᵐ[μ 1] primitive f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hcongr hf.coeFn_toLp hx
  have hV : MemLp (primitive f) 2 (μ 1) := (hmem (hf.toLp f)).ae_eq he
  refine ⟨hV, ?_⟩
  exact MemLp.toLp_congr (hmem (hf.toLp f)) hV he

private lemma unit_primitive_gap (q : ℕ) (hq : 1 ≤ q) (A : ℝ → ℂ)
    (hA : MemLp A 2 (μ 1))
    (hm : ∀ r : ℕ, r < q → ∫ x in Icc (0 : ℝ) 1, (x : ℂ) ^ r * A x = 0) :
    E 1 (primitive A) ≤ 1 / (4 * (q : ℝ) * ((q : ℝ) + 1)) * E 1 A := by
  obtain ⟨d, a, ha, hlim⟩ := corrected_polynomial_approximation q hq A hA hm
  obtain ⟨T, hT⟩ := primitive_L2_continuity
  obtain ⟨hV, hVA⟩ := hT A hA
  let p (j : ℕ) := PolynomialL2Derivative.expansion (d j) (a j)
  have hlimV := T.continuous.continuousAt.tendsto.comp hlim
  have hleft : Tendsto (fun j => E 1 (primitive (pv (p j)))) atTop
      (𝓝 (E 1 (primitive A))) := by
    have he (j : ℕ) : E 1 (primitive (pv (p j))) =
        ‖T ((polynomial_memLp 1 (p j)).toLp (pv (p j)))‖ ^ 2 := by
      obtain ⟨hW, hWj⟩ := hT (pv (p j)) (polynomial_memLp 1 (p j))
      rw [energy_eq_norm_sq hW, ← hWj]
    simp_rw [he]
    rw [energy_eq_norm_sq hV, ← hVA]
    exact hlimV.norm.pow 2
  have hright : Tendsto (fun j =>
      (1 / (4 * (q : ℝ) * ((q : ℝ) + 1))) * E 1 (pv (p j))) atTop
      (𝓝 ((1 / (4 * (q : ℝ) * ((q : ℝ) + 1))) * E 1 A)) := by
    have he (j : ℕ) : E 1 (pv (p j)) = ‖(polynomial_memLp 1 (p j)).toLp (pv (p j))‖ ^ 2 :=
      energy_eq_norm_sq (polynomial_memLp 1 (p j))
    simp_rw [he, energy_eq_norm_sq hA]
    exact tendsto_const_nhds.mul (hlim.norm.pow 2)
  exact le_of_tendsto_of_tendsto' hleft hright
    (fun j => LegendrePrimitiveGap.complex_legendre_primitive_gap (d j) q hq (a j) (ha j))

/-- Dilation of the merely L2 input, its moments and its actual primitive.
The energy factors are D^{-1} and D^{-3}; these are essential to D^2. -/
private lemma dilation_data (D : ℝ) (hD : 0 < D) (q : ℕ) (A : ℝ → ℂ)
    (hA : MemLp A 2 (μ D))
    (hm : ∀ r : ℕ, r < q → ∫ x in Icc 0 D, (x : ℂ) ^ r * A x = 0) :
    let B : ℝ → ℂ := fun t => A (D * t)
    MemLp B 2 (μ 1) ∧
      (∀ r : ℕ, r < q → ∫ t in Icc (0 : ℝ) 1, (t : ℂ) ^ r * B t = 0) ∧
      E 1 B = D⁻¹ * E D A ∧
      E 1 (primitive B) = (D ^ 3)⁻¹ * E D (primitive A) := by
  dsimp only
  have hD0 : D ≠ 0 := hD.ne'
  have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD0
  have hi : IntervalIntegrable A volume 0 D :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hD.le).mpr
      (hA.integrable (by norm_num))
  have hiB : IntervalIntegrable (fun t => A (D * t)) volume 0 1 := by
    simpa only [zero_div, div_self hD0] using hi.comp_mul_left (c := D)
  have hs : IntervalIntegrable (fun x => ‖A x‖ ^ 2) volume 0 D :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hD.le).mpr
      ((memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).mp hA)
  have hsB : IntervalIntegrable (fun t => ‖A (D * t)‖ ^ 2) volume 0 1 := by
    simpa only [zero_div, div_self hD0] using hs.comp_mul_left (c := D)
  have hiBc : Integrable (fun t => A (D * t)) (μ 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hiB
  refine ⟨(memLp_two_iff_integrable_sq_norm hiBc.aestronglyMeasurable).mpr
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hsB),
    ?_, ?_, ?_⟩
  · intro r hr
    rw [setIntegral_eq_intervalIntegral (by norm_num)]
    have h := intervalIntegral.integral_comp_mul_left
      (a := (0 : ℝ)) (b := (1 : ℝ)) (fun x => (x : ℂ) ^ r * A x) hD0
    simp only [mul_zero, mul_one, Complex.ofReal_mul, mul_pow, mul_assoc,
      intervalIntegral.integral_const_mul] at h
    rw [← setIntegral_eq_intervalIntegral hD.le, hm r hr] at h
    simp only [smul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero r hDc)
  · have h := intervalIntegral.integral_comp_mul_left
      (a := (0 : ℝ)) (b := (1 : ℝ)) (fun x => ‖A x‖ ^ 2) hD0
    simpa only [energy_eq_intervalIntegral (by norm_num : (0 : ℝ) ≤ 1),
      energy_eq_intervalIntegral hD.le, mul_zero, mul_one, smul_eq_mul] using h
  · have hp (t : ℝ) : primitive (fun u => A (D * u)) t =
        (D : ℂ)⁻¹ * primitive A (D * t) := by
      have h := intervalIntegral.integral_comp_mul_left
        (a := (0 : ℝ)) (b := t) A hD0
      simpa only [primitive, mul_zero, Complex.real_smul, Complex.ofReal_inv] using h
    have he : E 1 (fun t => primitive A (D * t)) = D⁻¹ * E D (primitive A) := by
      have h := intervalIntegral.integral_comp_mul_left
        (a := (0 : ℝ)) (b := (1 : ℝ)) (fun x => ‖primitive A x‖ ^ 2) hD0
      simpa only [energy_eq_intervalIntegral (by norm_num : (0 : ℝ) ≤ 1),
        energy_eq_intervalIntegral hD.le, mul_zero, mul_one, smul_eq_mul] using h
    calc
      E 1 (primitive (fun t => A (D * t))) = D⁻¹ ^ 2 *
          E 1 (fun t => primitive A (D * t)) := by
        simp only [E, hp, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hD, mul_pow, integral_const_mul]
      _ = (D ^ 3)⁻¹ * E D (primitive A) := by rw [he]; ring

/-- For every D>0, q≥1 and arbitrary complex L2 function on [0,D], vanishing
moments below q give the original quantitative primitive bound. -/
theorem complex_L2_moment_primitive_gap
    (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q) (A : ℝ → ℂ)
    (hA : MemLp A 2 (volume.restrict (Icc 0 D)))
    (hm : ∀ r : ℕ, r < q → ∫ x in Icc 0 D, (x : ℂ) ^ r * A x = 0) :
    (∫ x in Icc 0 D, ‖∫ t in (0 : ℝ)..x, A t‖ ^ 2) ≤
      D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) * (∫ x in Icc 0 D, ‖A x‖ ^ 2) := by
  obtain ⟨hB, hmB, heB, heV⟩ := dilation_data D hD q A hA hm
  have hu := unit_primitive_gap q hq (fun t => A (D * t)) hB hmB
  rw [heB, heV] at hu
  have hp : 0 < D ^ 3 := pow_pos hD 3
  have hD0 : D ≠ 0 := hD.ne'
  have hq0 : (q : ℝ) ≠ 0 := by
    have : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    exact this.ne'
  have hq1 : (q : ℝ) + 1 ≠ 0 := by positivity
  calc
    E D (primitive A) = D ^ 3 * ((D ^ 3)⁻¹ * E D (primitive A)) := by
      field_simp [hD0]
    _ ≤ D ^ 3 * ((1 / (4 * (q : ℝ) * ((q : ℝ) + 1))) * (D⁻¹ * E D A)) :=
      mul_le_mul_of_nonneg_left hu hp.le
    _ = D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) * E D A := by
      field_simp [hD0, hq0, hq1]

end D5.S3.Analytic.MomentOrthogonalPrimitiveGap
