/- GID: D5/S3/Analytic/Interpolation/FiniteMomentCorrelation
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/FiniteMomentCorrelation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.ContinuousMap.Weierstrass, mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus]
   utility: none
   digest: Uniform cancellation of continuously weighted atomic prefix correlations under sufficiently many vanishing moments. -/

import D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
import D5.S3.Analytic.Entire.ExponentialPolynomial
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
On a fixed positive window, vanishing sufficiently many atomic moments makes
any continuous weighted prefix correlation arbitrarily small relative to the
prefix energy. The moment order precedes the entire finite atomic family.

The algebraic core is the exact identity
  integral p(s) max(d-s,0) ds = Q(d)-Q(-D)-(d+D)Q'(-D),
where Q''=p and the integral is over [-D,D]. All scalars here are complex.
The right side is a polynomial in d. Composing it with X to x(i)-X and using
the original moments annihilates each inner atomic sum. This keeps the actual
orientation x(i)-x(j) and never conjugates the wrong factor.

Only finite sums pass through integrals; no product-integral theorem, Fourier
transform, distribution, separation hypothesis or cardinality bound is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u
open MeasureTheory Set
open scoped BigOperators Polynomial
open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy

namespace D5.S3.Analytic.Interpolation.FiniteMomentCorrelation

/-- FTC with an explicit primitive, including the endpoints d=-D and d=D. -/
private lemma polynomial_hinge_integral (p q : ℂ[X])
    (hq : q.derivative.derivative = p) (D d : ℝ)
    (hD : 0 ≤ D) (hd : |d| ≤ D) :
    (∫ s in Icc (-D) D,
      p.eval (s : ℂ) * ((max (d - s) 0 : ℝ) : ℂ)) =
      q.eval (d : ℂ) - q.eval (-D : ℂ) -
        ((d : ℂ) + (D : ℂ)) * q.derivative.eval (-D : ℂ) := by
  have hbounds : -D ≤ d ∧ d ≤ D := abs_le.mp hd
  let f : ℝ → ℂ := fun s =>
    p.eval (s : ℂ) * ((max (d - s) 0 : ℝ) : ℂ)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hleft : (∫ s in (-D)..d, f s) =
      ∫ s in (-D)..d, p.eval (s : ℂ) * ((d : ℂ) - (s : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hbounds.1] at hs
    dsimp only [f]
    rw [max_eq_left (by linarith [hs.2] : 0 ≤ d - s), Complex.ofReal_sub]
  have hright : (∫ s in d..D, f s) = 0 := by
    calc
      _ = ∫ _s in d..D, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hbounds.2] at hs
        dsimp only [f]
        rw [max_eq_right (by linarith [hs.1] : d - s ≤ 0)]
        simp
      _ = 0 := by simp
  have hprimitive :
      (∫ s in (-D)..d, p.eval (s : ℂ) * ((d : ℂ) - (s : ℂ))) =
        q.eval (d : ℂ) - q.eval (-D : ℂ) -
          ((d : ℂ) + (D : ℂ)) * q.derivative.eval (-D : ℂ) := by
    let G : ℝ → ℂ := fun s =>
      ((d : ℂ) - (s : ℂ)) * q.derivative.eval (s : ℂ) + q.eval (s : ℂ)
    have hFTC :
        (∫ s in (-D)..d, p.eval (s : ℂ) * ((d : ℂ) - (s : ℂ))) = G d - G (-D) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro s _
        have hlinear : HasDerivAt (fun y : ℝ => (d : ℂ) - (y : ℂ)) (-1) s := by
          simpa using ((hasDerivAt_const s (d : ℝ)).sub (hasDerivAt_id s)).ofReal_comp
        have hp' : HasDerivAt (fun y : ℝ => q.derivative.eval (y : ℂ))
            (p.eval (s : ℂ)) s := by
          simpa only [hq] using (q.derivative.hasDerivAt (s : ℂ)).comp_ofReal
        have hq' := (q.hasDerivAt (s : ℂ)).comp_ofReal
        convert (hlinear.mul hp').add hq' using 1 <;> ring
      · exact ((p.continuous.comp Complex.continuous_ofReal).mul
          (by fun_prop : Continuous (fun s : ℝ => (d : ℂ) - (s : ℂ)))).intervalIntegrable (-D) d
    rw [hFTC]
    dsimp [G]
    push_cast
    ring
  change (∫ s in Icc (-D) D, f s) = _
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -D ≤ D),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (-D) d) (hf.intervalIntegrable d D),
    hleft, hright, add_zero, hprimitive]

/-- The window integral is represented by one polynomial, before any atoms
are selected. The extra affine terms are retained exactly. -/
private lemma polynomial_hinge_window (p : ℂ[X]) (D : ℝ) (hD : 0 ≤ D) :
    ∃ R : ℂ[X], ∀ d : ℝ, |d| ≤ D →
      (∫ s in Icc (-D) D,
        p.eval (s : ℂ) * ((max (d - s) 0 : ℝ) : ℂ)) = R.eval (d : ℂ) := by
  obtain ⟨r, hr⟩ := D5.S3.Analytic.Entire.exists_polynomial_primitive p
  obtain ⟨q, hq⟩ := D5.S3.Analytic.Entire.exists_polynomial_primitive r
  have hqq : q.derivative.derivative = p := by rw [hq, hr]
  refine ⟨q - Polynomial.C (q.eval (-D : ℂ)) -
    (Polynomial.X + Polynomial.C (D : ℂ)) *
      Polynomial.C (q.derivative.eval (-D : ℂ)), ?_⟩
  intro d hd
  rw [polynomial_hinge_integral p q hqq D d hD hd]
  simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_add, Polynomial.eval_X]

/-- Moments annihilate every polynomial below their order. -/
private lemma moments_polynomial {I : Type u} [Fintype I]
    (x : I → ℝ) (a : I → ℂ) (N : ℕ)
    (hm : ∀ r : ℕ, r < N → ∑ i, a i * (x i : ℂ) ^ r = 0)
    (p : ℂ[X]) (hp : p.natDegree < N) :
    (∑ i, a i * p.eval (x i : ℂ)) = 0 := by
  classical
  simp_rw [Polynomial.eval_eq_sum_range' hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro r hr
  calc
    (∑ i, a i * (p.coeff r * (x i : ℂ) ^ r)) =
        p.coeff r * (∑ i, a i * (x i : ℂ) ^ r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [hm r (Finset.mem_range.mp hr), mul_zero]

/-- Public owner bridge, written in the direction used by the new proof. -/
private lemma correlation_eq_hinge {I : Type u} [Fintype I]
    (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0) (s : ℝ) :
    (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v) =
      -(∑ i, ∑ j, star (a i) * a j * ((max (x i - x j - s) 0 : ℝ) : ℂ)) := by
  have h := (shifted_hinge_prefix_energy x a ha s).2.2.1
  simpa only [neg_neg] using congrArg Neg.neg h.symm

/-- All polynomially weighted correlations vanish once the window polynomial
is annihilated. Only the j moments are used; star(a i) remains untouched. -/
private lemma polynomial_correlation_zero {I : Type u} [Fintype I]
    (x : I → ℝ) (a : I → ℂ) (D : ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (p R : ℂ[X])
    (hR : ∀ d : ℝ, |d| ≤ D →
      (∫ s in Icc (-D) D,
        p.eval (s : ℂ) * ((max (d - s) 0 : ℝ) : ℂ)) = R.eval (d : ℂ))
    (hm : ∀ r : ℕ, r < R.natDegree + 1 → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    (∫ s in Icc (-D) D, p.eval (s : ℂ) *
      (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v)) = 0 := by
  classical
  have ha : ∑ i, a i = 0 := by
    simpa only [pow_zero, mul_one] using hm 0 (by omega)
  have hd (i j : I) : |x i - x j| ≤ D := by
    exact abs_le.mpr ⟨by linarith [(hx i).1, (hx j).2],
      by linarith [(hx i).2, (hx j).1]⟩
  have hrow (i : I) : (∑ j, a j * R.eval ((x i - x j : ℝ) : ℂ)) = 0 := by
    let T : ℂ[X] := Polynomial.C (x i : ℂ) - Polynomial.X
    have hT : T.natDegree ≤ 1 := by
      dsimp [T]
      simpa only [Polynomial.natDegree_C, Polynomial.natDegree_X,
        max_eq_right (Nat.zero_le 1)] using
        (Polynomial.natDegree_sub_le (Polynomial.C (x i : ℂ)) Polynomial.X)
    have hcomp : (R.comp T).natDegree < R.natDegree + 1 := by
      calc
        (R.comp T).natDegree ≤ R.natDegree * T.natDegree := Polynomial.natDegree_comp_le
        _ ≤ R.natDegree * 1 := Nat.mul_le_mul_left _ hT
        _ < R.natDegree + 1 := by omega
    have h := moments_polynomial x a (R.natDegree + 1) hm (R.comp T) hcomp
    simpa only [T, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_X, Complex.ofReal_sub] using h
  have hdouble : (∑ i, ∑ j, star (a i) * a j *
      R.eval ((x i - x j : ℝ) : ℂ)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    calc
      _ = star (a i) * (∑ j, a j * R.eval ((x i - x j : ℝ) : ℂ)) := by
        simp only [Finset.mul_sum, mul_assoc]
      _ = 0 := by rw [hrow i, mul_zero]
  have hi (i j : I) : IntegrableOn (fun s : ℝ => star (a i) * a j *
      (p.eval (s : ℂ) * ((max (x i - x j - s) 0 : ℝ) : ℂ))) (Icc (-D) D) :=
    (by fun_prop : Continuous (fun s : ℝ => star (a i) * a j *
      (p.eval (s : ℂ) * ((max (x i - x j - s) 0 : ℝ) : ℂ)))).integrableOn_Icc
  have hswap :
      (∫ s in Icc (-D) D, p.eval (s : ℂ) *
        (∑ i, ∑ j, star (a i) * a j * ((max (x i - x j - s) 0 : ℝ) : ℂ))) =
      ∑ i, ∑ j, star (a i) * a j * R.eval ((x i - x j : ℝ) : ℂ) := by
    calc
      _ = ∫ s in Icc (-D) D, ∑ i, ∑ j, star (a i) * a j *
          (p.eval (s : ℂ) * ((max (x i - x j - s) 0 : ℝ) : ℂ)) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun s => by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring)
      _ = ∑ i, ∑ j, ∫ s in Icc (-D) D, star (a i) * a j *
          (p.eval (s : ℂ) * ((max (x i - x j - s) 0 : ℝ) : ℂ)) := by
        rw [integral_finsetSum _ (fun i _ =>
          integrable_finsetSum _ (fun j _ => hi i j))]
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum _ (fun j _ => hi i j)]
      _ = _ := by
        simp only [integral_const_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hR (x i - x j) (hd i j)]
  calc
    _ = -(∫ s in Icc (-D) D, p.eval (s : ℂ) *
        (∑ i, ∑ j, star (a i) * a j * ((max (x i - x j - s) 0 : ℝ) : ℂ))) := by
      simp_rw [correlation_eq_hinge x a ha, mul_neg]
      rw [integral_neg]
    _ = 0 := by rw [hswap, hdouble, neg_zero]

/-- Real and imaginary Weierstrass approximations are combined in C[X]. -/
private lemma complex_polynomial_approximation (D : ℝ) (w : ℝ → ℂ)
    (hw : ContinuousOn w (Icc (-D) D)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : ℂ[X], ∀ s ∈ Icc (-D) D, ‖p.eval (s : ℂ) - w s‖ < δ := by
  have hre : ContinuousOn (fun s => (w s).re) (Icc (-D) D) :=
    Complex.continuous_re.comp_continuousOn hw
  have him : ContinuousOn (fun s => (w s).im) (Icc (-D) D) :=
    Complex.continuous_im.comp_continuousOn hw
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-D) D
    (fun s => (w s).re) hre (δ / 2) (by positivity)
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn (-D) D
    (fun s => (w s).im) him (δ / 2) (by positivity)
  let P : ℂ[X] := p.map Complex.ofRealHom +
    Polynomial.C Complex.I * q.map Complex.ofRealHom
  have hcast (r : ℝ[X]) (s : ℝ) :
      (r.map Complex.ofRealHom).eval (s : ℂ) = ((r.eval s : ℝ) : ℂ) :=
    Polynomial.eval_map_apply Complex.ofRealHom s
  refine ⟨P, ?_⟩
  intro s hs
  have hreal : (P.eval (s : ℂ) - w s).re = p.eval s - (w s).re := by
    simp [P, hcast]
  have himag : (P.eval (s : ℂ) - w s).im = q.eval s - (w s).im := by
    simp [P, hcast]
  calc
    ‖P.eval (s : ℂ) - w s‖ ≤
        |(P.eval (s : ℂ) - w s).re| + |(P.eval (s : ℂ) - w s).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ < δ := by rw [hreal, himag]; linarith [hp s hs, hq s hs]

/-- For each positive window, continuous complex weight and positive tolerance,
one moment order works for every finite atomic family in the entire universe.
No distinctness, ordering, nonemptiness or coefficient bound is assumed. -/
theorem finite_moment_correlation (D : ℝ) (hD : 0 < D)
    (w : ℝ → ℂ) (hw : ContinuousOn w (Icc (-D) D))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ {I : Type u} [Fintype I] (x : I → ℝ) (a : I → ℂ)
        (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
        (hm : ∀ r : ℕ, r < N → ∑ i, a i * (x i : ℂ) ^ r = 0),
        let F := «prefix» x a
        let E : ℝ := ∫ v : ℝ, ‖F v‖ ^ 2
        let C : ℝ → ℂ := fun s => ∫ v : ℝ, star (F (v + s)) * F v
        ‖∫ s in Icc (-D) D, w s * C s‖ ≤ ε * E := by
  classical
  let δ : ℝ := ε / (2 * D)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p, hp⟩ := complex_polynomial_approximation D w hw δ hδ
  obtain ⟨R, hR⟩ := polynomial_hinge_window p D hD.le
  refine ⟨R.natDegree + 1, by omega, ?_⟩
  intro I inst x a hx hm
  dsimp only
  let E : ℝ := ∫ v : ℝ, ‖«prefix» x a v‖ ^ 2
  let C : ℝ → ℂ := fun s =>
    ∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v
  change ‖∫ s in Icc (-D) D, w s * C s‖ ≤ ε * E
  have ha : ∑ i, a i = 0 := by
    simpa only [pow_zero, mul_one] using hm 0 (by omega)
  have hCeq : C = fun s =>
      -(∑ i, ∑ j, star (a i) * a j * ((max (x i - x j - s) 0 : ℝ) : ℂ)) := by
    funext s
    exact correlation_eq_hinge x a ha s
  have hC : Continuous C := by rw [hCeq]; fun_prop
  have hCb (s : ℝ) : ‖C s‖ ≤ E := by
    have h := shifted_hinge_prefix_energy x a ha s
    have hh := h.2.2.2
    rw [h.2.2.1, norm_neg] at hh
    exact hh
  have hpoly : (∫ s in Icc (-D) D, p.eval (s : ℂ) * C s) = 0 :=
    polynomial_correlation_zero x a D hx p R hR hm
  have hiw : IntegrableOn (fun s => w s * C s) (Icc (-D) D) :=
    (hw.mul hC.continuousOn).integrableOn_Icc
  have hip : IntegrableOn (fun s : ℝ => p.eval (s : ℂ) * C s) (Icc (-D) D) :=
    ((p.continuous.comp Complex.continuous_ofReal).mul hC).integrableOn_Icc
  have hrem : (∫ s in Icc (-D) D, (w s - p.eval (s : ℂ)) * C s) =
      ∫ s in Icc (-D) D, w s * C s := by
    simp_rw [sub_mul]
    rw [integral_sub hiw hip, hpoly, sub_zero]
  rw [← hrem]
  calc
    ‖∫ s in Icc (-D) D, (w s - p.eval (s : ℂ)) * C s‖ ≤
        (δ * E) * volume.real (Icc (-D) D) := by
      apply norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
      intro s hs
      rw [norm_mul]
      have herr : ‖w s - p.eval (s : ℂ)‖ ≤ δ := by
        rw [norm_sub_rev]
        exact (hp s hs).le
      exact mul_le_mul herr (hCb s) (norm_nonneg _) hδ.le
    _ = ε * E := by
      rw [Real.volume_real_Icc_of_le (by linarith : -D ≤ D)]
      dsimp [δ]
      field_simp [hD.ne'] <;> ring

end D5.S3.Analytic.Interpolation.FiniteMomentCorrelation
