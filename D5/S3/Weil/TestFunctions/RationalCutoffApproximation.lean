/- GID: D5/S3/Weil/TestFunctions/RationalCutoffApproximation
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/RationalCutoffApproximation
   mirror-E: none(waiver:analytic-density-without-effective-degree-bound)
   anchors: []
   utility: none
   digest: Fixed-cutoff rational density in two physical jets and the full paired zero sum. -/

import D5.S3.Weil.InterpolationJets.QuantitativeEvenSeed
import D5.S3.Weil.BurnolGram.ExplicitWeilFourthMomentTail
import D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.TestFunctions.RationalCutoffApproximation

open Set MeasureTheory Polynomial
open scoped ContDiff BigOperators ComplexConjugate
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.InterpolationJets.QuantitativeEvenSeed

/-- Simultaneous rational approximation of the first three physical jets.
The second derivative is approximated first, and two polynomial primitives
recover the lower jets with independently approximated initial conditions. -/
theorem exists_rational_two_jet (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ p : ℚ[X], ∀ x ∈ Icc (-B) B,
      ‖f x - aeval x p‖ ≤ ε ∧
      ‖deriv f x - aeval x p.derivative‖ ≤ ε ∧
      ‖deriv (deriv f) x - aeval x p.derivative.derivative‖ ≤ ε := by
  classical
  let δ : ℝ := ε / (2 * (B + 1) ^ 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hf1 : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hf2 : Continuous (deriv (deriv f)) :=
    (contDiff_infty_iff_deriv.mp hf1).2.continuous
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-B) B
    (deriv (deriv f)) hf2.continuousOn (δ / 2) (by positivity)
  let N := P.natDegree + 1
  let W : ℝ := (max 1 B) ^ P.natDegree
  have hN : 0 < (N : ℝ) := by dsimp [N]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  let η : ℝ := δ / (2 * N * W)
  have hη : 0 < η := by dsimp [η]; positivity
  have hrat (y : ℝ) : ∃ a : ℚ, ‖y - (a : ℝ)‖ < η := by
    obtain ⟨a, ha, hb⟩ := exists_rat_btwn (show y - η < y + η by linarith)
    exact ⟨a, by rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith⟩
  choose a ha using fun i : ℕ => hrat (P.coeff i)
  let q : ℚ[X] := ∑ i ∈ Finset.range N, monomial i (a i)
  have hq (x : ℝ) (hx : x ∈ Icc (-B) B) :
      ‖deriv (deriv f) x - aeval x q‖ ≤ δ := by
    have hxB : ‖x‖ ≤ max 1 B := (abs_le.mpr hx).trans (le_max_right _ _)
    have hpow (i : ℕ) (hi : i ∈ Finset.range N) : ‖x ^ i‖ ≤ W := by
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) hxB i).trans
        (pow_le_pow_right₀ (le_max_left _ _) (by exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    have heval : P.eval x - aeval x q =
        ∑ i ∈ Finset.range N, (P.coeff i - (a i : ℝ)) * x ^ i := by
      conv_lhs => lhs; rw [P.as_sum_range]
      simp [q, N, aeval_def, eval_finsetSum,
        eval₂_monomial, eval_monomial, ← Finset.sum_sub_distrib, sub_mul]
    have herr : ‖P.eval x - aeval x q‖ ≤ δ / 2 := by
      rw [heval]
      calc
        _ ≤ ∑ i ∈ Finset.range N, ‖(P.coeff i - (a i : ℝ)) * x ^ i‖ :=
          norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range N, η * W := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_mul]
          exact mul_le_mul (ha i).le (hpow i hi) (norm_nonneg _) hη.le
        _ = δ / 2 := by simp [η]; field_simp
    calc
      _ ≤ ‖deriv (deriv f) x - P.eval x‖ + ‖P.eval x - aeval x q‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ / 2 + δ / 2 := add_le_add
        (by simpa [Real.norm_eq_abs, abs_sub_comm] using (hP x hx).le) herr
      _ = δ := by ring
  have primitive (r : ℚ[X]) : ∃ s : ℚ[X], s.derivative = r ∧ s.eval 0 = 0 := by
    induction r using Polynomial.induction_on' with
    | add r t hr ht =>
        obtain ⟨s, hs, hs0⟩ := hr
        obtain ⟨u, hu, hu0⟩ := ht
        exact ⟨s + u, by simp [hs, hu], by simp [hs0, hu0]⟩
    | monomial n c =>
        refine ⟨monomial (n + 1) (c / (n + 1)), ?_, by simp⟩
        rw [derivative_monomial_succ]
        congr 1
        field_simp
  obtain ⟨u, hu, hu0⟩ := primitive q
  obtain ⟨v, hv, hv0⟩ := primitive u
  have hinit (y : ℝ) : ∃ a : ℚ, ‖y - (a : ℝ)‖ < δ := by
    obtain ⟨a, ha, hb⟩ := exists_rat_btwn (show y - δ < y + δ by linarith)
    exact ⟨a, by rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith⟩
  obtain ⟨c0, hc0⟩ := hinit (f 0)
  obtain ⟨c1, hc1⟩ := hinit (deriv f 0)
  let p : ℚ[X] := v + C c1 * X + C c0
  have hp2 : p.derivative.derivative = q := by simp [p, hv, hu]
  have hp0 : aeval (0 : ℝ) p = (c0 : ℝ) := by
    simp [p, aeval_def, (Polynomial.coeff_zero_eq_eval_zero v).trans hv0]
  have hp1 : aeval (0 : ℝ) p.derivative = (c1 : ℝ) := by
    simp [p, hv, aeval_def, (Polynomial.coeff_zero_eq_eval_zero u).trans hu0]
  have hzero : (0 : ℝ) ∈ Icc (-B) B := ⟨by linarith, hB.le⟩
  have hsecond (x : ℝ) (hx : x ∈ Icc (-B) B) :
      ‖deriv (deriv f) x - aeval x p.derivative.derivative‖ ≤ δ := by
    simpa [hp2] using hq x hx
  have hfirst (x : ℝ) (hx : x ∈ Icc (-B) B) :
      ‖deriv f x - aeval x p.derivative‖ ≤ δ * (B + 1) := by
    have ht := (convex_Icc (-B) B).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun x => deriv f x - aeval x p.derivative)
      (fun x _ => ((hf1.differentiable (by simp) x).hasDerivAt.sub
        (p.derivative.hasDerivAt_aeval x)).hasDerivWithinAt)
      hsecond hzero hx
    have hx' : ‖x‖ ≤ B := abs_le.mpr hx
    rw [sub_zero] at ht
    calc
      _ ≤ ‖(deriv f x - aeval x p.derivative) -
          (deriv f 0 - aeval 0 p.derivative)‖ +
          ‖deriv f 0 - aeval 0 p.derivative‖ := by
          simpa only [sub_add_cancel] using (norm_add_le
            ((deriv f x - aeval x p.derivative) - (deriv f 0 - aeval 0 p.derivative))
            (deriv f 0 - aeval 0 p.derivative))
      _ ≤ δ * B + δ := add_le_add
        (ht.trans (mul_le_mul_of_nonneg_left hx' hδ.le)) (by simpa [hp1] using hc1.le)
      _ = _ := by ring
  have hvalue (x : ℝ) (hx : x ∈ Icc (-B) B) :
      ‖f x - aeval x p‖ ≤ δ * (B + 1) ^ 2 := by
    have ht := (convex_Icc (-B) B).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun x => f x - aeval x p)
      (fun x _ => ((hf.differentiable (by simp) x).hasDerivAt.sub
        (p.hasDerivAt_aeval x)).hasDerivWithinAt) hfirst hzero hx
    have hx' : ‖x‖ ≤ B := abs_le.mpr hx
    rw [sub_zero] at ht
    calc
      _ ≤ ‖(f x - aeval x p) - (f 0 - aeval 0 p)‖ + ‖f 0 - aeval 0 p‖ :=
        by
          simpa only [sub_add_cancel] using (norm_add_le
            ((f x - aeval x p) - (f 0 - aeval 0 p)) (f 0 - aeval 0 p))
      _ ≤ δ * (B + 1) * B + δ := add_le_add
        (ht.trans (mul_le_mul_of_nonneg_left hx' (by positivity)))
        (by simpa [hp0] using hc0.le)
      _ ≤ _ := by nlinarith
  have hbudget : δ * (B + 1) ^ 2 ≤ ε := by
    dsimp [δ]
    field_simp
    linarith
  refine ⟨p, fun x hx => ⟨(hvalue x hx).trans hbudget,
    (hfirst x hx).trans ?_, (hsecond x hx).trans ?_⟩⟩
  · calc
      δ * (B + 1) ≤ δ * (B + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg B]) hδ.le
      _ ≤ ε := hbudget
  · calc
      δ ≤ δ * (B + 1) ^ 2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (show 1 ≤ (B + 1) ^ 2 by nlinarith [sq_nonneg B]) hδ.le
      _ ≤ ε := hbudget

/-- The even part of a pair of rational polynomials, evaluated on the real line. -/
def rationalEvenPolynomial (p q : ℚ[X]) (x : ℝ) : ℂ :=
  (((aeval x p : ℝ) + aeval (-x) p) / 2 : ℝ) +
    Complex.I * ((((aeval x q : ℝ) + aeval (-x) q) / 2 : ℝ) : ℂ)

/-- A fixed plateau of radius R and outer support radius 2R. -/
def rationalCutoffTest (R : ℕ) (hR : 0 < R) (p q : ℚ[X]) : WeilTestFunction where
  toFun x := (radiusBump (2 * (R : ℝ)) (by exact_mod_cast (by omega : 0 < 2 * R)) x : ℂ) *
    rationalEvenPolynomial p q x
  contDiff' := by
    apply ContDiff.mul
    · exact Complex.ofRealCLM.contDiff.comp (radiusBump _ _).contDiff
    · have hpoly (r : ℚ[X]) : ContDiff ℝ ∞ (fun x : ℝ =>
          ((aeval x r : ℝ) + aeval (-x) r) / 2) :=
        ((r.contDiff_aeval ∞).add ((r.contDiff_aeval ∞).comp contDiff_neg)).div_const 2
      exact (Complex.ofRealCLM.contDiff.comp (hpoly p)).add
        (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hpoly q)))
  hasCompactSupport' :=
    ((radiusBump (2 * (R : ℝ))
      (mul_pos (by norm_num) (Nat.cast_pos.mpr hR))).hasCompactSupport.comp_left
        Complex.ofReal_zero).mul_right
  even' x := by simp [rationalEvenPolynomial, (radiusBump _ _).neg, add_comm]

/-- The fixed rational family is dense in the physical zeroth-plus-second
L1 seminorm. The product rule controls both derivatives of the plateau. -/
theorem exists_rational_cutoff_two_jet
    (g : WeilTestFunction) (R : ℕ) (hR : 0 < R)
    (hs : tsupport (g : ℝ → ℂ) ⊆ Icc (-(R : ℝ)) R)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℚ[X],
      tsupport (rationalCutoffTest R hR p q : ℝ → ℂ) ⊆ Icc (-(2 * R : ℝ)) (2 * R) ∧
      (∫ x : ℝ, ‖g x - rationalCutoffTest R hR p q x‖) +
        (∫ x : ℝ, ‖deriv (deriv (fun y => g y - rationalCutoffTest R hR p q y)) x‖) < ε := by
  classical
  have hRr : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  let χ := radiusBump (2 * R) (by positivity : (0 : ℝ) < 2 * R)
  let c : ℝ → ℂ := fun x => (χ x : ℂ)
  have hc : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hc1 : ContDiff ℝ ∞ (deriv c) := (contDiff_infty_iff_deriv.mp hc).2
  have hc2 : ContDiff ℝ ∞ (deriv (deriv c)) := (contDiff_infty_iff_deriv.mp hc1).2
  let S := Icc (-(2 * R : ℝ)) (2 * R)
  obtain ⟨C1, hC1⟩ := (isCompact_Icc : IsCompact S).exists_bound_of_continuousOn
    hc1.continuous.continuousOn
  obtain ⟨C2, hC2⟩ := (isCompact_Icc : IsCompact S).exists_bound_of_continuousOn
    hc2.continuous.continuousOn
  let K : ℝ := 1 + |C1| + |C2|
  have hK : 0 < K := by dsimp [K]; positivity
  let η : ℝ := ε / (64 * R * K)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨p, hp⟩ := exists_rational_two_jet (fun x => (g x).re)
    (Complex.reCLM.contDiff.comp g.contDiff) (2 * R) η (by positivity) hη
  obtain ⟨q, hq⟩ := exists_rational_two_jet (fun x => (g x).im)
    (Complex.imCLM.contDiff.comp g.contDiff) (2 * R) η (by positivity) hη
  let F (p q : ℚ[X]) (x : ℝ) : ℂ := (aeval x p : ℝ) + Complex.I * (aeval x q : ℝ)
  have hFd (p q : ℚ[X]) (x : ℝ) :
      HasDerivAt (F p q) (F p.derivative q.derivative x) x := by
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (p.hasDerivAt_aeval x)).add
      ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
        (q.hasDerivAt_aeval x)).const_mul Complex.I)
  have hFs : ContDiff ℝ ∞ (F p q) :=
    (Complex.ofRealCLM.contDiff.comp (p.contDiff_aeval ∞)).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (q.contDiff_aeval ∞)))
  let e : ℝ → ℂ := fun x => g x - F p q x
  have he : ContDiff ℝ ∞ e := g.contDiff.sub hFs
  have he1 : ContDiff ℝ ∞ (deriv e) := (contDiff_infty_iff_deriv.mp he).2
  have hg1 : ContDiff ℝ ∞ (deriv (g : ℝ → ℂ)) :=
    (contDiff_infty_iff_deriv.mp g.contDiff).2
  have hprojection (f : ℝ → ℂ) (hf : Differentiable ℝ f) (L : ℂ →L[ℝ] ℝ) :
      deriv (fun x => L (f x)) = fun x => L (deriv f x) := by
    funext x
    exact (L.hasFDerivAt.comp_hasDerivAt x (hf x).hasDerivAt).deriv
  have hproj0 := hprojection (g : ℝ → ℂ) (g.contDiff.differentiable (by simp))
  have hproj1 := hprojection (deriv (g : ℝ → ℂ)) (hg1.differentiable (by simp))
  have hed : deriv e = fun x => deriv (g : ℝ → ℂ) x - F p.derivative q.derivative x := by
    funext x
    exact ((g.contDiff.differentiable (by simp) x).hasDerivAt.sub (hFd p q x)).deriv
  have hedd : deriv (deriv e) = fun x =>
      deriv (deriv (g : ℝ → ℂ)) x - F p.derivative.derivative q.derivative.derivative x := by
    rw [hed]
    funext x
    exact ((hg1.differentiable (by simp) x).hasDerivAt.sub
      (hFd p.derivative q.derivative x)).deriv
  have hcomplex (z : ℂ) (a b : ℝ) (hr : ‖z.re - a‖ ≤ η) (hi : ‖z.im - b‖ ≤ η) :
      ‖z - ((a : ℂ) + Complex.I * b)‖ ≤ 2 * η := by
    have ht := Complex.norm_le_abs_re_add_abs_im (z - ((a : ℂ) + Complex.I * b))
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero, add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im,
      one_mul, zero_add] at ht
    rw [Real.norm_eq_abs] at hr hi
    linarith
  have hejets (x : ℝ) (hx : x ∈ S) :
      ‖e x‖ ≤ 2 * η ∧ ‖deriv e x‖ ≤ 2 * η ∧ ‖deriv (deriv e) x‖ ≤ 2 * η := by
    obtain ⟨hp0, hp1, hp2⟩ := hp x hx
    obtain ⟨hq0, hq1, hq2⟩ := hq x hx
    have hr0 := hproj0 Complex.reCLM
    have hi0 := hproj0 Complex.imCLM
    have hr1 := hproj1 Complex.reCLM
    have hi1 := hproj1 Complex.imCLM
    simp only [Complex.reCLM_apply] at hr0 hr1
    simp only [Complex.imCLM_apply] at hi0 hi1
    rw [hr0] at hp1 hp2
    rw [hi0] at hq1 hq2
    rw [hr1] at hp2
    rw [hi1] at hq2
    exact ⟨hcomplex _ _ _ hp0 hq0,
      by rw [hed]; exact hcomplex _ _ _ hp1 hq1,
      by rw [hedd]; exact hcomplex _ _ _ hp2 hq2⟩
  let a : ℝ → ℂ := fun x => (e x + e (-x)) / 2
  have ha : ContDiff ℝ ∞ a := (he.add (he.comp contDiff_neg)).div_const 2
  have ha1 : deriv a = fun x => (deriv e x - deriv e (-x)) / 2 := by
    funext x
    exact (((he.differentiable (by simp) x).hasDerivAt.add
      (((he.differentiable (by simp) (-x)).hasDerivAt).scomp x
        (hasDerivAt_id x).neg)).div_const 2).deriv.trans (by simp only [neg_one_smul]; ring)
  have ha2 : deriv (deriv a) = fun x =>
      (deriv (deriv e) x + deriv (deriv e) (-x)) / 2 := by
    rw [ha1]
    funext x
    exact (((he1.differentiable (by simp) x).hasDerivAt.sub
      (((he1.differentiable (by simp) (-x)).hasDerivAt).scomp x
        (hasDerivAt_id x).neg)).div_const 2).deriv.trans (by simp only [neg_one_smul]; ring)
  have hajets (x : ℝ) (hx : x ∈ S) :
      ‖a x‖ ≤ 2 * η ∧ ‖deriv a x‖ ≤ 2 * η ∧ ‖deriv (deriv a) x‖ ≤ 2 * η := by
    have hxneg : -x ∈ S := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    obtain ⟨he0, he1, he2⟩ := hejets x hx
    obtain ⟨hen0, hen1, hen2⟩ := hejets (-x) hxneg
    have hsum (u v : ℂ) (hu : ‖u‖ ≤ 2 * η) (hv : ‖v‖ ≤ 2 * η) :
        ‖(u + v) / 2‖ ≤ 2 * η := by
      rw [norm_div, Complex.norm_ofNat]
      exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
        ((norm_add_le _ _).trans (by linarith))
    refine ⟨hsum _ _ he0 hen0, ?_, ?_⟩
    · simp only [ha1, sub_eq_add_neg]
      exact hsum _ _ he1 (by simpa using hen1)
    · rw [ha2]
      exact hsum _ _ he2 hen2
  have hcS : tsupport c ⊆ S := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have hxχ : χ x ≠ 0 := by intro hz; exact hx (by simp [c, hz])
    have hball : x ∈ Metric.ball (0 : ℝ) (2 * R) := by
      have hx' : x ∈ Function.support χ := hxχ
      rw [χ.support_eq] at hx'
      exact hx'
    have hb : |x| < 2 * R := by simpa [Real.dist_eq] using hball
    exact abs_le.mp hb.le
  have hcginv (x : ℝ) : c x * g x = g x := by
    by_cases hx : g x = 0
    · simp [hx]
    · have hxs := hs (subset_tsupport (g : ℝ → ℂ) hx)
      have hχ : χ x = 1 := χ.one_of_mem_closedBall (by
        change dist x 0 ≤ (2 * (R : ℝ)) / 2
        simpa [Real.dist_eq] using abs_le.mpr hxs)
      simp [c, hχ]
  let h := rationalCutoffTest R hR p q
  have hdiff : (fun x => g x - h x) = fun x => c x * a x := by
    funext x
    have hsym : a x = g x - rationalEvenPolynomial p q x := by
      dsimp [a, e, F, rationalEvenPolynomial]
      rw [g.even]
      push_cast
      ring
    rw [hsym, mul_sub, hcginv]
    rfl
  have hhs : tsupport (h : ℝ → ℂ) ⊆ S := tsupport_mul_subset_left.trans hcS
  have hds : tsupport (fun x => g x - h x) ⊆ S := by
    rw [hdiff]
    exact tsupport_mul_subset_left.trans hcS
  have hdd : deriv (deriv (fun x => g x - h x)) = fun x =>
      deriv (deriv c) x * a x + 2 * deriv c x * deriv a x +
        c x * deriv (deriv a) x := by
    rw [hdiff]
    have hd : deriv (fun x => c x * a x) = fun x => deriv c x * a x + c x * deriv a x := by
      funext x
      exact ((hc.differentiable (by simp) x).hasDerivAt.mul
        (ha.differentiable (by simp) x).hasDerivAt).deriv
    rw [hd]
    have ha' : ContDiff ℝ ∞ (deriv a) := (contDiff_infty_iff_deriv.mp ha).2
    funext x
    exact (((hc1.differentiable (by simp) x).hasDerivAt.mul
      (ha.differentiable (by simp) x).hasDerivAt).add
      ((hc.differentiable (by simp) x).hasDerivAt.mul
        (ha'.differentiable (by simp) x).hasDerivAt)).deriv.trans (by ring)
  have hc0 (x : ℝ) : ‖c x‖ ≤ 1 := by
    simpa [c, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ χ x from χ.nonneg)] using
      (show χ x ≤ 1 from χ.le_one)
  have hc1K (x : ℝ) (hx : x ∈ S) : ‖deriv c x‖ ≤ K :=
    (hC1 x hx).trans (by dsimp [K]; linarith [le_abs_self C1, abs_nonneg C2])
  have hc2K (x : ℝ) (hx : x ∈ S) : ‖deriv (deriv c) x‖ ≤ K :=
    (hC2 x hx).trans (by dsimp [K]; linarith [le_abs_self C2, abs_nonneg C1])
  have hK1 : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg C1, abs_nonneg C2]
  have hv (x : ℝ) (hx : x ∈ S) : ‖g x - h x‖ ≤ 2 * K * η := by
    rw [congrFun hdiff x, norm_mul]
    calc
      _ ≤ K * (2 * η) := mul_le_mul ((hc0 x).trans hK1) (hajets x hx).1
        (norm_nonneg _) hK.le
      _ = _ := by ring
  have hsecond (x : ℝ) (hx : x ∈ S) :
      ‖deriv (deriv (fun y => g y - h y)) x‖ ≤ 8 * K * η := by
    rw [hdd]
    have ht := (norm_add_le (deriv (deriv c) x * a x + 2 * deriv c x * deriv a x)
      (c x * deriv (deriv a) x)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    simp only [norm_mul, Complex.norm_ofNat] at ht
    have hj := hajets x hx
    have h0 := mul_le_mul (hc2K x hx) hj.1 (norm_nonneg _) hK.le
    have h1 := mul_le_mul (hc1K x hx) hj.2.1 (norm_nonneg _) hK.le
    have h2 := mul_le_mul ((hc0 x).trans hK1) hj.2.2 (norm_nonneg _) hK.le
    nlinarith
  have lint (f : ℝ → ℂ) (hf : tsupport f ⊆ S) (A : ℝ)
      (hA : ∀ x ∈ S, ‖f x‖ ≤ A) : (∫ x : ℝ, ‖f x‖) ≤ 4 * R * A := by
    have heq : (∫ x in S, ‖f x‖) = ∫ x, ‖f x‖ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have hz : f x = 0 := by
          by_contra hn
          exact hx (hf (subset_tsupport f hn))
        simp [hz]
    rw [← heq]
    have hb := norm_setIntegral_le_of_norm_le_const
      (f := fun x => ‖f x‖) (isCompact_Icc.measure_lt_top : volume S < ⊤)
      (fun x hx => by simpa using hA x hx)
    have hvS : volume.real S = 4 * R := by
      change (volume (Icc (-(2 * (R : ℝ))) (2 * R))).toReal = _
      rw [Real.volume_Icc, ENNReal.toReal_ofReal
        (show 0 ≤ 2 * (R : ℝ) - -(2 * R) by linarith)]
      ring
    rw [hvS, Real.norm_eq_abs] at hb
    exact (le_abs_self _).trans (by nlinarith [hb])
  have hsecondS : tsupport (deriv (deriv (fun x => g x - h x))) ⊆ S :=
    tsupport_deriv_subset.trans (tsupport_deriv_subset.trans hds)
  refine ⟨p, q, hhs, ?_⟩
  change (∫ x : ℝ, ‖g x - h x‖) +
    (∫ x : ℝ, ‖deriv (deriv (fun y => g y - h y)) x‖) < ε
  have hb := add_le_add (lint _ hds _ hv) (lint _ hsecondS _ hsecond)
  have hstrict : 4 * (R : ℝ) * (2 * K * η) + 4 * R * (8 * K * η) < ε := by
    dsimp [η]
    field_simp
    nlinarith
  exact hb.trans_lt hstrict

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.Convention
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds
open D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
open D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare
open D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
open D5.S3.Weil.BurnolGram.WeilMixedHeadTailBudget
open D5.S3.Weil.BurnolGram.ExplicitWeilFourthMomentTail

/-- Rational tests with a fixed cutoff approximate both the physical two-jet
seminorm and the complete symmetric convolution-square sum. The paired
complex-frequency factors and all analytic multiplicities are retained. -/
theorem exists_rational_cutoff_approximation
    (Z : ZeroData) (g : WeilTestFunction) (R : ℕ) (hR : 0 < R)
    (hs : tsupport (g : ℝ → ℂ) ⊆ Icc (-(R : ℝ)) R)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℚ[X],
      tsupport (rationalCutoffTest R hR p q : ℝ → ℂ) ⊆ Icc (-(2 * R : ℝ)) (2 * R) ∧
      (∫ x : ℝ, ‖g x - rationalCutoffTest R hR p q x‖) +
        (∫ x : ℝ, ‖deriv (deriv (fun y => g y - rationalCutoffTest R hR p q y)) x‖) < ε ∧
      ‖zeroSum Z (convolutionSquare g) (symmetricConvergent_of_zeroData Z _) -
        zeroSum Z (convolutionSquare (rationalCutoffTest R hR p q))
          (symmetricConvergent_of_zeroData Z _)‖ < ε := by
  classical
  let E := Z.symmetricIndices 6
  have htail := (zeroData_fourth_moment_tail_rational Z 5 (by decide) E
    (by norm_num [E])).1
  have hmoment : Summable (fourthMomentSummand Z) :=
    E.summable_compl_iff.mp htail
  let M : ℝ := ∑' n : ℕ, fourthMomentSummand Z n
  have hM : 0 ≤ M := tsum_nonneg fun n => by
    unfold fourthMomentSummand inverseQuadraticEnvelope
    positivity
  let Cg := closedStripJetBudget g (1 / 2)
  have hCg : 0 ≤ Cg := (closedStripJetBudget_spec g (1 / 2) (by norm_num)).1
  let A := Real.exp (R : ℝ)
  have hA : 0 < A := Real.exp_pos _
  let δ := min (ε / 2) (min (1 / (2 * A)) (ε / (2 * A * (2 * Cg + 1) * (M + 1))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hδ1 : δ ≤ 1 / (2 * A) := (min_le_right _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ ε / (2 * A * (2 * Cg + 1) * (M + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  let Cd := A * δ
  have hCd : 0 ≤ Cd := by dsimp [Cd]; positivity
  have hCd1 : Cd ≤ 1 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2 * A)).mp hδ1
    dsimp [Cd]
    nlinarith
  have hsmall : Cd * (2 * Cg + Cd) * M < ε := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2 * A * (2 * Cg + 1) * (M + 1))).mp hδ2
    have hprod : Cd * (2 * Cg + Cd) * M ≤ Cd * (2 * Cg + 1) * (M + 1) := by
      gcongr
      linarith
    apply hprod.trans_lt
    dsimp [Cd] at *
    nlinarith
  obtain ⟨p, q, hhS, hj⟩ := exists_rational_cutoff_two_jet g R hR hs δ hδ
  let h := rationalCutoffTest R hR p q
  let d : WeilTestFunction :=
    { toFun := fun x => g x - h x
      contDiff' := g.contDiff.sub h.contDiff
      hasCompactSupport' := g.hasCompactSupport.sub h.hasCompactSupport
      even' := fun x => by rw [g.even, h.even] }
  have hdS : tsupport (d : ℝ → ℂ) ⊆ Icc (-(2 * R : ℝ)) (2 * R) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_cases hg : g x = 0
    · have hh : h x ≠ 0 := by
        intro hz
        apply hx
        change g x - h x = 0
        rw [hg, hz, sub_self]
      exact hhS (subset_tsupport (h : ℝ → ℂ) hh)
    · have hb := hs (subset_tsupport (g : ℝ → ℂ) hg)
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) R, hb.1, hb.2]
  have hdBudget : closedStripJetBudget d (1 / 2) ≤ Cd := by
    have hb := closedStripJetBudget_le_support_jets d (2 * R) (1 / 2)
      (∫ x : ℝ, ‖d x‖) (∫ x : ℝ, ‖((deriv^[2]) (d : ℝ → ℂ)) x‖)
      (by norm_num) hdS le_rfl le_rfl
    have hj' : (∫ x : ℝ, ‖d x‖) +
        (∫ x : ℝ, ‖((deriv^[2]) (d : ℝ → ℂ)) x‖) ≤ δ := by
      change (∫ x : ℝ, ‖g x - h x‖) +
        (∫ x : ℝ, ‖deriv (deriv (fun y => g y - h y)) x‖) ≤ δ
      exact hj.le
    have hexp : Real.exp ((1 / 2 : ℝ) * (2 * R)) = A := by
      congr 1
      ring
    rw [hexp] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left hj' hA.le)
  have htransform (z : ℂ) : fourierLaplace d z = fourierLaplace g z - fourierLaplace h z := by
    have hint (b : WeilTestFunction) : Integrable (fun x : ℝ => fourierKernel z x * b x) :=
      ((by unfold fourierKernel; fun_prop : Continuous (fourierKernel z)).mul
        b.continuous).integrable_of_hasCompactSupport b.hasCompactSupport.mul_left
    change (∫ x : ℝ, fourierKernel z x * d x) =
      (∫ x : ℝ, fourierKernel z x * g x) - ∫ x : ℝ, fourierKernel z x * h x
    rw [← integral_sub (hint g) (hint h)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      change fourierKernel z x * (g x - h x) =
        fourierKernel z x * g x - fourierKernel z x * h x
      ring)
  have hstrip (n : ℕ) : |(Z.gamma n).im| ≤ (1 / 2 : ℝ) := by
    rw [ZeroData.gamma, ← gammaOf_eq_spectralParameter]
    exact (Zeta23.WeilEF.abs_gammaOf_im_lt (Z.zero_isNontrivial n).2).le
  have hb (b : WeilTestFunction) (C : ℝ) (hC : closedStripJetBudget b (1 / 2) ≤ C)
      (n : ℕ) :
      ‖fourierLaplace b (Z.gamma n)‖ ≤ C * inverseQuadraticEnvelope Z n ∧
      ‖fourierLaplace b (conj (Z.gamma n))‖ ≤ C * inverseQuadraticEnvelope Z n := by
    have ht := (closedStripJetBudget_spec b (1 / 2) (by norm_num)).2
    have hden : 0 ≤ inverseQuadraticEnvelope Z n := by unfold inverseQuadraticEnvelope; positivity
    constructor
    · have hu : ‖fourierLaplace b (Z.gamma n)‖ ≤
          closedStripJetBudget b (1 / 2) * inverseQuadraticEnvelope Z n := by
        simpa only [inverseQuadraticEnvelope, div_eq_mul_inv] using
          (ht (Z.gamma n) (hstrip n))
      exact hu.trans (mul_le_mul_of_nonneg_right hC hden)
    · have hu : ‖fourierLaplace b (conj (Z.gamma n))‖ ≤
          closedStripJetBudget b (1 / 2) * inverseQuadraticEnvelope Z n := by
        simpa only [inverseQuadraticEnvelope, div_eq_mul_inv, Complex.conj_re] using
          (ht (conj (Z.gamma n)) (by simpa using hstrip n))
      exact hu.trans (mul_le_mul_of_nonneg_right hC hden)
  have hpoint (n : ℕ) :
      ‖zeroSummand Z (convolutionSquare g) n - zeroSummand Z (convolutionSquare h) n‖ ≤
        (Cd * (2 * Cg + Cd)) * fourthMomentSummand Z n := by
    let w := inverseQuadraticEnvelope Z n
    have hw : 0 ≤ w := by dsimp [w, inverseQuadraticEnvelope]; positivity
    have hg := hb g Cg le_rfl n
    have hd := hb d Cd hdBudget n
    rw [htransform, htransform] at hd
    have hh : ‖fourierLaplace h (Z.gamma n)‖ ≤ (Cg + Cd) * w := by
      have ht := norm_le_norm_add_norm_sub' (fourierLaplace h (Z.gamma n))
        (fourierLaplace g (Z.gamma n))
      rw [norm_sub_rev] at ht
      nlinarith [hg.1, hd.1]
    have hid :
        fourierLaplace g (Z.gamma n) * conj (fourierLaplace g (conj (Z.gamma n))) -
          fourierLaplace h (Z.gamma n) * conj (fourierLaplace h (conj (Z.gamma n))) =
        (fourierLaplace g (Z.gamma n) - fourierLaplace h (Z.gamma n)) *
          conj (fourierLaplace g (conj (Z.gamma n))) +
        fourierLaplace h (Z.gamma n) *
          conj (fourierLaplace g (conj (Z.gamma n)) - fourierLaplace h (conj (Z.gamma n))) := by
      rw [map_sub]
      ring
    simp only [zeroSummand, fourierLaplace_convolutionSquare_complex]
    rw [← mul_sub, norm_mul, Complex.norm_natCast, hid]
    have ht := norm_add_le
      ((fourierLaplace g (Z.gamma n) - fourierLaplace h (Z.gamma n)) *
        conj (fourierLaplace g (conj (Z.gamma n))))
      (fourierLaplace h (Z.gamma n) *
        conj (fourierLaplace g (conj (Z.gamma n)) - fourierLaplace h (conj (Z.gamma n))))
    simp only [norm_mul, Complex.norm_conj] at ht
    have hleft := mul_le_mul hd.1 hg.2 (norm_nonneg _) (mul_nonneg hCd hw)
    have hright := mul_le_mul hh hd.2 (norm_nonneg _) (mul_nonneg (add_nonneg hCg hCd) hw)
    calc
      _ ≤ (Z.multiplicity n : ℝ) *
          ((Cd * w) * (Cg * w) + ((Cg + Cd) * w) * (Cd * w)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact ht.trans (add_le_add hleft hright)
      _ = _ := by unfold fourthMomentSummand; dsimp [w]; ring
  have hgs := zeroSummand_summable_of_zeroData Z (convolutionSquare g)
  have hhs := zeroSummand_summable_of_zeroData Z (convolutionSquare h)
  have hsum :
      ‖zeroSum Z (convolutionSquare g) (symmetricConvergent_of_zeroData Z _) -
        zeroSum Z (convolutionSquare h) (symmetricConvergent_of_zeroData Z _)‖ ≤
          Cd * (2 * Cg + Cd) * M := by
    rw [zeroSum_eq_tsum_of_zeroData, zeroSum_eq_tsum_of_zeroData, ← hgs.tsum_sub hhs]
    calc
      _ ≤ ∑' n : ℕ, ‖zeroSummand Z (convolutionSquare g) n -
          zeroSummand Z (convolutionSquare h) n‖ := norm_tsum_le_tsum_norm (hgs.sub hhs).norm
      _ ≤ ∑' n : ℕ, (Cd * (2 * Cg + Cd)) * fourthMomentSummand Z n :=
        (hgs.sub hhs).norm.tsum_le_tsum hpoint (hmoment.mul_left _)
      _ = _ := tsum_mul_left
  exact ⟨p, q, hhS, hj.trans hδε, hsum.trans_lt hsmall⟩

#print axioms exists_rational_two_jet
#print axioms exists_rational_cutoff_two_jet
#print axioms exists_rational_cutoff_approximation

end D5.S3.Weil.TestFunctions.RationalCutoffApproximation
