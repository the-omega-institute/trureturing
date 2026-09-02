/- GID: D5/S3/Weil/TestFunctions/EvenTestFunctionFiniteInterpolation
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/EvenTestFunctionFiniteInterpolation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Even test functions interpolate finite data at sign-separated nodes. -/

import D5.S3.Weil.TestFunctions.FinitePaleyWienerInterpolation

/- Library-search audit trail (2026-09-02):
   * Searches for the theorem name, the sign-separation hypothesis, and the
     interpolation conclusion found no D5 declaration with this statement.
   * `finite_exact_paley_wiener_interpolation` treats conjugation-compatible
     raw functions; it does not produce an even `WeilTestFunction` for
     arbitrary sign-separated values.
   * Pinned Mathlib supplies square-factorization, Lagrange interpolation,
     derivative support, integration by parts, and real-line dilation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Function MeasureTheory Metric Polynomial Set
open scoped ComplexConjugate ContDiff
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions

namespace D5.S3.Weil.TestFunctions.EvenTestFunctionFiniteInterpolation

private theorem square_nodes_injective
    (S : Finset Complex)
    (hsep : forall {z w : Complex}, z ∈ S -> w ∈ S -> z ≠ w -> z ≠ -w) :
    Function.Injective (fun z : S => z.1 ^ 2) := by
  intro z w hsq
  rcases eq_or_eq_neg_of_sq_eq_sq z.1 w.1 hsq with h | h
  · exact Subtype.ext h
  · by_contra hne
    have hzw : z.1 ≠ w.1 := fun heq => hne (Subtype.ext heq)
    exact (hsep z.2 w.2 hzw) h

private theorem fourierLaplace_iterate_deriv
    (q : Nat) (g : Real -> Complex) (hgSmooth : ContDiff Real ∞ g)
    (hgCompact : HasCompactSupport g) (z : Complex) :
    (∫ x : Real, Complex.exp (-Complex.I * z * (x : Complex)) * ((deriv^[q]) g) x) =
      (Complex.I * z) ^ q *
        (∫ x : Real, Complex.exp (-Complex.I * z * (x : Complex)) * g x) := by
  have hcompact (n : Nat) : HasCompactSupport ((deriv^[n]) g) := by
    induction n with
    | zero => simpa
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact ih.deriv
  induction q with
  | zero => simp
  | succ q ih =>
      let v : Real -> Complex := (deriv^[q]) g
      let v' : Real -> Complex := (deriv^[q + 1]) g
      let u : Real -> Complex := fun x =>
        Complex.exp (-Complex.I * z * (x : Complex))
      let u' : Real -> Complex := fun x =>
        (-Complex.I * z) * Complex.exp (-Complex.I * z * (x : Complex))
      have hvSmooth : ContDiff Real ∞ v :=
        ContDiff.iterate_deriv q hgSmooth
      have hvCompact : HasCompactSupport v := by
        simpa only [v] using hcompact q
      have hv'Compact : HasCompactSupport v' := by
        simpa only [v, v', Function.iterate_succ_apply'] using hvCompact.deriv
      have huDeriv (x : Real) : HasDerivAt u (u' x) x := by
        have hinner : HasDerivAt (fun y : Real =>
            (-Complex.I * z) * (y : Complex)) (-Complex.I * z) x :=
          by simpa using
            ((hasDerivAt_id x).ofReal_comp).const_mul (-Complex.I * z)
        simpa only [u, u', neg_mul, mul_comm] using hinner.cexp
      have hvDeriv (x : Real) : HasDerivAt v (v' x) x := by
        simpa only [v, v', Function.iterate_succ_apply'] using
          ((ContDiff.iterate_deriv q hgSmooth).differentiable (by simp) x).hasDerivAt
      have huv' : Integrable (u * v') :=
        ((by fun_prop : Continuous u).mul
          (ContDiff.iterate_deriv (q + 1) hgSmooth).continuous).integrable_of_hasCompactSupport
          hv'Compact.mul_left
      have hu'v : Integrable (u' * v) :=
        (by fun_prop : Continuous (u' * v)).integrable_of_hasCompactSupport
          hvCompact.mul_left
      have huv : Integrable (u * v) :=
        (by fun_prop : Continuous (u * v)).integrable_of_hasCompactSupport
          hvCompact.mul_left
      have hparts := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
        (u := u) (u' := u') (v := v) (v' := v')
        (fun x _ => huDeriv x) (fun x _ => hvDeriv x) huv' hu'v huv
      change (∫ x : Real, u x * v' x) = _
      rw [hparts]
      change -(∫ x : Real, ((-Complex.I * z) * u x) * v x) = _
      rw [show (fun x : Real => ((-Complex.I * z) * u x) * v x) =
          fun x => (-Complex.I * z) * (u x * v x) by
        funext x
        ring]
      rw [integral_const_mul, ih, pow_succ]
      ring

private theorem iterate_deriv_even
    (k : Nat) (g : Real -> Complex) (hgEven : forall x, g (-x) = g x) (x : Real) :
    ((deriv^[2 * k]) g) (-x) = ((deriv^[2 * k]) g) x := by
  rw [← iteratedDeriv_eq_iterate]
  have hfun : (fun y : Real => g (-y)) = g := funext hgEven
  have heq := congrArg (fun h : Real -> Complex => iteratedDeriv (2 * k) h x) hfun
  rw [iteratedDeriv_comp_neg] at heq
  simpa [pow_mul] using heq

private theorem fourierLaplace_scale
    (g : WeilTestFunction) (a : Real) (ha : 0 < a) (z : Complex) :
    (∫ x : Real, Complex.exp (-Complex.I * z * (x : Complex)) * g (x / a)) =
      (a : Complex) * fourierLaplace g ((a : Complex) * z) := by
  have hscale := Measure.integral_comp_div
    (fun y : Real =>
      Complex.exp (-Complex.I * z * ((a * y : Real) : Complex)) * g y) a
  rw [abs_of_pos ha] at hscale
  convert hscale using 1 <;>
    try simp only [fourierLaplace_apply]
  · apply integral_congr_ae
    filter_upwards with x
    congr 2
    push_cast
    field_simp [ha.ne']
  · congr 1
    apply integral_congr_ae
    filter_upwards with x
    congr 2
    rw [Complex.ofReal_mul]
    ring

set_option maxHeartbeats 2000000 in
-- Normalizing and scaling the canonical smooth bump expands bundled support proofs.
private theorem exists_common_nonvanishing_even_seed (S : Finset Complex) :
    exists psi : WeilTestFunction,
      forall z : S, fourierLaplace psi z.1 ≠ 0 := by
  let psi0 : WeilTestFunction :=
    { toFun := fun x => (standardBump.normed volume x : Complex)
      contDiff' := Complex.ofRealCLM.contDiff.comp standardBump.contDiff_normed
      hasCompactSupport' := by
        change HasCompactSupport
          (Complex.ofRealCLM ∘ standardBump.normed volume)
        exact standardBump.hasCompactSupport_normed.comp_left (by simp)
      even' := by
        intro x
        exact_mod_cast standardBump.normed_neg x }
  have hzero : fourierLaplace psi0 0 = 1 := by
    rw [fourierLaplace_apply]
    simp only [mul_zero, zero_mul, Complex.exp_zero, one_mul]
    change (∫ x : Real, (standardBump.normed volume x : Complex)) = 1
    rw [integral_complex_ofReal]
    exact_mod_cast standardBump.integral_normed
  have hnear : (fourierLaplace psi0) ⁻¹' Metric.ball (1 : Complex) 1 ∈
      nhds (0 : Complex) := by
    apply (fourierLaplace_entire psi0).continuous.continuousAt
    simpa only [hzero] using Metric.ball_mem_nhds (1 : Complex) zero_lt_one
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let B : Real := ∑ z : S, norm z.1
  have hB : 0 <= B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let a : Real := epsilon / (B + 1)
  have ha : 0 < a := div_pos hepsilon (by linarith)
  have haz (z : S) : (a : Complex) * z.1 ∈ Metric.ball 0 epsilon := by
    have hzB : norm z.1 <= B := by
      exact Finset.single_le_sum (fun w _ => norm_nonneg w.1) (Finset.mem_univ z)
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha]
    change a * norm z.1 < epsilon
    calc
      a * norm z.1 <= a * B := mul_le_mul_of_nonneg_left hzB ha.le
      _ < epsilon := by
        dsimp only [a]
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ (by linarith : 0 < B + 1)).2
        nlinarith
  let psi : WeilTestFunction :=
    { toFun := fun x => psi0 (x / a)
      contDiff' := psi0.contDiff.comp (by fun_prop)
      hasCompactSupport' := by
        have hhome := psi0.hasCompactSupport.comp_homeomorph
          (Homeomorph.mulRight₀ a⁻¹ (inv_ne_zero ha.ne'))
        simpa only [Function.comp_def, Homeomorph.coe_mulRight₀, div_eq_mul_inv] using hhome
      even' := by
        intro x
        rw [show -x / a = -(x / a) by ring, psi0.even] }
  refine ⟨psi, ?_⟩
  intro z
  change (∫ x : Real, Complex.exp (-Complex.I * z.1 * (x : Complex)) * psi0 (x / a)) ≠ 0
  rw [fourierLaplace_scale psi0 a ha z.1]
  apply mul_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne')
  intro hvanish
  have himage := hball (haz z)
  rw [mem_preimage, mem_ball, hvanish, dist_zero_left, norm_one] at himage
  exact lt_irrefl (1 : Real) himage

private noncomputable def evenPolynomialDifferential
    (P : Complex[X]) (psi : WeilTestFunction) : WeilTestFunction where
  toFun x := ∑ k ∈ P.support,
    P.coeff k * (-Complex.I) ^ (2 * k) * ((deriv^[2 * k]) psi) x
  contDiff' := by
    apply ContDiff.sum
    intro k _
    have hk := ContDiff.iterate_deriv (2 * k) psi.contDiff
    fun_prop
  hasCompactSupport' := by
    rw [show (fun x : Real => ∑ k ∈ P.support,
        P.coeff k * (-Complex.I) ^ (2 * k) * ((deriv^[2 * k]) psi) x) =
        ∑ k ∈ P.support, fun x : Real =>
          P.coeff k * (-Complex.I) ^ (2 * k) * ((deriv^[2 * k]) psi) x by
      funext x
      simp]
    apply HasCompactSupport.finset_sum (s := P.support)
    intro k _
    have hiterated : HasCompactSupport ((deriv^[2 * k]) (psi : Real -> Complex)) := by
      induction (2 * k) with
      | zero => simpa using psi.hasCompactSupport
      | succ q ih =>
          rw [Function.iterate_succ_apply']
          exact ih.deriv
    exact hiterated.mul_left
  even' := by
    intro x
    apply Finset.sum_congr rfl
    intro k _
    rw [iterate_deriv_even k psi psi.even]

private theorem fourierLaplace_evenPolynomialDifferential
    (P : Complex[X]) (psi : WeilTestFunction) (z : Complex) :
    fourierLaplace (evenPolynomialDifferential P psi) z =
      P.eval (z ^ 2) * fourierLaplace psi z := by
  rw [fourierLaplace_apply]
  change (∫ x : Real,
      Complex.exp (-Complex.I * z * (x : Complex)) *
        ∑ k ∈ P.support,
          P.coeff k * (-Complex.I) ^ (2 * k) * ((deriv^[2 * k]) psi) x) = _
  rw [show (fun x : Real =>
      Complex.exp (-Complex.I * z * (x : Complex)) *
        ∑ k ∈ P.support,
          P.coeff k * (-Complex.I) ^ (2 * k) * ((deriv^[2 * k]) psi) x) =
      fun x : Real => ∑ k ∈ P.support,
        Complex.exp (-Complex.I * z * (x : Complex)) *
          (P.coeff k * (-Complex.I) ^ (2 * k) * ((deriv^[2 * k]) psi) x) by
    funext x
    simp only [Finset.mul_sum]]
  have htermSmooth (k : Nat) : ContDiff Real ∞ (fun x : Real =>
      P.coeff k * (-Complex.I) ^ (2 * k) * ((deriv^[2 * k]) psi) x) := by
    have hk := ContDiff.iterate_deriv (2 * k) psi.contDiff
    fun_prop
  have htermCompact (k : Nat) : HasCompactSupport (fun x : Real =>
      P.coeff k * (-Complex.I) ^ (2 * k) * ((deriv^[2 * k]) psi) x) := by
    have hiterated : HasCompactSupport ((deriv^[2 * k]) (psi : Real -> Complex)) := by
      induction (2 * k) with
      | zero => simpa using psi.hasCompactSupport
      | succ q ih =>
          rw [Function.iterate_succ_apply']
          exact ih.deriv
    exact hiterated.mul_left
  have htermIntegrable (k : Nat) : Integrable (fun x : Real =>
      Complex.exp (-Complex.I * z * (x : Complex)) *
        (P.coeff k * (-Complex.I) ^ (2 * k) * ((deriv^[2 * k]) psi) x)) := by
    exact ((by fun_prop : Continuous
        (fun x : Real => Complex.exp (-Complex.I * z * (x : Complex)))).mul
      (htermSmooth k).continuous).integrable_of_hasCompactSupport
        (htermCompact k).mul_left
  rw [integral_finsetSum _ fun k _ => htermIntegrable k]
  have htermTransform (k : Nat) :
      (∫ x : Real,
        Complex.exp (-Complex.I * z * (x : Complex)) *
          (P.coeff k * (-Complex.I) ^ (2 * k) * ((deriv^[2 * k]) psi) x)) =
        (P.coeff k * (-Complex.I) ^ (2 * k)) *
          ((Complex.I * z) ^ (2 * k) * fourierLaplace psi z) := by
    rw [show (fun x : Real =>
        Complex.exp (-Complex.I * z * (x : Complex)) *
          (P.coeff k * (-Complex.I) ^ (2 * k) * ((deriv^[2 * k]) psi) x)) =
        fun x : Real => (P.coeff k * (-Complex.I) ^ (2 * k)) *
          (Complex.exp (-Complex.I * z * (x : Complex)) * ((deriv^[2 * k]) psi) x) by
      funext x
      ring]
    rw [integral_const_mul,
      fourierLaplace_iterate_deriv (2 * k) psi psi.contDiff psi.hasCompactSupport z]
    rfl
  simp_rw [htermTransform]
  rw [Polynomial.eval_eq_sum]
  simp only [Polynomial.sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hbase : (-Complex.I) * (Complex.I * z) = z := by
    rw [neg_mul, ← mul_assoc, Complex.I_mul_I]
    ring
  have hpow :
      (-Complex.I) ^ (2 * k) * (Complex.I * z) ^ (2 * k) = (z ^ 2) ^ k := by
    rw [← mul_pow, hbase, pow_mul]
  calc
    P.coeff k * (-Complex.I) ^ (2 * k) *
        ((Complex.I * z) ^ (2 * k) * fourierLaplace psi z) =
      P.coeff k *
        ((-Complex.I) ^ (2 * k) * (Complex.I * z) ^ (2 * k)) *
          fourierLaplace psi z := by ring
    _ = P.coeff k * (z ^ 2) ^ k * fourierLaplace psi z := by rw [hpow]

/-- Arbitrary complex values at finitely many nodes with no distinct opposite
pair are Fourier-Laplace values of one even Weil test function. -/
theorem even_weilTestFunction_finite_interpolation
    (S : Finset ℂ)
    (hsep : ∀ ⦃z w : ℂ⦄, z ∈ S → w ∈ S → z ≠ w → z ≠ -w)
    (a : S → ℂ) :
    ∃ g : WeilTestFunction,
      ∀ z : S, fourierLaplace g z.1 = a z := by
  obtain ⟨psi, hpsiNonzero⟩ := exists_common_nonvanishing_even_seed S
  let target : S -> Complex := fun z => a z / fourierLaplace psi z.1
  let P : Complex[X] := Lagrange.interpolate Finset.univ
    (fun z : S => z.1 ^ 2) target
  have hP (z : S) : P.eval (z.1 ^ 2) = target z := by
    exact Lagrange.eval_interpolate_at_node target
      (square_nodes_injective S (@hsep)).injOn (Finset.mem_univ z)
  refine ⟨evenPolynomialDifferential P psi, ?_⟩
  intro z
  rw [fourierLaplace_evenPolynomialDifferential, hP]
  dsimp only [target]
  exact div_mul_cancel₀ (a z) (hpsiNonzero z)

example : ∀ ⦃z w : ℂ⦄, z ∈ (∅ : Finset ℂ) → w ∈ (∅ : Finset ℂ) →
    z ≠ w → z ≠ -w := by
  simp

example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

#print axioms even_weilTestFunction_finite_interpolation

end D5.S3.Weil.TestFunctions.EvenTestFunctionFiniteInterpolation
