/- GID: D5/S3/Weil/TestFunctions/FinitePaleyWienerInterpolation
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/FinitePaleyWienerInterpolation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite compatible data admit exact compact smooth Fourier-Laplace interpolation. -/

import D5.S3.Fourier.FourierLaplaceEntire
import D5.S3.Weil.FourierLaplace
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/- Library-search audit trail (2026-08-30):
   * The canonical `WeilTestFunction` and `fourierLaplace` are imported; no
     second transform primitive is declared for the Hermitian carrier.
   * Body-shape searches for finite Fourier-Laplace interpolation, a common
     nonvanishing compact bump, and polynomial differential action found no
     D5 owner.
   * Pinned Mathlib supplies `Polynomial.interpolate`, compact-support
     derivative control, integration by parts, and real-line dilation of
     integrals, but no exact theorem combining these clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Function MeasureTheory Metric Polynomial Set
open scoped ComplexConjugate ContDiff
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions

namespace D5.S3.Weil.TestFunctions.FinitePaleyWienerInterpolation

local notation "FL[" g "](" z ")" =>
  (∫ x : Real, Complex.exp (-Complex.I * z * (x : Complex)) * g x)

private theorem fourier_laplace_iterate_deriv
    (q : Nat) (g : Real -> Complex) (hgSmooth : ContDiff Real ∞ g)
    (hgCompact : HasCompactSupport g) (z : Complex) :
    FL[((deriv^[q]) g)](z) = (Complex.I * z) ^ q * FL[g](z) := by
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

private theorem fourier_laplace_scale
    (g : WeilTestFunction) (a : Real) (ha : 0 < a) (z : Complex) :
    FL[(fun x : Real => g (x / a))](z) =
      (a : Complex) * fourierLaplace g ((a : Complex) * z) := by
  have hscale := Measure.integral_comp_div
    (fun y : Real =>
      Complex.exp (-Complex.I * z * ((a * y : Real) : Complex)) * g y) a
  rw [abs_of_pos ha] at hscale
  change FL[(fun x : Real => g (x / a))](z) = _
  convert hscale using 1 <;>
    simp only [fourierLaplace_apply]
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

private theorem eval_map_conj (P : Complex[X]) (z : Complex) :
    (P.map (starRingEnd Complex)).eval z = conj (P.eval (conj z)) := by
  simpa using
    (Polynomial.eval_map_apply (p := P) (starRingEnd Complex) (conj z))

private theorem iteratedDeriv_conj (k : Nat) (g : Real → Complex) :
    iteratedDeriv k (fun x => conj (g x)) = fun x => conj (iteratedDeriv k g x) := by
  induction k with
  | zero => simp only [iteratedDeriv_zero]
  | succ k ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
      exact deriv.star'

private theorem iterate_deriv_reflection
    (k : Nat) (g : Real → Complex)
    (hgHermitian : ∀ x, g (-x) = conj (g x)) (x : Real) :
    ((deriv^[k]) g) (-x) =
      ((-1 : Real) ^ k) • conj (((deriv^[k]) g) x) := by
  rw [← iteratedDeriv_eq_iterate]
  have hfun : (fun y : Real => g (-y)) = fun y => conj (g y) :=
    funext hgHermitian
  have heq := congrArg (fun h : Real → Complex => iteratedDeriv k h x) hfun
  rw [iteratedDeriv_comp_neg, iteratedDeriv_conj] at heq
  calc
    iteratedDeriv k g (-x) =
        (((-1 : Real) ^ k) * ((-1 : Real) ^ k)) • iteratedDeriv k g (-x) := by
      rw [← mul_pow]
      norm_num
    _ = ((-1 : Real) ^ k) •
        (((-1 : Real) ^ k) • iteratedDeriv k g (-x)) := by
      rw [smul_smul]
    _ = ((-1 : Real) ^ k) • conj (iteratedDeriv k g x) := by
      rw [heq]

set_option maxHeartbeats 2000000 in
-- Normalizing the canonical smooth bump expands several bundled support proofs.
private theorem exists_common_nonvanishing_seed {M : Nat} (z : Fin M -> Complex) :
    exists psi : WeilTestFunction,
      (forall x, psi (-x) = conj (psi x)) /\
      (forall j, fourierLaplace psi (z j) ≠ 0) := by
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
  let B : Real := ∑ j : Fin M, norm (z j)
  have hB : 0 <= B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let a : Real := epsilon / (B + 1)
  have ha : 0 < a := div_pos hepsilon (by linarith)
  have haz (j : Fin M) : (a : Complex) * z j ∈ Metric.ball 0 epsilon := by
    have hjB : norm (z j) <= B := by
      exact Finset.single_le_sum (fun i _ => norm_nonneg (z i)) (Finset.mem_univ j)
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha]
    change a * norm (z j) < epsilon
    calc
      a * norm (z j) <= a * B := mul_le_mul_of_nonneg_left hjB ha.le
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
  have hpsiNonzero (j : Fin M) : fourierLaplace psi (z j) ≠ 0 := by
    change FL[(fun x : Real => psi0 (x / a))](z j) ≠ 0
    rw [fourier_laplace_scale psi0 a ha (z j)]
    apply mul_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne')
    intro hvanish
    have himage := hball (haz j)
    rw [mem_preimage, mem_ball, hvanish, dist_zero_left, norm_one] at himage
    exact lt_irrefl (1 : Real) himage
  have hpsiHermitian (x : Real) : psi (-x) = conj (psi x) := by
    dsimp only [psi]
    change psi0.toFun (-x / a) = conj (psi0.toFun (x / a))
    dsimp only [psi0]
    rw [show -x / a = -(x / a) by ring, standardBump.normed_neg]
    exact (Complex.conj_ofReal _).symm
  exact ⟨psi, hpsiHermitian, hpsiNonzero⟩

private theorem polynomial_differential_properties
    (P : Complex[X]) (psi : Real -> Complex)
    (hpsiSmooth : ContDiff Real ∞ psi)
    (hpsiCompact : HasCompactSupport psi) :
    let raw : Real -> Complex := fun x =>
      ∑ k ∈ P.support,
        P.coeff k * (-Complex.I) ^ k * ((deriv^[k]) psi) x
    ContDiff Real ∞ raw /\
      HasCompactSupport raw /\
      forall z, FL[raw](z) = P.eval z * FL[psi](z) := by
  dsimp only
  have htermSmooth (k : Nat) : ContDiff Real ∞ (fun x : Real =>
      P.coeff k * (-Complex.I) ^ k * ((deriv^[k]) psi) x) := by
    have hk := ContDiff.iterate_deriv k hpsiSmooth
    fun_prop
  have htermCompact (k : Nat) : HasCompactSupport (fun x : Real =>
      P.coeff k * (-Complex.I) ^ k * ((deriv^[k]) psi) x) := by
    have hiterated : HasCompactSupport ((deriv^[k]) psi) := by
      induction k with
      | zero => simpa
      | succ k ih =>
          rw [Function.iterate_succ_apply']
          exact ih.deriv
    exact hiterated.mul_left
  refine ⟨ContDiff.sum fun k _ => htermSmooth k,
    ?_, ?_⟩
  · rw [show (fun x : Real => ∑ k ∈ P.support,
        P.coeff k * (-Complex.I) ^ k * ((deriv^[k]) psi) x) =
        ∑ k ∈ P.support, fun x : Real =>
          P.coeff k * (-Complex.I) ^ k * ((deriv^[k]) psi) x by
      funext x
      simp]
    exact HasCompactSupport.finset_sum (s := P.support) fun k _ => htermCompact k
  intro z
  rw [show (fun x : Real =>
      Complex.exp (-Complex.I * z * (x : Complex)) *
        ∑ k ∈ P.support,
          P.coeff k * (-Complex.I) ^ k * ((deriv^[k]) psi) x) =
      fun x : Real => ∑ k ∈ P.support,
        Complex.exp (-Complex.I * z * (x : Complex)) *
          (P.coeff k * (-Complex.I) ^ k * ((deriv^[k]) psi) x) by
    funext x
    simp only [Finset.mul_sum]]
  have htermIntegrable (k : Nat) : Integrable (fun x : Real =>
      Complex.exp (-Complex.I * z * (x : Complex)) *
        (P.coeff k * (-Complex.I) ^ k * ((deriv^[k]) psi) x)) := by
    exact ((by fun_prop : Continuous
        (fun x : Real => Complex.exp (-Complex.I * z * (x : Complex)))).mul
      (htermSmooth k).continuous).integrable_of_hasCompactSupport
        (htermCompact k).mul_left
  rw [integral_finsetSum _ fun k _ => htermIntegrable k]
  have htermTransform (k : Nat) :
      (∫ x : Real,
        Complex.exp (-Complex.I * z * (x : Complex)) *
          (P.coeff k * (-Complex.I) ^ k * ((deriv^[k]) psi) x)) =
        (P.coeff k * (-Complex.I) ^ k) *
          ((Complex.I * z) ^ k * FL[psi](z)) := by
    rw [show (fun x : Real =>
        Complex.exp (-Complex.I * z * (x : Complex)) *
          (P.coeff k * (-Complex.I) ^ k * ((deriv^[k]) psi) x)) =
        fun x : Real => (P.coeff k * (-Complex.I) ^ k) *
          (Complex.exp (-Complex.I * z * (x : Complex)) * ((deriv^[k]) psi) x) by
      funext x
      ring]
    rw [integral_const_mul,
      fourier_laplace_iterate_deriv k psi hpsiSmooth hpsiCompact z]
  simp_rw [htermTransform]
  rw [Polynomial.eval_eq_sum]
  simp only [Polynomial.sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hpow : (-Complex.I) ^ k * (Complex.I * z) ^ k = z ^ k := by
    have hbase : (-Complex.I) * (Complex.I * z) = z := by
      rw [neg_mul, ← mul_assoc, Complex.I_mul_I]
      ring
    rw [← mul_pow, hbase]
  calc
    P.coeff k * (-Complex.I) ^ k * ((Complex.I * z) ^ k * FL[psi](z)) =
        P.coeff k * (((-Complex.I) ^ k * (Complex.I * z) ^ k) * FL[psi](z)) := by
      ring
    _ = P.coeff k * z ^ k * FL[psi](z) := by
      rw [hpow]
      ring

private theorem polynomial_differential_hermitian
    (P : Complex[X]) (psi : Real -> Complex)
    (hpsiHermitian : forall x, psi (-x) = conj (psi x))
    (hPcoeff : forall k, P.coeff k = conj (P.coeff k)) :
    let f : Real -> Complex := fun x =>
      ∑ k ∈ P.support,
        P.coeff k * (-Complex.I) ^ k * ((deriv^[k]) psi) x
    forall x, f (-x) = conj (f x) := by
  dsimp only
  intro x
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [iterate_deriv_reflection k psi hpsiHermitian]
  simp only [Complex.real_smul, map_mul, map_pow, map_neg,
    Complex.conj_I, neg_neg]
  rw [← hPcoeff k]
  have hpower :
      (-Complex.I) ^ k * ((((-1 : Real) ^ k : Real) : Complex)) = Complex.I ^ k := by
    rw [Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one, ← mul_pow]
    ring
  calc
    P.coeff k * (-Complex.I) ^ k *
        ((((-1 : Real) ^ k : Real) : Complex) * conj (((deriv^[k]) psi) x)) =
        P.coeff k * (((-Complex.I) ^ k *
          (((-1 : Real) ^ k : Real) : Complex)) * conj (((deriv^[k]) psi) x)) := by
      ring
    _ = P.coeff k * (Complex.I ^ k * conj (((deriv^[k]) psi) x)) := by
      rw [hpower]
    _ = P.coeff k * Complex.I ^ k * conj (((deriv^[k]) psi) x) := by
      ring

/-- Finite distinct complex nodes with conjugation-compatible values admit an
exact compactly supported smooth Hermitian Fourier-Laplace interpolant. The
public witnesses record the nonvanishing seed, Lagrange polynomial,
conjugation-symmetric polynomial differential construction, transform
factorization, unchanged support window, and Hermitian structure. Under the source's frozen
exp(-i z x) convention, integration by parts sends partial_x to i z, so its
printed P(i partial_x) psi yields P(-z); the public witness uses
P(-i partial_x) to realize the stated P(z) factorization. -/
theorem finite_exact_paley_wiener_interpolation
    {M : Nat} (z r : Fin M -> Complex) (hz : Function.Injective z)
    (conjIndex : Fin M -> Fin M)
    (hzConj : forall j, z (conjIndex j) = conj (z j))
    (hrConj : forall j, r (conjIndex j) = conj (r j)) :
    exists (L : Real) (psi : Real -> Complex) (P : Complex[X])
      (f : Real -> Complex),
      0 < L /\
      ContDiff Real ∞ psi /\
      HasCompactSupport psi /\
      tsupport psi <= Ioo (-L) L /\
      (forall j, FL[psi](z j) ≠ 0) /\
      (forall j, P.eval (z j) = r j / FL[psi](z j)) /\
      f = (fun x => ∑ k ∈ P.support,
        P.coeff k * (-Complex.I) ^ k * ((deriv^[k]) psi) x) /\
      ContDiff Real ∞ f /\
      HasCompactSupport f /\
      tsupport f <= Ioo (-L) L /\
      (forall x, f (-x) = conj (f x)) /\
      (forall w, FL[f](w) = P.eval w * FL[psi](w)) /\
      forall j, FL[f](z j) = r j := by
  obtain ⟨psi, hpsiHermitian, hpsiNonzero⟩ :=
    exists_common_nonvanishing_seed z
  have hpsiSmooth : ContDiff Real ∞ (psi : Real -> Complex) := psi.contDiff
  have hpsiCompact : HasCompactSupport (psi : Real -> Complex) := psi.hasCompactSupport
  have hpsiTransformConj (w : Complex) :
      FL[psi](conj w) = conj (FL[psi](w)) := by
    have hinvolution : involution psi = psi := by
      ext x
      rw [involution_apply, hpsiHermitian]
      simp
    have htransform := fourierLaplace_involution_conj psi (conj w)
    rw [hinvolution, starRingEnd_self_apply] at htransform
    simpa only [fourierLaplace_apply] using htransform
  let target : Fin M -> Complex := fun j => r j / FL[psi](z j)
  have htargetConj (j : Fin M) :
      target (conjIndex j) = conj (target j) := by
    dsimp only [target]
    rw [hrConj, hzConj, hpsiTransformConj]
    rw [div_eq_mul_inv, div_eq_mul_inv, map_mul, map_inv₀]
  let Q : Complex[X] := Lagrange.interpolate Finset.univ z target
  have hQ (j : Fin M) : Q.eval (z j) = target j := by
    exact Lagrange.eval_interpolate_at_node target hz.injOn (Finset.mem_univ j)
  let P : Complex[X] := (2 : Complex)⁻¹ •
    (Q + Q.map (starRingEnd Complex))
  have hP (j : Fin M) : P.eval (z j) = target j := by
    dsimp only [P]
    rw [Polynomial.eval_smul, Polynomial.eval_add, hQ,
      eval_map_conj, ← hzConj j, hQ, htargetConj]
    change (2 : Complex)⁻¹ • (target j + conj (conj (target j))) = target j
    rw [starRingEnd_self_apply]
    ring
  have hPcoeff (k : Nat) : P.coeff k = conj (P.coeff k) := by
    dsimp only [P]
    simp only [Polynomial.coeff_smul, Polynomial.coeff_add,
      Polynomial.coeff_map, smul_eq_mul, starRingEnd_apply, map_mul, map_inv₀,
      map_ofNat, map_add]
    rw [star_star]
    ring
  let f : Real -> Complex := fun x => ∑ k ∈ P.support,
    P.coeff k * (-Complex.I) ^ k * ((deriv^[k]) psi) x
  obtain ⟨hfSmooth, hfCompact, hfTransform⟩ :=
    polynomial_differential_properties P psi hpsiSmooth hpsiCompact
  have hfHermitian : forall x, f (-x) = conj (f x) :=
    polynomial_differential_hermitian P psi hpsiHermitian hPcoeff
  have hfInterpolation (j : Fin M) : FL[f](z j) = r j := by
    rw [hfTransform, hP]
    dsimp only [target]
    exact div_mul_cancel₀ (r j) (hpsiNonzero j)
  have hallCompact : IsCompact (tsupport psi ∪ tsupport f) :=
    hpsiCompact.isCompact.union hfCompact.isCompact
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Real)).mp hallCompact.isBounded
  let L : Real := abs R + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hwindow : tsupport psi ∪ tsupport f <= Ioo (-L) L := by
    intro x hx
    have hxR : abs x <= R := by
      simpa using hR hx
    rw [mem_Ioo]
    have hxAbs : abs x < L := lt_of_le_of_lt hxR (by
      dsimp only [L]
      linarith [le_abs_self R])
    exact (abs_lt.mp hxAbs)
  refine ⟨L, psi, P, f, hL, hpsiSmooth, hpsiCompact,
    ?_, hpsiNonzero, ?_, rfl, hfSmooth, hfCompact, ?_, hfHermitian,
    hfTransform, hfInterpolation⟩
  · exact fun x hx => hwindow (Or.inl hx)
  · intro j
    simpa only [target] using hP j
  · exact fun x hx => hwindow (Or.inr hx)

#print axioms finite_exact_paley_wiener_interpolation

end D5.S3.Weil.TestFunctions.FinitePaleyWienerInterpolation
