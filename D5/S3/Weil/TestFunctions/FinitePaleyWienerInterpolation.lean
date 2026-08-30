/- GID: D5/S3/Weil/TestFunctions/FinitePaleyWienerInterpolation
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/FinitePaleyWienerInterpolation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite compatible data admit exact compact smooth Fourier-Laplace interpolation. -/

import D5.S3.Fourier.FourierLaplaceEntire
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.Deriv.Support
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

private theorem hasCompactSupport_iterate_deriv
    (q : Nat) {g : Real -> Complex} (hg : HasCompactSupport g) :
    HasCompactSupport ((deriv^[q]) g) := by
  induction q with
  | zero => simpa
  | succ q ih =>
      rw [Function.iterate_succ_apply']
      exact ih.deriv

private theorem fourier_laplace_iterate_deriv
    (q : Nat) (g : Real -> Complex) (hgSmooth : ContDiff Real ∞ g)
    (hgCompact : HasCompactSupport g) (z : Complex) :
    FL[((deriv^[q]) g)](z) = (Complex.I * z) ^ q * FL[g](z) := by
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
      have hvCompact : HasCompactSupport v :=
        hasCompactSupport_iterate_deriv q hgCompact
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

set_option maxHeartbeats 2000000 in
-- Normalizing the canonical smooth bump expands several bundled support proofs.
private theorem exists_common_nonvanishing_seed {M : Nat} (z : Fin M -> Complex) :
    exists psi : Real -> Complex,
      ContDiff Real ∞ psi /\
      HasCompactSupport psi /\
      (forall j, FL[psi](z j) ≠ 0) := by
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
  let psi : Real -> Complex := fun x => psi0 (x / a)
  have hpsiSmooth : ContDiff Real ∞ psi := by
    exact psi0.contDiff.comp (by fun_prop)
  have hpsiCompact : HasCompactSupport psi := by
    have hhome := psi0.hasCompactSupport.comp_homeomorph
      (Homeomorph.mulRight₀ a⁻¹ (inv_ne_zero ha.ne'))
    simpa only [psi, Function.comp_def, Homeomorph.coe_mulRight₀, div_eq_mul_inv] using hhome
  have hpsiNonzero (j : Fin M) : FL[psi](z j) ≠ 0 := by
    rw [show FL[psi](z j) = (a : Complex) *
        fourierLaplace psi0 ((a : Complex) * z j) by
      simpa only [psi] using fourier_laplace_scale psi0 a ha (z j)]
    apply mul_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne')
    intro hvanish
    have himage := hball (haz j)
    rw [mem_preimage, mem_ball, hvanish, dist_zero_left, norm_one] at himage
    exact lt_irrefl (1 : Real) himage
  exact ⟨psi, hpsiSmooth, hpsiCompact, hpsiNonzero⟩

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
      P.coeff k * (-Complex.I) ^ k * ((deriv^[k]) psi) x) :=
    (hasCompactSupport_iterate_deriv k hpsiCompact).mul_left
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

private theorem hermitian_symmetrization_properties
    (raw : Real -> Complex) (hrawSmooth : ContDiff Real ∞ raw)
    (hrawCompact : HasCompactSupport raw) :
    let f : Real -> Complex := fun x => (raw x + conj (raw (-x))) / 2
    ContDiff Real ∞ f /\
      HasCompactSupport f /\
      (forall x, f (-x) = conj (f x)) /\
      forall z, FL[f](z) = (FL[raw](z) + conj (FL[raw](conj z))) / 2 := by
  dsimp only
  have hreflectedCompact : HasCompactSupport (fun x : Real => raw (-x)) := by
    simpa [Function.comp_def, Homeomorph.neg] using
      hrawCompact.comp_homeomorph (Homeomorph.neg Real)
  have hconjCompact : HasCompactSupport (fun x : Real => conj (raw (-x))) :=
    hreflectedCompact.comp_left (by simp)
  have hnegSmooth : ContDiff Real ∞ (fun x : Real => raw (-x)) :=
    hrawSmooth.comp contDiff_neg
  have hconjSmooth : ContDiff Real ∞ (fun x : Real => conj (raw (-x))) := by
    change ContDiff Real ∞ (Complex.conjCLE ∘ fun x : Real => raw (-x))
    exact Complex.conjCLE.contDiff.comp hnegSmooth
  have hfSmooth : ContDiff Real ∞
      (fun x : Real => (raw x + conj (raw (-x))) / 2) :=
    (hrawSmooth.add hconjSmooth).div_const 2
  have hfCompact : HasCompactSupport
      (fun x : Real => (raw x + conj (raw (-x))) / 2) := by
    have hmul : HasCompactSupport
        ((fun _ : Real => (2 : Complex)⁻¹) *
          (raw + fun x : Real => conj (raw (-x)))) :=
      (hrawCompact.add hconjCompact).mul_left
    convert hmul using 1
    funext x
    simp only [Pi.mul_apply, Pi.add_apply, div_eq_mul_inv]
    ring
  refine ⟨hfSmooth, hfCompact, ?_, ?_⟩
  · intro x
    simp only [neg_neg]
    have hstarTwo : (starRingEnd Complex) 2 = 2 := by
      rw [starRingEnd_apply, star_ofNat]
    rw [map_div₀, map_add, hstarTwo]
    simp
    ring
  · intro z
    have hinvolution : FL[(fun x : Real => conj (raw (-x)))](z) =
        conj (FL[raw](conj z)) := by
      rw [← integral_conj]
      rw [← integral_neg_eq_self
        (fun x : Real =>
          Complex.exp (-Complex.I * z * (x : Complex)) * conj (raw (-x))) volume]
      apply integral_congr_ae
      filter_upwards with x
      simp only [neg_neg, map_mul]
      rw [← Complex.exp_conj]
      congr 2
      simp
    rw [show (fun x : Real =>
        Complex.exp (-Complex.I * z * (x : Complex)) *
          ((raw x + conj (raw (-x))) / 2)) =
        fun x : Real => (Complex.exp (-Complex.I * z * (x : Complex)) * raw x +
          Complex.exp (-Complex.I * z * (x : Complex)) * conj (raw (-x))) / 2 by
      funext x
      ring]
    rw [integral_div, integral_add]
    · rw [hinvolution]
    · exact (by fun_prop : Continuous (fun x : Real =>
          Complex.exp (-Complex.I * z * (x : Complex)) * raw x)).integrable_of_hasCompactSupport
        hrawCompact.mul_left
    · exact (by fun_prop : Continuous (fun x : Real =>
          Complex.exp (-Complex.I * z * (x : Complex)) *
            conj (raw (-x)))).integrable_of_hasCompactSupport hconjCompact.mul_left

/-- Finite distinct complex nodes with conjugation-compatible values admit an
exact compactly supported smooth Hermitian Fourier-Laplace interpolant. The
public witnesses record the nonvanishing seed, Lagrange polynomial,
polynomial differential construction, transform factorization, unchanged
support window, and final Hermitian symmetrization. Under the source's frozen
exp(-i z x) convention, integration by parts sends partial_x to i z, so its
printed P(i partial_x) psi yields P(-z); the public witness uses
P(-i partial_x) to realize the stated P(z) factorization. -/
theorem finite_exact_paley_wiener_interpolation
    {M : Nat} (z r : Fin M -> Complex) (hz : Function.Injective z)
    (conjIndex : Fin M -> Fin M)
    (hzConj : forall j, z (conjIndex j) = conj (z j))
    (hrConj : forall j, r (conjIndex j) = conj (r j)) :
    exists (L : Real) (psi : Real -> Complex) (P : Complex[X])
      (raw f : Real -> Complex),
      0 < L /\
      ContDiff Real ∞ psi /\
      HasCompactSupport psi /\
      tsupport psi <= Ioo (-L) L /\
      (forall j, FL[psi](z j) ≠ 0) /\
      (forall j, P.eval (z j) = r j / FL[psi](z j)) /\
      raw = (fun x => ∑ k ∈ P.support,
        P.coeff k * (-Complex.I) ^ k * ((deriv^[k]) psi) x) /\
      ContDiff Real ∞ raw /\
      HasCompactSupport raw /\
      tsupport raw <= Ioo (-L) L /\
      (forall w, FL[raw](w) = P.eval w * FL[psi](w)) /\
      f = (fun x => (raw x + conj (raw (-x))) / 2) /\
      ContDiff Real ∞ f /\
      HasCompactSupport f /\
      tsupport f <= Ioo (-L) L /\
      (forall x, f (-x) = conj (f x)) /\
      forall j, FL[f](z j) = r j := by
  obtain ⟨psi, hpsiSmooth, hpsiCompact, hpsiNonzero⟩ :=
    exists_common_nonvanishing_seed z
  let target : Fin M -> Complex := fun j => r j / FL[psi](z j)
  let P : Complex[X] := Lagrange.interpolate Finset.univ z target
  have hP (j : Fin M) : P.eval (z j) = target j := by
    exact Lagrange.eval_interpolate_at_node target hz.injOn (Finset.mem_univ j)
  let raw : Real -> Complex := fun x => ∑ k ∈ P.support,
    P.coeff k * (-Complex.I) ^ k * ((deriv^[k]) psi) x
  obtain ⟨hrawSmooth, hrawCompact, hrawTransform⟩ :=
    polynomial_differential_properties P psi hpsiSmooth hpsiCompact
  let f : Real -> Complex := fun x => (raw x + conj (raw (-x))) / 2
  obtain ⟨hfSmooth, hfCompact, hfHermitian, hfTransform⟩ :=
    hermitian_symmetrization_properties raw hrawSmooth hrawCompact
  have hrawInterpolation (j : Fin M) : FL[raw](z j) = r j := by
    rw [hrawTransform, hP]
    dsimp only [target]
    exact div_mul_cancel₀ (r j) (hpsiNonzero j)
  have hfInterpolation (j : Fin M) : FL[f](z j) = r j := by
    rw [hfTransform, hrawInterpolation]
    have hconjRaw : FL[raw](conj (z j)) = conj (r j) := by
      rw [← hzConj j, hrawInterpolation, hrConj]
    rw [hconjRaw]
    simp
  have hallCompact : IsCompact (tsupport psi ∪ tsupport raw ∪ tsupport f) :=
    (hpsiCompact.isCompact.union hrawCompact.isCompact).union hfCompact.isCompact
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Real)).mp hallCompact.isBounded
  let L : Real := abs R + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hwindow : tsupport psi ∪ tsupport raw ∪ tsupport f <= Ioo (-L) L := by
    intro x hx
    have hxR : abs x <= R := by
      simpa using hR hx
    rw [mem_Ioo]
    have hxAbs : abs x < L := lt_of_le_of_lt hxR (by
      dsimp only [L]
      linarith [le_abs_self R])
    exact (abs_lt.mp hxAbs)
  refine ⟨L, psi, P, raw, f, hL, hpsiSmooth, hpsiCompact,
    ?_, hpsiNonzero, ?_, rfl, hrawSmooth, hrawCompact, ?_, hrawTransform,
    rfl, hfSmooth, hfCompact, ?_, hfHermitian, hfInterpolation⟩
  · exact fun x hx => hwindow (Or.inl (Or.inl hx))
  · intro j
    simpa only [target] using hP j
  · exact fun x hx => hwindow (Or.inl (Or.inr hx))
  · exact fun x hx => hwindow (Or.inr hx)

#print axioms finite_exact_paley_wiener_interpolation

end D5.S3.Weil.TestFunctions.FinitePaleyWienerInterpolation
