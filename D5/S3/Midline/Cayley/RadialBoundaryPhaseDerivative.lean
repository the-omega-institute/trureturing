/- GID: D5/S3/Midline/Cayley/RadialBoundaryPhaseDerivative
   generality: I
   mirror-B: D5/B/S3/Midline/Cayley/RadialBoundaryPhaseDerivative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equate Cayley radial and boundary phase derivatives with the Poisson kernel. -/

import D5.S3.Weil.TestFunctions.CayleyMomentTransport
import D5.S3.Weil.ZetaAnalytic.RiemannPoissonDensity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Radial boundary phase derivative

The boundary argument is represented by its global smooth lift
`pi - 2 * arctan (gamma / a)`.  Its exponential is the canonical boundary
Cayley point, so the statement is independent of a principal-argument branch
cut at the point `-1`.

Library-search audit trail (2026-08-31):

* D5 searches for radial Cayley derivatives, boundary phase derivatives,
  Poisson kernels, and Cauchy-Riemann identities found no whole-statement
  owner.  `CayleyMomentTransport` supplies the canonical `cayleyCharacter`
  and its positive-scale circle bundling; its private angle calculation is
  inlined here instead of being redeclared as a second named owner.
* Body-shape searches for the off-axis coordinate
  `(gamma - I * delta + I * a) / (gamma - I * delta - I * a)` found no D5
  primitive.  The coordinate and all derived source objects are therefore
  constructed locally in the public theorem.
* Pinned Mathlib supplies `Real.hasDerivAt_arctan`, `Real.hasDerivAt_log`,
  complex norm-square identities, and elementary trigonometric formulas, but
  no packaged radial-boundary-phase theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped Topology
open D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography
open D5.S3.Weil.TestFunctions.CayleyMomentTransport
open D5.S3.Weil.ZetaAnalytic.RiemannPoissonDensity

namespace D5.S3.Midline.Cayley.RadialBoundaryPhaseDerivative

/-- The logarithmic normal displacement of the off-axis Cayley coordinate and
the smooth boundary phase lift have the same Poisson-kernel derivative.  The
public unit-circle clauses record that the normal coordinate is invisible
exactly on the boundary axis. -/
theorem radial_boundary_phase_derivative (a gamma : Real) (ha : 0 < a) :
    let cayleyCoordinate := fun gamma delta : Real =>
      (((gamma : Complex) - Complex.I * delta + Complex.I * a) /
        ((gamma : Complex) - Complex.I * delta - Complex.I * a))
    let radialCoordinate := fun gamma delta : Real =>
      Real.log ‖cayleyCoordinate gamma delta‖
    let boundaryPhase := fun gamma : Real =>
      Real.pi - 2 * Real.arctan (gamma / a)
    let poissonKernel := fun gamma : Real =>
      D5.S3.Weil.ZetaAnalytic.RiemannPoissonDensity.poissonKernel a gamma
    ((Circle.exp (boundaryPhase gamma) : Circle) : Complex) =
        cayleyCoordinate gamma 0 ∧
      ‖cayleyCoordinate gamma 0‖ = 1 ∧
      (∀ delta, delta ≠ 0 → ‖cayleyCoordinate gamma delta‖ ≠ 1) ∧
      HasDerivAt (radialCoordinate gamma)
        (-2 * Real.pi * poissonKernel gamma) 0 ∧
      HasDerivAt boundaryPhase
        (-2 * Real.pi * poissonKernel gamma) gamma := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · let t : Real := gamma / a
    have htden : 1 + t ^ 2 ≠ 0 := by positivity
    have hcos : Real.cos (2 * Real.arctan t) =
        (1 - t ^ 2) / (1 + t ^ 2) := by
      rw [Real.cos_two_mul, Real.cos_sq_arctan]
      field_simp [htden]
      ring
    have hsin : Real.sin (2 * Real.arctan t) =
        2 * t / (1 + t ^ 2) := by
      rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
      have hsqrt : Real.sqrt (1 + t ^ 2) ≠ 0 := by positivity
      field_simp [hsqrt]
      rw [Real.sq_sqrt (by positivity)]
    rw [Circle.coe_exp, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [Real.cos_pi_sub, Real.sin_pi_sub, hcos, hsin]
    simp only [Complex.ofReal_zero, mul_zero, sub_zero]
    change _ = cayleyCharacter a gamma
    rw [cayleyCharacter]
    dsimp only [t]
    push_cast
    have hdenominator : (gamma : Complex) - Complex.I * a ≠ 0 := by
      intro h
      have himaginary := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re] at himaginary
      norm_num at himaginary
      linarith
    field_simp [hdenominator, htden, ha.ne']
    have hsum : ((a : Complex) ^ 2 + (gamma : Complex) ^ 2) ≠ 0 := by
      exact_mod_cast (show a ^ 2 + gamma ^ 2 ≠ 0 by positivity)
    have hright : (gamma : Complex) - (a : Complex) * Complex.I ≠ 0 := by
      simpa [mul_comm] using hdenominator
    field_simp [hsum, hright]
    ring_nf
    simp only [Complex.I_sq]
    ring
  · simp only [Complex.ofReal_zero, mul_zero, sub_zero]
    change ‖cayleyCharacter a gamma‖ = 1
    exact mem_sphere_zero_iff_norm.mp (cayleyCircle a ha gamma).property
  · intro delta hdelta hunit
    let numerator : Complex :=
      (gamma : Complex) - Complex.I * delta + Complex.I * a
    let denominator : Complex :=
      (gamma : Complex) - Complex.I * delta - Complex.I * a
    change ‖numerator / denominator‖ = 1 at hunit
    by_cases hdenominator : denominator = 0
    · rw [hdenominator, div_zero, norm_zero] at hunit
      norm_num at hunit
    · rw [norm_div] at hunit
      have hdenominatorNorm : ‖denominator‖ ≠ 0 :=
        norm_ne_zero_iff.mpr hdenominator
      have hnorm : ‖numerator‖ = ‖denominator‖ :=
        (div_eq_one_iff_eq hdenominatorNorm).mp hunit
      have hsquare := congrArg (fun x : Real => x ^ 2) hnorm
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
        Complex.normSq_apply] at hsquare
      dsimp only [numerator, denominator] at hsquare
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
        zero_mul, one_mul, add_zero, sub_zero, Complex.add_im,
        Complex.sub_im, zero_sub] at hsquare
      norm_num [Complex.mul_im] at hsquare
      have : delta = 0 := by nlinarith
      exact hdelta this
  · let explicitRadius := fun delta : Real =>
      Real.log (gamma ^ 2 + (a - delta) ^ 2) / 2 -
        Real.log (gamma ^ 2 + (a + delta) ^ 2) / 2
    have hdenominator : gamma ^ 2 + a ^ 2 ≠ 0 := by positivity
    have hminus : HasDerivAt
        (fun delta : Real => gamma ^ 2 + (a - delta) ^ 2)
        (-(2 * a)) 0 := by
      have hlinear : HasDerivAt (fun delta : Real => a - delta) (-1) 0 := by
        simpa using (hasDerivAt_id (0 : Real)).const_sub a
      have hraw := (hlinear.pow 2).const_add (gamma ^ 2)
      simpa only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one,
        sub_zero, mul_one, mul_neg, neg_neg] using hraw
    have hplus : HasDerivAt
        (fun delta : Real => gamma ^ 2 + (a + delta) ^ 2)
        (2 * a) 0 := by
      have hlinear : HasDerivAt (fun delta : Real => a + delta) 1 0 := by
        simpa [add_comm] using (hasDerivAt_id (0 : Real)).add_const a
      have hraw := (hlinear.pow 2).const_add (gamma ^ 2)
      simpa only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one,
        add_zero, mul_one] using hraw
    have hexplicit : HasDerivAt explicitRadius
        (-2 * a / (gamma ^ 2 + a ^ 2)) 0 := by
      have hminusNonzero : gamma ^ 2 + (a - 0) ^ 2 ≠ 0 := by
        simpa using hdenominator
      have hplusNonzero : gamma ^ 2 + (a + 0) ^ 2 ≠ 0 := by
        simpa using hdenominator
      have hraw := (hminus.log hminusNonzero).div_const 2 |>.sub
        ((hplus.log hplusNonzero).div_const 2)
      apply hraw.congr_deriv
      field_simp [hdenominator]
      ring
    have heventually :
        (fun delta : Real => Real.log
          ‖((gamma : Complex) - Complex.I * delta + Complex.I * a) /
            ((gamma : Complex) - Complex.I * delta - Complex.I * a)‖) =ᶠ[𝓝 0]
          explicitRadius := by
      filter_upwards [Metric.ball_mem_nhds (0 : Real) ha] with delta hball
      have habs : |delta| < a := by
        simpa [Real.dist_eq] using hball
      have hminusPositive : 0 < a - delta := by
        linarith [le_abs_self delta]
      have hplusPositive : 0 < a + delta := by
        linarith [neg_abs_le delta]
      have hnumerator :
          (gamma : Complex) - Complex.I * delta + Complex.I * a ≠ 0 := by
        intro h
        have himaginary := congrArg Complex.im h
        simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im,
          Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.zero_im, zero_mul, one_mul, zero_sub, zero_add] at himaginary
        linarith
      have hdenominatorComplex :
          (gamma : Complex) - Complex.I * delta - Complex.I * a ≠ 0 := by
        intro h
        have himaginary := congrArg Complex.im h
        simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.zero_im,
          zero_mul, one_mul, zero_sub] at himaginary
        linarith
      rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr hnumerator)
        (norm_ne_zero_iff.mpr hdenominatorComplex)]
      rw [Complex.norm_def, Complex.norm_def,
        Real.log_sqrt (Complex.normSq_nonneg _),
        Real.log_sqrt (Complex.normSq_nonneg _)]
      dsimp only [explicitRadius]
      congr 2 <;>
        simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re,
          Complex.ofReal_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
          Complex.I_im,
          Complex.ofReal_im, zero_mul, one_mul, add_zero, sub_zero,
          Complex.add_im, Complex.sub_im, zero_add, zero_sub] <;> ring
    have hsource := hexplicit.congr_of_eventuallyEq heventually
    apply hsource.congr_deriv
    rw [D5.S3.Weil.ZetaAnalytic.RiemannPoissonDensity.poissonKernel]
    field_simp [Real.pi_ne_zero, hdenominator]
  · have hbase := (Real.hasDerivAt_arctan (gamma / a)).comp gamma
      ((hasDerivAt_id gamma).div_const a) |>.const_mul 2 |>.const_sub Real.pi
    have hvalue :
        -(2 * ((1 / (1 + (gamma / a) ^ 2)) * (1 / a))) =
          -2 * Real.pi *
            poissonKernel a gamma := by
      rw [D5.S3.Weil.ZetaAnalytic.RiemannPoissonDensity.poissonKernel]
      field_simp [Real.pi_ne_zero, ha.ne',
        show gamma ^ 2 + a ^ 2 ≠ 0 by positivity]
      ring
    simpa only [Function.comp_apply, id_eq] using hbase.congr_deriv hvalue

#print axioms radial_boundary_phase_derivative

end D5.S3.Midline.Cayley.RadialBoundaryPhaseDerivative
