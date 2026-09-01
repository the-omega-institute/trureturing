/- GID: D5/S3/Constants/Characterizations/FirstFrozenTheoremSuite
   generality: G
   mirror-B: D5/B/S3/Constants/Characterizations/FirstFrozenTheoremSuite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Ten classical completion identities share one checked theorem suite. -/

import D5.S1.FixedPoints.Algebraic.GoldenFixedPoint
import D5.S3.Analytic.Asymptotics.PrimeDeletedLambertMellin
import D5.S3.Analytic.Asymptotics.SpectralZetaContinuation
import D5.S3.Analytic.Characterizations.VisibleGaussianMass
import D5.S3.Constants.Characterizations.ExponentialFlowUniqueness
import D5.S3.Constants.Characterizations.LocalPrecisionUnit
import D5.S3.Constants.Limits.EulerResidualCancellation
import D5.S3.Fourier.CompletionConstants.GaussianSelfDualPi
import D5.S3.Zeros.Symmetry.FiniteShiftedBlaschkeSymmetry

/- Library-search audit trail (2026-09-01):
   * The repository has exact frozen declarations for the Fourier, exponential-flow,
     golden-fixed-point, local-precision, Euler-residual, critical-line, and
     prime-deleted Lambert clauses. They are imported and applied below.
   * `VisibleGaussianMass.visible_gaussian_mass` supplies the series side of the
     Ramanujan clause. Pinned Mathlib's `integral_gaussian_Ioi` and
     `intervalIntegral.integral_interval_add_Ioi` supply its completed tail.
   * Pinned Mathlib's `integral_comp_rpow_Ioi_of_pos` and
     `Complex.integral_cpow_mul_exp_neg_mul_Ioi` supply the Gaussian Mellin clause.
   * `SpectralZetaContinuation.linear_density_spectral_zeta_continuation` supplies
     the continuation and residue from the Golden counting-density estimate. No
     current-tree declaration proves that estimate for the source's explicit
     fractional-part spectrum, so it remains the single parameterized premise. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.Characterizations.FirstFrozenTheoremSuite

open Asymptotics Filter MeasureTheory Set Topology
open scoped ComplexConjugate FourierTransform

open D5.S1.FixedPoints.Algebraic.GoldenFixedPoint
open D5.S3.Analytic.Asymptotics.LinearDensityHeatTrace
open D5.S3.Analytic.Asymptotics.PrimeDeletedLambertMellin
open D5.S3.Analytic.Asymptotics.SpectralZetaContinuation
open D5.S3.Analytic.Characterizations.VisibleGaussianMass
open D5.S3.Constants.Characterizations.ExponentialFlowUniqueness
open D5.S3.Constants.Characterizations.LocalPrecisionUnit
open D5.S3.Constants.Limits.EulerResidualCancellation
open D5.S3.Fourier.CompletionConstants.GaussianSelfDualPi
open D5.S3.Weil.Convention
open D5.S3.Zeros.Symmetry.FiniteShiftedBlaschkeSymmetry

noncomputable section

/-- The source's Golden exponent, shifted so the Lean index `n = 0` represents
the mathematical index `n = 1`. -/
noncomputable def goldenExponent (n : Nat) : Real :=
  Real.sqrt 5 * (n + 1) + 1 / Real.goldenRatio -
    Int.fract (((n + 2 : Nat) : Real) * Real.goldenRatio)

/-- The bounded-error counting estimate asserted before the source's Golden
spectral-zeta theorem. This is the one external premise of the suite. -/
def GoldenCountingDensity : Prop :=
  (fun u => spectralCounting goldenExponent u - (1 / Real.sqrt 5) * u) =O[atTop]
    (fun _ => (1 : Real))

/-- The Gaussian tail completing the visible odd-double-factorial series. -/
noncomputable def ramanujanGaussianTail (x : Real) : Real :=
  Real.exp (x / 2) / Real.sqrt x *
    (∫ t : Real in Ioi (Real.sqrt x), Real.exp (-t ^ 2 / 2))

private theorem sqrt_five_gt_two : (2 : Real) < Real.sqrt 5 := by
  have hsquare : (Real.sqrt 5) ^ 2 = (5 : Real) := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 5]

private theorem goldenExponent_pos (n : Nat) : 0 < goldenExponent n := by
  have hn : (0 : Real) <= n := by positivity
  have hfract := Int.fract_lt_one
    (((n + 2 : Nat) : Real) * Real.goldenRatio)
  have hinv : 0 < (1 / Real.goldenRatio : Real) := by positivity
  dsimp only [goldenExponent]
  nlinarith [sqrt_five_gt_two]

private theorem goldenExponent_gt_nat (n : Nat) : (n : Real) < goldenExponent n := by
  have hn : (0 : Real) <= n := by positivity
  have hfract := Int.fract_lt_one
    (((n + 2 : Nat) : Real) * Real.goldenRatio)
  have hinv : 0 < (1 / Real.goldenRatio : Real) := by positivity
  dsimp only [goldenExponent]
  nlinarith [sqrt_five_gt_two]

private theorem goldenExponent_strictMono : StrictMono goldenExponent := by
  intro m n hmn
  have hmn' : (m : Real) + 1 <= (n : Real) := by exact_mod_cast hmn
  have hmfract := Int.fract_nonneg
    (((m + 2 : Nat) : Real) * Real.goldenRatio)
  have hnfract := Int.fract_lt_one
    (((n + 2 : Nat) : Real) * Real.goldenRatio)
  dsimp only [goldenExponent]
  nlinarith [sqrt_five_gt_two]

private theorem goldenExponent_finite_sublevels (u : Real) :
    Set.Finite {n | goldenExponent n <= u} := by
  obtain ⟨N : Nat, hN⟩ := exists_nat_gt u
  apply (Set.finite_le_nat N).subset
  intro n hn
  have hnlt : (n : Real) < u := (goldenExponent_gt_nat n).trans_le hn
  have hnN : n < N := by exact_mod_cast hnlt.trans hN
  exact hnN.le

/-- The Mellin transform of the Fourier-normalized Gaussian is its
Archimedean Gamma factor on the explicit convergence half-plane. -/
theorem gaussian_mellin_factor (s : Complex) (hs : 0 < s.re) :
    2 * (∫ x : Real in Ioi 0,
      (Real.exp (-Real.pi * x ^ 2) : Complex) * (x : Complex) ^ (s - 1)) =
      (Real.pi : Complex) ^ (-s / 2) * Complex.Gamma (s / 2) := by
  have hsHalf : 0 < (s / 2).re := by
    simpa only [Complex.div_ofNat_re] using
      (div_pos hs (by norm_num : (0 : Real) < 2))
  let g : Real -> Complex := fun y =>
    (y : Complex) ^ (s / 2 - 1) * Complex.exp (-(Real.pi * y : Real))
  have hsubstitution :=
    integral_comp_rpow_Ioi_of_pos (g := g) (p := (2 : Real)) (by norm_num)
  have hgamma := Complex.integral_cpow_mul_exp_neg_mul_Ioi hsHalf Real.pi_pos
  calc
    2 * (∫ x : Real in Ioi 0,
        (Real.exp (-Real.pi * x ^ 2) : Complex) * (x : Complex) ^ (s - 1)) =
        ∫ x : Real in Ioi 0,
          ((2 : Real) * x ^ ((2 : Real) - 1)) • g (x ^ (2 : Real)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : 0 < x := hx
      have hxne : (x : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
      have hpower :
          (x : Complex) *
              ((x : Complex) ^ (s / 2 - 1) * (x : Complex) ^ (s / 2 - 1)) =
            (x : Complex) ^ (s - 1) := by
        calc
          (x : Complex) *
                ((x : Complex) ^ (s / 2 - 1) * (x : Complex) ^ (s / 2 - 1)) =
              ((x : Complex) * (x : Complex) ^ (s / 2 - 1)) *
                (x : Complex) ^ (s / 2 - 1) := by ring
          _ = ((x : Complex) ^ (1 : Complex) * (x : Complex) ^ (s / 2 - 1)) *
                (x : Complex) ^ (s / 2 - 1) := by rw [Complex.cpow_one]
          _ = (x : Complex) ^ (1 + (s / 2 - 1)) *
                (x : Complex) ^ (s / 2 - 1) := by
              rw [← Complex.cpow_add _ _ hxne]
          _ = (x : Complex) ^ ((1 + (s / 2 - 1)) + (s / 2 - 1)) := by
              rw [← Complex.cpow_add _ _ hxne]
          _ = (x : Complex) ^ (s - 1) := by
              congr 1
              ring
      simp only [g, Real.rpow_two, Complex.real_smul, Complex.ofReal_mul,
        Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow]
      rw [show (x : Complex) ^ 2 = (x : Complex) * (x : Complex) by ring,
        Complex.mul_cpow_ofReal_nonneg hx0.le hx0.le, ← hpower]
      push_cast
      rw [show x ^ ((2 : Real) - 1) = x by norm_num [Real.rpow_one]]
      ring
    _ = ∫ y : Real in Ioi 0, g y := hsubstitution
    _ = (1 / Real.pi : Complex) ^ (s / 2) * Complex.Gamma (s / 2) := by
      simpa [g, mul_comm] using hgamma
    _ = (Real.pi : Complex) ^ (-s / 2) * Complex.Gamma (s / 2) := by
      congr 1
      rw [one_div, Complex.inv_cpow _ _ (by
          rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
          exact ne_of_lt Real.pi_pos), ← Complex.cpow_neg]
      congr 1
      ring

/-- The source's visible series plus its explicitly defined Gaussian tail is
the completed half-Gaussian mass. -/
theorem ramanujan_gaussian_completion (x : Real) (hx : 0 < x) :
    (∑' n : Nat, x ^ n / (Nat.doubleFactorial (2 * n + 1) : Real)) +
        ramanujanGaussianTail x =
      Real.sqrt (Real.pi * Real.exp x / (2 * x)) := by
  let f : Real -> Real := fun t => Real.exp (-t ^ 2 / 2)
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hf : IntegrableOn f (Ioi 0) := by
    have h : IntegrableOn
        (fun t : Real => Real.exp (-(1 / 2 : Real) * t ^ 2)) (Ioi 0) :=
      (integrable_exp_neg_mul_sq
        (by norm_num : (0 : Real) < 1 / 2)).integrableOn
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [f]
    congr 1
    ring
  have hsplit :
      (∫ t : Real in 0..Real.sqrt x, f t) +
          (∫ t : Real in Ioi (Real.sqrt x), f t) =
        ∫ t : Real in Ioi 0, f t :=
    intervalIntegral.integral_interval_add_Ioi hf
      (hf.mono_set (Ioi_subset_Ioi hsqrt.le))
  have hmass : (∫ t : Real in Ioi 0, f t) = Real.sqrt (Real.pi / 2) := by
    rw [show (∫ t : Real in Ioi 0, f t) =
        ∫ t : Real in Ioi 0, Real.exp (-(1 / 2 : Real) * t ^ 2) by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp only [f]
      congr 1
      ring]
    rw [integral_gaussian_Ioi]
    apply (sq_eq_sq₀ (by positivity :
      0 <= Real.sqrt (Real.pi / (1 / 2 : Real)) / 2)
      (Real.sqrt_nonneg _)).mp
    rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    ring
  rw [visible_gaussian_mass x hx, ramanujanGaussianTail]
  change Real.exp (x / 2) / Real.sqrt x * (∫ t : Real in 0..Real.sqrt x, f t) +
      Real.exp (x / 2) / Real.sqrt x *
        (∫ t : Real in Ioi (Real.sqrt x), f t) = _
  rw [← mul_add, hsplit, hmass]
  apply (sq_eq_sq₀ (by positivity :
    0 <= Real.exp (x / 2) / Real.sqrt x * Real.sqrt (Real.pi / 2))
    (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity : 0 <= Real.pi * Real.exp x / (2 * x))]
  have hsqrtSq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  have hmassSq : (Real.sqrt (Real.pi / 2)) ^ 2 = Real.pi / 2 :=
    Real.sq_sqrt (by positivity)
  have hexpSq : (Real.exp (x / 2)) ^ 2 = Real.exp x := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, div_pow, hsqrtSq, hmassSq, hexpSq]
  field_simp [hx.ne']

/-- The ten displayed results in the source atom, with the sole missing
Golden counting-density estimate exposed as a premise. -/
theorem first_frozen_theorem_suite
    (a x : Real) (ha : 0 < a) (hx : 0 < x)
    (E : Real -> Real) (hpositive : ∀ y, 0 < E y)
    (hregular : ContDiff Real 1 E)
    (hmul : ∀ y z, E (y + z) = E y * E z)
    (hnormalized : deriv E 0 = 1)
    (prime exponent : Nat) (hprime : prime.Prime) (hexponent : 1 < exponent)
    (s w : Complex) (hs : 0 < s.re) (hw : 1 < w.re)
    (hgoldenDensity : GoldenCountingDensity) :
    (𝓕 (fun y : Real => (Real.exp (-a * y ^ 2) : Complex)) =
        (fun y : Real => (Real.exp (-a * y ^ 2) : Complex)) <-> a = Real.pi) ∧
    (2 * (∫ y : Real in Ioi 0,
        (Real.exp (-Real.pi * y ^ 2) : Complex) * (y : Complex) ^ (s - 1)) =
      (Real.pi : Complex) ^ (-s / 2) * Complex.Gamma (s / 2)) ∧
    (∀ y, E y = Real.exp y) ∧
    (∀ y : Real, 0 < y ->
      (y = 1 + 1 / y <-> y = (1 + Real.sqrt 5) / 2)) ∧
    (∀ ell : Real,
      Real.exp (-ell) = (prime : Real)⁻¹ <-> ell = Real.log prime) ∧
    Tendsto
      (fun n : Nat => (harmonic n : Real) - Real.log n - Real.eulerMascheroniConstant)
      atTop (nhds 0) ∧
    (s = 1 - conj s <-> s.re = (1 : Real) / 2) ∧
    ((∑' n : Nat, x ^ n / (Nat.doubleFactorial (2 * n + 1) : Real)) +
      ramanujanGaussianTail x =
        Real.sqrt (Real.pi * Real.exp x / (2 * x))) ∧
    (mellin (primeDeletedLambertKernel prime exponent) w =
      Complex.Gamma w * riemannZeta w *
        riemannZeta (w + exponent) *
          (1 - (prime : Complex) ^ (-(w + exponent)))) ∧
    (IsSpectralZetaContinuation goldenExponent
        (continuedSpectralZeta goldenExponent (1 / Real.sqrt 5)) ∧
      Tendsto (fun z : Complex =>
          (z - 1) * continuedSpectralZeta goldenExponent (1 / Real.sqrt 5) z)
        (nhdsWithin 1 {1}ᶜ) (nhds ((1 / Real.sqrt 5 : Real) : Complex))) := by
  letI : Fact prime.Prime := ⟨hprime⟩
  refine ⟨gaussian_self_dual_iff a ha, gaussian_mellin_factor s hs,
    exponential_flow_unique E hpositive hregular hmul hnormalized, ?_, ?_,
    harmonic_log_euler_residual_tendsto_zero, ?_,
    ramanujan_gaussian_completion x hx,
    prime_deleted_lambert_mellin prime exponent hprime hexponent w hw, ?_⟩
  · intro y hy
    simpa [goldenReciprocalMap, eq_comm] using golden_fixed_point_unique.2.2 y hy
  · intro ell
    have hlocal := local_precision_unit_unique prime
    constructor
    · intro hell
      exact hlocal.1.2 ell ⟨hell.trans Padic.norm_p.symm, Padic.norm_p⟩
    · rintro rfl
      exact hlocal.1.1.1.trans hlocal.1.1.2
  · simpa [Zeta23.reflect, eq_comm] using (critical_line_mirror_spec s).2.2.2
  · exact linear_density_spectral_zeta_continuation goldenExponent
      (1 / Real.sqrt 5) goldenExponent_pos goldenExponent_strictMono
      goldenExponent_finite_sublevels hgoldenDensity

/-- A concrete normalized flow satisfies all four flow premises and evaluates
to the expected positive value at one. -/
example :
    (∀ y : Real, 0 < Real.exp y) ∧
      ContDiff Real 1 Real.exp ∧
      (∀ y z : Real, Real.exp (y + z) = Real.exp y * Real.exp z) ∧
      deriv Real.exp 0 = 1 ∧ Real.exp 1 = Real.exp 1 := by
  refine ⟨Real.exp_pos, Real.contDiff_exp, Real.exp_add, ?_, rfl⟩
  simpa using Real.hasDerivAt_exp 0 |>.deriv

/-- The zero flow gives a numerical negative probe: its derivative premise is
zero rather than one, and its claimed value at zero is false. -/
example :
    deriv (fun _ : Real => (0 : Real)) 0 = 0 ∧
      deriv (fun _ : Real => (0 : Real)) 0 ≠ 1 ∧
      (fun _ : Real => (0 : Real)) 0 ≠ Real.exp 0 := by
  norm_num

#print axioms first_frozen_theorem_suite

end

end D5.S3.Constants.Characterizations.FirstFrozenTheoremSuite
