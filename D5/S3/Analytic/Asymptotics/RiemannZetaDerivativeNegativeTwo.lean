/- GID: D5/S3/Analytic/Asymptotics/RiemannZetaDerivativeNegativeTwo
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/RiemannZetaDerivativeNegativeTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The zeta derivative at negative two is minus zeta three over four pi squared. -/

import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic

/- Library-search audit trail (2026-09-04):
   * D5 searches covered four-term zeta expansions, negative-one and
     negative-two values, zeta derivatives, Apéry's constant, reciprocal-zeta
     cancellation, and logarithmic curvature in symbolic and ASCII spellings.
     No declaration states the derivative identity proved below.
   * The gict-v3.6 digestion record and residual/digest indexes list this atom
     as residual-open with no coverage GID. The retired formalization-receipt
     tree is absent and was neither inspected nor recreated.
   * Pinned Mathlib directly owns `riemannZeta_zero`,
     `riemannZeta_neg_nat_eq_bernoulli`,
     `riemannZeta_neg_two_mul_nat_add_one`, and the sharper near-pole result
     `inv_riemannZeta_sub_sub_isLittleO`; none is repackaged here.
   * Generalized functional-equation and derivative searches found
     `riemannZeta_one_sub`, `Complex.hasDerivAt_cos`, and
     `Complex.Gamma_nat_eq_factorial`, but no derivative value at `-2`.
   * Logs of every origin/lane/math branch above origin/dev contain no matching
     atom identifier or equivalent in-flight derivative theorem.
   * The source's full asymptotic cannot be stated until `S`, `c1`, and `c2`
     have formal definitions. Also, pointwise `1 / riemannZeta 1 = 0` is false
     in Mathlib because the pole has a finite junk value. The theorem below
     therefore isolates the nontrivial analytic identity that justifies the
     displayed logarithmic coefficient. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Asymptotics.RiemannZetaDerivativeNegativeTwo

open Complex Filter Set Topology

private def functionalAmplitude (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-s) * Gamma s

private def functionalCosine (s : ℂ) : ℂ :=
  cos ((Real.pi : ℂ) * s / 2)

private def functionalRight (s : ℂ) : ℂ :=
  functionalAmplitude s * functionalCosine s * riemannZeta s

private theorem functional_equation_near_three :
    (fun s : ℂ => riemannZeta (1 - s)) =ᶠ[𝓝 (3 : ℂ)] functionalRight := by
  have hopen : IsOpen {s : ℂ | 2 < s.re} :=
    isOpen_lt continuous_const continuous_re
  have hthree : (3 : ℂ) ∈ {s : ℂ | 2 < s.re} := by norm_num
  filter_upwards [hopen.mem_nhds hthree] with s hs
  have hnegative (n : Nat) : s ≠ -n := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [neg_re, natCast_re] at hre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    change 2 < s.re at hs
    linarith
  have hone : s ≠ 1 := by
    intro heq
    subst s
    norm_num at hs
  simpa only [functionalRight, functionalAmplitude, functionalCosine] using
    riemannZeta_one_sub hnegative hone

/-- The functional equation differentiated at `s = 3` gives
`zeta'(-2) = -zeta(3)/(4*pi^2)`. This is the Apéry-value denominator entering
the logarithmic-curvature coefficient in the source expansion.
-/
theorem riemann_zeta_derivative_negative_two :
    deriv riemannZeta (-2) =
      -riemannZeta 3 / (4 * (Real.pi : ℂ) ^ 2) := by
  have hleft :
      deriv (fun s : ℂ => riemannZeta (1 - s)) 3 = -deriv riemannZeta (-2) := by
    have hinner : HasDerivAt (fun s : ℂ => 1 - s) (-1) 3 := by
      exact (hasDerivAt_id (3 : ℂ)).const_sub 1
    have hzeta : HasDerivAt riemannZeta (deriv riemannZeta (-2)) (-2) :=
      (differentiableAt_riemannZeta (s := (-2 : ℂ)) (by norm_num)).hasDerivAt
    have hzetaAtInner :
        HasDerivAt riemannZeta (deriv riemannZeta (-2)) (1 - (3 : ℂ)) := by
      convert hzeta using 1 <;> norm_num
    have hcomposed := (hzetaAtInner.comp (3 : ℂ) hinner).deriv
    change deriv (riemannZeta ∘ fun s : ℂ => 1 - s) 3 = -deriv riemannZeta (-2)
    simpa using hcomposed

  have htwoPi : 2 * (Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpower :
      DifferentiableAt ℂ (fun s : ℂ => (2 * (Real.pi : ℂ)) ^ (-s)) 3 :=
    ((hasDerivAt_id (3 : ℂ)).neg.const_cpow (Or.inl htwoPi)).differentiableAt
  have hgamma : DifferentiableAt ℂ Gamma 3 :=
    differentiableAt_Gamma 3 (by norm_cast; simp)
  have hamplitude : DifferentiableAt ℂ functionalAmplitude 3 := by
    have hfunction :
        (((fun _ : ℂ => (2 : ℂ)) * fun s : ℂ => (2 * (Real.pi : ℂ)) ^ (-s)) * Gamma) =
          functionalAmplitude := by
      funext s
      rfl
    rw [← hfunction]
    exact ((differentiableAt_const (c := (2 : ℂ))).mul hpower).mul hgamma

  have hargument :
      HasDerivAt (fun s : ℂ => (Real.pi : ℂ) * s / 2) ((Real.pi : ℂ) / 2) 3 := by
    simpa using ((hasDerivAt_id (3 : ℂ)).const_mul (Real.pi : ℂ)).div_const 2
  have hsin : sin ((Real.pi : ℂ) * 3 / 2) = -1 := by
    rw [show (Real.pi : ℂ) * 3 / 2 = (Real.pi : ℂ) + Real.pi / 2 by ring,
      sin_add_pi_div_two, cos_pi]
  have hcosine :
      HasDerivAt functionalCosine ((Real.pi : ℂ) / 2) 3 := by
    have hraw := (Complex.hasDerivAt_cos ((Real.pi : ℂ) * 3 / 2)).comp 3 hargument
    have hfunction :
        (fun s : ℂ => cos ((Real.pi : ℂ) * s / 2)) = functionalCosine := by
      funext s
      rfl
    rw [← hfunction]
    simpa [Function.comp_def, hsin] using hraw
  have hcosineValue : functionalCosine 3 = 0 := by
    rw [functionalCosine,
      show (Real.pi : ℂ) * 3 / 2 = (Real.pi : ℂ) + Real.pi / 2 by ring,
      cos_add_pi_div_two, sin_pi, neg_zero]
  have hzetaThree : DifferentiableAt ℂ riemannZeta 3 :=
    differentiableAt_riemannZeta (by norm_num)
  have hrightRaw :
      deriv functionalRight 3 =
        functionalAmplitude 3 * ((Real.pi : ℂ) / 2) * riemannZeta 3 := by
    have hderiv := (hamplitude.hasDerivAt.mul hcosine).mul hzetaThree.hasDerivAt
    have hfunction :
        functionalAmplitude * functionalCosine * riemannZeta = functionalRight := by
      funext s
      rfl
    rw [← hfunction]
    simpa [hcosineValue] using hderiv.deriv

  have hgammaThree : Gamma (3 : ℂ) = 2 := by
    convert Complex.Gamma_nat_eq_factorial 2 using 1 <;> norm_num
  have hpowerThree :
      (2 * (Real.pi : ℂ)) ^ (-(3 : ℂ)) = ((2 * (Real.pi : ℂ)) ^ 3)⁻¹ := by
    rw [Complex.cpow_neg]
    exact congrArg (fun z : ℂ => z⁻¹) (Complex.cpow_natCast (2 * (Real.pi : ℂ)) 3)
  have hconstant :
      functionalAmplitude 3 * ((Real.pi : ℂ) / 2) =
        1 / (4 * (Real.pi : ℂ) ^ 2) := by
    rw [functionalAmplitude, hpowerThree, hgammaThree]
    field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring
  have hright :
      deriv functionalRight 3 = riemannZeta 3 / (4 * (Real.pi : ℂ) ^ 2) := by
    rw [hrightRaw, hconstant]
    ring

  have hderivatives := functional_equation_near_three.deriv_eq
  rw [hleft, hright] at hderivatives
  linear_combination -hderivatives

#print axioms riemann_zeta_derivative_negative_two

end D5.S3.Analytic.Asymptotics.RiemannZetaDerivativeNegativeTwo
