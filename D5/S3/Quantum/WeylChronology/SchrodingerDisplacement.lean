/- GID: D5/S3/Quantum/WeylChronology/SchrodingerDisplacement
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:exact-symbolic-realization)
   anchors: []
   digest: Concrete continuous Weyl displacements act on wavefunctions without CCR axioms. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# A concrete continuous Weyl realization

In dimensionless quadratures [Q,P]=i/2, D(x+iy) acts as
`exp(i*(2*y*q-x*y))*f(q-x)`. We prove this function action's Weyl
composition law, inverse and pointwise intensity transport directly.
No CCR, truncated oscillator, Fock-space cutoff or Baker-Campbell-Hausdorff
axiom is introduced. The carrier is actual functions R -> C. L2 completion,
strong continuity and self-adjoint generator domains are not asserted here.

Library audit (2026-09-06): repository `Weyl` finds the frozen finite ZMod
clock/shift family in Quantum/Algebra, which cannot instantiate arbitrary
real translations. `Schrodinger` finds uncertainty/channel results, not this
continuous displacement action. Mathlib owns complex exp and its addition
and unit-modulus laws; those are reused. This classical representation is
not claimed as a new physical result.

Sources: Vutha et al., arXiv:1702.01833, displacement composition;
Fluehmann and Home, PRL 125, 043602 (2020), arXiv:1907.06478, displacement
readout; Razian et al., arXiv:2604.06565v1, eqs. (4)-(5), ancilla phase.
The latter is a 2026 preprint, not an experimental validation of this code.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.SchrodingerDisplacement

noncomputable section

/-- Continuous displacement in the Q=x convention (hbar=1/2). -/
def displacement (x y : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun q => Complex.exp (((2 * y * q - x * y : ℝ) : ℂ) * Complex.I) * f (q - x)

/-- The continuous cocycle is obtained from the literal wavefunction action.
The left operator acts last, as in ordinary operator multiplication. -/
theorem displacement_comp (x y u v : ℝ) (f : ℝ → ℂ) :
    displacement x y (displacement u v f) =
      Complex.exp (((y * u - x * v : ℝ) : ℂ) * Complex.I) •
        displacement (x + u) (y + v) f := by
  funext q
  have hexp :
      Complex.exp (((2 * y * q - x * y : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((2 * v * (q - x) - u * v : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((y * u - x * v : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((2 * (y + v) * q - (x + u) * (y + v) : ℝ) : ℂ) *
            Complex.I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hshift : q - x - u = q - (x + u) := by ring
  change _ * (_ * f (q - x - u)) = _ * (_ * f (q - (x + u)))
  rw [← mul_assoc, ← mul_assoc, hexp, hshift]

/-- Scalar phases pass through the displacement action. -/
theorem displacement_smul (x y : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    displacement x y (c • f) = c • displacement x y f := by
  funext q
  change _ * (c * f (q - x)) = c * (_ * f (q - x))
  ring

/-- Reversing both displacement coordinates is an exact two-sided inverse. -/
theorem displacement_inverse (x y : ℝ) (f : ℝ → ℂ) :
    displacement (-x) (-y) (displacement x y f) = f ∧
      displacement x y (displacement (-x) (-y) f) = f := by
  constructor <;> rw [displacement_comp] <;>
    simp [displacement, sub_eq_add_neg, mul_comm]

/-- Multiplication by a phase cannot be detected in the pointwise intensity. -/
theorem phase_intensity_invisible (θ : ℝ) (z : ℂ) :
    Complex.normSq (Complex.exp ((θ : ℂ) * Complex.I) * z) = Complex.normSq z := by
  have hphase : Complex.normSq (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
    rw [Complex.normSq_apply]
    simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [Complex.normSq_mul, hphase, one_mul]

/-- Intensity is translated; the cocycle is invisible without a phase reference. -/
theorem displacement_intensity (x y q : ℝ) (f : ℝ → ℂ) :
    Complex.normSq (displacement x y f q) = Complex.normSq (f (q - x)) :=
  phase_intensity_invisible (2 * y * q - x * y) (f (q - x))

#print axioms displacement_comp
#print axioms displacement_inverse
#print axioms displacement_intensity

end
end D5.S3.Quantum.WeylChronology.SchrodingerDisplacement
