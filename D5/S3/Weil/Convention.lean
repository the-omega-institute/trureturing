/- GID: D5/S3/Weil/Convention
   generality: I
   mirror-B: none(waiver:formal-analysis-foundation-only)
   mirror-E: none(waiver:definitions-and-mathlib-inventory-only)
   anchors: []
   digest: Fix classical zeta and angular-frequency Fourier conventions for the Weil ladder. -/

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace D5.S3.Weil.Convention

/-!
The convention is the angular-frequency normalization
`hat g (xi) = integral x, exp (-i * xi * x) * g x`.  Thus the inverse
transform carries `1 / (2 * pi)`.  Mathlib's real Fourier transform uses
`exp (-2 * pi * i * x * w)`; the corresponding mathlib frequency is
`w = xi / (2 * pi)`.

The exact Weil explicit-formula identity is deliberately absent.  It is a
later binding obligation (D5-T0018-F), not a theorem of this convention file.
-/

/-- Whether the pinned mathlib tree directly supplies a requested analytic object. -/
inductive MathlibAvailability where
  | found
  | missing
  deriving DecidableEq, Repr

/-- The classical zeta has the concrete total-function type used by mathlib. -/
abbrev ZetaFunction := ℂ → ℂ

/-- The Riemann zeta convention is exactly mathlib's `riemannZeta`. -/
noncomputable def classicalZeta : ZetaFunction := riemannZeta

/-- The unique meromorphic pole is at `s = 1`; mathlib totalizes the value there. -/
def zetaPole : ℂ := 1

/-- The self-dual abscissa in the functional equation. -/
noncomputable def criticalAbscissa : ℝ := 1 / 2

/-- The kernel for the angular-frequency Fourier-Laplace transform. -/
noncomputable def fourierKernel (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-Complex.I * z * (x : ℂ))

/-- Convert angular frequency to mathlib's `2 * pi` Fourier frequency. -/
noncomputable def mathlibFrequency (xi : ℝ) : ℝ := xi / (2 * Real.pi)

/-- The scalar in the inverse angular-frequency Fourier transform. -/
noncomputable def inverseFourierFactor : ℝ := (2 * Real.pi)⁻¹

/-- The constant term in the classical zeta explicit formula (Weil 1952). -/
noncomputable def logTwoPi : ℝ := Real.log (2 * Real.pi)

/-- The real shift in the completed-zeta digamma argument `1/4 + i*t/2`. -/
noncomputable def archimedeanShift : ℝ := 1 / 4

/-- The frequency scale in the completed-zeta digamma argument. -/
noncomputable def archimedeanFrequencyScale : ℝ := 1 / 2

/-- `riemannZeta : ℂ → ℂ` and its continuation away from one are present. -/
def riemannZetaStatus : MathlibAvailability := .found

/-- `Fourier.fourierIntegral` and the real specialization `𝓕` are present. -/
def fourierIntegralStatus : MathlibAvailability := .found

/-- Bundled rapidly decreasing smooth functions are present as `SchwartzMap`. -/
def schwartzMapStatus : MathlibAvailability := .found

/-- Bundled smooth compactly supported functions are present as `TestFunction`. -/
def testFunctionStatus : MathlibAvailability := .found

/-- No direct pinned theorem states entire Fourier-Laplace extension from compact support. -/
def compactSupportFourierLaplaceEntireStatus : MathlibAvailability := .missing

/-- No canonical zeta Weil explicit-formula functional is present in pinned mathlib. -/
def canonicalWeilExplicitFormulaStatus : MathlibAvailability := .missing

@[simp] theorem classical_zeta_eq_mathlib : classicalZeta = riemannZeta := rfl

/-- The only analytic fact frozen at level A is mathlib's existing off-pole result. -/
theorem classical_zeta_analytic_off_pole :
    AnalyticOnNhd ℂ classicalZeta ({zetaPole}ᶜ : Set ℂ) := by
  simpa [classicalZeta, zetaPole] using analyticOn_riemannZeta

end D5.S3.Weil.Convention
