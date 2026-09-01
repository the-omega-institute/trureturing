/- GID: D5/S3/Zeros/Symmetry/CriticalCenterCoordinate
   generality: I
   mirror-B: D5/B/S3/Zeros/Symmetry/CriticalCenterCoordinate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify the critical line with the real axis by an affine complex equivalence. -/

import D5.S3.Weil.ZeroSum
import D5.S3.Zeros.Symmetry.FiniteShiftedBlaschkeSymmetry

/- Library-search audit trail (2026-09-01):
   * Repository searches found the exact coordinate definition as
     `ZeroSum.spectralParameter` and its reconstruction theorem. They are
     reused below rather than restated as a second source.
   * `ConvolutionSquareCriticalLine.gamma_im_eq_zero_iff_zero_on_critical_line`
     proves the real-axis criterion only for enumerated zeros. No declaration
     supplies both inverse laws for arbitrary complex points.
   * `FiniteShiftedBlaschkeSymmetry.critical_line_mirror_spec` identifies the
     critical line as the fixed locus of `Zeta23.reflect`; no existing theorem
     transports that involution to complex conjugation in spectral coordinates.
   * Pinned Mathlib supplies complex component simplification, ring
     normalization, and general multiplication equivalences. Searches of all
     installed Lean packages found no packaged critical-center equivalence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Symmetry.CriticalCenterCoordinate

open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroSum
open scoped ComplexConjugate

/-- The existing spectral parameter is the critical-center coordinate. -/
abbrev centralCoord : ℂ → ℂ :=
  spectralParameter

/-- Recover the original point from its critical-center coordinate. -/
def invCentralCoord (z : ℂ) : ℂ :=
  (criticalAbscissa : ℂ) + Complex.I * z

@[simp]
theorem central_coord_re (rho : ℂ) :
    (centralCoord rho).re = rho.im := by
  simp [centralCoord, spectralParameter, criticalAbscissa]

@[simp]
theorem central_coord_im (rho : ℂ) :
    (centralCoord rho).im = -(rho.re - (1 : ℝ) / 2) := by
  simp [centralCoord, spectralParameter, criticalAbscissa]

/-- The critical line becomes the real axis in critical-center coordinates. -/
theorem critical_line_iff_central_coord_im_zero (rho : ℂ) :
    rho.re = (1 : ℝ) / 2 ↔ (centralCoord rho).im = 0 := by
  rw [central_coord_im]
  constructor <;> intro h <;> linarith

@[simp]
theorem inv_central_coord_central_coord (rho : ℂ) :
    invCentralCoord (centralCoord rho) = rho := by
  exact spectralParameter_reconstruct rho

@[simp]
theorem central_coord_inv_central_coord (z : ℂ) :
    centralCoord (invCentralCoord z) = z := by
  apply Complex.ext <;>
    simp [centralCoord, invCentralCoord, spectralParameter, criticalAbscissa]

/-- Critical-center coordinates give an affine equivalence of the complex plane. -/
def centralCoordEquiv : ℂ ≃ ℂ where
  toFun := centralCoord
  invFun := invCentralCoord
  left_inv := inv_central_coord_central_coord
  right_inv := central_coord_inv_central_coord

/-- Functional-equation reflection acts by negation in center coordinates. -/
theorem central_coord_functional_reflection (rho : ℂ) :
    centralCoord (1 - rho) = -centralCoord rho :=
  spectralParameter_reflection rho

/-- Conjugating the original point acts by negative conjugation in center coordinates. -/
theorem central_coord_conjugation (rho : ℂ) :
    centralCoord (conj rho) = -conj (centralCoord rho) :=
  spectralParameter_conjugation rho

/-- Same-height reflection across the critical line becomes complex conjugation. -/
theorem central_coord_reflect (rho : ℂ) :
    centralCoord (Zeta23.reflect rho) = conj (centralCoord rho) := by
  simp [centralCoord, Zeta23.reflect, spectralParameter_reflection,
    spectralParameter_conjugation]

/-- The component formulas, real-axis criterion, inverse laws, and reflected
orbit action of the critical-center coordinate. -/
theorem critical_center_coordinate_spec (rho : ℂ) :
    (centralCoord rho).re = rho.im ∧
      (centralCoord rho).im = -(rho.re - (1 : ℝ) / 2) ∧
      (rho.re = (1 : ℝ) / 2 ↔ (centralCoord rho).im = 0) ∧
      invCentralCoord (centralCoord rho) = rho ∧
      (∀ z : ℂ, centralCoord (invCentralCoord z) = z) ∧
      centralCoord (1 - rho) = -centralCoord rho ∧
      centralCoord (conj rho) = -conj (centralCoord rho) ∧
      centralCoord (Zeta23.reflect rho) = conj (centralCoord rho) := by
  exact ⟨central_coord_re rho, central_coord_im rho,
    critical_line_iff_central_coord_im_zero rho,
    inv_central_coord_central_coord rho, central_coord_inv_central_coord,
    central_coord_functional_reflection rho, central_coord_conjugation rho,
    central_coord_reflect rho⟩

/-- The on-line point `1/2 + 3i` has the real center coordinate `3`. -/
theorem critical_line_coordinate_witness :
    let rho : ℂ := (1 / 2 : ℂ) + 3 * Complex.I
    centralCoord rho = (3 : ℂ) ∧
      rho.re = (1 : ℝ) / 2 ∧
      (centralCoord rho).im = 0 := by
  dsimp only
  constructor
  · apply Complex.ext <;> norm_num
  · norm_num

/-- The off-line point `3/4 + 3i` has center coordinate `3 - i/4`. -/
theorem off_line_coordinate_witness :
    let rho : ℂ := (3 / 4 : ℂ) + 3 * Complex.I
    centralCoord rho = (3 : ℂ) - (1 / 4 : ℂ) * Complex.I ∧
      rho.re ≠ (1 : ℝ) / 2 ∧
      (centralCoord rho).im = -(1 : ℝ) / 4 ∧
      (centralCoord rho).im ≠ 0 := by
  dsimp only
  constructor
  · apply Complex.ext <;> norm_num
  · norm_num

#print axioms critical_center_coordinate_spec
#print axioms critical_line_coordinate_witness
#print axioms off_line_coordinate_witness

end D5.S3.Zeros.Symmetry.CriticalCenterCoordinate
