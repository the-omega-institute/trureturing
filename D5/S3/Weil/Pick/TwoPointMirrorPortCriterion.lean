/- GID: D5/S3/Weil/Pick/TwoPointMirrorPortCriterion
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/TwoPointMirrorPortCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two regular upper-half-plane samples detect precisely the cross residue of a finite mirror-resolvent pair. -/

import OmegaBuild.Commands
import D5.S3.SpectralTopology.FiniteSpectralLocalizer
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

compile_only_with_mathlib

/-!
# Two-point visibility of a mirror-resolvent pair

For a nonreal pole `mu`, an arbitrary matrix residue `C` gives the reflected
transfer `C / (mu - z) + Cᴴ / (star mu - z)`. Its Nevanlinna Gram at two
distinct regular upper-half-plane locations is an invertible congruence of
the existing zero-scale spectral localizer of `C`.

Consequently the Gram is positive semidefinite exactly when `C = 0`.
For ports `Gminus`, `Gplus` the residue is `Gminusᴴ * Gplus`; equal ports
therefore detect every nonzero probe, while orthogonal bilateral ports can
have zero transfer. The result concerns a finite rational model and does
not identify its transfer with a completed-zeta or Weil readout.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder
open D5.S3.SpectralTopology.FiniteSpectralLocalizer

namespace D5.S3.Weil.Pick.TwoPointMirrorPortCriterion

variable {Port : Type*} [Fintype Port] [DecidableEq Port]

/-- A matrix residue and its adjoint at a conjugate pair of poles. -/
def mirrorResolvent (mu : ℂ) (C : Matrix Port Port ℂ) (z : ℂ) :
    Matrix Port Port ℂ :=
  (mu - z)⁻¹ • C + (star mu - z)⁻¹ • Cᴴ

/-- The matrix Nevanlinna difference quotient of the reflected transfer. -/
def mirrorNevanlinnaBlock (mu : ℂ) (C : Matrix Port Port ℂ) (z w : ℂ) :
    Matrix Port Port ℂ :=
  (z - star w)⁻¹ • (mirrorResolvent mu C z - (mirrorResolvent mu C w)ᴴ)

/-- The full Gram retains every port at each of the two sample locations. -/
def mirrorNevanlinnaGram (mu : ℂ) (C : Matrix Port Port ℂ) (z : Fin 2 → ℂ) :
    Matrix (Port ⊕ Port) (Port ⊕ Port) ℂ :=
  fromBlocks
    (mirrorNevanlinnaBlock mu C (z 0) (z 0))
    (mirrorNevanlinnaBlock mu C (z 0) (z 1))
    (mirrorNevanlinnaBlock mu C (z 1) (z 0))
    (mirrorNevanlinnaBlock mu C (z 1) (z 1))

/-- The ordinary two-point Cauchy matrix, lifted to the port coordinates. -/
def mirrorCauchyFeature (mu : ℂ) (z : Fin 2 → ℂ) :
    Matrix (Port ⊕ Port) (Port ⊕ Port) ℂ :=
  fromBlocks
    ((mu - z 0)⁻¹ • (1 : Matrix Port Port ℂ))
    ((star mu - z 0)⁻¹ • (1 : Matrix Port Port ℂ))
    ((mu - z 1)⁻¹ • (1 : Matrix Port Port ℂ))
    ((star mu - z 1)⁻¹ • (1 : Matrix Port Port ℂ))

private def factoredBlock (mu : ℂ) (C : Matrix Port Port ℂ) (z w : ℂ) :
    Matrix Port Port ℂ :=
  ((mu - z)⁻¹ * star ((star mu - w)⁻¹)) • C +
    ((star mu - z)⁻¹ * star ((mu - w)⁻¹)) • Cᴴ

private theorem nevanlinnaBlock_eq_factored
    (mu : ℂ) (C : Matrix Port Port ℂ) (z w : ℂ)
    (hz : mu - z ≠ 0 ∧ star mu - z ≠ 0)
    (hw : mu - w ≠ 0 ∧ star mu - w ≠ 0)
    (hcross : z - star w ≠ 0) :
    mirrorNevanlinnaBlock mu C z w = factoredBlock mu C z w := by
  have hw' : mu - star w ≠ 0 := by
    simpa using star_ne_zero.mpr hw.2
  have hw'' : star mu - star w ≠ 0 := by
    simpa using star_ne_zero.mpr hw.1
  ext i j
  simp [mirrorNevanlinnaBlock, mirrorResolvent, factoredBlock,
    Matrix.conjTranspose_smul]
  field_simp [hz.1, hz.2, hw', hw'', hcross]
  <;> ring

private theorem scalar_block_isUnit (a b c d : ℂ) (hdet : a * d - b * c ≠ 0) :
    IsUnit (fromBlocks (a • (1 : Matrix Port Port ℂ)) (b • 1)
      (c • 1) (d • 1)) := by
  have h11 : a * (d / (a * d - b * c)) + b * (-c / (a * d - b * c)) = 1 := by
    field_simp [hdet]
    <;> ring
  have h12 : a * (-b / (a * d - b * c)) + b * (a / (a * d - b * c)) = 0 := by
    ring
  have h21 : c * (d / (a * d - b * c)) + d * (-c / (a * d - b * c)) = 0 := by
    ring
  have h22 : c * (-b / (a * d - b * c)) + d * (a / (a * d - b * c)) = 1 := by
    field_simp [hdet]
    <;> ring
  apply isUnit_iff_exists_inv.mpr
  refine ⟨fromBlocks ((d / (a * d - b * c)) • (1 : Matrix Port Port ℂ))
    ((-b / (a * d - b * c)) • 1) ((-c / (a * d - b * c)) • 1)
    ((a / (a * d - b * c)) • 1), ?_⟩
  rw [fromBlocks_multiply]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    smul_smul, ← add_smul]
  rw [h11, h12, h21, h22]
  simp

private theorem cauchyFeature_isUnit (mu : ℂ) (z : Fin 2 → ℂ)
    (hmu : mu ≠ star mu) (hdistinct : z 0 ≠ z 1)
    (hregular : ∀ i, mu - z i ≠ 0 ∧ star mu - z i ≠ 0) :
    IsUnit (mirrorCauchyFeature (Port := Port) mu z) := by
  apply scalar_block_isUnit
  have hnum : (mu - star mu) * (z 1 - z 0) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hmu) (sub_ne_zero.mpr hdistinct.symm)
  intro h
  apply hnum
  field_simp [(hregular 0).1, (hregular 0).2,
    (hregular 1).1, (hregular 1).2] at h
  linear_combination h

private theorem localizer_posSemidef_iff (C : Matrix Port Port ℂ) :
    (finiteSpectralLocalizer (0 : Matrix Port Port ℂ) C 0 0 0).PosSemidef ↔
      C = 0 := by
  have heq : finiteSpectralLocalizer (0 : Matrix Port Port ℂ) C 0 0 0 =
      fromBlocks 0 C Cᴴ 0 := by
    simp [finiteSpectralLocalizer, spectralShift]
  rw [heq]
  constructor
  · intro h
    have htrace : (fromBlocks (0 : Matrix Port Port ℂ) C Cᴴ 0).trace = 0 := by
      simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]
    have hzero := h.trace_eq_zero_iff.mp htrace
    ext i j
    exact congrArg (fun A : Matrix (Port ⊕ Port) (Port ⊕ Port) ℂ =>
      A (Sum.inl i) (Sum.inr j)) hzero
  · rintro rfl
    simpa using (Matrix.PosSemidef.zero :
      (0 : Matrix (Port ⊕ Port) (Port ⊕ Port) ℂ).PosSemidef)

/-- Two distinct regular upper samples give a certified invertible congruence
with the zero-scale chiral spectral localizer, without any rank assumption on
the matrix residue. -/
theorem two_point_mirror_congruence
    (mu : ℂ) (C : Matrix Port Port ℂ) (z : Fin 2 → ℂ)
    (hmu : mu ≠ star mu) (hdistinct : z 0 ≠ z 1)
    (hupper : ∀ i, 0 < (z i).im)
    (hregular : ∀ i, mu - z i ≠ 0 ∧ star mu - z i ≠ 0) :
    mirrorNevanlinnaGram mu C z =
        mirrorCauchyFeature mu z *
          finiteSpectralLocalizer (0 : Matrix Port Port ℂ) C 0 0 0 *
            (mirrorCauchyFeature mu z)ᴴ ∧
      IsUnit (mirrorCauchyFeature (Port := Port) mu z) := by
  refine ⟨?_, cauchyFeature_isUnit mu z hmu hdistinct hregular⟩
  have hcross (i j : Fin 2) : z i - star (z j) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith [hupper i, hupper j]
  simp only [mirrorNevanlinnaGram, nevanlinnaBlock_eq_factored mu C _ _
    (hregular _) (hregular _) (hcross _ _)]
  simp [mirrorCauchyFeature, finiteSpectralLocalizer, spectralShift,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, factoredBlock, mul_comm, add_comm]

/-- A full two-location Nevanlinna Gram is positive semidefinite exactly when
the mirror pair has zero cross residue. One admissible pair already suffices. -/
theorem two_point_mirror_posSemidef_iff
    (mu : ℂ) (C : Matrix Port Port ℂ) (z : Fin 2 → ℂ)
    (hmu : mu ≠ star mu) (hdistinct : z 0 ≠ z 1)
    (hupper : ∀ i, 0 < (z i).im)
    (hregular : ∀ i, mu - z i ≠ 0 ∧ star mu - z i ≠ 0) :
    (mirrorNevanlinnaGram mu C z).PosSemidef ↔ C = 0 := by
  obtain ⟨hfactor, hunit⟩ :=
    two_point_mirror_congruence mu C z hmu hdistinct hupper hregular
  rw [hfactor]
  exact hunit.posSemidef_star_right_conjugate_iff.trans (localizer_posSemidef_iff C)

example
    {Fiber : Type*} [Fintype Fiber]
    (mu : ℂ) (G : Matrix Fiber Port ℂ) (z : Fin 2 → ℂ)
    (hmu : mu ≠ star mu) (hdistinct : z 0 ≠ z 1)
    (hupper : ∀ i, 0 < (z i).im)
    (hregular : ∀ i, mu - z i ≠ 0 ∧ star mu - z i ≠ 0) :
    (mirrorNevanlinnaGram mu (Gᴴ * G) z).PosSemidef ↔ G = 0 := by
  rw [two_point_mirror_posSemidef_iff mu (Gᴴ * G) z hmu hdistinct hupper hregular]
  exact Matrix.conjTranspose_mul_self_eq_zero

#print axioms two_point_mirror_congruence
#print axioms two_point_mirror_posSemidef_iff

end D5.S3.Weil.Pick.TwoPointMirrorPortCriterion
