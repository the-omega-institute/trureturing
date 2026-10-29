/- GID: D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original integral lattice discriminant sectors and inverse theta dissection. -/

import D5.S3.VertexAlgebra.LatticePositiveEnergy
import D5.S3.Fourier.MatrixGaussianTheta
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.LinearAlgebra.BilinearForm.DualLattice

set_option autoImplicit false
set_option maxHeartbeats 800000

open Matrix
open scoped BigOperators

namespace D5.S3.VertexAlgebra.LatticeDiscriminantTheta
open LatticeGeneratingFieldLocality LatticePositiveEnergy
open D5.S3.Fourier.MatrixGaussian
noncomputable section

def gramReal (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℝ :=
  D.G.map (Int.cast : ℤ → ℝ)

def gramRat (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℚ :=
  D.G.map (Int.cast : ℤ → ℚ)

def gramMap (D : LatticeData) : Charge D →ₗ[ℤ] Charge D := Matrix.toLin' D.G

def gramRange (D : LatticeData) : Submodule ℤ (Charge D) := (gramMap D).range

/-- The actual cokernel of the original integral Gram endomorphism. -/
abbrev Discriminant (D : LatticeData) := Charge D ⧸ gramRange D

def classOf (D : LatticeData) (r : Charge D) : Discriminant D :=
  Submodule.Quotient.mk r

private lemma real_det (D : LatticeData) : (gramReal D).det = (D.G.det : ℝ) := by
  exact (Int.castRingHom ℝ).map_det D.G |>.symm

private lemma rat_det (D : LatticeData) : (gramRat D).det = (D.G.det : ℚ) := by
  exact (Int.castRingHom ℚ).map_det D.G |>.symm

private lemma real_unit (D : LatticeData) (hD : (gramReal D).PosDef) :
    IsUnit (gramReal D).det := isUnit_iff_ne_zero.mpr hD.det_pos.ne'

private lemma rat_unit (D : LatticeData) (hD : (gramReal D).PosDef) :
    IsUnit (gramRat D).det := by
  apply isUnit_iff_ne_zero.mpr
  rw [rat_det]
  exact_mod_cast (show D.G.det ≠ 0 by
    intro h
    have := hD.det_pos
    simp [real_det, h] at this)

private lemma gramMap_injective (D : LatticeData) (hD : (gramReal D).PosDef) :
    Function.Injective (gramMap D) := by
  intro x y h
  have hc : gramReal D *ᵥ (fun i => (x i : ℝ)) =
      gramReal D *ᵥ (fun i => (y i : ℝ)) := by
    simpa only [gramMap, Matrix.toLin'_apply, gramReal,
      ← (Int.castRingHom ℝ).map_mulVec] using congrArg (fun v i => (v i : ℝ)) h
  have he := (Matrix.mulVec_injective_iff_isUnit.mpr
    ((gramReal D).isUnit_iff_isUnit_det.mpr (real_unit D hD))) hc
  ext i
  exact_mod_cast congrFun he i

private def rangeEquiv (D : LatticeData) (hD : (gramReal D).PosDef) :
    Charge D ≃ₗ[ℤ] gramRange D :=
  LinearEquiv.ofInjective (gramMap D) (gramMap_injective D hD)

instance discriminantFinite (D : LatticeData) [hD : Fact (gramReal D).PosDef] :
    Finite (Discriminant D) :=
  Submodule.finiteQuotientOfFreeOfRankEq (gramRange D) (rangeEquiv D hD.out).symm.finrank_eq

private lemma discriminant_card (D : LatticeData) (hD : (gramReal D).PosDef) :
    Nat.card (Discriminant D) = D.G.det.natAbs := by
  have h := Submodule.natAbs_det_equiv (gramRange D) (rangeEquiv D hD)
  have he : (gramRange D).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap ((rangeEquiv D hD) : Charge D →+ gramRange D) =
      gramMap D := by
    ext x i
    rfl
  rw [he, gramMap, LinearMap.det_toLin'] at h
  exact h.symm

/-- Inversion is performed in the rational scalar extension. -/
def inverseRat (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℚ := (gramRat D)⁻¹

private lemma inverse_cast (D : LatticeData) (hD : (gramReal D).PosDef) :
    (inverseRat D).map (Rat.castHom ℝ) = (gramReal D)⁻¹ := by
  apply (Matrix.inv_eq_right_inv ?_).symm
  have h := congrArg (fun A : Matrix (Fin D.rank) (Fin D.rank) ℚ =>
    A.map (Rat.castHom ℝ)) (Matrix.mul_nonsing_inv (gramRat D) (rat_unit D hD))
  simpa [← RingHom.mapMatrix_apply, map_mul, gramReal, gramRat, inverseRat,
    Matrix.map_map, Function.comp_def] using h

private lemma gramReal_symm (D : LatticeData) : (gramReal D)ᵀ = gramReal D := by
  ext i j
  exact congrArg (Int.cast : ℤ → ℝ) (D.symmetric j i)

private lemma gramRat_symm (D : LatticeData) : (gramRat D)ᵀ = gramRat D := by
  ext i j
  exact congrArg (Int.cast : ℤ → ℚ) (D.symmetric j i)

end
end D5.S3.VertexAlgebra.LatticeDiscriminantTheta
