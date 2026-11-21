/- GID: D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Matrix-unit realization of the geodesic modular operator and its Kronecker representation. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Matrix-unit realization of Capel and Costa Rico's geodesic relative entropy,
arXiv:2608.15833v1, equations (52), (59), and (63). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI

open Matrix
open scoped ComplexOrder CStarAlgebra Kronecker Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Equation (52), acting on an arbitrary Hilbert–Schmidt matrix. -/
def geodesicAction (t : ℝ) (r s X : Matrix n n ℂ) : Matrix n n ℂ :=
  cfc (fun z : ℝ => z ^ (1 - t)) r * X *
    (cfc (fun z : ℝ => (Real.sqrt z)⁻¹) s *
      cfc (fun z : ℝ => z ^ t) r * cfc (fun z : ℝ => (Real.sqrt z)⁻¹) s)

/-- The operator of equation (52) in the orthonormal matrix-unit basis. -/
def geodesicModular (t : ℝ) (r s : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  fun i j => geodesicAction t r s (Matrix.single j.1 j.2 1) i.1 i.2

/-- Vectorization of the square root in the same orthonormal basis. -/
def weightedVector (s : Matrix n n ℂ) (i : n × n) : ℂ :=
  cfc Real.sqrt s i.1 i.2

/-- Equation (59) with the relative-entropy function from equation (63). -/
def geodesicRelativeEntropy (t : ℝ) (r s : Matrix n n ℂ) : ℝ :=
  (star (weightedVector s) ⬝ᵥ
    (cfc (fun z : ℝ => z * Real.log z) (geodesicModular t r s) *ᵥ weightedVector s)).re

/-- Matrix units identify the right action with the transpose of its matrix. -/
theorem geodesicModular_eq_kronecker (t : ℝ) (r s : Matrix n n ℂ) :
    geodesicModular t r s =
      cfc (fun z : ℝ => z ^ (1 - t)) r ⊗ₖ
        (cfc (fun z : ℝ => (Real.sqrt z)⁻¹) s * cfc (fun z : ℝ => z ^ t) r *
          cfc (fun z : ℝ => (Real.sqrt z)⁻¹) s)ᵀ := by
  ext i j
  let L : Matrix n n ℂ := cfc (fun z : ℝ => z ^ (1 - t)) r
  let R : Matrix n n ℂ := cfc (fun z : ℝ => (Real.sqrt z)⁻¹) s * cfc (fun z : ℝ => z ^ t) r *
    cfc (fun z : ℝ => (Real.sqrt z)⁻¹) s
  change (L * Matrix.single j.1 j.2 (1 : ℂ) * R) i.1 i.2 = L i.1 j.1 * R j.2 i.2
  rw [Matrix.mul_mul_apply, Matrix.single_mulVec_eq, one_mul, dotProduct_smul,
    dotProduct_single_one]
  exact mul_comm (R j.2 i.2) (L i.1 j.1)

end

end D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI
