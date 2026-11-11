/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonJordan
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonJordan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Cartesian Fourier similarity and generalized eigenspaces of alternating polygons. -/

import D5.S3.FluidDynamics.Vortices.AlternatingPolygonFourier

/-! Transport of the complete paired restrictions to the actual Cartesian derivative. -/
noncomputable section
open scoped BigOperators
open Matrix

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open InverseChordCirculant AlternatingPolygonSpectrum AlternatingPolygonModes
open AlternatingPolygonFourier

abbrev Cartesian (m : ℕ) := Fin (2 * m) ⊕ Fin (2 * m) → ℂ
abbrev Modes (m : ℕ) := ZMod (2 * m) → ℂ × ℂ

/-- The actual complexification, acting on Cartesian displacements. -/
def actualOperator (m : ℕ) : Module.End ℂ (Cartesian m) :=
  ((jacobian (2 * m)).map Complex.ofRealHom).toLin'

def modeOperator (m : ℕ) : Module.End ℂ (Modes m) :=
  pairedOperator (fun q => (ell m q : ℂ)) (fun q => ((ell m (q + m) + 1 : ℝ) : ℂ))

private theorem complex_rotation_inverse (N : ℕ) :
    (rotation N).map Complex.ofRealHom * (rotation N).transpose.map Complex.ofRealHom = 1 := by
  rw [← Matrix.map_mul, rotation_mul_transpose]
  exact map_one Complex.ofRealHom.mapMatrix

/-- The existing orthogonal rotation, used as an actual coordinate equivalence. -/
def rotationCoordinates (m : ℕ) : Cartesian m ≃ₗ[ℂ] Cartesian m :=
  Matrix.toLin'OfInv (complex_rotation_inverse (2 * m))
    (mul_eq_one_comm.mp (complex_rotation_inverse (2 * m)))

/-- Cartesian -> radial/tangential -> paired Fourier coordinates. -/
def cartesianCoordinates (m : ℕ) [NeZero (2 * m)] : Cartesian m ≃ₗ[ℂ] Modes m :=
  (rotationCoordinates m).trans (frequencyCoordinates m)

/-- Every coordinate, and therefore every invariant block, belongs to the
actual Cartesian derivative, with no assumed spectral hypothesis. -/
theorem actual_normal_form (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) (v : Cartesian m) :
    cartesianCoordinates m (actualOperator m v) = modeOperator m (cartesianCoordinates m v) := by
  let R := (AlternatingPolygonSpectrum.rotation (2 * m)).map Complex.ofRealHom
  let T := (AlternatingPolygonSpectrum.rotation (2 * m)).transpose.map Complex.ofRealHom
  let J := (jacobian (2 * m)).map Complex.ofRealHom
  let M := (Matrix.fromBlocks 0 (blockB m) (blockC m) 0).map Complex.ofRealHom
  have hRT : R * T = 1 := complex_rotation_inverse _
  have hM : T * J * R = M := by
    simpa only [Matrix.map_mul] using
      congrArg (fun A : Matrix (Fin (2 * m) ⊕ Fin (2 * m))
        (Fin (2 * m) ⊕ Fin (2 * m)) ℝ => A.map Complex.ofRealHom)
        (rotated_jacobian_all m hm)
  have hcomm : T * J = M * T := by
    have h := congrArg (fun A => A * T) hM
    simpa only [Matrix.mul_assoc, hRT, Matrix.mul_one] using h
  change frequencyCoordinates m (T.mulVec (J.mulVec v)) =
    modeOperator m (frequencyCoordinates m (T.mulVec v))
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
  exact frequency_block m (T.mulVec v)

/-- Full generalized eigenspaces transport through the actual Fourier
similarity; the nonzero restriction argument applies to all complex μ. -/
theorem actual_nonzero_semisimple (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
    {μ : ℂ} (hμ : μ ≠ 0) :
    (actualOperator m).maxGenEigenspace μ = (actualOperator m).eigenspace μ := by
  apply le_antisymm
  · intro v hv
    have hφ : (modeOperator m).comp (cartesianCoordinates m).toLinearMap =
        (cartesianCoordinates m).toLinearMap.comp (actualOperator m) := by
      apply LinearMap.ext
      intro v
      exact (actual_normal_form m hm v).symm
    have hmap := Module.End.map_genEigenspace_le (cartesianCoordinates m).toLinearMap hφ μ ⊤
    have hv' : cartesianCoordinates m v ∈ (modeOperator m).maxGenEigenspace μ :=
      hmap (Submodule.mem_map_of_mem hv)
    rw [show (modeOperator m).maxGenEigenspace μ = (modeOperator m).eigenspace μ from
      paired_nonzero_semisimple _ _ hμ] at hv'
    rw [Module.End.mem_eigenspace_iff] at hv' ⊢
    apply (cartesianCoordinates m).injective
    rw [actual_normal_form m hm, map_smul]
    exact hv'
  · exact Module.End.eigenspace_le_maxGenEigenspace

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
