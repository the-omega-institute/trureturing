/- GID: D5/S3/Arith/Lattices/EnergyBoundarySelectionLaw
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/EnergyBoundarySelectionLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The explicit five-adic boundary map carries lattice energy to twice its residue. -/

import D5.S3.Arith.Lattices.ExactDualLatticeFormula

namespace D5.S3.Arith.Lattices.EnergyBoundarySelectionLaw

open D5.S3.Arith.Lattices.ExactDualLatticeFormula

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Coordinate indices for the three-dimensional boundary space over `ZMod 5`. -/
abbrev BoundaryIndex := Fin 3

/-- The source's reduction map from the chosen basis of `Lambda^2 A4` to its
three-dimensional boundary space. -/
def boundaryProjectionMatrix : Matrix BoundaryIndex LatticeIndex (ZMod 5) :=
  !![1, 0, 4, 0, 1, 0;
     0, 1, 4, 0, 0, 1;
     0, 0, 0, 1, 4, 1]

/-- The nondegenerate symmetric form on the boundary space. -/
def boundaryFormMatrix : Matrix BoundaryIndex BoundaryIndex (ZMod 5) :=
  !![1, 2, 3;
     2, 1, 2;
     3, 2, 1]

/-- Coordinatewise reduction of an integral lattice vector modulo five. -/
def reduceModFive (x : LatticeIndex -> Int) : LatticeIndex -> ZMod 5 :=
  fun i => x i

/-- The boundary value `rho_5(x)` determined by the displayed reduction matrix. -/
def boundaryProjection (x : LatticeIndex -> Int) : BoundaryIndex -> ZMod 5 :=
  Matrix.mulVec boundaryProjectionMatrix (reduceModFive x)

/-- The boundary quadratic form `q_R(v) = v^T H v`. -/
def boundaryQuadratic (v : BoundaryIndex -> ZMod 5) : ZMod 5 :=
  dotProduct v (Matrix.mulVec boundaryFormMatrix v)

/-- The lattice Gram energy reduced modulo five. -/
def latticeEnergyModFive (x : LatticeIndex -> Int) : ZMod 5 :=
  let gramModFive := integralGramMatrix.map (Int.castRingHom (ZMod 5))
  dotProduct (reduceModFive x) (Matrix.mulVec gramModFive (reduceModFive x))

set_option maxRecDepth 10000 in
private lemma boundary_matrix_identity :
    boundaryProjectionMatrix.transpose * boundaryFormMatrix * boundaryProjectionMatrix =
      (2 : ZMod 5) • integralGramMatrix.map (Int.castRingHom (ZMod 5)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundaryProjectionMatrix, boundaryFormMatrix, integralGramMatrix,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] <;> decide

/-- **Energy-boundary selection law.** For every integral coordinate vector in
the chosen basis of `Lambda^2 A4`, its boundary quadratic value is twice its
lattice energy modulo five. -/
theorem energy_boundary_selection_law (x : LatticeIndex -> Int) :
    boundaryQuadratic (boundaryProjection x) =
      2 * latticeEnergyModFive x := by
  let y := reduceModFive x
  let gramModFive := integralGramMatrix.map (Int.castRingHom (ZMod 5))
  change dotProduct (Matrix.mulVec boundaryProjectionMatrix y)
      (Matrix.mulVec boundaryFormMatrix (Matrix.mulVec boundaryProjectionMatrix y)) =
    2 * dotProduct y (Matrix.mulVec gramModFive y)
  calc
    _ = dotProduct y (Matrix.mulVec boundaryProjectionMatrix.transpose
          (Matrix.mulVec boundaryFormMatrix (Matrix.mulVec boundaryProjectionMatrix y))) := by
      simpa [Matrix.vecMul_transpose] using
        (Matrix.dotProduct_mulVec y boundaryProjectionMatrix.transpose
          (Matrix.mulVec boundaryFormMatrix (Matrix.mulVec boundaryProjectionMatrix y))).symm
    _ = dotProduct y
          (Matrix.mulVec
            (boundaryProjectionMatrix.transpose * boundaryFormMatrix *
              boundaryProjectionMatrix) y) := by
      simp only [Matrix.mulVec_mulVec]
      rw [Matrix.mul_assoc]
    _ = dotProduct y
          (Matrix.mulVec ((2 : ZMod 5) • gramModFive) y) := by
      rw [boundary_matrix_identity]
    _ = 2 * dotProduct y (Matrix.mulVec gramModFive y) := by
      simp [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

#print axioms energy_boundary_selection_law

end D5.S3.Arith.Lattices.EnergyBoundarySelectionLaw
