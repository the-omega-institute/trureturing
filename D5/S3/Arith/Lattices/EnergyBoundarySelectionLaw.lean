/- GID: D5/S3/Arith/Lattices/EnergyBoundarySelectionLaw
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/EnergyBoundarySelectionLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Five-adic boundary energy is twice the six-dimensional lattice energy modulo five. -/

import D5.S3.Arith.Lattices.ExactDualLatticeFormula

/- Library-search audit trail (2026-08-28):
   * Repository searches found the canonical `Lambda^2 A4` coordinate index and integral Gram
     matrix in `ExactDualLatticeFormula`; this module imports those declarations instead of
     restating the six-dimensional carrier.
   * Searches by the displayed rows of `R_5` and `H`, and by the boundary-map quadratic body,
     found no existing D5 declaration.
   * Pinned Mathlib provides the general `Matrix.mulVec` and `dotProduct` operations, but no
     theorem for these concrete matrices. The proof below checks the source matrix identity by
     exact normalization in `ZMod 5`. -/

namespace D5.S3.Arith.Lattices.EnergyBoundarySelectionLaw

open D5.S3.Arith.Lattices.ExactDualLatticeFormula

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Coordinate indices for the three-dimensional five-adic boundary space. -/
abbrev BoundaryIndex := Fin 3

/-- The three-dimensional boundary space over the residue field of order five. -/
abbrev BoundarySpace := BoundaryIndex -> ZMod 5

/-- The source matrix `R_5` reducing six lattice coordinates to three boundary coordinates. -/
def boundaryMatrix : Matrix BoundaryIndex LatticeIndex (ZMod 5) :=
  !![1, 0, 4, 0, 1, 0;
     0, 1, 4, 0, 0, 1;
     0, 0, 0, 1, 4, 1]

/-- The symmetric matrix defining the source quadratic form on the boundary. -/
def boundaryQuadraticMatrix : Matrix BoundaryIndex BoundaryIndex (ZMod 5) :=
  !![1, 2, 3;
     2, 1, 2;
     3, 2, 1]

/-- Reduction of an integral lattice coordinate vector through the displayed boundary matrix. -/
def boundaryMap (x : LatticeIndex -> Int) : BoundarySpace :=
  Matrix.mulVec boundaryMatrix (fun i => (x i : ZMod 5))

/-- The boundary quadratic form `q_R(v) = v^T H v`. -/
def boundaryQuadraticForm (v : BoundarySpace) : ZMod 5 :=
  dotProduct v (Matrix.mulVec boundaryQuadraticMatrix v)

/-- The Gram energy of an integral `Lambda^2 A4` coordinate vector, reduced modulo five. -/
def latticeEnergyModFive (x : LatticeIndex -> Int) : ZMod 5 :=
  let reduced : LatticeIndex -> ZMod 5 := fun i => (x i : ZMod 5)
  dotProduct reduced
    (Matrix.mulVec (integralGramMatrix.map (Int.castRingHom (ZMod 5))) reduced)

private theorem boundary_matrix_identity :
    boundaryMatrix.transpose * boundaryQuadraticMatrix * boundaryMatrix =
      (2 : ZMod 5) • integralGramMatrix.map (Int.castRingHom (ZMod 5)) := by
  decide

/-- **Energy-boundary selection law.** For every integral coordinate vector of
`Lambda^2 A4`, the quadratic value of its explicit three-dimensional boundary reduction is
twice its Gram energy modulo five. -/
theorem energy_boundary_selection_law (x : LatticeIndex -> Int) :
    boundaryQuadraticForm (boundaryMap x) = 2 * latticeEnergyModFive x := by
  let reduced : LatticeIndex -> ZMod 5 := fun i => (x i : ZMod 5)
  change dotProduct (Matrix.mulVec boundaryMatrix reduced)
      (Matrix.mulVec boundaryQuadraticMatrix (Matrix.mulVec boundaryMatrix reduced)) =
    2 * dotProduct reduced
      (Matrix.mulVec (integralGramMatrix.map (Int.castRingHom (ZMod 5))) reduced)
  rw [← Matrix.toBilin'_apply', ← Matrix.toBilin'_apply']
  rw [← Matrix.toLin'_apply]
  change ((Matrix.toBilin' boundaryQuadraticMatrix).comp
      (Matrix.toLin' boundaryMatrix) (Matrix.toLin' boundaryMatrix)) reduced reduced = _
  rw [Matrix.toBilin'_comp, boundary_matrix_identity]
  simp

-- Domain-inhabitance probe on the exact six-coordinate integral carrier.
example : LatticeIndex -> Int := fun _ => 0

-- Nontrivialization probe: the first basis coordinate has nonzero boundary energy.
example :
    boundaryQuadraticForm (boundaryMap (fun i => if i = 0 then 1 else 0)) = 1 := by
  norm_num [boundaryQuadraticForm, boundaryMap, boundaryQuadraticMatrix, boundaryMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

#print axioms energy_boundary_selection_law

end D5.S3.Arith.Lattices.EnergyBoundarySelectionLaw
