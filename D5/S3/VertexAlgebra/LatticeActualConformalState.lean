/- GID: D5/S3/VertexAlgebra/LatticeActualConformalState
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeActualConformalState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An arbitrary matrix quadratic state has precisely the actual Sugawara field. -/

import D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus
import D5.S3.VertexAlgebra.LatticeSugawaraCurrents

/-
The genuine quadratic conformal state of the actual lattice state-field map.
No inverse-Gram or symmetry premise is used in this file, and rank zero is
included. The normal-product identity is derived from the saved actual
residue reconstruction; it respects the construction's canonical occurrence
lists without choosing or assuming an order for the two occurrences.

Classical source: Bakalov--Kac, math/0402315v1, section 4.1, equations
(4.12)--(4.16), DOI 10.1142/9789812702562_0001. The imported matrix Sugawara
architecture retains Kalle Kytölä's Apache 2.0 attribution and pinned
VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeActualConformalState
open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeFiniteNegativeGeneration
open LatticeAllStateReconstruction LatticeSugawaraConformal
open LatticeSugawaraCurrents
open LatticeActualStateFieldCalculus MvPolynomial
open scoped BigOperators VertexOperator
noncomputable section

def currentState (D : LatticeData) (i : Fin D.rank) : Carrier D :=
  Finsupp.single 0 (X (i, 0))

theorem current_state_creation (D : LatticeData) (i : Fin D.rank) :
    ((neutralField D i)[[-1]]) (vacuum D) = currentState D i := by
  rw [LatticeActualGeneratorLocality.neutral_modes]
  simp [neutralMode, neutralPolynomialMode, vacuum, currentState]

theorem current_state_field (D : LatticeData) (i : Fin D.rank) :
    Y D (currentState D i) = neutralField D i := by
  rw [← current_state_creation]
  exact stateField_current D i

theorem current_minus_one_current (D : LatticeData) (i j : Fin D.rank) :
    mu D (currentState D i) (-1) (currentState D j) =
      Finsupp.single 0 (X (i, 0) * X (j, 0)) := by
  rw [mu, current_state_field, LatticeActualGeneratorLocality.neutral_modes]
  simp [currentState, neutralMode, neutralPolynomialMode]

/-- Exact evaluation of the actual canonical quadratic state. -/
theorem quadratic_state_field (D : LatticeData) (i j : Fin D.rank) :
    Y D (Finsupp.single 0 (X (i, 0) * X (j, 0))) =
      quadraticSummand D i j := by
  rw [← current_minus_one_current, minus_one_product_field,
    current_state_field, current_state_field]
  rfl

/-- Neutral normal products are symmetric as a consequence of the actual
state-product theorem and the commutative oscillator polynomial. -/
theorem quadraticSummand_symmetric (D : LatticeData) (i j : Fin D.rank) :
    quadraticSummand D i j = quadraticSummand D j i := by
  rw [← quadratic_state_field, ← quadratic_state_field, mul_comm]

/-- The half-weighted arbitrary-matrix quadratic oscillator polynomial. -/
def conformalPolynomial (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Oscillator D :=
  (2 : ℂ)⁻¹ • ∑ i : Fin D.rank, ∑ j : Fin D.rank,
    H i j • (X (i, 0) * X (j, 0))

def omega (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Carrier D :=
  Finsupp.single 0 (conformalPolynomial D H)

/-- Actual Y identification for every matrix, every charge lattice and every
finite rank, without an inverse or symmetry restriction. -/
theorem Y_omega (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Y D (omega D H) = sugawaraField D H := by
  classical
  unfold omega conformalPolynomial sugawaraField
  rw [← Finsupp.smul_single, map_smul]
  simp_rw [Finsupp.single_finsetSum, map_sum, ← Finsupp.smul_single,
    map_smul, quadratic_state_field]

theorem omega_modes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) :
    ((Y D (omega D H))[[m + 1]]) = sugawaraMode D H m := by
  rw [Y_omega]
  rfl

/-- The -2 Sugawara mode creates precisely this actual conformal state. -/
theorem omega_eq_minus_two_vacuum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    omega D H = sugawaraMode D H (-2) (vacuum D) := by
  rw [← omega_modes]
  exact (stateField_creation D (omega D H)).symm

end
end D5.S3.VertexAlgebra.LatticeActualConformalState
