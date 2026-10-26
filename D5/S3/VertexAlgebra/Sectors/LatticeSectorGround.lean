/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorGround
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorGround
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual creation series and nonzero normalized ground intertwiner coefficient. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorOperatorSpace
import D5.S3.VertexAlgebra.Sectors.LatticeNeutralVertexAlgebra

/-!
The full ground coefficient series is the prescribed creation exponential,
including its cocycle sign and bilinear Laurent shift. This is the classical
Bakalov--Kac formula, math/0402315v1, section 4.1. It proves nonvacuity for
zero charges and rank zero as well as for every other ordinary lattice.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal
open scoped VertexOperator
noncomputable section

/-- The genuine creation series, not only its leading scalar. -/
theorem canonical_ground_series (D : LatticeData) (α β : Charge D) (n : ℤ) :
    canonical D α β 1 n 1 =
      epsilon D α β • creationCoeff D α (-n - 1 - bilinear D α β) := by
  change (((Y D (Finsupp.single α (1 : Oscillator D)))[[n]])
    (Finsupp.single β (1 : Oscillator D))) (α + β) = _
  rw [stateField_ground, actualField, VertexOperator.ncoeff_of_coeff,
    (actual_creation_coefficient_transport D α α).2.2.1]
  have hs : (1 : Polynomial (Oscillator D)).support = {0} := by
    simpa using Polynomial.support_C (show (1 : Oscillator D) ≠ 0 from one_ne_zero)
  simp [rawSingle, translatedPolynomial, hs]

/-- The exact normalized ground coefficient used for classification. -/
theorem canonical_ground_normalization (D : LatticeData) (α β : Charge D) :
    canonical D α β 1 (-bilinear D α β - 1) 1 = epsilon D α β • (1 : Oscillator D) := by
  rw [canonical_ground_series]
  have e : -(-bilinear D α β - 1) - 1 - bilinear D α β = 0 := by omega
  simp [e, creationCoeff, exponential_constant]

/-- The canonical mixed operator is nonzero for every pair of integral charges. -/
theorem canonicalIO_ne_zero (D : LatticeData) (α β : Charge D) :
    canonicalIO D α β ≠ 0 := by
  intro h
  have e := congrArg (fun I : IO D α β (α + β) =>
    I.val 1 (-bilinear D α β - 1) 1) h
  change canonical D α β 1 (-bilinear D α β - 1) 1 = 0 at e
  rw [canonical_ground_normalization] at e
  have sign : epsilon D α β ≠ 0 := by
    unfold epsilon paritySign
    split_ifs <;> norm_num
  exact (smul_eq_zero.mp e).elim sign one_ne_zero

end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
