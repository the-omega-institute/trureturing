/- GID: D5/S3/VertexAlgebra/LatticeHalfFockOriginalMixedIterate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockOriginalMixedIterate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original ordinary current and native half-current interfaces. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockOriginalMixedIterate

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeHalfFockFirstDescendant
open scoped BigOperators VertexOperator

noncomputable section

def sourceCurrent (D : LatticeData) (h : Fin D.rank → ℂ) : VertexOperator ℂ (Carrier D) :=
  LatticeAllStateField.Y D (originalFirstDescendant D h 0)

theorem sourceCurrent_field (D : LatticeData) (h : Fin D.rank → ℂ) :
    sourceCurrent D h = ∑ colour, h colour • neutralField D colour := by
  simp only [sourceCurrent, originalFirstDescendant, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro colour member
  have current : ((neutralField D colour)[[-1]]) (LatticeAllStateField.vacuum D) =
      Finsupp.single (0 : Charge D) (MvPolynomial.X (colour, 0) : Oscillator D) := by
    rw [LatticeSugawaraCurrents.neutralField_ncoeff]
    simp [neutralMode, neutralPolynomialMode, LatticeAllStateField.vacuum]
  rw [← current, LatticeAllStateField.stateField_current]

theorem sourceCurrent_mode (D : LatticeData) (h : Fin D.rank → ℂ) (mode : ℤ) :
    (sourceCurrent D h)[[mode]] = ∑ colour, h colour • neutralMode D colour mode := by
  rw [sourceCurrent_field]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    LatticeSugawaraCurrents.neutralField_ncoeff]

end
end D5.S3.VertexAlgebra.LatticeHalfFockOriginalMixedIterate
