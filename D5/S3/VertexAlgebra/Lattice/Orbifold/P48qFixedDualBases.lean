/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedDualBases
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transport the fixed basis and its Gram dual into the charged field. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMomentumEnergy
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge)
open P48qMomentumEnergy (fixedBasis fixedGram fixedGramDual fixedGram_pair_dual)
open P48qTwistedChargeAction (lattice g Momentum)

noncomputable section

/-- The momentum-energy basis and its Gram dual in the field's fixed eigenspace. -/
def fixedDualBases : FixedDualBases := by
  let transport := LinearEquiv.ofEq P48qMomentumEnergy.Fixed Fixed (by
    simp only [P48qMomentumEnergy.Fixed, Fixed, Module.End.eigenspace_def, one_smul])
  refine
    { creators := fixedBasis.map transport
      annihilators := (fixedGramDual fixedBasis).map transport
      pairing := ?_ }
  intro i j
  simp only [Module.Basis.map_apply, transport, LinearEquiv.coe_ofEq_apply]
  change fixedGram (fixedBasis i) (fixedGramDual fixedBasis j) = _
  exact fixedGram_pair_dual fixedBasis i j

/-- The P48q charged field with its fixed-mode bases supplied. -/
def concreteChargedField (a : Charge lattice) : VertexOperator ℂ State :=
  chargedField fixedDualBases a

theorem concreteChargedField_ground_leading (a : Charge lattice) (p : Momentum) :
    ((HahnModule.of ℂ).symm
      (concreteChargedField a (Finsupp.single p 1))).coeff (momentumExponent a p) =
      Finsupp.single (ThirdTwistedChargeAction.shift lattice g a p)
        (chargePhase a p • (1 : Fock)) :=
  chargedField_ground_leading fixedDualBases a p

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
