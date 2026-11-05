import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.CorrectedInversion.Dual

/-!
Faithful source-law reconstruction for the original finite functional-dual law.
No Contract.Registration or declared_validated status is asserted. Whole-family
variation, sensitivity, observational dependence and current selector binding
remain obligations under https://github.com/the-omega-institute/trureturing/issues/21332.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.CorrectedInversion.Dual
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open TwistedGround.ActualChargedAdjoint
open _root_.D5.S3.VertexAlgebra.CorrectedInversion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric (complexSignature complexEqual)
open scoped BigOperators

def arena : Arena where
  signature := complexSignature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (v : Carrier D) (e : ℤ) (x y : ActualTensor D hu),
      readout.readout () () (K_L D hu e x y v)
        (∑ d ∈ (coordinateInversion D v).support,
          K_R D hu (d-e) x y (coordinateInversion D v d))
theorem source_bridge : (type_of% (@actual_dual_inversion)) ↔ arena.Law complexEqual := Iff.rfl
abbrev realizationObligation := Registration arena (type_of% (@actual_dual_inversion))

end Reg.D5.S3.VertexAlgebra.CorrectedInversion.Dual
