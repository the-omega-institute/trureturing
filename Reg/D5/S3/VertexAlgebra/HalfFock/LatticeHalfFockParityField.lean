import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCorrectedField LatticeHalfFockParityT LatticeInvolution
open _root_.D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField

noncomputable section

/-- The original source, signed coefficient and determinant witness stay in scope. -/
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  a : Carrier D
  e : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun p => ActualTensor p.D p.hu) (fun p => ActualTensor p.D p.hu)

def actual : Realization signature := realize signature
  (fun _ p x => actualParity p.D p.hu ((correctedField p.D p.hu p.a).coeff p.e x))
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Carrier D)
    (e : ℤ) (x : ActualTensor D hu),
    readout.readout () ⟨D, hu, a, e⟩ x =
      (correctedField D hu (theta D a)).coeff e (actualParity D hu x)

theorem source_bridge :
    (type_of% (@correctedField_target_parity)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := correctedField_target_parity

/- Partial source-bound audit evidence. Whole-family variation, sensitivity,
   actual observational dependence, the dependent-family Registration and the
   final enrolled-template readout/sourceSelection/escapeFrom binding remain
   unfinished. No Contract.Registration or declared_validated is asserted. -/

end
end Reg.D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField
