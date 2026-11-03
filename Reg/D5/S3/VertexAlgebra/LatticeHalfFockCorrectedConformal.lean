import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal

/-! Exact source bridges for the consumed neutral identity suppliers. -/

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev BoundData := {D : LatticeData // IsUnit D.G.det}

namespace Neutral
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  BoundData (fun _ => Unit) (fun p => NativeField p.val p.property)
def actual : Realization signature := realize signature
  (fun _ p _ => chargedField p.val p.property 0) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det),
    readout.readout () ⟨D, hu⟩ () = FieldNormalProduct.identityField
theorem source_bridge : (type_of% (@current_charged_zero_identity)) ↔ arena.Law actual := Iff.rfl
end Neutral

namespace IdentityCoefficient
abbrev Parameter := Σ data : BoundData, ℤ
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun p => ActualTensor p.1.val p.1.property)
    (fun p => ActualTensor p.1.val p.1.property)
def actual : Realization signature := realize signature
  (fun _ p v => (FieldNormalProduct.identityField (V := ActualTensor p.1.val p.1.property)).coeff p.2 v)
  (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ) (v : ActualTensor D hu),
    readout.readout () ⟨⟨D, hu⟩, e⟩ v = if e = 0 then v else 0
theorem source_bridge : (type_of% (@current_identity_coefficient)) ↔ arena.Law actual := Iff.rfl
end IdentityCoefficient

/- Owner-specific partial evidence for the two visibility-only suppliers.
   No full Contract.Registration or declared_validated audit is asserted.
   Whole-family variation, sensitivity, observational dependence and exact
   sourceSelection reconstruction remain unresolved under
   https://github.com/the-omega-institute/trureturing/issues/24524 and
   https://github.com/the-omega-institute/trureturing/issues/24498. -/

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal
