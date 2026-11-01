import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.HalfFock.GroundCompression

/-! Exact source bridges for canonical augmentation; complete audits remain open. -/

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockGroundCompression
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockFiniteCorrection
open LatticeHalfFockCorrectedField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundCompression
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
noncomputable section

abbrev BoundData := {D : LatticeData // IsUnit D.G.det}

namespace Retraction
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  BoundData (fun _ => Unit) (fun p => Module.End ℂ (ActualGround p.val p.property))
def actual : Realization signature := realize signature
  (fun _ p _ => (pi p.val p.property).comp (iota p.val p.property))
  (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det),
    readout.readout () ⟨D, hu⟩ () = LinearMap.id
theorem source_bridge : (type_of% (@ground_retraction)) ↔ arena.Law actual := Iff.rfl
end Retraction

abbrev Parameter := Σ data : BoundData, ℤ
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun p => Oscillator p.1.val)
    (fun p => Module.End ℂ (ActualGround p.1.val p.1.property))

namespace Normal
def actual : Realization signature := realize signature
  (fun _ p r => (pi p.1.val p.1.property).comp
    (((polynomialField p.1.val p.1.property 0 r).coeff p.2).comp (iota p.1.val p.1.property)))
  (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (r : Oscillator D) (e : ℤ),
    readout.readout () ⟨⟨D, hu⟩, e⟩ r =
      (if e = 0 then epsilon D r else 0) • LinearMap.id
theorem source_bridge : (type_of% (@polynomialField_ground_compression)) ↔ arena.Law actual := Iff.rfl
end Normal

namespace Corrected
def actual : Realization signature := realize signature
  (fun _ p r => (pi p.1.val p.1.property).comp
    (((correctedField p.1.val p.1.property (Finsupp.single 0 r)).coeff p.2).comp
      (iota p.1.val p.1.property)))
  (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (p : Oscillator D) (e : ℤ),
    readout.readout () ⟨⟨D, hu⟩, e⟩ p =
      (∑ s ∈ (Corr D 0 p).support,
        if e = -2 * (s : ℤ) then epsilon D ((Corr D 0 p) s) else 0) • LinearMap.id
theorem source_bridge : (type_of% (@correctedField_ground_compression)) ↔ arena.Law actual := Iff.rfl
end Corrected

/- These are exact original-telescope source bridges through the existing
   dependent template, not complete Contract.Registration values.
   Whole-family variation, sensitivity, observational dependence and exact
   sourceSelection reconstruction for the source-dependent End-valued readout
   remain unresolved: https://github.com/the-omega-institute/trureturing/issues/24524
   and https://github.com/the-omega-institute/trureturing/issues/24498.
   No declared_validated registration is asserted for this owner, its consumed
   retraction helper, or the visibility-only neutral identity suppliers. -/

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockGroundCompression
