import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality

/- Exact typed mirrors preserve source-type evidence only.
   They are not declared_validated four-slot registrations. -/
abbrev sourceScope_physicalCurrent_current_locality :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality.physicalCurrent_current_locality)
theorem source_actual_physicalCurrent_current_locality : sourceScope_physicalCurrent_current_locality :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality.physicalCurrent_current_locality

abbrev sourceScope_physicalCurrent_charge_locality :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality.physicalCurrent_charge_locality)
theorem source_actual_physicalCurrent_charge_locality : sourceScope_physicalCurrent_charge_locality :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality.physicalCurrent_charge_locality

abbrev sourceScope_physicalJet_charge_locality :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality.physicalJet_charge_locality)
theorem source_actual_physicalJet_charge_locality : sourceScope_physicalJet_charge_locality :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality.physicalJet_charge_locality

abbrev sourceScope_physicalJet_pair_locality :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality.physicalJet_pair_locality)
theorem source_actual_physicalJet_pair_locality : sourceScope_physicalJet_pair_locality :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality.physicalJet_pair_locality

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockPhysicalRescaling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open FieldNormalProductLocality
open scoped VertexOperator BigOperators
noncomputable section
abbrev AuditData := { D : LatticeData // IsUnit D.G.det }
/- The actual family and exact source bridge below are partial audit evidence.
   Whole-family variation, sensitivity, observational dependence and exact
   sourceSelection reconstruction remain unfinished at
   https://github.com/the-omega-institute/trureturing/issues/19578.
   No Contract.Registration is asserted without those proofs. -/
open LatticeHalfFockPhysicalGeneratorLocality

namespace CurrentCurrentAttempt
abbrev Parameter := Σ data : AuditData, Fin data.val.rank × Fin data.val.rank
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun _ => ℤ × ℤ) (fun p => Module.End ℂ (ActualTensor p.1.val p.1.property))
def actual : Realization signature := realize signature
  (fun _ p modes => commutator (physicalJet p.1.val p.1.property (p.2.1, 0)) (physicalJet p.1.val p.1.property (p.2.2, 0)) modes.1 modes.2) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (first : Fin D.rank) (second : Fin D.rank),
    delta^[2] (fun left right => readout.readout () ⟨⟨D, hu⟩, first, second⟩ (left, right)) = 0
theorem source_bridge : (type_of% (@physicalCurrent_current_locality)) ↔ arena.Law actual := Iff.rfl
end CurrentCurrentAttempt

namespace CurrentChargeAttempt
abbrev Parameter := Σ data : AuditData, Fin data.val.rank × Charge data.val × ℤ
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun _ => ℤ × ℤ) (fun p => Module.End ℂ (ActualTensor p.1.val p.1.property))
def actual : Realization signature := realize signature
  (fun _ p modes => commutator (physicalJet p.1.val p.1.property (p.2.1, 0)) (physicalSlice p.1.val p.1.property (chargedField p.1.val p.1.property p.2.2.1) p.2.2.2) modes.1 modes.2) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (first : Fin D.rank) (second : Charge D) (parity : ℤ),
    delta^[1] (fun left right => readout.readout () ⟨⟨D, hu⟩, first, second, parity⟩ (left, right)) = 0
theorem source_bridge : (type_of% (@physicalCurrent_charge_locality)) ↔ arena.Law actual := Iff.rfl
end CurrentChargeAttempt

namespace JetChargeAttempt
abbrev Parameter := Σ data : AuditData, Index data.val × Charge data.val × ℤ
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun _ => ℤ × ℤ) (fun p => Module.End ℂ (ActualTensor p.1.val p.1.property))
def actual : Realization signature := realize signature
  (fun _ p modes => commutator (physicalJet p.1.val p.1.property p.2.1) (physicalSlice p.1.val p.1.property (chargedField p.1.val p.1.property p.2.2.1) p.2.2.2) modes.1 modes.2) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (first : Index D) (second : Charge D) (parity : ℤ),
    delta^[first.2 + 1] (fun left right => readout.readout () ⟨⟨D, hu⟩, first, second, parity⟩ (left, right)) = 0
theorem source_bridge : (type_of% (@physicalJet_charge_locality)) ↔ arena.Law actual := Iff.rfl
end JetChargeAttempt

namespace JetPairAttempt
abbrev Parameter := Σ data : AuditData, Index data.val × Index data.val
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun _ => ℤ × ℤ) (fun p => Module.End ℂ (ActualTensor p.1.val p.1.property))
def actual : Realization signature := realize signature
  (fun _ p modes => commutator (physicalJet p.1.val p.1.property p.2.1) (physicalJet p.1.val p.1.property p.2.2) modes.1 modes.2) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (first : Index D) (second : Index D),
    delta^[first.2 + second.2 + 2] (fun left right => readout.readout () ⟨⟨D, hu⟩, first, second⟩ (left, right)) = 0
theorem source_bridge : (type_of% (@physicalJet_pair_locality)) ↔ arena.Law actual := Iff.rfl
end JetPairAttempt

end

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality
