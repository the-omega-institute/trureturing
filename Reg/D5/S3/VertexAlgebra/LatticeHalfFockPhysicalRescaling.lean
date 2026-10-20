import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling

/- Exact typed mirrors preserve source-type evidence only.
   They are not declared_validated four-slot registrations. -/
abbrev sourceScope_physicalSlice_mode :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling.physicalSlice_mode)
theorem source_actual_physicalSlice_mode : sourceScope_physicalSlice_mode :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling.physicalSlice_mode

abbrev sourceScope_physicalJet_mode :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling.physicalJet_mode)
theorem source_actual_physicalJet_mode : sourceScope_physicalJet_mode :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling.physicalJet_mode

abbrev sourceScope_physicalSlice_singletonLinear :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling.physicalSlice_singletonLinear)
theorem source_actual_physicalSlice_singletonLinear : sourceScope_physicalSlice_singletonLinear :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling.physicalSlice_singletonLinear

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockPhysicalRescaling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped VertexOperator
noncomputable section
namespace SliceMode
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  ℤ (fun _ => ℤ) (fun _ => ℤ)
def actual : Realization signature := realize signature
  (fun _ shift mode => -2 * mode - shift - 2) (fun empty => nomatch empty)
def rejected : Realization signature := realize signature
  (fun _ _ _ => -1) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (shift mode : ℤ),
    (physicalSlice D hu field shift)[[mode]] = field.coeff (readout.readout () shift mode)
theorem source_bridge : (type_of% (@physicalSlice_mode)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let D := Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.hyperbolic
  let hu := Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.hyperbolic_unit
  let v := Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.probeState
  have bad := law D hu (chargedField D hu 0) 0 (-1)
  rw [physicalSlice_mode] at bad
  have value := LinearMap.congr_fun bad v
  have zero : chargedCoefficient D hu 0 (-1) v = 0 := by
    apply charged_polynomial_lower_bound
    norm_num [D, hu, v,
      Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.probeState,
      chargeNorm, bilinear, nativeOddWeightedDegree, MvPolynomial.weightedTotalDegree]
  apply Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.probe_leading
  have reduced : chargedCoefficient D hu 0 0 v = chargedCoefficient D hu 0 (-1) v := by
    simpa only [rejected, realize, chargedField, HVertexOperator.coeff_of_coeff,
      mul_neg, mul_one, neg_neg, sub_zero, sub_self] using value
  exact reduced.trans zero
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨0, 0, 1, by norm_num [actual, realize]⟩
def familyRegistration : Registration arena (type_of% (@physicalSlice_mode)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp physicalSlice_mode, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling.physicalSlice_mode) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling.physicalSlice_mode "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling.SliceMode.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end SliceMode
/- The actual family and exact source bridge below are partial audit evidence.
   Whole-family variation, sensitivity, observational dependence and exact
   sourceSelection reconstruction remain unfinished at
   https://github.com/the-omega-institute/trureturing/issues/19578.
   No Contract.Registration is asserted without those proofs. -/

namespace JetModeAttempt
abbrev Parameter := Σ data : {D : LatticeData // IsUnit D.G.det}, Index data.val
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun _ => ℤ) (fun p => Module.End ℂ (ActualTensor p.1.val p.1.property))
def actual : Realization signature := realize signature
  (fun _ p mode => jetCurrent p.1.val p.1.property p.2 mode) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D) (mode : ℤ),
    (physicalJet D hu index)[[mode]] = readout.readout () ⟨⟨D, hu⟩, index⟩ mode
theorem source_bridge : (type_of% (@physicalJet_mode)) ↔ arena.Law actual := Iff.rfl
end JetModeAttempt

namespace SingletonSliceAttempt
abbrev Parameter := Σ data : {D : LatticeData // IsUnit D.G.det},
  Index data.val × NativeField data.val data.property
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun _ => ℤ) (fun p => VertexOperator ℂ (ActualTensor p.1.val p.1.property))
def actual : Realization signature := realize signature
  (fun _ p shift => (FieldNormalProduct.normalMinusOne (physicalJet p.1.val p.1.property p.2.1)
    (physicalSlice p.1.val p.1.property p.2.2 shift)).val) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (field : NativeField D hu) (shift : ℤ),
    physicalSlice D hu (singletonLinear D hu index field) (shift + 2 * index.2 + 1) =
      readout.readout () ⟨⟨D, hu⟩, index, field⟩ shift
theorem source_bridge : (type_of% (@physicalSlice_singletonLinear)) ↔ arena.Law actual := Iff.rfl
end SingletonSliceAttempt

end

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling
