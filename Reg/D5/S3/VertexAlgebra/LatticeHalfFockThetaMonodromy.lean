import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy
open _root_.D5.S3.VertexAlgebra.LatticeInvolution
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped TensorProduct

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters
    (fun parameter => Carrier parameter.lattice × ℤ)
    (fun parameter => Module.End ℂ (ActualTensor parameter.lattice parameter.native))

def coefficientReadout : Realization signature :=
  realize signature (fun _ parameter state =>
    (Ytw parameter.lattice parameter.native state.1).coeff state.2)
    (fun empty => nomatch empty)

def reflectedReadout : Realization signature :=
  realize signature (fun _ parameter state =>
    (Ytw parameter.lattice parameter.native (theta parameter.lattice state.1)).coeff state.2)
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun empty => nomatch empty)

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro axis; exact Fin.elim0 axis
  even_diagonal := by intro axis; exact Fin.elim0 axis

private theorem emptyNative : IsUnit emptyLattice.G.det := by
  simp [emptyLattice, Matrix.det_isEmpty]

private def emptyParameter : Parameters := ⟨emptyLattice, emptyNative⟩

private theorem identity_nonzero (parameter : Parameters) :
    (1 : Module.End ℂ (ActualTensor parameter.lattice parameter.native)) ≠ 0 := by
  let ground : ActualGround parameter.lattice parameter.native := fun _ => 1
  have groundNonzero : ground ≠ 0 := by
    intro equality
    have coordinate := congrFun equality 0
    change (1 : ℂ) = 0 at coordinate
    exact one_ne_zero coordinate
  have leading := charged_ground_leading parameter.lattice parameter.native 0 ground groundNonzero
  have normalized : chargedCoefficient parameter.lattice parameter.native 0 0 = 1 := by
    have field := charged_zero_identity parameter.lattice parameter.native
    have coefficient := congrArg
      (fun value : NativeField parameter.lattice parameter.native => value.coeff 0) field
    simpa only [_root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField,
      VertexOperator.of_coeff, chargedField, HVertexOperator.coeff_of_coeff,
      if_pos rfl, ite_true, Module.End.one_eq_id] using coefficient
  have leadingZero : chargedCoefficient parameter.lattice parameter.native 0 0
      ((1 : Oscillator parameter.lattice) ⊗ₜ[ℂ] ground) ≠ 0 := by
    simpa [chargeNorm, bilinear] using leading
  intro equality
  rw [normalized, equality] at leadingZero
  exact leadingZero (by simp)

private theorem coefficient_dependence : ObservationalDependence signature coefficientReadout := by
  intro role
  refine ⟨emptyParameter, ⟨Finsupp.single 0 1, 0⟩, ⟨0, 0⟩, ?_⟩
  change (Ytw emptyLattice emptyNative (Finsupp.single 0 1)).coeff 0 ≠ (Ytw _ _ 0).coeff 0
  rw [Ytw_vacuum]
  simpa only [_root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField,
    VertexOperator.of_coeff, HVertexOperator.coeff_of_coeff, if_pos rfl,
    ite_true, map_zero, Pi.zero_apply, Module.End.one_eq_id]
      using identity_nonzero emptyParameter

private theorem reflected_dependence : ObservationalDependence signature reflectedReadout := by
  intro role
  refine ⟨emptyParameter, ⟨Finsupp.single 0 1, 0⟩, ⟨0, 0⟩, ?_⟩
  change (Ytw emptyLattice emptyNative (theta emptyLattice (Finsupp.single 0 1))).coeff 0 ≠
    (Ytw emptyLattice emptyNative (theta emptyLattice 0)).coeff 0
  have vacuumFixed : theta emptyLattice (Finsupp.single 0 1) = Finsupp.single 0 1 := by
    exact theta_vacuum emptyLattice
  rw [vacuumFixed, Ytw_vacuum]
  simpa only [_root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField,
    VertexOperator.of_coeff, HVertexOperator.coeff_of_coeff, if_pos rfl,
    ite_true, map_zero, Pi.zero_apply, Module.End.one_eq_id]
      using identity_nonzero emptyParameter

namespace Monodromy

def arena : Arena where
  signature := signature
  Law observation := ∀ (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (source : Carrier lattice) (exponent : ℤ),
    observation.readout () ⟨lattice, native⟩ ⟨source, exponent⟩ =
      ((-1 : ℂ) ^ exponent) • (Ytw lattice native source).coeff exponent

theorem bridge : (type_of% (@Ytw_theta)) ↔ arena.Law reflectedReadout := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have equality := law emptyLattice emptyNative 0 0
  apply identity_nonzero emptyParameter
  simpa [rejected, realize] using equality

def familyRegistration : Registration arena (type_of% (@Ytw_theta)) where
  actual := reflectedReadout
  bridge := bridge
  variation := ⟨bridge.mp Ytw_theta, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := reflected_dependence

end Monodromy

namespace CoefficientSelection

def arena : Arena where
  signature := signature
  Law observation := ∀ (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (source : Carrier lattice) (eigenvalue : ℂ), theta lattice source = eigenvalue • source →
    ∀ exponent : ℤ, eigenvalue ≠ (-1 : ℂ) ^ exponent →
      observation.readout () ⟨lattice, native⟩ ⟨source, exponent⟩ = 0

theorem bridge : (type_of% (@Ytw_coefficient_selection)) ↔
    arena.Law coefficientReadout := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have equality := law emptyLattice emptyNative 0 0 (by simp) 0 (by norm_num)
  exact identity_nonzero emptyParameter equality

def familyRegistration : Registration arena (type_of% (@Ytw_coefficient_selection)) where
  actual := coefficientReadout
  bridge := bridge
  variation := ⟨bridge.mp Ytw_coefficient_selection, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := coefficient_dependence

end CoefficientSelection

namespace EvenOddSelection

def arena : Arena where
  signature := signature
  Law observation := ∀ (lattice : LatticeData) (native : IsUnit lattice.G.det),
    (∀ source : Carrier lattice, theta lattice source = source →
      ∀ exponent : ℤ, Odd exponent →
        observation.readout () ⟨lattice, native⟩ ⟨source, exponent⟩ = 0) ∧
    (∀ source : Carrier lattice, theta lattice source = -source →
      ∀ exponent : ℤ, Even exponent →
        observation.readout () ⟨lattice, native⟩ ⟨source, exponent⟩ = 0)

theorem bridge : (type_of% (@Ytw_even_odd_selection)) ↔ arena.Law coefficientReadout := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have equality := (law emptyLattice emptyNative).1 0 (by simp) 1 (by decide)
  exact identity_nonzero emptyParameter equality

def familyRegistration : Registration arena (type_of% (@Ytw_even_odd_selection)) where
  actual := coefficientReadout
  bridge := bridge
  variation := ⟨bridge.mp Ytw_even_odd_selection, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := coefficient_dependence

end EvenOddSelection

namespace PhysicalModeSelection

def arena : Arena where
  signature := signature
  Law observation := ∀ (lattice : LatticeData) (native : IsUnit lattice.G.det)
    (source : Carrier lattice) (alpha beta : ℤ), (alpha = 0 ∨ alpha = 1) →
    (beta = 0 ∨ beta = 1) → theta lattice source = ((-1 : ℂ) ^ alpha) • source →
    alpha ≠ beta → ∀ mode : ℤ,
      observation.readout () ⟨lattice, native⟩ ⟨source, -2 * mode - beta - 2⟩ = 0

theorem bridge : (type_of% (@Ytw_physical_mode_selection)) ↔
    arena.Law coefficientReadout := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have equality := law emptyLattice emptyNative 0 0 1 (Or.inl rfl) (Or.inr rfl)
    (by simp) (by norm_num) 0
  exact identity_nonzero emptyParameter equality

def familyRegistration : Registration arena (type_of% (@Ytw_physical_mode_selection)) where
  actual := coefficientReadout
  bridge := bridge
  variation := ⟨bridge.mp Ytw_physical_mode_selection, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := coefficient_dependence

end PhysicalModeSelection

namespace Monodromy

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy.Ytw_theta)
    (type_of% (realize signature reflectedReadout.readout reflectedReadout.anchor)) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy.Ytw_theta.__information_unit
  realizationName := ``familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature reflectedReadout.readout reflectedReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Monodromy

namespace CoefficientSelection

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy.Ytw_coefficient_selection)
    (type_of% (realize signature coefficientReadout.readout coefficientReadout.anchor)) Unit Unit where
  unitName := Lean.Name.str ``Ytw_coefficient_selection "__information_unit"
  realizationName := ``familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature coefficientReadout.readout coefficientReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end CoefficientSelection

namespace EvenOddSelection

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy.Ytw_even_odd_selection)
    (type_of% (realize signature coefficientReadout.readout coefficientReadout.anchor)) Unit Unit where
  unitName := Lean.Name.str ``Ytw_even_odd_selection "__information_unit"
  realizationName := ``familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature coefficientReadout.readout coefficientReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "arg", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end EvenOddSelection

namespace PhysicalModeSelection

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy.Ytw_physical_mode_selection)
    (type_of% (realize signature coefficientReadout.readout coefficientReadout.anchor)) Unit Unit where
  unitName := Lean.Name.str ``Ytw_physical_mode_selection "__information_unit"
  realizationName := ``familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature coefficientReadout.readout coefficientReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end PhysicalModeSelection

#print axioms Monodromy.registration
#print axioms CoefficientSelection.registration
#print axioms EvenOddSelection.registration
#print axioms PhysicalModeSelection.registration

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy
