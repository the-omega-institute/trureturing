import D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev Parameters := Σ _data : LatticeData, ℕ

abbrev Representations (parameters : Parameters) :=
  Representation ℂ (Extension parameters.1 ⧸ K parameters.1) (Ground parameters.2)

abbrev signature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Parameters Representations Representations

def actual : Realization signature :=
  realize signature (fun _ _ rho => rho) (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ parameters _ =>
    Representation.trivial ℂ (Extension parameters.1 ⧸ K parameters.1) (Ground parameters.2))
    (fun empty => nomatch empty)

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := ∀ (data : LatticeData) (_unit : IsUnit data.G.det)
    (rank : ℕ) (_rank_eq : data.rank = rank + rank)
    (rho : Representation ℂ (Extension data ⧸ K data) (Ground rank))
    (_central : rho (QuotientGroup.mk (⟨1, 0⟩ : Extension data)) =
      -(1 : Module.End ℂ (Ground rank))),
    Nonempty (GroundAlgebra data rank (observation.readout () ⟨data, rank⟩ rho))

theorem exact_source_bridge :
    (type_of% (@actual_operator_algebra)) ↔
      arena.Law actual := Iff.rfl

private def hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro first second; fin_cases first <;> fin_cases second <;> rfl
  even_diagonal := by intro axis; fin_cases axis <;> exact ⟨0, rfl⟩

private theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
  have determinant : hyperbolic.G.det = -1 := by
    change (Matrix.det (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ)) = -1
    norm_num [Matrix.det_fin_two]
  rw [determinant]
  exact isUnit_neg_one

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨rank, rho, rank_eq, _, central, _⟩ :=
    actual_twisted_ground_representation hyperbolic hyperbolic_unit
  obtain ⟨algebra⟩ := law hyperbolic hyperbolic_unit rank rank_eq rho central
  have distinct : (0 : ModTwoCharge hyperbolic) ≠ 1 := by
    intro equality
    have coordinate := congrFun equality (0 : Fin 2)
    norm_num [F₂] at coordinate
  have pairing := algebra.trace_dual 0 1
  have positive : (Module.finrank ℂ (Ground rank) : ℂ) ≠ 0 := by
    simp [Ground, Half, Module.finrank_fintype_fun_eq_card, F₂]
  simp only [rejected, realize, dualOperator, chargeOperator, Representation.trivial,
    MonoidHom.one_apply, one_mul, LinearMap.trace_one, if_neg distinct] at pairing
  exact positive pairing

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  obtain ⟨rank, rho, _, _, central, _⟩ :=
    actual_twisted_ground_representation hyperbolic hyperbolic_unit
  refine ⟨⟨hyperbolic, rank⟩, rho,
    Representation.trivial ℂ (Extension hyperbolic ⧸ K hyperbolic) (Ground rank), ?_⟩
  change rho ≠ Representation.trivial ℂ (Extension hyperbolic ⧸ K hyperbolic) (Ground rank)
  intro equality
  rw [equality] at central
  have contradiction := congrArg (fun operator : Module.End ℂ (Ground rank) =>
    operator (fun _ => 1) (0 : Half rank)) central
  norm_num [Representation.trivial] at contradiction

def familyRegistration : Registration arena
    (type_of% (@actual_operator_algebra)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp actual_operator_algebra, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_operator_algebra)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra.actual_operator_algebra
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

def traceArena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := ∀ (data : LatticeData) (_unit : IsUnit data.G.det)
    {rank : ℕ} (rho : Representation ℂ (Extension data ⧸ K data) (Ground rank))
    (_central : rho (QuotientGroup.mk (⟨1, 0⟩ : Extension data)) =
      -(1 : Module.End ℂ (Ground rank)))
    (element : Extension data ⧸ K data) (_nonzero : quotientCharge data element ≠ 0),
    LinearMap.trace ℂ (Ground rank) (observation.readout () ⟨data, rank⟩ rho element) = 0

theorem trace_source_bridge :
    (type_of% (@nonzero_charge_trace)) ↔ traceArena.Law actual := Iff.rfl

private theorem rejected_trace_law : ¬ traceArena.Law rejected := by
  intro law
  obtain ⟨rank, rho, _, _, central, _⟩ :=
    actual_twisted_ground_representation hyperbolic hyperbolic_unit
  have nonzero : quotientCharge hyperbolic (chargeLift hyperbolic 1) ≠ 0 := by
    change (reduction hyperbolic (⟨0, integralLift hyperbolic 1⟩ : Extension hyperbolic)).charge ≠ 0
    intro equality
    have coordinate := congrFun equality (0 : Fin 2)
    norm_num [reduction, reduceCharge, integralLift, F₂] at coordinate
  have vanished := law hyperbolic hyperbolic_unit (rank := rank) rho central
    (chargeLift hyperbolic 1) nonzero
  have positive : (Module.finrank ℂ (Ground rank) : ℂ) ≠ 0 := by
    simp [Ground, Half, Module.finrank_fintype_fun_eq_card, F₂]
  apply positive
  simpa only [rejected, realize, Representation.trivial, MonoidHom.one_apply,
    LinearMap.trace_one] using vanished

def traceFamilyRegistration : Registration traceArena
    (type_of% (@nonzero_charge_trace)) where
  actual := actual
  bridge := trace_source_bridge
  variation := ⟨trace_source_bridge.mp nonzero_charge_trace, rejected, rejected_trace_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    traceArena.Law actual rejected rejected_trace_law
  dependence := dependence

def traceRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nonzero_charge_trace)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra.nonzero_charge_trace
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra.traceFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨traceArena⟩
  objectArena := .source ⟨traceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source traceArena ⟨traceFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms traceFamilyRegistration

#print axioms familyRegistration

end

end Reg.D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra
