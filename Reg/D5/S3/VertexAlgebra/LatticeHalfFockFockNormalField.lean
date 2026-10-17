import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped TensorProduct

noncomputable section

private abbrev hyperbolic : LatticeData where
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

private def ground : ActualGround hyperbolic hyperbolic_unit := fun _ => 1
private def vacuum : ActualTensor hyperbolic hyperbolic_unit :=
  (1 : Oscillator hyperbolic) ⊗ₜ[ℂ] ground

private theorem ground_nonzero : ground ≠ 0 := by
  intro equality
  have coordinate := congrFun equality
    (0 : _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.Half
      (groundRank
        hyperbolic hyperbolic_unit))
  exact one_ne_zero (show (1 : ℂ) = 0 from coordinate)

private def collapse : ActualTensor hyperbolic hyperbolic_unit →ₗ[ℂ]
    ActualGround hyperbolic hyperbolic_unit :=
  (TensorProduct.lid ℂ _).toLinearMap.comp
    (TensorProduct.map
      (MvPolynomial.eval₂AlgHom ℂ
        (fun _ : Index hyperbolic => (1 : ℂ))).toLinearMap LinearMap.id)

private theorem vacuum_nonzero : vacuum ≠ 0 := by
  intro equality
  apply ground_nonzero
  have observed := congrArg collapse equality
  simpa [collapse, vacuum] using observed

private def identityNative (D : LatticeData) (hu : IsUnit D.G.det) : NativeField D hu :=
  _root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField

namespace SameSign

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  first : Fin lattice.rank
  second : Fin lattice.rank
  left : ℤ
  right : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun p => ActualTensor p.lattice p.native) (fun p => ActualTensor p.lattice p.native)

def actual : Realization signature := realize signature (fun _ p vector =>
  _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent p.lattice (ActualGround p.lattice p.native)
    p.first p.left
    (_root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent p.lattice
      (ActualGround p.lattice p.native) p.second p.right vector))
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ vector => vector)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : Fin D.rank) (left right : ℤ),
    ((left < 0 ∧ right < 0) ∨ (0 ≤ left ∧ 0 ≤ right)) →
    ∀ vector : ActualTensor D hu,
    readout.readout () ⟨D, hu, first, second, left, right⟩ vector =
      _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent D (ActualGround D hu) second right
        (_root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent D (ActualGround D hu)
          first left vector)

theorem source_bridge : (type_of% (@tensor_current_same_sign)) ↔ arena.Law actual := Iff.rfl

private theorem vacuum_bound : ∀ colour mode, (0 : ℤ) ≤ mode →
    _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent hyperbolic
      (ActualGround hyperbolic hyperbolic_unit) colour mode vacuum = 0 := by
  intro colour mode positive
  have bound : (_root_.D5.S3.VertexAlgebra.LatticeHalfFock.bound hyperbolic 1 : ℤ) ≤ mode := by
    simpa [_root_.D5.S3.VertexAlgebra.LatticeHalfFock.bound] using positive
  simp [vacuum, _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent,
    _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorEnd,
    _root_.D5.S3.VertexAlgebra.LatticeHalfFock.current_vanish hyperbolic colour 1 mode bound]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic hyperbolic_unit 0 0 0 0 (Or.inr ⟨le_rfl, le_rfl⟩) vacuum
  apply vacuum_nonzero
  simpa [rejected, realize, vacuum_bound] using bad

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨hyperbolic, hyperbolic_unit, 0, 0, -1, -1⟩, 0, vacuum, ?_⟩
  intro equality
  have observed := congrArg collapse equality
  apply ground_nonzero
  simpa [actual, realize, collapse, vacuum,
    _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent,
    _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorEnd,
    _root_.D5.S3.VertexAlgebra.LatticeHalfFock.current, TensorProduct.map_tmul,
    LinearMap.mulLeft_apply] using observed.symm

def familyRegistration : Registration arena (type_of% (@tensor_current_same_sign)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp tensor_current_same_sign, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tensor_current_same_sign) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.tensor_current_same_sign "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.SameSign.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end SameSign

namespace Factorization

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  field : NativeField lattice native
  word : List (Index lattice)
  modes : ModeTuple lattice word

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun _ => ℤ) (fun p => Module.End ℂ (ActualTensor p.lattice p.native))

def actual : Realization signature := realize signature (fun _ p exponent =>
  flatCoefficient p.lattice p.native p.field p.word p.modes exponent)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (word : List (Index D)) (modes : ModeTuple D word) (exponent : ℤ),
    readout.readout () ⟨D, hu, field, word, modes⟩ exponent =
      leftAction D hu word modes * field.coeff
        (exponent + 2 * modeSum D word modes + jetShift D word) * rightAction D hu word modes

theorem source_bridge : (type_of% (@flatCoefficient_factorization)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic hyperbolic_unit (identityNative hyperbolic hyperbolic_unit) [] () 0
  have applied := congrArg (fun f : Module.End ℂ (ActualTensor hyperbolic hyperbolic_unit) =>
    f vacuum) bad
  apply vacuum_nonzero
  change (0 : ActualTensor hyperbolic hyperbolic_unit) = vacuum at applied
  exact applied.symm

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨hyperbolic, hyperbolic_unit, identityNative hyperbolic hyperbolic_unit, [], ()⟩,
    0, 1, ?_⟩
  intro equality
  have applied := congrArg (fun f : Module.End ℂ (ActualTensor hyperbolic hyperbolic_unit) =>
    f vacuum) equality
  apply vacuum_nonzero
  change vacuum = (0 : ActualTensor hyperbolic hyperbolic_unit) at applied
  exact applied

def familyRegistration : Registration arena (type_of% (@flatCoefficient_factorization)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp flatCoefficient_factorization, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@flatCoefficient_factorization) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.flatCoefficient_factorization "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.Factorization.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Factorization

namespace SupportBound

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  field : NativeField lattice native
  word : List (Index lattice)
  exponent : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun p => ActualTensor p.lattice p.native)
  (fun p => ModeTuple p.lattice p.word → ActualTensor p.lattice p.native)

def actual : Realization signature := realize signature (fun _ p vector =>
  flatTerm p.lattice p.native p.field p.word p.exponent vector)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ vector _ => vector)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (field : NativeField D hu)
    (word : List (Index D)) (exponent : ℤ) (vector : ActualTensor D hu) (cutoff : ℕ),
    (∀ colour mode, (cutoff : ℤ) ≤ mode →
      _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent D (ActualGround D hu)
        colour mode vector = 0) →
    Function.support (readout.readout () ⟨D, hu, field, word, exponent⟩ vector) ⊆
      modeBox D word
        (min (flatLower D hu field word vector cutoff - exponent - jetShift D word) 0 -
          (word.length : ℤ) * cutoff) cutoff

theorem source_bridge : (type_of% (@flatTerm_support_bound)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have included := law hyperbolic hyperbolic_unit 0 [(0, 0)] 0 vacuum 0 SameSign.vacuum_bound
  have member : ((1, ()) : ModeTuple hyperbolic [(0, 0)]) ∈
      Function.support (rejected.readout ()
        ⟨hyperbolic, hyperbolic_unit, 0, [(0, 0)], 0⟩ vacuum) := vacuum_nonzero
  have impossible := included member
  simp [modeBox, Finset.mem_product, Finset.mem_Icc] at impossible

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨hyperbolic, hyperbolic_unit, identityNative hyperbolic hyperbolic_unit, [], 0⟩,
    0, vacuum, ?_⟩
  intro equality
  have applied := congrFun equality ()
  apply vacuum_nonzero
  change (0 : ActualTensor hyperbolic hyperbolic_unit) = vacuum at applied
  exact applied.symm

def familyRegistration : Registration arena (type_of% (@flatTerm_support_bound)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp flatTerm_support_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@flatTerm_support_bound) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.flatTerm_support_bound "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.SupportBound.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end SupportBound

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
