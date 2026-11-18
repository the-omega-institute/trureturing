import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
noncomputable section
open scoped BigOperators Topology ENNReal
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianResolvent OriginalGaussianDifferentiation OriginalGaussianBilinearTranspose
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
abbrev eqSignature : Signature where
  Params := Type
  State T := T
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ T := T → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def eqActual : Realization eqSignature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def eqRejected : Realization eqSignature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
theorem eqDependence : ObservationalDependence eqSignature eqActual := by
  intro i
  refine ⟨ℂ, 0, 1, ?_⟩
  intro h
  have he : (1 : ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero he

namespace sourceBilinearFunctional_comm
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (x y : H),
    R.readout () _ (sourceBilinearFunctional x y) (sourceBilinearFunctional y x)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (0 : H) (0 : H)
def family : Registration arena (type_of% (@sourceBilinearFunctional_comm)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@sourceBilinearFunctional_comm, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceBilinearFunctional_comm) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose.sourceBilinearFunctional_comm.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose.sourceBilinearFunctional_comm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sourceBilinearFunctional_comm

namespace operator_bilinear_transpose
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {z : ℂ} (hz : ‖z‖ < 1) (x y : H),
    R.readout () _ (sourceBilinearFunctional x (operator z y)) (sourceBilinearFunctional (operator z x) y)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (z := 0) (by simp) (0 : H) (0 : H)
def family : Registration arena (type_of% (@operator_bilinear_transpose)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@operator_bilinear_transpose, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@operator_bilinear_transpose) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose.operator_bilinear_transpose.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose.operator_bilinear_transpose.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end operator_bilinear_transpose

namespace resolvent_bilinear_transpose
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {z : ℂ} (hz : ‖z‖ < 1) (x y : H),
    R.readout () _ (sourceBilinearFunctional x (resolvent z y)) (sourceBilinearFunctional (resolvent z x) y)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (z := 0) (by simp) (0 : H) (0 : H)
def family : Registration arena (type_of% (@resolvent_bilinear_transpose)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@resolvent_bilinear_transpose, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@resolvent_bilinear_transpose) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose.resolvent_bilinear_transpose.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose.resolvent_bilinear_transpose.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end resolvent_bilinear_transpose

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
