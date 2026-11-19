import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement
noncomputable section
open scoped BigOperators Topology ENNReal Matrix Matrix.Norms.L2Operator Kronecker
open Filter
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.TwistedGround
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianWeightedResolvent
open OriginalGaussianUniformCutoff
open OriginalGaussianDisplacement

open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod
open LatticeHalfFockFiniteCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement
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
private theorem eqDependence : ObservationalDependence eqSignature eqActual := by
  intro i
  refine ⟨ℂ, 0, 1, ?_⟩
  intro h
  have he : (1 : ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero he
abbrev leSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def leActual : Realization leSignature := realize _ (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def leRejected : Realization leSignature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem leDependence : ObservationalDependence leSignature leActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
  norm_num at he
abbrev limitSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℂ → ℂ)
    (fun _ => (ℂ → ℂ) → Set ℂ → Prop)
def limitActual : Realization limitSignature :=
  realize _ (fun _ _ F f s => TendstoUniformlyOn F f atTop s) (fun e => nomatch e)
def limitRejected : Realization limitSignature :=
  realize _ (fun _ _ _ _ _ => False) (fun e => nomatch e)
private theorem limitDependence : ObservationalDependence limitSignature limitActual := by
  intro i
  refine ⟨(), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro h
  have he := congrFun (congrFun h (fun _ => 0)) (Set.univ : Set ℂ)
  have hz : limitActual.readout () () (fun _ _ => 0) (fun _ => 0) Set.univ :=
    tendsto_const_nhds.tendstoUniformlyOn_const Set.univ
  have ho := Eq.mp he hz
  have hp := ho.tendsto_at (Set.mem_univ (0 : ℂ))
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hp)
private abbrev hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  even_diagonal := by intro i; fin_cases i <;> exact ⟨0, rfl⟩
private theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
  have h : hyperbolic.G.det = -1 := by
    change (Matrix.det (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ)) = -1
    norm_num [Matrix.det_fin_two]
  rw [h]
  exact isUnit_neg_one
private def labels : PUnit → Bool × Index hyperbolic := fun _ => (false, (0, 0))

namespace section_symm
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (N : ℕ) (z : ℂ),
    R.readout () _ ((finiteSection N z).transpose) (finiteSection N z) 
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h 0 0
def family : Registration arena (type_of% (@section_symm)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@section_symm, eqRejected, rejected_fails⟩
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
    (@section_symm) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement.section_symm.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement.section_symm.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement
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
end section_symm

namespace zeroExtend_signed
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (N : ℕ) {σ z : ℂ} (hσ : ‖σ‖ = 1)
    (hz : ‖z‖ < 1) (x : EuclideanSpace ℂ (Fin N)),
    R.readout () _ (sectionSignedResolvent N σ z (zeroExtend N x)) (zeroExtend N (WithLp.toLp 2 ((finiteSigned N σ z).mulVec x))) 
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h 0 (σ := 1) (z := 0) (by simp) (by simp) 0
def family : Registration arena (type_of% (@zeroExtend_signed)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@zeroExtend_signed, eqRejected, rejected_fails⟩
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
    (@zeroExtend_signed) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement.zeroExtend_signed.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement.zeroExtend_signed.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end zeroExtend_signed

namespace section_zeroExtend
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (N : ℕ) (z : ℂ) (x : EuclideanSpace ℂ (Fin N)),
    R.readout () _ (sectionOp N z (zeroExtend N x)) (zeroExtend N (WithLp.toLp 2 ((finiteSection N z).mulVec x))) 
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h 0 0 0
def family : Registration arena (type_of% (@section_zeroExtend)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@section_zeroExtend, eqRejected, rejected_fails⟩
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
    (@section_zeroExtend) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement.section_zeroExtend.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement.section_zeroExtend.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end section_zeroExtend

namespace zeroExtend_square_inverse
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (N : ℕ) {z : ℂ} (hz : ‖z‖ < 1)
    (x : EuclideanSpace ℂ (Fin N)),
    R.readout () _ ((∑' k : ℕ, (sectionOp N z ^ 2) ^ k) (zeroExtend N x)) (zeroExtend N (WithLp.toLp 2 ((Ring.inverse (1 - finiteSection N z ^ 2)).mulVec x))) 
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h 0 (z := 0) (by simp) 0
def family : Registration arena (type_of% (@zeroExtend_square_inverse)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@zeroExtend_square_inverse, eqRejected, rejected_fails⟩
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
    (@zeroExtend_square_inverse) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement.zeroExtend_square_inverse.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement.zeroExtend_square_inverse.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement
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
end zeroExtend_square_inverse

namespace signed_resolvent_displacement
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (n m : ℕ),
    (R.readout () _ ((n + 1 : ℂ) * OriginalGaussianResolvent.resolvent (Real.sqrt r : ℂ) (basis m) n -
      (m + 1 : ℂ) * oppositeResolvent (Real.sqrt r : ℂ) (basis m) n) (oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr hr1) n *
          OriginalGaussianResolvent.resolvent (Real.sqrt r : ℂ) (weightedSource r hr hr1) m) ) ∧
    ((n + 1 : ℂ) * oppositeResolvent (Real.sqrt r : ℂ) (basis m) n -
      (m + 1 : ℂ) * OriginalGaussianResolvent.resolvent (Real.sqrt r : ℂ) (basis m) n =
        -(OriginalGaussianResolvent.resolvent (Real.sqrt r : ℂ) (weightedSource r hr hr1) n *
          oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr hr1) m))
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact (h (r := 0) le_rfl (by norm_num) 0 0).1
def family : Registration arena (type_of% (@signed_resolvent_displacement)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@signed_resolvent_displacement, eqRejected, rejected_fails⟩
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
    (@signed_resolvent_displacement) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement.signed_resolvent_displacement.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement.signed_resolvent_displacement.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end signed_resolvent_displacement

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement
