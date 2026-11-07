import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import Reg.D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality
import D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
/-! Full-telescope source realizations and single-readout sensitivity evidence. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology VertexOperator
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.Analysis.OriginalSmearing
open _root_.D5.S3.VertexAlgebra.Analysis.SmoothCircleFourier
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.LatticeAllStateField
open _root_.D5.S3.VertexAlgebra.FieldNormalProductLocality
namespace Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
open _root_.Reg.D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality
abbrev VecParams := Σ _M : Model, ℕ
abbrev VecParams.M (p : VecParams) : Model := p.1
abbrev VecParams.k (p : VecParams) : ℕ := p.2
abbrev vecSignature : Signature := _root_.Reg.Support.UniverseSingleReadout.signature
  VecParams (fun p => p.M.Sobolev p.k) (fun p => p.M.Sobolev p.k → Prop)
def vecActual : Realization vecSignature :=
  realize vecSignature (fun _ _ x y => x=y) (fun e => nomatch e)
def vecRejected : Realization vecSignature :=
  realize vecSignature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem vec_dependence : ObservationalDependence vecSignature vecActual := by
  intro i
  let v := testModel.embed 0 (vacuum testModel.D)
  refine ⟨⟨testModel,0⟩,v,0,?_⟩
  intro h
  have hh := congrFun h v
  have hz : (0 : testModel.Hilbert)=v := Eq.mp hh rfl
  exact vacuum_embed_ne hz.symm
abbrev deltaSignature : Signature := _root_.Reg.Support.UniverseSingleReadout.signature
  OpsParams (fun p => ℤ → ℤ → opsSignature.State p)
    (fun p => (ℤ → ℤ → opsSignature.State p) → Prop)
def deltaActual : Realization deltaSignature :=
  realize deltaSignature (fun _ _ x y => x=y) (fun e => nomatch e)
def deltaRejected : Realization deltaSignature :=
  realize deltaSignature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem delta_dependence : ObservationalDependence deltaSignature deltaActual := by
  intro i
  obtain ⟨p,x,y,h⟩ := ops_dependence ()
  have hxy : x ≠ y := by
    intro hxy
    apply h
    cases hxy
    rfl
  refine ⟨p,(fun _ _ => x),(fun _ _ => y),?_⟩
  intro hh
  have hyx : (fun _ _ : ℤ => y) = (fun _ _ : ℤ => x) :=
    Eq.mp (congrFun hh (fun _ _ => x)) rfl
  exact hxy (congrArg (fun T => T 0 0) hyx).symm
abbrev normSignature : Signature := _root_.Reg.Support.UniverseSingleReadout.signature
  Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def normActual : Realization normSignature :=
  realize normSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def normRejected : Realization normSignature :=
  realize normSignature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem norm_dependence : ObservationalDependence normSignature normActual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro h
  have hh := congrFun h (0 : ℝ)
  have hz : (1 : ℝ) ≤ 0 := Eq.mp hh le_rfl
  norm_num at hz
abbrev seriesSignature : Signature := _root_.Reg.Support.UniverseSingleReadout.signature
  Unit (fun _ => (ℤ × ℤ) → ℝ) (fun _ => Bool)
def seriesActual : Realization seriesSignature :=
  by
    classical
    exact realize seriesSignature (fun _ _ x => decide (Summable x)) (fun e => nomatch e)
def seriesRejected : Realization seriesSignature :=
  realize seriesSignature (fun _ _ _ => false) (fun e => nomatch e)
private theorem series_dependence : ObservationalDependence seriesSignature seriesActual := by
  classical
  intro i
  refine ⟨(),0,(fun _ => 1),?_⟩
  change decide (Summable (0 : (ℤ × ℤ) → ℝ)) ≠
    decide (Summable (fun _ : ℤ × ℤ => (1 : ℝ)))
  simpa [summable_const_iff] using (summable_zero : Summable (0 : (ℤ × ℤ) → ℝ))

namespace modeProduct_embed
def arena : Arena where
  signature := vecSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (k : ℕ) (m n : ℤ)
    (v : Carrier M.D) , R.readout () ⟨M,k⟩ (M.modeProduct a b k m n (M.embed (M.order a + M.order b + k) v)) (M.embed k (M.mode a m (M.mode b n v)))
private theorem rejected_bad : ¬ arena.Law vecRejected := by
  intro h
  exact h testModel 0 0 0 0 0 0
def evidence : Registration arena (type_of% (@modeProduct_embed)) where
  actual := vecActual
  bridge := Iff.rfl
  variation := ⟨@modeProduct_embed,vecRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    vecActual vecRejected rejected_bad
  dependence := vec_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@modeProduct_embed) (Realization vecSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeProduct_embed.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeProduct_embed.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize vecSignature vecActual.readout vecActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
    definition := none
    coordinates := #[0,3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end modeProduct_embed

namespace reverseModeProduct_embed
def arena : Arena where
  signature := vecSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (k : ℕ) (m n : ℤ)
    (v : Carrier M.D) , R.readout () ⟨M,k⟩ (M.reverseModeProduct a b k m n
        (M.embed (M.order a + M.order b + k) v)) (M.embed k (M.mode b n (M.mode a m v)))
private theorem rejected_bad : ¬ arena.Law vecRejected := by
  intro h
  exact h testModel 0 0 0 0 0 0
def evidence : Registration arena (type_of% (@reverseModeProduct_embed)) where
  actual := vecActual
  bridge := Iff.rfl
  variation := ⟨@reverseModeProduct_embed,vecRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    vecActual vecRejected rejected_bad
  dependence := vec_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reverseModeProduct_embed) (Realization vecSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.reverseModeProduct_embed.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.reverseModeProduct_embed.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize vecSignature vecActual.readout vecActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
    definition := none
    coordinates := #[0,3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end reverseModeProduct_embed

namespace modeCommutator_embed
def arena : Arena where
  signature := vecSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (k : ℕ) (m n : ℤ)
    (v : Carrier M.D) , R.readout () ⟨M,k⟩ (M.modeCommutator a b k m n (M.embed (M.order a + M.order b + k) v)) (M.embed k (M.mode a m (M.mode b n v) - M.mode b n (M.mode a m v)))
private theorem rejected_bad : ¬ arena.Law vecRejected := by
  intro h
  exact h testModel 0 0 0 0 0 0
def evidence : Registration arena (type_of% (@modeCommutator_embed)) where
  actual := vecActual
  bridge := Iff.rfl
  variation := ⟨@modeCommutator_embed,vecRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    vecActual vecRejected rejected_bad
  dependence := vec_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@modeCommutator_embed) (Realization vecSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeCommutator_embed.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeCommutator_embed.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize vecSignature vecActual.readout vecActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
    definition := none
    coordinates := #[0,3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end modeCommutator_embed

namespace modeCommutator_iterate_embed
def arena : Arena where
  signature := vecSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (k j : ℕ) (m n : ℤ)
    (v : Carrier M.D) , R.readout () ⟨M,k⟩ ((_root_.D5.S3.VertexAlgebra.FieldNormalProductLocality.delta^[j] (M.modeCommutator a b k)) m n
        (M.embed (M.order a + M.order b + k) v)) (M.embed k
        (((_root_.D5.S3.VertexAlgebra.FieldNormalProductLocality.delta^[j]
          (_root_.D5.S3.VertexAlgebra.FieldNormalProductLocality.commutator
            (_root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.actualField M.D a)
            (_root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality.actualField M.D b)))
          (m + chargeEnergy M.D a - 1) (n + chargeEnergy M.D b - 1)) v))
private theorem rejected_bad : ¬ arena.Law vecRejected := by
  intro h
  exact h testModel 0 0 0 0 0 0 0
def evidence : Registration arena (type_of% (@modeCommutator_iterate_embed)) where
  actual := vecActual
  bridge := Iff.rfl
  variation := ⟨@modeCommutator_iterate_embed,vecRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    vecActual vecRejected rejected_bad
  dependence := vec_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@modeCommutator_iterate_embed) (Realization vecSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeCommutator_iterate_embed.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeCommutator_iterate_embed.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize vecSignature vecActual.readout vecActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
    definition := none
    coordinates := #[0,3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end modeCommutator_iterate_embed

namespace modeCommutator_delta
def arena : Arena where
  signature := deltaSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (k : ℕ) , R.readout () ⟨M,a,b,k⟩ (_root_.D5.S3.VertexAlgebra.FieldNormalProductLocality.delta^[(-bilinear M.D a b).toNat]
      (M.modeCommutator a b k)) (0)
private theorem rejected_bad : ¬ arena.Law deltaRejected := by
  intro h
  exact h testModel 0 0 0
def evidence : Registration arena (type_of% (@modeCommutator_delta)) where
  actual := deltaActual
  bridge := Iff.rfl
  variation := ⟨@modeCommutator_delta,deltaRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    deltaActual deltaRejected rejected_bad
  dependence := delta_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@modeCommutator_delta) (Realization deltaSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeCommutator_delta.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeCommutator_delta.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize deltaSignature deltaActual.readout deltaActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end modeCommutator_delta

namespace modeProduct_norm
def arena : Arena where
  signature := normSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (k : ℕ) (m n : ℤ) , R.readout () () (‖M.modeProduct a b k m n‖) (M.modeConstant a * M.modeConstant b *
        (1 + |(m : ℝ)|)^(M.order a + k) *
        (1 + |(n : ℝ)|)^(M.order a + M.order b + k))
private theorem rejected_bad : ¬ arena.Law normRejected := by
  intro h
  exact h testModel 0 0 0 0 0
def evidence : Registration arena (type_of% (@modeProduct_norm)) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨@modeProduct_norm,normRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    normActual normRejected rejected_bad
  dependence := norm_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@modeProduct_norm) (Realization normSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeProduct_norm.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeProduct_norm.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize normSignature normActual.readout normActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end modeProduct_norm

namespace reverseModeProduct_norm
def arena : Arena where
  signature := normSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (k : ℕ) (m n : ℤ) , R.readout () () (‖M.reverseModeProduct a b k m n‖) (M.modeConstant a * M.modeConstant b *
        (1 + |(m : ℝ)|)^(M.order a + M.order b + k) *
        (1 + |(n : ℝ)|)^(M.order b + k))
private theorem rejected_bad : ¬ arena.Law normRejected := by
  intro h
  exact h testModel 0 0 0 0 0
def evidence : Registration arena (type_of% (@reverseModeProduct_norm)) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨@reverseModeProduct_norm,normRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    normActual normRejected rejected_bad
  dependence := norm_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reverseModeProduct_norm) (Realization normSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.reverseModeProduct_norm.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.reverseModeProduct_norm.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize normSignature normActual.readout normActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end reverseModeProduct_norm

namespace modeCommutator_norm
def arena : Arena where
  signature := normSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (k : ℕ) (m n : ℤ) , R.readout () () (‖M.modeCommutator a b k m n‖) (2 * M.modeConstant a * M.modeConstant b *
        (1 + |(m : ℝ)|)^(M.order a + M.order b + k) *
        (1 + |(n : ℝ)|)^(M.order a + M.order b + k))
private theorem rejected_bad : ¬ arena.Law normRejected := by
  intro h
  exact h testModel 0 0 0 0 0
def evidence : Registration arena (type_of% (@modeCommutator_norm)) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨@modeCommutator_norm,normRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    normActual normRejected rejected_bad
  dependence := norm_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@modeCommutator_norm) (Realization normSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeCommutator_norm.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeCommutator_norm.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize normSignature normActual.readout normActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end modeCommutator_norm

namespace modeProductTerm_le
def arena : Arena where
  signature := normSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (f g : Test) (k : ℕ) (p : ℤ × ℤ) , R.readout () () (‖M.modeProductTerm a b f g k p‖) (M.modeConstant a * M.modeConstant b *
        f.weight (M.order a + k) p.1 *
        g.weight (M.order a + M.order b + k) p.2)
private theorem rejected_bad : ¬ arena.Law normRejected := by
  intro h
  exact h testModel 0 0 zeroTest zeroTest 0 (0,0)
def evidence : Registration arena (type_of% (@modeProductTerm_le)) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨@modeProductTerm_le,normRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    normActual normRejected rejected_bad
  dependence := norm_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@modeProductTerm_le) (Realization normSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeProductTerm_le.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeProductTerm_le.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize normSignature normActual.readout normActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end modeProductTerm_le

namespace reverseModeProductTerm_le
def arena : Arena where
  signature := normSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (f g : Test)
    (k : ℕ) (p : ℤ × ℤ) , R.readout () () (‖M.reverseModeProductTerm a b f g k p‖) (M.modeConstant a * M.modeConstant b *
        f.weight (M.order a + M.order b + k) p.1 *
        g.weight (M.order b + k) p.2)
private theorem rejected_bad : ¬ arena.Law normRejected := by
  intro h
  exact h testModel 0 0 zeroTest zeroTest 0 (0,0)
def evidence : Registration arena (type_of% (@reverseModeProductTerm_le)) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨@reverseModeProductTerm_le,normRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    normActual normRejected rejected_bad
  dependence := norm_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reverseModeProductTerm_le) (Realization normSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.reverseModeProductTerm_le.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.reverseModeProductTerm_le.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize normSignature normActual.readout normActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end reverseModeProductTerm_le

namespace modeProduct_absolute
def arena : Arena where
  signature := seriesSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (f g : Test) (k : ℕ) , R.readout () () (fun p : ℤ × ℤ => ‖M.modeProductTerm a b f g k p‖) = true
private theorem rejected_bad : ¬ arena.Law seriesRejected := by
  intro h
  have hh := h testModel 0 0 zeroTest zeroTest 0
  change false = true at hh
  cases hh
def evidence : Registration arena (type_of% (@modeProduct_absolute)) where
  actual := seriesActual
  bridge := by simp only [arena, seriesActual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, seriesActual, realize, decide_eq_true_eq] using @modeProduct_absolute,seriesRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    seriesActual seriesRejected rejected_bad
  dependence := series_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@modeProduct_absolute) (Realization seriesSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeProduct_absolute.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeProduct_absolute.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize seriesSignature seriesActual.readout seriesActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end modeProduct_absolute

namespace reverseModeProduct_absolute
def arena : Arena where
  signature := seriesSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (f g : Test) (k : ℕ) , R.readout () () (fun p : ℤ × ℤ => ‖M.reverseModeProductTerm a b f g k p‖) = true
private theorem rejected_bad : ¬ arena.Law seriesRejected := by
  intro h
  have hh := h testModel 0 0 zeroTest zeroTest 0
  change false = true at hh
  cases hh
def evidence : Registration arena (type_of% (@reverseModeProduct_absolute)) where
  actual := seriesActual
  bridge := by simp only [arena, seriesActual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, seriesActual, realize, decide_eq_true_eq] using @reverseModeProduct_absolute,seriesRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    seriesActual seriesRejected rejected_bad
  dependence := series_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reverseModeProduct_absolute) (Realization seriesSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.reverseModeProduct_absolute.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.reverseModeProduct_absolute.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize seriesSignature seriesActual.readout seriesActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end reverseModeProduct_absolute

namespace modeCommutator_absolute
def arena : Arena where
  signature := seriesSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (f g : Test) (k : ℕ) , R.readout () () (fun p : ℤ × ℤ => ‖M.modeCommutatorTerm a b f g k p‖) = true
private theorem rejected_bad : ¬ arena.Law seriesRejected := by
  intro h
  have hh := h testModel 0 0 zeroTest zeroTest 0
  change false = true at hh
  cases hh
def evidence : Registration arena (type_of% (@modeCommutator_absolute)) where
  actual := seriesActual
  bridge := by simp only [arena, seriesActual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, seriesActual, realize, decide_eq_true_eq] using @modeCommutator_absolute,seriesRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    seriesActual seriesRejected rejected_bad
  dependence := series_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@modeCommutator_absolute) (Realization seriesSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeCommutator_absolute.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.modeCommutator_absolute.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize seriesSignature seriesActual.readout seriesActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end modeCommutator_absolute

namespace smearComposition_eq_tsum
def arena : Arena where
  signature := opsSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (f g : Test) (k : ℕ) , R.readout () ⟨M,a,b,k⟩ (M.smearComposition a b f g k) (∑' p : ℤ × ℤ, M.modeProductTerm a b f g k p)
private theorem rejected_bad : ¬ arena.Law opsRejected := by
  intro h
  exact h testModel 0 0 zeroTest zeroTest 0
def evidence : Registration arena (type_of% (@smearComposition_eq_tsum)) where
  actual := opsActual
  bridge := Iff.rfl
  variation := ⟨@smearComposition_eq_tsum,opsRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    opsActual opsRejected rejected_bad
  dependence := ops_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@smearComposition_eq_tsum) (Realization opsSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.smearComposition_eq_tsum.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.smearComposition_eq_tsum.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize opsSignature opsActual.readout opsActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
    definition := none
    coordinates := #[0,1,2,5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end smearComposition_eq_tsum

namespace reverseSmearComposition_eq_tsum
def arena : Arena where
  signature := opsSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (f g : Test) (k : ℕ) , R.readout () ⟨M,a,b,k⟩ (M.reverseSmearComposition a b f g k) (∑' p : ℤ × ℤ, M.reverseModeProductTerm a b f g k p)
private theorem rejected_bad : ¬ arena.Law opsRejected := by
  intro h
  exact h testModel 0 0 zeroTest zeroTest 0
def evidence : Registration arena (type_of% (@reverseSmearComposition_eq_tsum)) where
  actual := opsActual
  bridge := Iff.rfl
  variation := ⟨@reverseSmearComposition_eq_tsum,opsRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    opsActual opsRejected rejected_bad
  dependence := ops_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reverseSmearComposition_eq_tsum) (Realization opsSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.reverseSmearComposition_eq_tsum.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.reverseSmearComposition_eq_tsum.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize opsSignature opsActual.readout opsActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
    definition := none
    coordinates := #[0,1,2,5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end reverseSmearComposition_eq_tsum

namespace smear_comp_eq_double_tsum
def arena : Arena where
  signature := opsSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (f g : Test) (k : ℕ) , R.readout () ⟨M,a,b,k⟩ (M.castSource (by omega : M.order b + (M.order a + k) =
        M.order a + M.order b + k)
        ((M.smear a f k).comp (M.smear b g (M.order a + k))) -
      M.castSource (by omega : M.order a + (M.order b + k) =
        M.order a + M.order b + k)
        ((M.smear b g k).comp (M.smear a f (M.order b + k)))) (∑' p : ℤ × ℤ, (f.coefficient p.1 * g.coefficient p.2) •
        M.modeCommutator a b k p.1 p.2)
private theorem rejected_bad : ¬ arena.Law opsRejected := by
  intro h
  exact h testModel 0 0 zeroTest zeroTest 0
def evidence : Registration arena (type_of% (@smear_comp_eq_double_tsum)) where
  actual := opsActual
  bridge := Iff.rfl
  variation := ⟨@smear_comp_eq_double_tsum,opsRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    opsActual opsRejected rejected_bad
  dependence := ops_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@smear_comp_eq_double_tsum) (Realization opsSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.smear_comp_eq_double_tsum.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator.smear_comp_eq_double_tsum.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize opsSignature opsActual.readout opsActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
    definition := none
    coordinates := #[0,1,2,5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end smear_comp_eq_double_tsum
end Reg.D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
