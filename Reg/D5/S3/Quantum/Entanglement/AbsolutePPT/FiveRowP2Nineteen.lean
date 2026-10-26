import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Nineteen
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
set_option autoImplicit false
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Nineteen
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Finset
open scoped BigOperators ComplexOrder
namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Nineteen
noncomputable section
/- SOURCE ATTEMPT ONLY. No current binding evidence or declared_validated
claim. Original telescopes and comparisons below are retained exactly.
Raw sourceSelection paths are manual candidate paths, pending authoritative
source reconstruction and template-binding validation. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def orderActual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def equalityActual : Realization signature :=
  realize signature (fun _ _ x y => x=y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem order_dependence : ObservationalDependence signature orderActual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro he
  have hz : (0:ℝ) ≤ 0 := le_rfl
  have hf : (1:ℝ) ≤ 0 := Eq.mp (congrFun he 0) hz
  norm_num at hf
private theorem equality_dependence : ObservationalDependence signature equalityActual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro he
  have hf : (1:ℝ)=0 := Eq.mp (congrFun he 0) rfl
  norm_num at hf
private theorem sensitivity (law : Realization signature → Prop)
    (actual : Realization signature) (hbad : ¬ law rejected) :
    Sensitivity ⟨signature,law⟩ actual := by
  constructor
  · intro i
    refine ⟨rejected,?_,?_,hbad⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

namespace concentrated_nineteen
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r H D a q s j : ℝ) (h : Hyp r H D a q s) (hj : 10 ≤ j) (hj' : j ≤ 80), R.readout () () (energy 95 j r H D a q) ((5/456)*(mass 95 j r H D)^2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : Hyp 0 0 0 0 0 5 := by constructor <;> norm_num
  exact h 0 0 0 0 0 5 10 hz (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Nineteen.concentrated_nineteen)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Nineteen.concentrated_nineteen,rejected,rejected_law⟩
  sensitivity := sensitivity arena.Law orderActual rejected_law
  dependence := order_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Nineteen.concentrated_nineteen) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Nineteen.concentrated_nineteen.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Nineteen.concentrated_nineteen.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Nineteen
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]
end concentrated_nineteen

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Nineteen
