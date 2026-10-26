import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
set_option autoImplicit false
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Finset
open scoped BigOperators ComplexOrder
namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates
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

namespace upper_certificate
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r H D a q s : ℝ} (h : Hyp r H D a q s) (hr : 1/5 ≤ r), R.readout () () (W r H D a q) (B r)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : Hyp (1/2) 0 0 0 0 0 := by constructor <;> norm_num
  exact h hz (by norm_num)
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates.upper_certificate)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates.upper_certificate,rejected,rejected_law⟩
  sensitivity := sensitivity arena.Law orderActual rejected_law
  dependence := order_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates.upper_certificate) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates.upper_certificate.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates.upper_certificate.family
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
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]
end upper_certificate

namespace smallq_certificate
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r H D a q s : ℝ} (h : Hyp r H D a q s) (hr : 1/12 ≤ r) (hr' : r ≤ 1/5) (hq : q ≤ 1), R.readout () () (W r H D a q) (B r)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : Hyp (1/5) 0 0 0 0 3 := by constructor <;> norm_num
  exact h hz (by norm_num) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates.smallq_certificate)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates.smallq_certificate,rejected,rejected_law⟩
  sensitivity := sensitivity arena.Law orderActual rejected_law
  dependence := order_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates.smallq_certificate) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates.smallq_certificate.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates.smallq_certificate.family
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
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates
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
end smallq_certificate

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates
