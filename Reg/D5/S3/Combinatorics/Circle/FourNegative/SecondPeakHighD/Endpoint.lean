import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Endpoint
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Endpoint
open _root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
noncomputable section
abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ
  State p := List (Fin (p.1+p.2.1+p.2.2.1+p.2.2.2))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p sigma => JointLift p.1 p.2.1 p.2.2.1 p.2.2.2 sigma)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c d : ℕ) (_ha : 3≤a) (_hac : a<c) (_hcd : c+2≤d) (_hdb : d<b),
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, R.readout () ⟨a,b,c,d⟩ sigma j
private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  obtain ⟨sigma,j,hb⟩ := h 3 7 4 6 (by omega) (by omega) (by omega) (by omega)
  exact hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  obtain ⟨sigma,j,h⟩ := actualSource_second_peak_high_d_joint_lift 3 7 4 6
    (by omega) (by omega) (by omega) (by omega)
  refine ⟨⟨3,7,4,6⟩,sigma,[],?_⟩
  intro he
  have hh : JointLift 3 7 4 6 [] j := (congrFun he j).mp h
  have hl := hh.2.1.1.length_eq
  simp at hl

def source_registration : Registration arena (type_of% (@actualSource_second_peak_high_d_joint_lift)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actualSource_second_peak_high_d_joint_lift,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.actualSource_second_peak_high_d_joint_lift)
    (Realization signature) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.actualSource_second_peak_high_d_joint_lift.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Endpoint.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Endpoint
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg","body","arg","body","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms source_registration
#print axioms audit
end
end Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Endpoint
