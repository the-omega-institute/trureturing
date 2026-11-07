import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural
open _root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
noncomputable section
abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℕ → Bool → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p v => Good (2^p.1) 2 (2^p.2) v)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P H : ℕ), 3 ≤ P → ∃ v m M : ℕ, R.readout () ⟨P,H⟩ v m M true
private theorem actual_law : arena.Law actual := q_two_dyadic_good
private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  obtain ⟨v,m,M,hg⟩ := h 3 0 (by decide)
  exact hg
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  obtain ⟨v,m,M,hg⟩ := q_two_dyadic_good 3 0 (by decide)
  refine ⟨⟨3,0⟩,v,0,?_⟩
  intro he
  have hz : Good (2^3) 2 (2^0) 0 m M true := (congrFun (congrFun (congrFun he m) M) true).mp hg
  have := hz.1
  omega

def source_registration : Registration arena (type_of% (@q_two_dyadic_good)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro side
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      have : j=side := Subsingleton.elim _ _
      exact False.elim (hj this)
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.q_two_dyadic_good)
    (Realization signature) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.q_two_dyadic_good.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","arg","body","arg","body","arg","body","fn","fn","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural
