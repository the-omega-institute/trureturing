import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.SmallSelection
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.SmallSelection
open _root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH
open _root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, ℕ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → ℤ → Bool → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p v => rowBounds 4 p.1 ((2:ℤ)^p.2.1) ((2:ℤ)^p.2.2) v)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p Q H : ℕ) (_hp : p=4 ∨ p=8 ∨ p=16 ∨ p=32)
      (_hQ : 1≤Q) (_hH : 2≤H),
    ∃ v m M : ℕ, ∃ before : Bool,
      Submask m M ∧ m<M ∧ R.readout () ⟨p,Q,H⟩ v m M before

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  obtain ⟨v,m,M,before,_,_,hb⟩ := h 4 1 2 (by norm_num) (by norm_num) (by norm_num)
  exact hb

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  obtain ⟨v,m,M,before,_,_,hgood⟩ :=
    small_p_allh_selection 4 1 2 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨⟨4,1,2⟩,(v:ℤ),0,?_⟩
  intro he
  have he' := congrFun (congrFun (congrFun he (m:ℤ)) (M:ℤ)) before
  change rowBounds 4 4 ((2:ℤ)^1) ((2:ℤ)^2) v m M before =
    rowBounds 4 4 ((2:ℤ)^1) ((2:ℤ)^2) 0 m M before at he'
  have hbad := he'.mp hgood
  have := hbad.2.1
  norm_num at this

def source_registration : Registration arena (type_of% (@small_p_allh_selection)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨small_p_allh_selection,rejected,rejected_law⟩
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
    (@_root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.small_p_allh_selection)
    (Realization signature) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.small_p_allh_selection.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.SmallSelection.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.SmallSelection
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","arg","body","arg","body","arg","body","arg","body","arg","arg","fn","fn","fn"]
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
end Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.SmallSelection
