import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCount
import Reg.Support.DependentFamily

/-! Faithful two-readout audit for the all-r physical integer-zero count. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCount
open scoped BigOperators
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private def lhs (r : ℕ) : ℕ :=
  let d := 18*r+12
  76*(Finset.univ.filter (fun A : Finset (Fin (3*d)) =>
    (∑ i ∈ A, actualSource (3*d) ((2^d-1)*(2^(d+1)-3)) i)=0)).card
private def rhs (r : ℕ) : ℕ := 941*2^(18*r+12)+536

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role _ r => if role then lhs r else rhs r)
    (fun e => nomatch e)

def rejected (role : Bool) : Realization signature :=
  realize signature (fun j p r => if j=role then actual.readout j p r+1
    else actual.readout j p r) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : ℕ, R.readout true () r = R.readout false () r

private theorem actual_eq (r : ℕ) : lhs r=rhs r := actual_zero_subsets_card r

private theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  intro h
  have h0 := h 0
  have he := actual_eq 0
  cases role <;> simp [rejected,actual,realize] at h0 <;> omega

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  cases i
  · norm_num [actual,realize,rhs]
  · change lhs 0 ≠ lhs 1
    rw [actual_eq 0,actual_eq 1]
    norm_num [rhs]

def family : Registration arena (type_of% (@actual_zero_subsets_card)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_zero_subsets_card,rejected true,rejected_law true⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i,?_,rfl,rejected_law i⟩
      intro j hji
      simp only [rejected,realize,ite_eq_right hji]
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_zero_subsets_card) (Realization signature) Nat Bool where
  unitName := `D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCount.actual_zero_subsets_card.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCount.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun role _ r => if role then lhs r else rhs r)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCount
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCount
