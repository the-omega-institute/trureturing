import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCount
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
private def rhs (r : ℕ) : ℕ :=
  let d := 18*r+12
  941*2^d+536

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
  realize signature (fun j _ r => rhs r + (if j=role then 1 else 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : ℕ,
    let d := 18*r+12
    R.readout true () r = R.readout false () r

private theorem actual_eq (r : ℕ) : lhs r=rhs r := actual_zero_subsets_card r

#check @actual_eq

private theorem actual_readout_rhs (j : Bool) (p : Unit) (r : ℕ) :
    actual.readout j p r = rhs r := by
  cases p
  cases j
  · rfl
  · exact actual_eq r

#check @actual_readout_rhs

private theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  intro h
  have h0 := h 0
  cases role <;> norm_num [rejected,realize,rhs] at h0

#check @rejected_law

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  rw [actual_readout_rhs,actual_readout_rhs]
  norm_num [rhs]

#check @actual_dependence

def family : Registration arena (type_of% (@actual_zero_subsets_card)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_zero_subsets_card,rejected true,rejected_law true⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i,?_,rfl,rejected_law i⟩
      intro j hji
      funext p r
      simp only [rejected,realize,if_neg hji,add_zero,actual_readout_rhs]
    · intro e
      exact nomatch e
  dependence := actual_dependence

#check @family

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
#print axioms family
#print axioms audit
end Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCount
