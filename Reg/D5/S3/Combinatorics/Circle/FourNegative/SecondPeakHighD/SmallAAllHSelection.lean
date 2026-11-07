import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllHSelection
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllHSelection
open _root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllH
open _root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → ℤ → Bool → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p v => rowBounds ((2:ℤ)^p.1) ((2:ℤ)^p.2.1) ((2:ℤ)^p.2.2.1) ((2:ℤ)^p.2.2.2) v)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a P Q H : ℕ) (_ha : a=3 ∨ a=4)
      (_hP : 2≤P) (_hQ : 1≤Q) (_hH : 2≤H),
    ∃ v m M : ℕ, ∃ before : Bool,
      before=true ∧ Submask m M ∧ R.readout () ⟨a,P,Q,H⟩ v m M before

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  obtain ⟨v,m,M,before,_,_,hb⟩ := h 3 2 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hb

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  refine ⟨⟨3,2,1,2⟩,3,0,?_⟩
  intro he
  have hgood : rowBounds 8 4 2 4 3 36 37 true := by
    simpa [fixedFamilies] using (fixed_bounds 0 0 (by omega)).1
  have he' := congrFun (congrFun (congrFun he 36) 37) true
  change rowBounds ((2:ℤ)^3) ((2:ℤ)^2) ((2:ℤ)^1) ((2:ℤ)^2) 3 36 37 true =
    rowBounds ((2:ℤ)^3) ((2:ℤ)^2) ((2:ℤ)^1) ((2:ℤ)^2) 0 36 37 true at he'
  norm_num only [pow_one,show (2:ℤ)^2=4 by norm_num,show (2:ℤ)^3=8 by norm_num] at he'
  have hbad := he'.mp hgood
  have := hbad.2.1
  norm_num at this

def source_registration : Registration arena (type_of% (@small_a_selection)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨small_a_selection,rejected,rejected_law⟩
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
    (@_root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllH.small_a_selection)
    (Realization signature) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllH.small_a_selection.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllHSelection.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllHSelection
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg","body","arg","body","arg","body","arg","body","arg","arg","fn","fn","fn"]
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
end Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllHSelection
