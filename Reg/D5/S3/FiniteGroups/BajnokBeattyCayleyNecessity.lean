import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
import Reg.Support.DependentFamily

/-! The actual group-order parameter readout in the complete necessity theorem. -/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
open _root_.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _ : ℤ, ℤ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ k => (k : ℤ)) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ p _ => 2*p.1^2-p.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {t r : ℤ} {k : ℕ} (_ : 1 ≤ t) (_ : 0 ≤ r) (_ : r < t)
    (_ : R.readout () ⟨t,r⟩ k = 2*t^2-r) (a b : Target k)
    (_ : ∀ g : Target k, ∃ x y : ℤ, |x|+|y| ≤ 2*t ∧ x • a + y • b = g),
    2 ∣ r ∧ (Odd t → 4 ∣ r)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hcov : ∀ g : Target 1, ∃ x y : ℤ,
      |x|+|y| ≤ 2*(3 : ℤ) ∧ x • ((1,0) : Target 1) + y • ((0,1) : Target 1) = g := by
    rintro ⟨x,y⟩
    fin_cases x <;> fin_cases y
    · exact ⟨0,0,by norm_num,by norm_num <;> rfl⟩
    · exact ⟨0,1,by norm_num,by norm_num <;> rfl⟩
    · exact ⟨1,0,by norm_num,by norm_num <;> rfl⟩
    · exact ⟨1,1,by norm_num,by norm_num <;> rfl⟩
  have hh := h (k := 1) (t := 3) (r := 2)
    (by norm_num) (by norm_num) (by norm_num)
    (by rfl) (1,0) (0,1) hcov
  have hh4 := hh.2 (by decide : Odd (3 : ℤ))
  norm_num at hh4

def sourceRegistration : Registration arena (type_of% (@top_strip_necessity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨top_strip_necessity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨3,2⟩,1,2,?_⟩
    norm_num [actual, realize]

def topStripRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@top_strip_necessity) (Realization signature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity.top_strip_necessity.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ k => (k : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","domain","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
