import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyAllRegimes
import Reg.Support.DependentFamily

/-! The exact generating-pair predicate in the complete four-regime iff. -/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyAllRegimes

open _root_.D5.S3.FiniteGroups.BajnokBeattyAllRegimes
open _root_.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ k : ℕ, Σ _ : ℕ, Target k
  State p := Target p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (b : signature.State p) : Prop :=
  p.2.2 ≠ b ∧ ∀ g, ∃ x y : ℤ,
    g = x • p.2.2 + y • b ∧ |x| + |y| ≤ (p.2.1 : ℤ)

def actual : Realization signature := realize signature
  (fun _ p b => observed p b) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k s : ℕ) (_ : 0 < k) (_ : 0 < s),
    (∃ a b : Target k, R.readout () ⟨k, s, a⟩ b) ↔
    (Odd s ∧ 2 * k ≤ s ^ 2 - 1) ∨
    (Even s ∧ 2 * k ≤ s ^ 2 - s) ∨
    (s % 4 = 0 ∧ Even k ∧ s ^ 2 - s < 2 * k ∧ 2 * k ≤ s ^ 2) ∨
    (s % 4 = 2 ∧ k % 4 = 2 ∧ s ^ 2 - s < 2 * k ∧ 2 * k ≤ s ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hgood : (Even (2 : ℕ) ∧ 2 * 1 ≤ 2 ^ 2 - 2) := by decide
  obtain ⟨a, b, hab⟩ := (h 1 2 (by decide) (by decide)).mpr (Or.inr (Or.inl hgood))
  exact hab

def sourceRegistration : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
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
    obtain ⟨a, b, hab⟩ := (result 1 2 (by decide) (by decide)).mpr
      (Or.inr (Or.inl (by decide)))
    refine ⟨⟨1, 2, a⟩, b, a, ?_⟩
    intro he
    have hbad : observed ⟨1, 2, a⟩ a := Eq.mp he hab
    exact hbad.1 rfl

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyAllRegimes.result.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyAllRegimes.sourceRegistration
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
    (fun _ p b => observed p b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyAllRegimes
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","arg","body","arg","body"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyAllRegimes
