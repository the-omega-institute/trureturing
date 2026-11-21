import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.NumericalSemigroup.TwoWitnessResidues
import Reg.Support.DependentFamily

/-! Changing the first residue candidate changes the feasibility comparison. -/

namespace Reg.D5.S3.Combinatorics.NumericalSemigroup.TwoWitnessResidues

open _root_.D5.S3.Combinatorics.NumericalSemigroup.TwoWitnessResidues
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe v

noncomputable section

abbrev signature : Signature where
  Params := Type v
  State J := J → ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ J := J → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)

def constantNegative : Realization signature.{v} :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law R :=
    ∀ {J : Type v} (p u : J → ℤ), (∀ j, 0 ≤ p j) →
      ∀ {b t : ℤ}, 0 < b → 0 ≤ t →
        let q := t / b
        let r := t % b
        (∃ a c : ℤ, a * b + c = t ∧ ∀ j, 0 ≤ a * p j + c * u j) ↔
          (∀ j, 0 ≤ q * R.readout () J p j + r * u j) ∨
            (∀ j, 0 ≤ (q + 1) * p j + (r - b) * u j)

private theorem constant_negative_fails : ¬ arena.{v}.Law constantNegative := by
  intro law
  have result := (law (J := PUnit.{v+1}) (fun _ => 1) (fun _ => 4)
    (fun _ => by decide) (b := 2) (t := 2) (by decide) (by decide)).mp
    ⟨1, 0, by decide, fun _ => by decide⟩
  rcases result with first | second
  · have impossible : (0 : ℤ) ≤ -1 := first PUnit.unit
    exact (by decide : ¬ (0 : ℤ) ≤ -1) impossible
  · have impossible : (0 : ℤ) ≤ -6 := second PUnit.unit
    exact (by decide : ¬ (0 : ℤ) ≤ -6) impossible

def family : Registration arena.{v} (type_of% (@nonnegative_at_nearest_residue)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nonnegative_at_nearest_residue, constantNegative, constant_negative_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨constantNegative, ?_, rfl, constant_negative_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨PUnit.{v+1}, fun _ => 0, fun _ => 1, ?_⟩
    intro equal
    exact zero_ne_one (congrFun equal PUnit.unit)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nonnegative_at_nearest_residue) (Realization signature.{v}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.NumericalSemigroup.TwoWitnessResidues.nearestResidue
  realizationName := `Reg.D5.S3.Combinatorics.NumericalSemigroup.TwoWitnessResidues.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{v}⟩
  objectArena := .source ⟨arena.{v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.NumericalSemigroup.TwoWitnessResidues
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body",
          "body", "body", "arg", "fn", "arg", "body", "arg", "fn", "arg", "arg", "fn"]
        stateBinder := 1
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.NumericalSemigroup.TwoWitnessResidues
