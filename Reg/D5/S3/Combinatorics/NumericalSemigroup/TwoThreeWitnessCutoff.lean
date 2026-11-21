import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.NumericalSemigroup.TwoThreeWitnessCutoff
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.NumericalSemigroup.TwoThreeWitnessCutoff

open _root_.D5.S3.Combinatorics.NumericalSemigroup.TwoThreeWitnessCutoff
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℤ × ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ × ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)

def zeroWitness : Realization signature :=
  realize signature (fun _ _ _ => (0, 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := IsLeast {C : ℤ | ∃ p u : ℤ × ℤ, 0 < p.1 ∧ 0 < p.2 ∧ 2*u.1+3*u.2=1 ∧
      ∀ t : ℤ, C ≤ t → viable (R.readout () () p) u t} 8

private theorem zero_witness_fails : ¬ arena.Law zeroWitness := by
  intro law
  obtain ⟨p,u,_,_,degree,tail⟩ := law.1
  have atEight : viable (0,0) u 8 := tail 8 (by decide)
  obtain ⟨a,c,h⟩ := atEight
  change 0 ≤ a*0+c*u.1 ∧ 0 ≤ a*0+c*u.2 ∧ 2*(a*0+c*u.1)+3*(a*0+c*u.2)=8 at h
  simp only [mul_zero, zero_add] at h
  have cEight : c = 8 := by
    calc
      c = c * (2*u.1 + 3*u.2) := by rw [degree, mul_one]
      _ = _ := by nlinarith [h.2.2]
  rcases h with ⟨left,right,_⟩
  rw [cEight] at left right
  omega

def family : Registration arena (type_of% best_two_witness_cutoff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨best_two_witness_cutoff, zeroWitness, zero_witness_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨zeroWitness, ?_, rfl, zero_witness_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro role
    cases role
    exact ⟨(), (0,0), (1,1), by decide⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    best_two_witness_cutoff (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.NumericalSemigroup.TwoThreeWitnessCutoff.cutoff
  realizationName := `Reg.D5.S3.Combinatorics.NumericalSemigroup.TwoThreeWitnessCutoff.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.NumericalSemigroup.TwoThreeWitnessCutoff
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["fn", "arg", "arg", "body", "arg", "body", "arg", "body",
          "arg", "arg", "arg", "body", "body", "fn", "fn", "arg"]
        stateBinder := 1
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.NumericalSemigroup.TwoThreeWitnessCutoff
