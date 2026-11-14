import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Certificates.Algebra.BergmanQuestion23Refutation
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Certificates.Algebra.BergmanQuestion23Refutation

namespace Reg.D5.S0.Certificates.Algebra.BergmanQuestion23Refutation
universe u
noncomputable section

abbrev signature : Signature where
  Params := Σ F : Type u, Σ _ : Field F, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p m =>
    letI := p.2.1
    dimensionRatio p.1 m p.2.2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Both the full family and its unbounded-ratio conclusion remain in the source law. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ (F : Type u) [field : Field F] (n : ℕ) (_hn : 2 ≤ n),
    (∀ m : ℕ, 3 ≤ m → familyProperties F m n) ∧
    (∀ C : ℝ, ∃ m : ℕ, 3 ≤ m ∧ C < r.readout () ⟨F, field, n⟩ m)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨m, hm, hbad⟩ := (h (ULift.{u} ℚ) 2 (by decide)).2 0
  exact (lt_irrefl (0 : ℝ)) hbad

def familyAudit : Registration arena.{u}
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanQuestion23Refutation.family.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanQuestion23Refutation.family.{u},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let K := ULift.{u} ℚ
    obtain ⟨m, hm, hval⟩ :=
      (_root_.D5.S0.Certificates.Algebra.BergmanQuestion23Refutation.family
        K 2 (by decide)).2 (dimensionRatio K 3 2)
    refine ⟨⟨K, inferInstance, 2⟩, 3, m, ?_⟩
    change dimensionRatio K 3 2 ≠ dimensionRatio K m 2
    exact ne_of_lt hval

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanQuestion23Refutation.family.{u})
    (type_of% actual.{u}) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanQuestion23Refutation.family.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanQuestion23Refutation.familyAudit
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyAudit⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Algebra.BergmanQuestion23Refutation
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S0.Certificates.Algebra.BergmanQuestion23Refutation
