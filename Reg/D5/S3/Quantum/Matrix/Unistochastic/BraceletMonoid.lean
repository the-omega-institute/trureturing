import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.Unistochastic.BraceletMonoid
import Reg.Support.DependentFamily

/-! Source-bound audit for the all-dimensional bracelet monoid theorem. -/

namespace Reg.D5.S3.Quantum.Matrix.Unistochastic.BraceletMonoid

open _root_.D5.S3.Quantum.Matrix.Unistochastic.BraceletMonoid
open _root_.D5.S3.Quantum.Matrix.CirculantBraceletNonUnistochastic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Σ d : ℕ, Matrix (Fin d) (Fin d) ℝ
  State p := Matrix (Fin p.1) (Fin p.1) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1) (Fin p.1) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p B => p.2 * B) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (d : ℕ),
    IsBracelet (1 : Matrix (Fin d) (Fin d) ℝ) ∧
      ∀ A B : Matrix (Fin d) (Fin d) ℝ,
        IsBracelet A → IsBracelet B → IsBracelet (r.readout () ⟨d, A⟩ B)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hone := (bracelet_monoid 1).1
  have hzero : IsBracelet (0 : Matrix (Fin 1) (Fin 1) ℝ) := (h 1).2 1 1 hone hone
  have hsum := sum_col_of_mem_doublyStochastic hzero.1 (0 : Fin 1)
  simp at hsum

def sourceRegistration : Registration arena (type_of% @bracelet_monoid) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bracelet_monoid, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
    change (1 : Matrix (Fin 1) (Fin 1) ℝ) * 0 ≠ 1 * 1
    simp

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Matrix.Unistochastic.BraceletMonoid.bracelet_monoid)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.Unistochastic.BraceletMonoid.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.Unistochastic.BraceletMonoid.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p B => p.2 * B) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.Unistochastic.BraceletMonoid
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms sourceRegistration
#print axioms registration

end
end Reg.D5.S3.Quantum.Matrix.Unistochastic.BraceletMonoid
