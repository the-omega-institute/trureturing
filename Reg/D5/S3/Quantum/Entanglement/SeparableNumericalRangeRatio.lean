import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.SeparableNumericalRangeRatio
import Reg.Support.DependentFamily

/-! Source-bound audit of zero-determinant product factorization. -/

namespace Reg.D5.S3.Quantum.Entanglement.SeparableNumericalRangeRatio

open _root_.D5.S3.Quantum.Entanglement.SeparableNumericalRangeRatio
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the diagonal product in the zero-determinant hypothesis. -/
abbrev signature : Signature where
  Params := Unit
  State _ := Fin 2 × Fin 2 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ u => u (0, 0) * u (1, 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ u : Fin 2 × Fin 2 → ℂ,
    R.readout () () u = u (0, 1) * u (1, 0) →
      ∃ a b : Fin 2 → ℂ, ∀ i j, u (i, j) = a i * b j

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let u : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then 1 else 0
  obtain ⟨a, b, hab⟩ := h u (by simp [rejected, realize, u])
  have heq : (a 0 * b 0) * (a 1 * b 1) = (a 0 * b 1) * (a 1 * b 0) := by ring
  rw [← hab 0 0, ← hab 1 1, ← hab 0 1, ← hab 1 0] at heq
  norm_num [u] at heq

def source_registration : Registration arena (type_of% @zero_determinant_factorization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨zero_determinant_factorization, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℂ) * 0 ≠ 1 * 1
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@zero_determinant_factorization) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SeparableNumericalRangeRatio.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.SeparableNumericalRangeRatio.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ u => u (0, 0) * u (1, 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SeparableNumericalRangeRatio
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.SeparableNumericalRangeRatio
