import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity
import Reg.Support.DependentFamily

/-! Source-bound audit of negative-line parity over all linear doilies. -/

namespace Reg.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity

open _root_.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Count negative lines while retaining the ambient number of qubits. -/
abbrev signature : Signature where
  Params := ℕ
  State N := Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ U => (negativeLines U).card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The original dimension, nondegeneracy, and odd-cardinality assertion. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ), 2 ≤ N →
    ∀ U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2),
      IsLinearDoily U → Odd (R.readout () N U)

private theorem two_qubit_doily :
    IsLinearDoily (⊤ : Submodule (ZMod 2) (Fin 2 → ZMod 2 × ZMod 2)) := by
  constructor
  · simp [Module.finrank_pi_fintype]
  · intro u _ hu
    funext j
    apply Prod.ext
    · have h := hu (Pi.single j (0, 1)) (Submodule.mem_top)
      fin_cases j <;> simpa [B, Pi.single_apply] using h
    · have h := hu (Pi.single j (1, 0)) (Submodule.mem_top)
      fin_cases j <;> simpa [B, Pi.single_apply] using h

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 2 (by decide) ⊤ two_qubit_doily
  change Odd (0 : ℕ) at hbad
  simp at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, ⊥, ⊤, ?_⟩
  change (negativeLines (⊥ : Submodule (ZMod 2) (Fin 2 → ZMod 2 × ZMod 2))).card ≠
    (negativeLines (⊤ : Submodule (ZMod 2) (Fin 2 → ZMod 2 × ZMod 2))).card
  have hz : (negativeLines (⊥ : Submodule (ZMod 2) (Fin 2 → ZMod 2 × ZMod 2))).card = 0 := by
    simp [negativeLines, lines, points]
  rw [hz]
  intro h
  have hodd := result 2 (by decide) ⊤ two_qubit_doily
  rw [← h] at hodd
  simp at hodd

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.source_registration
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
    (realize signature (fun _ _ U => (negativeLines U).card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity
    definition := some {
      owner := `D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity
      name := `D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity
