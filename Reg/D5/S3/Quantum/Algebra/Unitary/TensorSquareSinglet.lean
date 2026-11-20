import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.Unitary.TensorSquareSinglet
import Reg.Support.DependentFamily

/-! Source-bound audit of the invariant subspaces of the tensor square of two qubits. The
readout is the scalar `det g` by which `g ⊗ g` acts on the singlet, read in the fourth
conjunct. -/

namespace Reg.D5.S3.Quantum.Algebra.Unitary.TensorSquareSinglet

open _root_.D5.S3.Quantum.Algebra.Unitary.TensorSquareSinglet
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Matrix Kronecker

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

namespace Scalar

/-- A scalar attached to a `2 × 2` complex matrix. -/
abbrev signature : Signature where
  Params := Unit
  State _ := Matrix (Fin 2) (Fin 2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ g => g.det) (fun e => nomatch e)

/-- The reading that returns `1` for every matrix. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Retain the complete statement of `singlet_invariant_subspaces`; only the scalar by which
`g ⊗ g` multiplies the singlet is read out. -/
abbrev arena : Arena where
  signature := signature
  Law r :=
    phaseMatrix ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
    rotationMatrix ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
    (∀ S : Set (Matrix (Fin 2) (Fin 2) ℂ), phaseMatrix ∈ S → rotationMatrix ∈ S →
      ∀ W : Submodule ℂ (EuclideanSpace ℂ (Fin 2 × Fin 2)),
        (∀ g ∈ S, ∀ x ∈ W, (g ⊗ₖ g).toEuclideanLin x ∈ W) ↔
          W = ⊥ ∨ W = ℂ ∙ singlet ∨ W = (ℂ ∙ singlet)ᗮ ∨ W = ⊤) ∧
    (∀ g : Matrix (Fin 2) (Fin 2) ℂ,
      (g ⊗ₖ g).toEuclideanLin singlet = r.readout () () g • singlet) ∧
    (∀ x : EuclideanSpace ℂ (Fin 2 × Fin 2), x ∈ (ℂ ∙ singlet)ᗮ ↔ x (0, 1) = x (1, 0)) ∧
    Module.finrank ℂ (ℂ ∙ singlet)ᗮ = 3

/-- The singlet is not zero: its `|01⟩` coordinate is `1`. -/
theorem singlet_ne_zero : singlet ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : EuclideanSpace ℂ (Fin 2 × Fin 2) => x (0, 1)) h
  simp [singlet] at h1

/-- For the zero matrix `g ⊗ g` kills the singlet, so the scalar cannot be `1`. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h.2.2.2.1 0
  simp only [rejected, realize, one_smul] at h0
  apply singlet_ne_zero
  rw [← h0]
  simp

/-- The determinants of the zero matrix and of the identity differ. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : Matrix (Fin 2) (Fin 2) ℂ).det ≠ (1 : Matrix (Fin 2) (Fin 2) ℂ).det
  simp

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @singlet_invariant_subspaces

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@singlet_invariant_subspaces, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Scalar

def singlet_invariant_subspaces_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@singlet_invariant_subspaces) (Realization Scalar.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Algebra.Unitary.TensorSquareSinglet.singlet_invariant_subspaces_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.Unitary.TensorSquareSinglet.Scalar.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Scalar.arena⟩
  objectArena := .source ⟨Scalar.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Scalar.arena ⟨Scalar.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Scalar.signature (fun _ _ g => g.det) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.Unitary.TensorSquareSinglet
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "fn", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Algebra.Unitary.TensorSquareSinglet
