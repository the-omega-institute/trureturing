import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Foundation.FiniteHermitianSign

set_option autoImplicit false

noncomputable section
namespace Reg.D5.S3.Quantum.Foundation.FiniteHermitianSign
open Matrix
open scoped ComplexOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Quantum.Foundation.FiniteHermitianSign
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_of_posSemidef)

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

private theorem traceNorm_zero (n : ℕ) : traceNorm (0 : Mat n) = 0 := by
  simpa using congrArg Complex.re
    (traceNorm_of_posSemidef (PosSemidef.zero : (0 : Mat n).PosSemidef))

private theorem traceNorm_one : traceNorm (1 : Mat 1) = 1 := by
  simpa using congrArg Complex.re
    (traceNorm_of_posSemidef (PosSemidef.one : (1 : Mat 1).PosSemidef))

abbrev normSignature : DependentFamily.Signature where
  Params := ℕ
  State := Mat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def normActual : DependentFamily.Realization normSignature :=
  DependentFamily.realize normSignature (fun _ (n : ℕ) (A : Mat n) => traceNorm A) (fun e => nomatch e)

def normShifted : DependentFamily.Realization normSignature :=
  DependentFamily.realize normSignature (fun _ (n : ℕ) (A : Mat n) => traceNorm A + 2) (fun e => nomatch e)

theorem normDependence : DependentFamily.ObservationalDependence normSignature normActual := by
  intro i
  cases i
  refine ⟨1, (0 : Mat 1), (1 : Mat 1), ?_⟩
  change traceNorm (0 : Mat 1) ≠ traceNorm (1 : Mat 1)
  rw [traceNorm_zero, traceNorm_one]
  norm_num

abbrev signSpecArena : DependentFamily.Arena where
  signature := normSignature
  Law := fun R => ∀ {n : ℕ} {A : Mat n} (hA : A.IsHermitian),
    (hermitianSign hA).IsHermitian ∧
    (1 - hermitianSign hA).PosSemidef ∧ (1 + hermitianSign hA).PosSemidef ∧
    (hermitianSign hA * A).trace.re = R.readout () n A

theorem signSpecShiftFails : ¬ signSpecArena.Law normShifted := by
  intro bad
  have hA : (0 : Mat 1).IsHermitian := (PosSemidef.zero : (0 : Mat 1).PosSemidef).isHermitian
  have actual := (hermitianSign_spec hA).2.2.2
  have shifted := (bad hA).2.2.2
  change (hermitianSign hA * (0 : Mat 1)).trace.re = traceNorm (0 : Mat 1) + 2 at shifted
  linarith

def signSpecFamily : DependentFamily.Registration signSpecArena
    (∀ {n : ℕ} {A : Mat n} (hA : A.IsHermitian),
      (hermitianSign hA).IsHermitian ∧
      (1 - hermitianSign hA).PosSemidef ∧ (1 + hermitianSign hA).PosSemidef ∧
      (hermitianSign hA * A).trace.re = traceNorm A) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨@hermitianSign_spec, normShifted, signSpecShiftFails⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨normShifted, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, signSpecShiftFails⟩
    · intro e
      exact nomatch e
  dependence := normDependence

abbrev eigSignature : DependentFamily.Signature where
  Params := Σ n, Mat n
  State := fun p => Fin p.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Fin p.1 → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def eigActual : DependentFamily.Realization eigSignature :=
  DependentFamily.realize eigSignature (fun _ p x => p.2 *ᵥ x) (fun e => nomatch e)

def eigErased : DependentFamily.Realization eigSignature :=
  DependentFamily.realize eigSignature (fun _ (p : Σ n, Mat n) _ => (0 : Fin p.1 → ℂ)) (fun e => nomatch e)

abbrev eigArena : DependentFamily.Arena where
  signature := eigSignature
  Law := fun R => ∀ {n : ℕ} {A : Mat n} (hA : A.IsHermitian) (x : Fin n → ℂ),
    (hermitianSign hA *ᵥ x = 0 ↔ R.readout () ⟨n, A⟩ x = 0) ∧
    (hermitianSign hA *ᵥ x = x ↔ x ∈ positiveSubspace hA) ∧
    (hermitianSign hA *ᵥ x = -x ↔ x ∈ negativeSubspace hA)

theorem eigErasureFails : ¬ eigArena.Law eigErased := by
  intro bad
  have hA : (1 : Mat 1).IsHermitian := isHermitian_one
  have h := (bad hA (1 : Fin 1 → ℂ)).1.mpr rfl
  have impossible := (hermitianSign_eigenspaces hA (1 : Fin 1 → ℂ)).1.mp h
  have h01 := congrFun impossible (0 : Fin 1)
  simp at h01

def eigFamily : DependentFamily.Registration eigArena
    (∀ {n : ℕ} {A : Mat n} (hA : A.IsHermitian) (x : Fin n → ℂ),
      (hermitianSign hA *ᵥ x = 0 ↔ A *ᵥ x = 0) ∧
      (hermitianSign hA *ᵥ x = x ↔ x ∈ positiveSubspace hA) ∧
      (hermitianSign hA *ᵥ x = -x ↔ x ∈ negativeSubspace hA)) where
  actual := eigActual
  bridge := Iff.rfl
  variation := ⟨@hermitianSign_eigenspaces, eigErased, eigErasureFails⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨eigErased, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, eigErasureFails⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨⟨1, (1 : Mat 1)⟩, (0 : Fin 1 → ℂ), (1 : Fin 1 → ℂ), ?_⟩
    change (1 : Mat 1) *ᵥ (0 : Fin 1 → ℂ) ≠ (1 : Mat 1) *ᵥ (1 : Fin 1 → ℂ)
    intro h
    have h01 := congrFun h (0 : Fin 1)
    simp at h01

noncomputable def signSpecRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@hermitianSign_spec) (DependentFamily.Realization normSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Foundation.FiniteHermitianSign.hermitianSign_spec.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.FiniteHermitianSign.signSpecFamily
  realizationSource := none
  generated := false
  arena := .source ⟨signSpecArena⟩
  objectArena := .source ⟨signSpecArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source signSpecArena ⟨signSpecFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize normSignature (fun _ (n : ℕ) (A : Mat n) => traceNorm A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.FiniteHermitianSign
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def eigenspacesRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@hermitianSign_eigenspaces) (DependentFamily.Realization eigSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Foundation.FiniteHermitianSign.hermitianSign_eigenspaces.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.FiniteHermitianSign.eigFamily
  realizationSource := none
  generated := false
  arena := .source ⟨eigArena⟩
  objectArena := .source ⟨eigArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source eigArena ⟨eigFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize eigSignature (fun _ p x => p.2 *ᵥ x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.FiniteHermitianSign
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Foundation.FiniteHermitianSign
