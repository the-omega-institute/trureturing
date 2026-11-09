import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurements.UltrafineThreeProductObservables
import Reg.Support.DependentFamily

/-! Source-bound audit of the useful three-product-observable family. -/

namespace Reg.D5.S3.Quantum.Measurements.UltrafineThreeProductObservables

open _root_.D5.S3.Quantum.Measurements.UltrafineThreeProductObservables
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix Finset
open scoped Kronecker

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe a product matrix while varying its first factor. -/
abbrev signature : Signature where
  Params := Σ _ : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ, Fin 3
  State _ := Matrix (Fin 3) (Fin 3) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p A => A ⊗ₖ p.1 p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the Hermitian factors, every useless pair, and the useful triple. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∃ a b : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ,
    (∀ i, (a i).IsHermitian ∧ (b i).IsHermitian) ∧
    (∀ i j, i ≠ j → IsUseless (fun k => a k ⊗ₖ b k) {i, j}) ∧
    ¬ IsUseless (fun k => r.readout () ⟨b, k⟩ (a k)) univ

theorem zero_useless : IsUseless
    (fun _ : Fin 3 => (0 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)) univ := by
  obtain ⟨a, b, _, hpairs, _⟩ := result
  intro ρ hρ
  obtain ⟨σ, hσ, hsep, _⟩ := hpairs 0 1 (by decide) ρ hρ
  exact ⟨σ, hσ, hsep, fun i _ => by simp⟩

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨a, b, _, _, h⟩
  exact h zero_useless

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨(fun _ => 1), 0⟩, 0, 1, ?_⟩
  simp [actual, realize]

def source_registration : Registration arena claim where
  actual := actual
  bridge := by simp [claim, actual, realize]
  variation := ⟨by simpa [arena, actual, realize, claim] using result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurements.UltrafineThreeProductObservables.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurements.UltrafineThreeProductObservables.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurements.UltrafineThreeProductObservables.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p A => A ⊗ₖ p.1 p.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.UltrafineThreeProductObservables
    definition := some {
      owner := `D5.S3.Quantum.Measurements.UltrafineThreeProductObservables
      name := `D5.S3.Quantum.Measurements.UltrafineThreeProductObservables.claim
      path := #[] }
    coordinates := #[1, 2]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "arg", "arg", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.Quantum.Measurements.UltrafineThreeProductObservables.result
#print _root_.D5.S3.Quantum.Measurements.UltrafineThreeProductObservables.claim
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurements.UltrafineThreeProductObservables
