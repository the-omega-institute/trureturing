import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.FockSpace.EvninQuantumSector
import Reg.Support.DependentFamily

/-! Source-bound audit of the top eigenvalue as the sector momentum varies. -/

namespace Reg.D5.S3.Quantum.FockSpace.EvninQuantumSector

open _root_.D5.S3.Quantum.FockSpace.EvninQuantumSector
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- Observe the spectral maximum as a function of momentum at fixed weight and particle number. -/
abbrev signature : Signature where
  Params := Σ _ : ℝ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p M => energy p.1 p.2 M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete sector law, varying the spectral maximum in its source occurrence. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (σ : ℝ), 1 ≤ σ → ∀ (N M : ℕ), ∀ [Nonempty (Sector M N M)],
    (hamiltonian σ N M).IsHermitian ∧
      IsGreatest (spectrum ℝ (hamiltonian σ N M)) (R.readout () ⟨σ, N⟩ M) ∧
      (occupationVector (raney σ 1) : Sector M N M → ℂ) ≠ 0 ∧
      hamiltonian σ N M *ᵥ occupationVector (raney σ 1) =
        energy σ N M • occupationVector (raney σ 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : Nonempty (Sector 0 2 0) :=
    ⟨⟨fun _ => 2, by simp [Fin.sum_univ_succ]⟩⟩
  have hzero := (h 1 (by norm_num) 2 0).2.1
  change IsGreatest (spectrum ℝ (hamiltonian 1 2 0)) 0 at hzero
  have hone := (top_finite_sector_eigenvalue 1 (by norm_num) 2 0).2.1
  have he := le_antisymm (hzero.2 hone.1) (hone.2 hzero.1)
  norm_num [energy] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 2⟩, 0, 1, ?_⟩
  change energy 1 2 0 ≠ energy 1 2 1
  norm_num [energy]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨top_finite_sector_eigenvalue, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.FockSpace.EvninQuantumSector.top_finite_sector_eigenvalue)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.FockSpace.EvninQuantumSector.unit
  realizationName := `Reg.D5.S3.Quantum.FockSpace.EvninQuantumSector.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p M => energy p.1 p.2 M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.FockSpace.EvninQuantumSector
    definition := some {
      owner := `D5.S3.Quantum.FockSpace.EvninQuantumSector
      name := `D5.S3.Quantum.FockSpace.EvninQuantumSector.claim
      path := #[] }
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.FockSpace.EvninQuantumSector
