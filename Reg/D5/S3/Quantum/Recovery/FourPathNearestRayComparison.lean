import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.FourPathNearestRayComparison
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.FourPathNearestRayComparison
open scoped Matrix.Norms.Frobenius

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Recovery.FourPathNearestRayComparison

abbrev signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {J : Type*} [Fintype J]
    (K B E F : J → Matrix Index Index ℂ) (τ dSq : J → ℝ) (c : ℝ),
    (∀ j, K j - B j = E j + F j) →
    (∀ j, ‖E j‖ ^ 2 ≤ 2 * τ j) →
    (∀ j, ‖F j‖ ^ 2 ≤ c * dSq j) →
    obs.readout () () true = true ∧
      finite_family_error_aggregation K B E F τ dSq c
        (by assumption) (by assumption) (by assumption)

abbrev claim : Prop := ∀ {J : Type*} [Fintype J]
    (K B E F : J → Matrix Index Index ℂ) (τ dSq : J → ℝ) (c : ℝ),
    (∀ j, K j - B j = E j + F j) →
    (∀ j, ‖E j‖ ^ 2 ≤ 2 * τ j) →
    (∀ j, ‖F j‖ ^ 2 ≤ c * dSq j) →
    4 * (∑ j, τ j) + 2 * c * (∑ j, dSq j) ≥ ∑ j, ‖K j - B j‖ ^ 2

theorem actual_law : arena.Law actual := by
  intro J inst K B E F τ dSq c hdecomp hE hF
  exact ⟨rfl, finite_family_error_aggregation K B E F τ dSq c hdecomp hE hF⟩

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let K : Fin 0 → Matrix Index Index ℂ := fun j => j.elim0
  let B : Fin 0 → Matrix Index Index ℂ := fun j => j.elim0
  let E : Fin 0 → Matrix Index Index ℂ := fun j => j.elim0
  let F : Fin 0 → Matrix Index Index ℂ := fun j => j.elim0
  let τ : Fin 0 → ℝ := fun j => j.elim0
  let dSq : Fin 0 → ℝ := fun j => j.elim0
  have hh := h (J := Fin 0) K B E F τ dSq 0
    (by intro j; exact j.elim0)
    (by intro j; exact j.elim0)
    (by intro j; exact j.elim0)
  exact Bool.noConfusion (by simpa [rejected, realize] using hh.1)

def source_registration : Registration arena claim where
  actual := actual
  bridge := by
    constructor
    · intro h J inst K B E F τ dSq c hdecomp hE hF
      exact ⟨rfl, h K B E F τ dSq c hdecomp hE hF⟩
    · intro h J inst K B E F τ dSq c hdecomp hE hF
      exact (h K B E F τ dSq c hdecomp hE hF).2
  variation := ⟨actual_law, ⟨rejected, rejected_law⟩⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), False, True, ?_⟩
    simp [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Recovery.FourPathNearestRayComparison.finite_family_error_aggregation)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.FourPathNearestRayComparison.finite_family_error_aggregation.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.FourPathNearestRayComparison.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ _ => true) (fun e _ => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev mass_signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def mass_actual : Realization mass_signature :=
  realize mass_signature (fun _ _ _ => true) (fun e _ => nomatch e)

def mass_rejected : Realization mass_signature :=
  realize mass_signature (fun _ _ _ => false) (fun e _ => nomatch e)

abbrev mass_arena : Arena where
  signature := mass_signature
  Law obs := ∀ {J : Type*} [Fintype J] (p q : J → ℝ) (σ : J → Bool),
    (∀ j, 0 ≤ p j) → (∀ j, 0 ≤ q j) →
    (∑ j, p j = 1) → (∑ j, q j = 1) →
    (∀ j, (σ j = true ∧ q j ≤ p j) ∨ (σ j = false ∧ p j < q j)) →
    obs.readout () () true = true ∧
      selected_mass_bounds_and_defect p q σ
        (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)

abbrev mass_claim : Prop := ∀ {J : Type*} [Fintype J] (p q : J → ℝ) (σ : J → Bool),
    (∀ j, 0 ≤ p j) → (∀ j, 0 ≤ q j) →
    (∑ j, p j = 1) → (∑ j, q j = 1) →
    (∀ j, (σ j = true ∧ q j ≤ p j) ∨ (σ j = false ∧ p j < q j)) →
    (0 ≤ ∑ j, if σ j = true then p j else 0) ∧
      (∑ j, if σ j = true then p j else 0) ≤ 1 ∧
      (0 ≤ ∑ j, if σ j = true then 0 else q j) ∧
      (∑ j, if σ j = true then 0 else q j) ≤ 1 ∧
      (1 - ∑ j, if σ j = true then p j else 0) +
          (1 - ∑ j, if σ j = true then 0 else q j) =
        ∑ j, min (p j) (q j)

theorem mass_actual_law : mass_arena.Law mass_actual := by
  intro J inst p q σ hp hq hsumP hsumQ hsel
  exact ⟨rfl, selected_mass_bounds_and_defect p q σ hp hq hsumP hsumQ hsel⟩

theorem mass_rejected_law : ¬ mass_arena.Law mass_rejected := by
  intro h
  have hh := h (J := Fin 0) (fun j => j.elim0) (fun j => j.elim0) (fun j => j.elim0)
    (by intro j; exact j.elim0) (by intro j; exact j.elim0)
    (by simp) (by simp) (by intro j; exact j.elim0)
  exact Bool.noConfusion (by simpa [mass_rejected, realize] using hh.1)

def mass_source_registration : Registration mass_arena mass_claim where
  actual := mass_actual
  bridge := by
    constructor
    · intro h J inst p q σ hp hq hsumP hsumQ hsel
      exact ⟨rfl, h p q σ hp hq hsumP hsumQ hsel⟩
    · intro h J inst p q σ hp hq hsumP hsumQ hsel
      exact (h p q σ hp hq hsumP hsumQ hsel).2
  variation := ⟨mass_actual_law, ⟨mass_rejected, mass_rejected_law⟩⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨mass_rejected, ?_, rfl, mass_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), False, True, ?_⟩
    simp [mass_actual, realize]

def mass_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Recovery.FourPathNearestRayComparison.selected_mass_bounds_and_defect)
      (Realization mass_signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.FourPathNearestRayComparison.selected_mass_bounds_and_defect.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.FourPathNearestRayComparison.mass_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨mass_arena⟩
  objectArena := .source ⟨mass_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source mass_arena ⟨mass_source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize mass_signature (fun _ _ _ => true) (fun e _ => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
#print axioms mass_source_registration
#print axioms mass_registration

end Reg.D5.S3.Quantum.Recovery.FourPathNearestRayComparison
