import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality
import Reg.Support.DependentFamily

/-! Source-bound audit of the effective-conductance lower bound. -/

namespace Reg.D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality

open _root_.D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the product of the proposed constant and effective conductance. -/
abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k g => k * g) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain all finite graphs, densities, test functions, and admissibility hypotheses. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ (v : Type) [Fintype v] [DecidableEq v] (c : v → v → ℝ), IsConductance c →
      ∀ x y : v, x ≠ y → ∀ α : ℝ, 0 < α → α < 1 → ∀ k : ℝ,
        (∀ f : (v → Fin 2) → ℝ,
          (1 / 2) * expect α (fun ζ => grad x y f ζ ^ 2) ≤
            k * exclusionEnergy c α f) →
        1 ≤ R.readout () k (effectiveConductance c x y)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : IsConductance (fun _ _ : Fin 2 => (1 : ℝ)) := by
    constructor <;> intros <;> norm_num
  have henergy (f : (Fin 2 → Fin 2) → ℝ) :
      (1 / 2) * expect (1 / 2) (fun ζ => grad 0 1 f ζ ^ 2) ≤
        (1 : ℝ) * exclusionEnergy (fun _ _ : Fin 2 => 1) (1 / 2) f := by
    simp [exclusionEnergy, Fin.sum_univ_two, grad, swap, Equiv.swap_comm]
    ring_nf
    simp [expect, dotProduct]
  have hbad := h (Fin 2) (fun _ _ => 1) hc 0 1 (by decide)
    (1 / 2) (by norm_num) (by norm_num) 1 henergy
  change (1 : ℝ) ≤ 0 at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change (1 : ℝ) * 0 ≠ 1 * 1
  norm_num

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
      (@result)
      (Realization signature) Unit Unit := {
  unitName := `ExclusionMovingParticleOptimality.result.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k g => k * g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality
    definition := some {
      owner := `D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality
      name := `D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.claim
      path := #[] }
    coordinates := #[11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality
