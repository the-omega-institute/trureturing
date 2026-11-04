import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumBounds.HighSpinCHSHNonviolation
import Reg.Support.DependentFamily

/-! Source-bound audit of the spin-dependent CHSH bound. -/

namespace Reg.D5.S3.QuantumBounds.HighSpinCHSHNonviolation

open _root_.D5.S3.QuantumBounds.HighSpinCHSHNonviolation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the bound as the doubled spin varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => (n : ℝ) ^ 2 / 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Retain every density, direction, and spin hypothesis of the claim. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, 2 ≤ n →
    ∀ ρ : Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ,
      ρ.PosSemidef → ρ.trace = 1 → ∀ a c b d : Fin 3 → ℝ,
        unit a → unit c → unit b → unit d →
          ‖(ρ * chshOperator n a c b d).trace‖ ≤ r.readout () () n

private def density : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  diagonal (fun i => if i = (0, 0) then 1 else 0)

private theorem density_positive : density.PosSemidef := by
  apply posSemidef_diagonal_iff.mpr
  intro i
  split_ifs <;> norm_num

private theorem density_trace : density.trace = 1 := by
  simp [density, Matrix.trace]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let z : Fin 3 → ℝ := ![0, 0, 1]
  have hz : unit z := by norm_num [unit, z]
  have hbad := h 2 (by norm_num) density density_positive density_trace z z z z hz hz hz hz
  change ‖(density * chshOperator 2 z z z z).trace‖ ≤ (-1 : ℝ) at hbad
  exact (not_le_of_gt (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0)
    (norm_nonneg _))) hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  change (2 : ℝ) ^ 2 / 2 ≠ (3 : ℝ) ^ 2 / 2
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
      (@_root_.D5.S3.QuantumBounds.HighSpinCHSHNonviolation.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumBounds.HighSpinCHSHNonviolation.unit
  realizationName :=
    `Reg.D5.S3.QuantumBounds.HighSpinCHSHNonviolation.source_registration
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
    (realize signature (fun _ _ n => (n : ℝ) ^ 2 / 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.HighSpinCHSHNonviolation
    definition := some {
      owner := `D5.S3.QuantumBounds.HighSpinCHSHNonviolation
      name := `D5.S3.QuantumBounds.HighSpinCHSHNonviolation.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg"]
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
end Reg.D5.S3.QuantumBounds.HighSpinCHSHNonviolation
