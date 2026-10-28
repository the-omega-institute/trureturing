import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Witness.AbsolutelyEntangledAllPartitions
import Reg.Support.DependentFamily

/-! Source-bound audit of the normalization of the simultaneous entanglement witnesses. -/

namespace Reg.D5.S3.Quantum.Entanglement.Witness.AbsolutelyEntangledAllPartitions

open _root_.D5.S3.Quantum.Entanglement.Witness.AbsolutelyEntangledAllPartitions
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the trace of a matrix in each dimension. -/
abbrev signature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ρ => Matrix.trace ρ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete witness-set claim, observing its trace-one requirement. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ d a b : ℕ, 2 ≤ a → 2 ≤ b → d = a * b →
    ∃ s : Finset (Matrix (Fin d) (Fin d) ℂ),
      (∀ ρ ∈ s, ρ.PosSemidef ∧ R.readout () d ρ = 1) ∧
      ∀ u ∈ Matrix.specialUnitaryGroup (Fin d) ℂ,
        ∃ ρ ∈ s, ∀ p : Partition d, ¬ Separable p (u * ρ * star u)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨s, hs, hu⟩ := h 4 2 2 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨ρ, hρ, _⟩ := hu 1 (one_mem (Matrix.specialUnitaryGroup (Fin 4) ℂ))
  have hzero := (hs ρ hρ).2
  change (0 : ℂ) = 1 at hzero
  exact zero_ne_one hzero

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change Matrix.trace (0 : Matrix (Fin 1) (Fin 1) ℂ) ≠
    Matrix.trace (1 : Matrix (Fin 1) (Fin 1) ℂ)
  norm_num [Matrix.trace_one]

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
      (@_root_.D5.S3.Quantum.Entanglement.Witness.AbsolutelyEntangledAllPartitions.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.AbsolutelyEntangledAllPartitions.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.Witness.AbsolutelyEntangledAllPartitions.source_registration
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
    (realize signature (fun _ _ ρ => Matrix.trace ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.AbsolutelyEntangledAllPartitions
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.Witness.AbsolutelyEntangledAllPartitions
      name := `D5.S3.Quantum.Entanglement.Witness.AbsolutelyEntangledAllPartitions.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body",
        "fn", "arg", "body", "body", "arg", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.Witness.AbsolutelyEntangledAllPartitions
