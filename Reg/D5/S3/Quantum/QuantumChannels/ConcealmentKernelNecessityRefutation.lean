import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import Reg.Support.DependentFamily

/-! # Density-set tomography readout -/

namespace Reg.D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
open _root_.D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
open _root_.D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
open _root_.D5.S3.Quantum.Measurement.BasisMeasurementProjection (HermitianSpace)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe whether the input set consists of densities and spans the Hermitian space. -/
abbrev signature : Signature where
  Params := ℕ
  State d := Set (Matrix (Fin d) (Fin d) ℂ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

open Classical in
def actual : Realization signature :=
  realize signature (fun _ _ T => decide (TomographicallyComplete T)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ d : ℕ, R.readout () d {ρ : Matrix (Fin d) (Fin d) ℂ | IsDensity ρ} = true

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0
  change false = true at he
  cases he

theorem empty_not_complete : ¬ TomographicallyComplete (∅ : Set (Matrix (Fin 1) (Fin 1) ℂ)) := by
  intro h
  have hmem : (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈ HermitianSpace 1 :=
    Matrix.isHermitian_one
  rw [← h.2, Submodule.span_empty] at hmem
  have hz : (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := hmem
  have he := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) hz
  norm_num at he

def source_registration : Registration arena (type_of% @all_density_tomographically_complete) where
  actual := actual
  bridge := by simp [actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using all_density_tomographically_complete,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, {ρ | IsDensity ρ}, ∅, ?_⟩
    simp [actual, realize, all_density_tomographically_complete, empty_not_complete]

open Classical in
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@all_density_tomographically_complete) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.unit
  realizationName := .str
    `Reg.D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
    "source_registration"
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
    (realize signature (fun _ _ T => decide (TomographicallyComplete T)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
