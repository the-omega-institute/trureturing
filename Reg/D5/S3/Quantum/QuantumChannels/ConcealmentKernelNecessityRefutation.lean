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

/-- Observe the set comprehension in the density-spanning statement. -/
abbrev signature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℂ → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Set (Matrix (Fin d) (Fin d) ℂ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => Set.ofPred p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ d : ℕ,
    TomographicallyComplete (R.readout () d (fun ρ : Matrix (Fin d) (Fin d) ℂ => IsDensity ρ))

theorem empty_not_complete : ¬ TomographicallyComplete (∅ : Set (Matrix (Fin 1) (Fin 1) ℂ)) := by
  intro h
  have hmem : (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈ HermitianSpace 1 :=
    Matrix.isHermitian_one
  rw [← h.2, Submodule.span_empty] at hmem
  have hz : (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := hmem
  have he := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) hz
  norm_num at he

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact empty_not_complete (h 1)

def source_registration : Registration arena (type_of% @all_density_tomographically_complete) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨all_density_tomographically_complete, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨0, (fun _ => False), (fun _ => True), ?_⟩
    change (∅ : Set (Matrix (Fin 0) (Fin 0) ℂ)) ≠ Set.univ
    exact Set.empty_ne_univ

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
    (realize signature (fun _ _ p => Set.ofPred p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg"]
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
end Reg.D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
