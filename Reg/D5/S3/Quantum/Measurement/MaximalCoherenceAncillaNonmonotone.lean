import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.MaximalCoherenceAncillaNonmonotone
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Measurement.MaximalCoherenceAncillaNonmonotone
open _root_.D5.S3.Quantum.Measurement.MaximalCoherenceAncillaNonmonotone
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Matrix.Norms.L2Operator

namespace EntryNorm
abbrev signature : Signature where
  Params := Σ d : ℕ, Fin d × Fin d
  State p := Matrix (Fin p.1) (Fin p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p A => A p.2.1 p.2.2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d), ‖R.readout () ⟨d,i,j⟩ A‖ ≤ ‖A‖
private theorem actual_law : arena.Law actual := by
  intro d A i j
  exact entry_le_norm A i j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (d := 1) 0 0 0
  norm_num [rejected, realize] at hh
private theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim _ _)).elim
  · intro i
    exact nomatch i
private theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨1,0,0⟩, 0, 1, ?_⟩
  change (0 : ℂ) ≠ 1
  exact zero_ne_one
def source_registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Measurement.MaximalCoherenceAncillaNonmonotone.entry_le_norm)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.MaximalCoherenceAncillaNonmonotone.entry_le_norm.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.MaximalCoherenceAncillaNonmonotone.EntryNorm.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p A => A p.2.1 p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.MaximalCoherenceAncillaNonmonotone
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end EntryNorm

end
end Reg.D5.S3.Quantum.Measurement.MaximalCoherenceAncillaNonmonotone
