import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum
open _root_.D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the sharp lower spectral bound, with the largest eigenvalue fixed. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ μ₁ μ₂ => -Real.sqrt (μ₁ * μ₂)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ μ₁ μ₂ => -Real.sqrt (μ₁ * μ₂) - 1) (fun e => nomatch e)

/-- Retain the ordering, characteristic polynomial and both directions of existence. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ μ₁ μ₂ μ₃ : ℝ, μ₂ ≤ μ₁ → μ₃ ≤ μ₂ →
    ((∃ W : Matrix (Fin 3) (Fin 3) ℂ, IsSymmetricWitness W ∧
        W.charpoly = (Polynomial.X - Polynomial.C (μ₁ : ℂ)) *
          (Polynomial.X - Polynomial.C (μ₂ : ℂ)) *
          (Polynomial.X - Polynomial.C (μ₃ : ℂ))) ↔
      (0 ≤ μ₂ ∧ R.readout () μ₁ μ₂ ≤ μ₃))

theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  have h30 : (-1 : ℝ) ≤ 0 := by norm_num
  have hx := (bad 0 0 (-1) le_rfl h30).mpr
    ⟨le_rfl, by norm_num [rejected, realize]⟩
  have hb := ((result 0 0 (-1) le_rfl h30).mp hx).2
  norm_num at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum.result)
      (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum.unit
  realizationName :=
    .str `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum
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
    (realize signature (fun _ μ₁ μ₂ => -Real.sqrt (μ₁ * μ₂)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum
      name := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum
