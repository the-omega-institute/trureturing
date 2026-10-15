import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients
open _root_.D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe a solution sequence at the index in the uniqueness conclusion. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ i a => a i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain existence, positivity, closed forms and agreement through degree `m`. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ m : ℕ, 2 ≤ m →
      ∃ b : ℕ → ℝ, ∃ c : ℕ → ℕ → ℝ,
        PositiveConstants m b c ∧
        ∀ Q κ : ℝ, 0 < Q → 0 < κ →
          (∃ a : ℕ → ℝ, System m Q κ a) ∧
          (∀ a : ℕ → ℝ,
            System m Q κ a → ClosedForms m Q κ b c a) ∧
          (∀ a a' : ℕ → ℝ,
            System m Q κ a →
            System m Q κ a' →
            ∀ i : ℕ, i ≤ m → a i = R.readout () i a')

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨b, c, _, hbc⟩ := h 2 (by norm_num)
  obtain ⟨⟨a, ha⟩, _, hagree⟩ := hbc 1 1 zero_lt_one zero_lt_one
  have hzero := hagree a a ha ha 0 (by norm_num)
  have hone := hagree a a ha ha 1 (by norm_num)
  change a 0 = 0 at hzero
  change a 1 = 0 at hone
  have heq := ha.1
  rw [hzero, hone] at heq
  norm_num at heq

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  exact zero_ne_one

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ i a => a i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients
    definition := some {
      owner := `D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients
      name := `D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.claim
      path := #[] }
    coordinates := #[12]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg",
        "body", "body", "body", "body", "arg", "arg",
        "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients
