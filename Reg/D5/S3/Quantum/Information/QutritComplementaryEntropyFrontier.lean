import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier
open _root_.D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Evaluate the frontier bound at the trade-off parameter. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ a f => f a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ a f => f a + 1) (fun e => nomatch e)

/-- Retain both trade-off directions and both exact attainers. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ,
      admissible V →
      ∀ a : ℝ, a ∈ Set.Icc 0 (1 / 3 : ℝ) →
        (mapEntropy V ≤ h a →
          R.readout () a g ≤ mapEntropy (swap V)) ∧
        (mapEntropy (swap V) ≤ h a →
          g a ≤ mapEntropy V)) ∧
    (∀ a : ℝ, a ∈ Set.Icc 0 (1 / 3 : ℝ) →
      (admissible (attainer a) ∧
        mapEntropy (attainer a) = h a ∧
        mapEntropy (swap (attainer a)) = g a) ∧
      (admissible (swap (attainer a)) ∧
        mapEntropy (swap (attainer a)) = g a ∧
        mapEntropy (swap (swap (attainer a))) = h a))

theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  have ha : (0 : ℝ) ∈ Set.Icc 0 (1 / 3 : ℝ) := by constructor <;> norm_num
  obtain ⟨hV, hH, hG⟩ := (result.2 0 ha).1
  have hb := (bad.1 (attainer 0) hV 0 ha).1 hH.le
  change g 0 + 1 ≤ mapEntropy (swap (attainer 0)) at hb
  rw [hG] at hb
  linarith

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
      (@_root_.D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a f => f a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier
    definition := some {
      owner := `D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier
      name := `D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier.claim
      path := #[] }
    coordinates := #[2]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "fn", "arg", "body",
        "fn", "arg"]
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
end Reg.D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier
