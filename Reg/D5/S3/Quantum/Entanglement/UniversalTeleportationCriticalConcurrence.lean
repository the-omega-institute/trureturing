import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.UniversalTeleportationCriticalConcurrence
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.UniversalTeleportationCriticalConcurrence
open _root_.D5.S3.Quantum.Entanglement.UniversalTeleportationCriticalConcurrence
open _root_.D5.S3.QuantumChannels.SwitchUselessConcatenationRefutation (IsKrausChannel)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the concurrence in the necessary strict threshold inequality. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ a => conc a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Both channel clauses and the full admissible interval are retained. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ a : ℝ, (1 / 2 : ℝ) < a → a < 1 →
    (∀ (m : ℕ) (K : Fin m → Matrix (Fin 2) (Fin 2) ℂ),
      IsKrausChannel (ι := Fin m) K → UsefulUQT (out a K) → Cstar < R.readout () () a) ∧
    (Cstar < conc a → ∃ (m : ℕ) (K : Fin m → Matrix (Fin 2) (Fin 2) ℂ),
      IsKrausChannel (ι := Fin m) K ∧ NonUnital K ∧ UsefulUQT (out a K))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hC : 0 ≤ Cstar := by unfold Cstar; positivity
  have hs3 : 1 < Real.sqrt 3 := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 3)
  have hs3' : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hsqC := Real.sq_sqrt (show 0 ≤ 5 - 2 * Real.sqrt 3 by linarith)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 / 4 * (1 - 3 / 4) by norm_num)
  have hthreshold : Cstar < conc (3 / 4) := by
    unfold Cstar conc
    nlinarith [Real.sqrt_nonneg (5 - 2 * Real.sqrt 3),
      Real.sqrt_nonneg (3 / 4 * (1 - 3 / 4))]
  obtain ⟨m, K, hK, _, hu⟩ :=
    (result (3 / 4) (by norm_num) (by norm_num)).2 hthreshold
  have hn := (h (3 / 4) (by norm_num) (by norm_num)).1 m K hK hu
  change Cstar < 0 at hn
  exact not_lt_of_ge hC hn

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1 / 2, ?_⟩
  change conc 0 ≠ conc (1 / 2)
  norm_num [conc, Real.sqrt_div]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.UniversalTeleportationCriticalConcurrence.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.UniversalTeleportationCriticalConcurrence.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.UniversalTeleportationCriticalConcurrence "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => conc a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.UniversalTeleportationCriticalConcurrence
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.UniversalTeleportationCriticalConcurrence
      name := `D5.S3.Quantum.Entanglement.UniversalTeleportationCriticalConcurrence.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "body", "body", "arg"]
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
end Reg.D5.S3.Quantum.Entanglement.UniversalTeleportationCriticalConcurrence
