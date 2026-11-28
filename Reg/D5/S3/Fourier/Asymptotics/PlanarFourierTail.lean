import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.PlanarFourierTail
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the absolute coefficient sum. -/

namespace Reg.D5.S3.Fourier.Asymptotics.PlanarFourierTail

open _root_.D5.S3.Fourier.Asymptotics.PlanarFourierTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℤ × ℤ → ℂ)
    (fun _ => Finset (ℤ × ℤ)) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ a s => ∑ m ∈ s, ‖a m‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s : Finset (ℤ × ℤ)) (a : ℤ × ℤ → ℂ) (J : ℕ) (ε K : ℝ),
    0 < J → 0 < ε → 0 ≤ K →
    (∀ m ∈ s, J < modeRadius m) →
    (∀ m ∈ s, ‖a m‖ ≤ K * ε ^ 2 / (1 + ε * modeRadius m) ^ 6) →
    R.readout () a s ≤ 2 * K / (ε ^ 4 * (J : ℝ) ^ 4)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h ∅ (fun _ => 0) 1 1 0 (by decide) (by norm_num) le_rfl
    (by simp) (by simp)
  norm_num [rejected, realize] at hzero

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨fun _ => 1, ∅, {(0, 0)}, ?_⟩
  simpa only [actual, realize, Finset.sum_empty, Finset.sum_singleton, norm_one] using
    (zero_ne_one : (0 : ℝ) ≠ 1)

def source_registration : Registration arena (type_of% @lattice_fourier_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lattice_fourier_tail, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@lattice_fourier_tail) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Fourier.Asymptotics.PlanarFourierTail.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.PlanarFourierTail.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ a s => ∑ m ∈ s, ‖a m‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.PlanarFourierTail
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end

end Reg.D5.S3.Fourier.Asymptotics.PlanarFourierTail
