import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the power Poisson density and its Stieltjes transform. -/

namespace Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight

open _root_.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Real Set MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace DenominatorPos

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature
    (fun _ r α => 1 - 2 * r * Real.cos (Real.pi * α) + r ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α r : ℝ}, 0 < α → α < 2 → α ≠ 1 → 0 < R.readout () r α

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (α := 1 / 2) (r := 0) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @power_poisson_denominator_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@power_poisson_denominator_pos, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@power_poisson_denominator_pos) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight.DenominatorPos
    "unit"
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight.DenominatorPos
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
  readout := some (realize signature
    (fun _ r α => 1 - 2 * r * Real.cos (Real.pi * α) + r ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg", "arg", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end DenominatorPos

end
end Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight

