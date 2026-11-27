import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
import Reg.Support.SingleDependentReadout

/-! Source-bound audits for the multiplicities, mode threshold and cutoff rates. -/

namespace Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold

open _root_.NullConeGravity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout
open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace FourDimensionalMultiplicity

abbrev sig := signature Unit (fun _ => ℕ) (fun _ => ℕ)
abbrev arena : Arena where
  signature := sig
  Law r := ∀ ℓ : ℕ, r.readout () () ℓ = 2 * ℓ + 1

private theorem rejected_law :
    ¬ arena.Law (realize sig (fun _ _ _ => 0) (fun e => nomatch e)) := by
  intro h
  have hzero := h 0
  norm_num [Realization.readout, realize] at hzero

def source_registration : Registration arena (type_of% @harmonicMult_four) where
  actual := realize sig (fun _ _ ℓ => harmonicMult 4 ℓ) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@harmonicMult_four, _, rejected_law⟩
  sensitivity := sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change harmonicMult 4 0 ≠ harmonicMult 4 1
    decide

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@harmonicMult_four) (Realization sig) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.FourDimensionalMultiplicity.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.FourDimensionalMultiplicity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ ℓ => harmonicMult 4 ℓ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
    definition := none, coordinates := #[]
    readouts := #[{
        path := #["body", "fn", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FourDimensionalMultiplicity

namespace FiveDimensionalMultiplicity

abbrev sig := signature Unit (fun _ => ℕ) (fun _ => ℕ)
abbrev arena : Arena where
  signature := sig
  Law r := ∀ ℓ : ℕ, r.readout () () ℓ = (ℓ + 1)^2

private theorem rejected_law :
    ¬ arena.Law (realize sig (fun _ _ _ => 0) (fun e => nomatch e)) := by
  intro h
  have hzero := h 0
  norm_num [Realization.readout, realize] at hzero

def source_registration : Registration arena (type_of% @harmonicMult_five) where
  actual := realize sig (fun _ _ ℓ => harmonicMult 5 ℓ) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@harmonicMult_five, _, rejected_law⟩
  sensitivity := sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change harmonicMult 5 0 ≠ harmonicMult 5 1
    decide

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@harmonicMult_five) (Realization sig) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.FiveDimensionalMultiplicity.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.FiveDimensionalMultiplicity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ ℓ => harmonicMult 5 ℓ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
    definition := none, coordinates := #[]
    readouts := #[{
        path := #["body", "fn", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FiveDimensionalMultiplicity

namespace SixDimensionalMultiplicity

abbrev sig := signature Unit (fun _ => ℕ) (fun _ => ℕ)
abbrev arena : Arena where
  signature := sig
  Law r := ∀ ℓ : ℕ, r.readout () () ℓ = (ℓ + 1) * (ℓ + 2) * (2 * ℓ + 3) / 6

private theorem rejected_law :
    ¬ arena.Law (realize sig (fun _ _ _ => 0) (fun e => nomatch e)) := by
  intro h
  have hzero := h 0
  norm_num [Realization.readout, realize] at hzero

def source_registration : Registration arena (type_of% @harmonicMult_six) where
  actual := realize sig (fun _ _ ℓ => harmonicMult 6 ℓ) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@harmonicMult_six, _, rejected_law⟩
  sensitivity := sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change harmonicMult 6 0 ≠ harmonicMult 6 1
    decide

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@harmonicMult_six) (Realization sig) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.SixDimensionalMultiplicity.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.SixDimensionalMultiplicity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ ℓ => harmonicMult 6 ℓ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
    definition := none, coordinates := #[]
    readouts := #[{
        path := #["body", "fn", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SixDimensionalMultiplicity

namespace MultiplicityBounds

abbrev sig := signature ℕ (fun _ => ℕ) (fun _ => ℕ)
abbrev arena : Arena where
  signature := sig
  Law r := ∀ D : ℕ, 4 ≤ D → ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ ℓ : ℕ, 1 ≤ ℓ →
    a * (ℓ : ℝ) ^ (D - 3) ≤ (r.readout () D ℓ : ℝ) ∧
      (harmonicMult D ℓ : ℝ) ≤ b * (ℓ : ℝ) ^ (D - 3)

private theorem rejected_law :
    ¬ arena.Law (realize sig (fun _ _ _ => 0) (fun e => nomatch e)) := by
  intro h
  obtain ⟨a, b, ha, _, hab⟩ := h 4 (by decide)
  have hlo := (hab 1 (by decide)).1
  norm_num [Realization.readout, realize] at hlo
  exact ha.not_ge hlo

def source_registration : Registration arena (type_of% @harmonicMult_bounds) where
  actual := realize sig (fun _ D ℓ => harmonicMult D ℓ) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@harmonicMult_bounds, _, rejected_law⟩
  sensitivity := sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨4, 0, 1, ?_⟩
    change harmonicMult 4 0 ≠ harmonicMult 4 1
    decide

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@harmonicMult_bounds) (Realization sig) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.MultiplicityBounds.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.MultiplicityBounds.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ D ℓ => harmonicMult D ℓ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
    definition := none, coordinates := #[0]
    readouts := #[{
        path := #["body", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "body", "fn", "arg", "arg", "arg"]
        stateBinder := 4, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MultiplicityBounds

namespace ModeSummability

abbrev sig := signature ℕ (fun _ => ℕ) (fun _ => ℝ)
abbrev arena : Arena where
  signature := sig
  Law r := ∀ D : ℕ, 4 ≤ D →
    ((Summable fun ℓ : ℕ => if ℓ = 0 then 0 else r.readout () D ℓ) ↔ D = 4 ∨ D = 5)

private theorem rejected_law :
    ¬ arena.Law (realize sig (fun _ _ _ => 0) (fun e => nomatch e)) := by
  intro h
  have hs : Summable (fun _ : ℕ => (0 : ℝ)) := summable_zero
  have hzero := (h 6 (by decide)).mp (by simpa [Realization.readout, realize] using hs)
  omega

def source_registration : Registration arena (type_of% @leadingModeWeight_summable_iff) where
  actual := realize sig (fun _ D ℓ => leadingModeWeight D ℓ) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@leadingModeWeight_summable_iff, _, rejected_law⟩
  sensitivity := sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨4, 1, 2, ?_⟩
    norm_num [Realization.readout, realize, leadingModeWeight, harmonicMult_four]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@leadingModeWeight_summable_iff) (Realization sig) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.ModeSummability.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.ModeSummability.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ D ℓ => leadingModeWeight D ℓ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
    definition := none, coordinates := #[0]
    readouts := #[{
        path := #["body", "body", "fn", "arg", "fn", "arg", "body", "arg"]
        stateBinder := 2, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ModeSummability

namespace LogarithmicCutoff

abbrev sig := signature Unit (fun _ => ℕ) (fun _ => ℝ)
abbrev arena : Arena where
  signature := sig
  Law r := ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ L : ℕ, 2 ≤ L →
    a * Real.log L ≤ ∑ n ∈ Finset.range L, r.readout () () (n + 1) ∧
    (∑ n ∈ Finset.range L, leadingModeWeight 6 (n + 1)) ≤ b * Real.log L

private theorem rejected_law :
    ¬ arena.Law (realize sig (fun _ _ _ => 0) (fun e => nomatch e)) := by
  rintro ⟨a, b, ha, _, hab⟩
  have hlo := (hab 2 (by decide)).1
  norm_num [Realization.readout, realize] at hlo
  exact (mul_pos ha (Real.log_pos (by norm_num : (1 : ℝ) < 2))).not_ge hlo

def source_registration : Registration arena (type_of% @leadingModeWeight_sum_six_bounds) where
  actual := realize sig (fun _ _ ℓ => leadingModeWeight 6 ℓ) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@leadingModeWeight_sum_six_bounds, _, rejected_law⟩
  sensitivity := sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨(), 1, 2, ?_⟩
    norm_num [Realization.readout, realize, leadingModeWeight, harmonicMult_six]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@leadingModeWeight_sum_six_bounds) (Realization sig) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.LogarithmicCutoff.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.LogarithmicCutoff.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ ℓ => leadingModeWeight 6 ℓ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
    definition := none, coordinates := #[]
    readouts := #[{
        path := #["arg", "body", "arg", "body", "arg", "arg", "body", "body", "fn", "arg", "arg", "arg", "body"]
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LogarithmicCutoff

namespace PowerCutoff

abbrev sig := signature ℕ (fun _ => ℕ) (fun _ => ℝ)
abbrev arena : Arena where
  signature := sig
  Law r := ∀ D : ℕ, 7 ≤ D → ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ L : ℕ, 1 ≤ L →
    a * (L : ℝ) ^ (D - 6) ≤ ∑ n ∈ Finset.range L, r.readout () D (n + 1) ∧
    (∑ n ∈ Finset.range L, leadingModeWeight D (n + 1)) ≤ b * (L : ℝ) ^ (D - 6)

private theorem rejected_law :
    ¬ arena.Law (realize sig (fun _ _ _ => 0) (fun e => nomatch e)) := by
  intro h
  obtain ⟨a, b, ha, _, hab⟩ := h 7 (by decide)
  have hlo := (hab 1 (by decide)).1
  norm_num [Realization.readout, realize] at hlo
  exact ha.not_ge hlo

def source_registration : Registration arena (type_of% @leadingModeWeight_sum_ge_seven_bounds) where
  actual := realize sig (fun _ D ℓ => leadingModeWeight D ℓ) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@leadingModeWeight_sum_ge_seven_bounds, _, rejected_law⟩
  sensitivity := sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨4, 1, 2, ?_⟩
    norm_num [Realization.readout, realize, leadingModeWeight, harmonicMult_four]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@leadingModeWeight_sum_ge_seven_bounds) (Realization sig) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.PowerCutoff.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.PowerCutoff.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ D ℓ => leadingModeWeight D ℓ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
    definition := none, coordinates := #[0]
    readouts := #[{
        path := #["body", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "body", "fn", "arg", "arg", "arg", "body"]
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PowerCutoff


end

end Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
