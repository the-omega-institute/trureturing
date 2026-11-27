import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
import Reg.Support.NullDiamondDimensionThreshold.Modes

/-! Source-bound audits for angular integrability and the de Sitter conformal model. -/

namespace Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold

open _root_.NullConeGravity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout
open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AngularPower

abbrev sig := signature ℕ (fun _ => ℝ) (fun _ => ℝ)
abbrev arena : Arena where
  signature := sig
  Law r := ∀ D : ℕ, 5 ≤ D →
    (IntegrableOn (r.readout () D) (Set.Ioc 0 2) volume ↔ D = 5)

private theorem rejected_law :
    ¬ arena.Law (realize sig (fun _ _ _ => 0) (fun e => nomatch e)) := by
  intro h
  have hzero := (h 6 (by decide)).mp (integrable_zero _ _ _)
  omega

def source_registration : Registration arena (type_of% @angular_power_sq_integrable_iff) where
  actual := realize sig (fun _ D t => t ^ (((D : ℝ) - 4) / 2) * (t ^ (-(((D : ℝ) - 4) / 2))) ^ 2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@angular_power_sq_integrable_iff, _, rejected_law⟩
  sensitivity := sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨6, 1, 2, ?_⟩
    norm_num [Realization.readout, realize, Real.rpow_neg, Real.rpow_one]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@angular_power_sq_integrable_iff) (Realization sig) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.AngularPower.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.AngularPower.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ D t => t ^ (((D : ℝ) - 4) / 2) * (t ^ (-(((D : ℝ) - 4) / 2))) ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
    definition := none, coordinates := #[0]
    readouts := #[{
        path := #["body", "body", "fn", "arg", "fn", "fn", "arg", "body"]
        stateBinder := 2, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AngularPower

namespace AngularDensity

abbrev sig := signature ℕ (fun _ => ℝ) (fun _ => ℝ)
abbrev arena : Arena where
  signature := sig
  Law r := ∀ D : ℕ, 4 ≤ D →
    (IntegrableOn (r.readout () D) (Set.Ioc 0 2) volume ↔ D = 4 ∨ D = 5)

private theorem rejected_law :
    ¬ arena.Law (realize sig (fun _ _ _ => 0) (fun e => nomatch e)) := by
  intro h
  have hzero := (h 6 (by decide)).mp (integrable_zero _ _ _)
  omega

def source_registration : Registration arena (type_of% @angularSquaredDensity_integrable_iff) where
  actual := realize sig (fun _ D t => angularSquaredDensity D t) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@angularSquaredDensity_integrable_iff, _, rejected_law⟩
  sensitivity := sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨6, 1, 2, ?_⟩
    norm_num [Realization.readout, realize, angularSquaredDensity, Real.rpow_neg, Real.rpow_one]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@angularSquaredDensity_integrable_iff) (Realization sig) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.AngularDensity.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.AngularDensity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ D t => angularSquaredDensity D t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
    definition := none, coordinates := #[0]
    readouts := #[{
        path := #["body", "body", "fn", "arg", "fn", "fn", "arg"]
        stateBinder := 0, functionOperand := true, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AngularDensity

namespace ConformalSubtraction

abbrev sig := signature ℕ (fun _ => ℝ) (fun _ => ℝ)
abbrev arena : Arena where
  signature := sig
  Law r := ∀ (D : ℕ), 4 ≤ D → ∀ m ξ H : ℝ,
    m^2 + ξ * r.readout () D H -
      (((D : ℝ) - 2)/2) * ((((D : ℝ) - 2)/2) + 1) * H^2 =
    deSitterConformalMassSq D m ξ H

private theorem rejected_law :
    ¬ arena.Law (realize sig (fun _ _ _ => 0) (fun e => nomatch e)) := by
  intro h
  have hzero := h 4 (by decide) 0 1 1
  norm_num [Realization.readout, realize, deSitterConformalMassSq,
    deSitterConformalCoupling, deSitterRicciScalar] at hzero

def source_registration : Registration arena (type_of% @deSitterConformalMassSq_eq_sub) where
  actual := realize sig (fun _ D H => deSitterRicciScalar D H) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@deSitterConformalMassSq_eq_sub, _, rejected_law⟩
  sensitivity := sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨4, 0, 1, ?_⟩
    norm_num [Realization.readout, realize, deSitterRicciScalar]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@deSitterConformalMassSq_eq_sub) (Realization sig) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.ConformalSubtraction.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.ConformalSubtraction.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ D H => deSitterRicciScalar D H) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
    definition := none, coordinates := #[0]
    readouts := #[{
        path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 4, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ConformalSubtraction

namespace ConformalCancellation

abbrev sig := signature Unit (fun _ => ℕ) (fun _ => ℝ)
abbrev arena : Arena where
  signature := sig
  Law r := ∀ (D : ℕ) (H : ℝ), deSitterConformalMassSq D 0 (r.readout () () D) H = 0

private theorem rejected_law :
    ¬ arena.Law (realize sig (fun _ _ _ => 0) (fun e => nomatch e)) := by
  intro h
  exact (deSitterConformalMassSq_minimal_neg 4 (by decide) 1 (by norm_num)).ne
    (h 4 1)

def source_registration : Registration arena (type_of% @deSitterConformalMassSq_conformal) where
  actual := realize sig (fun _ _ D => deSitterConformalCoupling D) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@deSitterConformalMassSq_conformal, _, rejected_law⟩
  sensitivity := sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨(), 4, 5, ?_⟩
    norm_num [Realization.readout, realize, deSitterConformalCoupling]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@deSitterConformalMassSq_conformal) (Realization sig) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.ConformalCancellation.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.ConformalCancellation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ D => deSitterConformalCoupling D) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
    definition := none, coordinates := #[]
    readouts := #[{
        path := #["body", "body", "fn", "arg", "fn", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ConformalCancellation

namespace MinimalMass

abbrev sig := signature ℕ (fun _ => ℝ) (fun _ => ℝ)
abbrev arena : Arena where
  signature := sig
  Law r := ∀ D : ℕ, 4 ≤ D → ∀ H : ℝ, 0 < H → r.readout () D H < 0

private theorem rejected_law :
    ¬ arena.Law (realize sig (fun _ _ _ => 0) (fun e => nomatch e)) := by
  intro h
  exact lt_irrefl (0 : ℝ) (h 4 (by decide) 1 (by norm_num))

def source_registration : Registration arena (type_of% @deSitterConformalMassSq_minimal_neg) where
  actual := realize sig (fun _ D H => deSitterConformalMassSq D 0 0 H) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@deSitterConformalMassSq_minimal_neg, _, rejected_law⟩
  sensitivity := sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨4, 0, 1, ?_⟩
    norm_num [Realization.readout, realize, deSitterConformalMassSq,
      deSitterConformalCoupling, deSitterRicciScalar]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@deSitterConformalMassSq_minimal_neg) (Realization sig) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.MinimalMass.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.MinimalMass.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ D H => deSitterConformalMassSq D 0 0 H) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
    definition := none, coordinates := #[0]
    readouts := #[{
        path := #["body", "body", "body", "body", "fn", "arg"]
        stateBinder := 2, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MinimalMass

namespace DeSitterSummability

abbrev sig := signature ℕ (fun _ => ℕ) (fun _ => ℝ)
abbrev arena : Arena where
  signature := sig
  Law r := ∀ D : ℕ, 4 ≤ D → ∀ m ξ H : ℝ,
    ((Summable fun ℓ : ℕ => if ℓ = 0 then 0 else
      deSitterConformalMassSq D m ξ H ^ 2 * r.readout () D ℓ) ↔
    deSitterConformalMassSq D m ξ H = 0 ∨ D = 4 ∨ D = 5)

private theorem rejected_law :
    ¬ arena.Law (realize sig (fun _ _ _ => 0) (fun e => nomatch e)) := by
  intro h
  have hs : Summable (fun _ : ℕ => (0 : ℝ)) := summable_zero
  have hzero := (h 6 (by decide) 0 0 1).mp (by simpa [Realization.readout, realize] using hs)
  norm_num at hzero
  exact (deSitterConformalMassSq_minimal_neg 6 (by decide) 1 (by norm_num)).ne hzero

def source_registration : Registration arena (type_of% @deSitter_leadingModeWeight_summable_iff) where
  actual := realize sig (fun _ D ℓ => leadingModeWeight D ℓ) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@deSitter_leadingModeWeight_summable_iff, _, rejected_law⟩
  sensitivity := sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨4, 1, 2, ?_⟩
    norm_num [Realization.readout, realize, leadingModeWeight, harmonicMult_four]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@deSitter_leadingModeWeight_summable_iff) (Realization sig) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.DeSitterSummability.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold.DeSitterSummability.source_registration
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
        path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "arg", "arg"]
        stateBinder := 5, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeSitterSummability

end

end Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
