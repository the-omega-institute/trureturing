import D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source registrations for the shell, band weights and cofinal energy criteria. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy

open Finset MeasureTheory LeanInformationAudit
open _root_.D5.S3.Arith.MoebiusLogarithmic (reciprocalSum)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy
open scoped BigOperators

abbrev rationalSignature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℚ)

abbrev realSignature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℝ)

abbrev weightSignature := _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ)
  (fun _ => ℕ) (fun _ => ℕ)

def energyReadout : Realization rationalSignature :=
  realize rationalSignature (fun _ _ P => energy P) (fun e => nomatch e)

def realEnergyReadout : Realization realSignature :=
  realize realSignature (fun _ _ P => (energy P : ℝ)) (fun e => nomatch e)

def cellReadout : Realization realSignature :=
  realize realSignature (fun _ _ j => (d j : ℝ)) (fun e => nomatch e)

def massReadout : Realization realSignature :=
  realize realSignature (fun _ _ P =>
    ∫ u in (1 : ℝ)..(P : ℝ), |reciprocalSum u - reciprocalSum (u / 2)|)
    (fun e => nomatch e)

def weightReadout : Realization weightSignature :=
  realize weightSignature (fun _ p n => bandWeight p.1 p.2 n) (fun e => nomatch e)

private theorem one_cell : Ico (1 : ℕ) 2 = {1} := by decide

private theorem d_one : d 1 = 1 := by
  have h : Ioc (1 / 2 : ℕ) 1 = {1} := by decide
  simp [d, h, mobiusReciprocal]

private theorem energy_one : energy 1 = 0 := by simp [energy]

private theorem energy_two : energy 2 = 1 := by simp [energy, d_one]

private theorem mass_at_two :
    (∫ u in (1 : ℝ)..((2 : ℕ) : ℝ), |reciprocalSum u - reciprocalSum (u / 2)|) = 1 := by
  rw [shell_mass_eq_sum_abs (P := 2) (by decide)]
  norm_num [one_cell, d_one]

private theorem energy_dependence : ObservationalDependence rationalSignature energyReadout := by
  intro _
  exact ⟨(), 1, 2, by change energy 1 ≠ energy 2; rw [energy_one, energy_two]; decide⟩

private theorem real_energy_dependence :
    ObservationalDependence realSignature realEnergyReadout := by
  intro _
  refine ⟨(), 1, 2, ?_⟩
  change (energy 1 : ℝ) ≠ (energy 2 : ℝ)
  norm_num [energy_one, energy_two]

namespace BandedSum

abbrev arena : Arena where
  signature := rationalSignature
  Law R := ∀ P : ℕ, R.readout () () P =
    ∑ m ∈ Ico 1 P, ∑ n ∈ Ico 1 P,
      (bandWeight P m n : ℚ) * (mobiusReciprocal m * mobiusReciprocal n)

def rejected : Realization rationalSignature :=
  realize rationalSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₁ := h 1
  change (1 : ℚ) = ∑ m ∈ Ico 1 1, ∑ n ∈ Ico 1 1, _ at h₁
  simp at h₁

def family : Registration arena (type_of% @energy_eq_banded_sum) where
  actual := energyReadout
  bridge := Iff.rfl
  variation := ⟨@energy_eq_banded_sum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law energyReadout rejected rejected_law
  dependence := energy_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@energy_eq_banded_sum) (Realization rationalSignature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy.BandedSum.unit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy.BandedSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rationalSignature energyReadout.readout energyReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end BandedSum

namespace RationalCriterion

abbrev arena : Arena where
  signature := rationalSignature
  Law R := RiemannHypothesis ↔ ∀ k : ℕ, 0 < k → ∀ N : ℕ, ∃ P : ℕ,
    N ≤ P ∧ (R.readout () () P)^k ≤ (P : ℚ)

def rejected : Realization rationalSignature := by
  classical
  exact realize rationalSignature (fun _ _ P => if RiemannHypothesis then (P : ℚ) + 1 else 0)
    (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  change (RiemannHypothesis ↔ ∀ k : ℕ, 0 < k → ∀ N : ℕ, ∃ P : ℕ,
    N ≤ P ∧ (if RiemannHypothesis then (P : ℚ) + 1 else 0)^k ≤ (P : ℚ)) at h
  by_cases hRH : RiemannHypothesis
  · obtain ⟨P, _, hP⟩ := h.mp hRH 1 Nat.one_pos 1
    rw [ite_eq_left hRH, pow_one] at hP
    linarith
  · apply hRH
    apply h.mpr
    intro k hk N
    exact ⟨N, le_rfl, by rw [ite_eq_right hRH, zero_pow hk.ne']; positivity⟩

def family : Registration arena (type_of% @riemannHypothesis_iff_cofinal_energy_pow) where
  actual := energyReadout
  bridge := Iff.rfl
  variation := ⟨@riemannHypothesis_iff_cofinal_energy_pow, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law energyReadout rejected rejected_law
  dependence := energy_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@riemannHypothesis_iff_cofinal_energy_pow) (Realization rationalSignature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy.RationalCriterion.unit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy.RationalCriterion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rationalSignature energyReadout.readout energyReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RationalCriterion

namespace RealCriterion

abbrev arena : Arena where
  signature := realSignature
  Law R := RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ P : ℕ,
    N ≤ P ∧ R.readout () () P ≤ (P : ℝ)^ε

def rejected : Realization realSignature := by
  classical
  exact realize realSignature (fun _ _ P => if RiemannHypothesis then (P : ℝ) + 1 else 0)
    (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  change (RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ P : ℕ,
    N ≤ P ∧ (if RiemannHypothesis then (P : ℝ) + 1 else 0) ≤ (P : ℝ)^ε) at h
  by_cases hRH : RiemannHypothesis
  · obtain ⟨P, _, hP⟩ := h.mp hRH 1 zero_lt_one 1
    rw [ite_eq_left hRH, Real.rpow_one] at hP
    linarith
  · apply hRH
    apply h.mpr
    intro ε _ N
    exact ⟨N, le_rfl, by rw [ite_eq_right hRH]; positivity⟩

def family : Registration arena (type_of% @riemannHypothesis_iff_cofinal_energy) where
  actual := realEnergyReadout
  bridge := Iff.rfl
  variation := ⟨@riemannHypothesis_iff_cofinal_energy, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law realEnergyReadout rejected rejected_law
  dependence := real_energy_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@riemannHypothesis_iff_cofinal_energy) (Realization realSignature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy.RealCriterion.unit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy.RealCriterion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature realEnergyReadout.readout realEnergyReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RealCriterion

namespace CellShell

abbrev arena : Arena where
  signature := realSignature
  Law R := ∀ {j : ℕ} {u : ℝ}, u ∈ Set.Ico (j : ℝ) ((j : ℝ) + 1) →
    reciprocalSum u - reciprocalSum (u / 2) = R.readout () () j

def rejected : Realization realSignature :=
  realize realSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hu : (1 : ℝ) ∈ Set.Ico ((1 : ℕ) : ℝ) (((1 : ℕ) : ℝ) + 1) := by
    norm_num [Set.mem_Ico]
  have h₁ := h hu
  rw [shell_eq_d_on_cell hu] at h₁
  change (d 1 : ℝ) = 0 at h₁
  norm_num [d_one] at h₁

private theorem dependence : ObservationalDependence realSignature cellReadout := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change (d 0 : ℝ) ≠ (d 1 : ℝ)
  have h : d 0 = 0 := by simp [d]
  norm_num [h, d_one]

def family : Registration arena (type_of% @shell_eq_d_on_cell) where
  actual := cellReadout
  bridge := Iff.rfl
  variation := ⟨@shell_eq_d_on_cell, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law cellReadout rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@shell_eq_d_on_cell) (Realization realSignature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy.CellShell.unit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy.CellShell.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature cellReadout.readout cellReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CellShell

namespace ShellMass

abbrev arena : Arena where
  signature := realSignature
  Law R := ∀ {P : ℕ}, 1 ≤ P →
    R.readout () () P = ∑ j ∈ Ico 1 P, |(d j : ℝ)|

def rejected : Realization realSignature :=
  realize realSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₂ := h (P := 2) (by decide)
  change (0 : ℝ) = ∑ j ∈ Ico 1 2, |(d j : ℝ)| at h₂
  norm_num [one_cell, d_one] at h₂

private theorem dependence : ObservationalDependence realSignature massReadout := by
  intro _
  refine ⟨(), 1, 2, ?_⟩
  change (∫ u in (1 : ℝ)..((1 : ℕ) : ℝ), |reciprocalSum u - reciprocalSum (u / 2)|) ≠
    ∫ u in (1 : ℝ)..((2 : ℕ) : ℝ), |reciprocalSum u - reciprocalSum (u / 2)|
  rw [shell_mass_eq_sum_abs (P := 1) le_rfl, mass_at_two]
  simp

def family : Registration arena (type_of% @shell_mass_eq_sum_abs) where
  actual := massReadout
  bridge := Iff.rfl
  variation := ⟨@shell_mass_eq_sum_abs, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law massReadout rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@shell_mass_eq_sum_abs) (Realization realSignature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy.ShellMass.unit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy.ShellMass.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature massReadout.readout massReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ShellMass

namespace MassBound

abbrev arena : Arena where
  signature := realSignature
  Law R := ∀ {P : ℕ}, 1 ≤ P →
    (∫ u in (1 : ℝ)..(P : ℝ), |reciprocalSum u - reciprocalSum (u / 2)|) ^ 2 ≤
      ((P - 1 : ℕ) : ℝ) * R.readout () () P

def rejected : Realization realSignature :=
  realize realSignature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₂ := h (P := 2) (by decide)
  change (∫ u in (1 : ℝ)..((2 : ℕ) : ℝ), |reciprocalSum u - reciprocalSum (u / 2)|) ^ 2 ≤
    ((2 - 1 : ℕ) : ℝ) * (-1) at h₂
  have hnonneg := sq_nonneg
    (∫ u in (1 : ℝ)..((2 : ℕ) : ℝ), |reciprocalSum u - reciprocalSum (u / 2)|)
  norm_num at h₂
  linarith

def family : Registration arena (type_of% @shell_mass_sq_le) where
  actual := realEnergyReadout
  bridge := Iff.rfl
  variation := ⟨@shell_mass_sq_le, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law realEnergyReadout rejected rejected_law
  dependence := real_energy_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@shell_mass_sq_le) (Realization realSignature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy.MassBound.unit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy.MassBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature realEnergyReadout.readout realEnergyReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MassBound

namespace SeparatedPair

abbrev arena : Arena where
  signature := weightSignature
  Law R := ∀ {P m n : ℕ}, 2 * min m n ≤ max m n →
    R.readout () ⟨P, m⟩ n = 0

def rejected : Realization weightSignature :=
  realize weightSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₂ := h (P := 2) (m := 1) (n := 2) (by decide)
  exact Nat.one_ne_zero h₂

private theorem dependence : ObservationalDependence weightSignature weightReadout := by
  intro _
  refine ⟨⟨2, 1⟩, 1, 2, ?_⟩
  change bandWeight 2 1 1 ≠ bandWeight 2 1 2
  decide

def family : Registration arena (type_of% @bandWeight_eq_zero_of_separated) where
  actual := weightReadout
  bridge := Iff.rfl
  variation := ⟨@bandWeight_eq_zero_of_separated, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law weightReadout rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bandWeight_eq_zero_of_separated) (Realization weightSignature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy.SeparatedPair.unit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy.SeparatedPair.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature weightReadout.readout weightReadout.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SeparatedPair

end Reg.D5.S3.Weil.ZetaPntBounds.FiniteDyadicMobiusEnergy
