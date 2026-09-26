import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicSeriesRegistration
import Reg.Support.MechanicalDyadicRegistration

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicSeriesRegistration.seriesArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries.geometric_readout_floor_series_and_mass,
      statementIdentity := "sha256:fd1a4e1caf3744647b114425eeaf3607fbbc885af074c2b36fda2f72411e9fd8",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicSeriesRegistration.seriesArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries.geometric_readout_floor_series_and_mass,
      statementIdentity := "sha256:fd1a4e1caf3744647b114425eeaf3607fbbc885af074c2b36fda2f72411e9fd8",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries }]
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries }

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries

open Set Finset
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S1.Words.Mechanical
open _root_.D5.S1.Words.Mechanical.MechanicalReadoutOrder
open _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicSeriesRegistration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

local instance : DecidableEq SeriesOutput := Classical.decEq _

def seriesClaim : Prop :=
  ∀ (r alpha x : ℝ), 0 ≤ r → r < 1 →
    alpha ∈ Icc (0 : ℝ) 1 → x ∈ Ico (0 : ℝ) 1 →
      geometricReadout r alpha x =
        ∑' j : ℕ, (1 - r) ^ 2 * r ^ j *
          (⌊x + ((j + 1 : ℕ) : ℝ) * alpha⌋ : ℝ) ∧
      (∑' j : ℕ, (1 - r) ^ 2 * r ^ j * ((j + 1 : ℕ) : ℝ)) = 1 ∧
      geometricReadout r alpha x =
        ∑' j : ℕ, (1 - r) ^ 2 * r ^ j *
          (∑ i ∈ range (j + 1),
            if (((i + 1 : ℕ) : ℝ) - x) / ((j + 1 : ℕ) : ℝ) ≤ alpha then
              (1 : ℝ) else 0)

theorem seriesBridge : LegacyPrimitiveRealization seriesArena.toPrimitiveLawArena
    seriesClaim seriesRealization := by
  constructor
  exact Iff.rfl

def seriesBad : PrimitiveRealization seriesArena.signature :=
  @mechanicalReadoutRealization SeriesOutput (Classical.decEq _)
    (fun _ : Unit =>
      (fun _ _ _ => (0 : ℝ), fun _ => (0 : ℝ), fun _ _ _ => (0 : ℝ)))

private theorem seriesBad_not_law : ¬ seriesArena.Law seriesBad := by
  intro h
  have hmass := (h 0 0 0 (by norm_num) (by norm_num)
    (by constructor <;> norm_num) (by constructor <;> norm_num)).2.1
  norm_num [seriesBad, mechanicalReadoutRealization] at hmass

theorem seriesVariation : seriesArena.Law seriesRealization ∧
    ¬ seriesArena.Law seriesBad := by
  exact ⟨seriesBridge.equivalence.mp
    (fun r alpha x hr0 hr1 ha hx =>
      geometric_readout_floor_series_and_mass r alpha x hr0 hr1 ha hx),
    seriesBad_not_law⟩

theorem seriesSensitivity : FiniteSlotSensitivity seriesArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    refine ⟨seriesRealization, seriesBad, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => seriesBad_not_law, fun _ => seriesVariation.1⟩
  · intro i
    exact Fin.elim0 i

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries.geometric_readout_floor_series_and_mass
  in seriesArena
  readout via (@mechanicalReadoutRealization SeriesOutput (Classical.decEq _)
    (fun _ : Unit => MechanicalReadoutSources.seriesReadout))
  primitives seriesRealization.toPrimitiveBundle
  realization seriesBridge
  variation seriesVariation sensitivity seriesSensitivity
  escape from (ℝ) escape continues (open)

open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries.geometric_readout_floor_series_and_mass
  unless row.any (fun record => match record.result with
      | .declaredValidated _ => true
      | _ => false) do
    throwError "atomic-series information registration is not declaredValidated"

end Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries
