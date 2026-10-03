import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicSeriesRegistration
import Reg.Support.MechanicalDyadicRegistration



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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries.geometric_readout_floor_series_and_mass) (type_of% (seriesArena)) (type_of% (seriesArena)) (type_of% (@mechanicalReadoutRealization SeriesOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.seriesReadout))) (type_of% (seriesVariation)) (type_of% (seriesSensitivity)) (type_of% (ℝ)) (Unit) (Unit) := {
  unitName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries.geometric_readout_floor_series_and_mass.__information_unit,
  realizationName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries.seriesBridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(seriesArena)⟩,
  objectArena := ⟨(seriesArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.toPrimitiveLawArena.{0, 0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicSeriesRegistration.seriesArena) (D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicSeriesRegistration.seriesRealization) (seriesRealization.toPrimitiveBundle) ⟨(seriesBridge)⟩,
  readout := some (@mechanicalReadoutRealization SeriesOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.seriesReadout)),
  variation := some ⟨(seriesVariation)⟩,
  sensitivity := some ⟨(seriesSensitivity)⟩,
  escapeFrom := some (ℝ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries
