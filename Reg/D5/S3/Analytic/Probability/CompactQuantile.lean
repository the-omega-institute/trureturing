import Reg.D5.S3.Analytic.Probability.CompactStrassenAuditSupport

/-! Typed source-law reconstruction for compact martingale transport. -/
open MeasureTheory Set Econlib.Probability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.CompactStrassenAudit
noncomputable section
universe u_1 u_2
namespace Reg.D5.S3.Analytic.Probability.CompactQuantile

namespace set_nonempty
abbrev arena : Arena where
  signature := ToReal
  Law r := source_law% MeasureTheory.Measure.Quantile.set_nonempty replacing (ENNReal.toReal) with (r.readout () ())
theorem source_bridge : (type_of% @MeasureTheory.Measure.Quantile.set_nonempty) ↔ arena.Law toRealActual := Iff.rfl
theorem actual_law : arena.Law toRealActual := by
  apply source_bridge.mp
  exact @MeasureTheory.Measure.Quantile.set_nonempty

def rejected : Realization ToReal :=
  realize ToReal (fun _ _ _ => -1) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (μ := Measure.dirac (0 : ℝ)) (t := 0) (by norm_num)
  obtain ⟨x, hx⟩ := hh
  change (0 : ℝ) ≤ -1 at hx
  norm_num at hx

theorem dependence : ObservationalDependence ToReal toRealActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  simp [toRealActual, realize]

def source_registration : Registration arena
    (type_of% @MeasureTheory.Measure.Quantile.set_nonempty) where
  actual := toRealActual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@MeasureTheory.Measure.Quantile.set_nonempty) (Realization ToReal) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.CompactQuantile.set_nonempty.unit
  realizationName := `Reg.D5.S3.Analytic.Probability.CompactQuantile.set_nonempty.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ToReal (fun _ _ x => x.toReal) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end set_nonempty

namespace quantile_le_iff
abbrev arena : Arena where
  signature := Quantile
  Law r := source_law% MeasureTheory.Measure.quantile_le_iff replacing (@MeasureTheory.Measure.quantile) with (r.readout ())
theorem source_bridge : (type_of% @MeasureTheory.Measure.quantile_le_iff) ↔ arena.Law quantileActual := Iff.rfl
theorem actual_law : arena.Law quantileActual := by
  apply source_bridge.mp
  exact @MeasureTheory.Measure.quantile_le_iff
end quantile_le_iff

namespace monotoneOn_quantile
abbrev arena : Arena where
  signature := Quantile
  Law r := source_law% MeasureTheory.Measure.monotoneOn_quantile replacing (@MeasureTheory.Measure.quantile) with (r.readout ())
theorem source_bridge : (type_of% @MeasureTheory.Measure.monotoneOn_quantile) ↔ arena.Law quantileActual := Iff.rfl
theorem actual_law : arena.Law quantileActual := by
  apply source_bridge.mp
  exact @MeasureTheory.Measure.monotoneOn_quantile
end monotoneOn_quantile

namespace aemeasurable_quantile_restrict_Ioo
abbrev arena : Arena where
  signature := Quantile
  Law r := source_law% MeasureTheory.Measure.aemeasurable_quantile_restrict_Ioo replacing (@MeasureTheory.Measure.quantile) with (r.readout ())
theorem source_bridge : (type_of% @MeasureTheory.Measure.aemeasurable_quantile_restrict_Ioo) ↔ arena.Law quantileActual := Iff.rfl
theorem actual_law : arena.Law quantileActual := by
  apply source_bridge.mp
  exact @MeasureTheory.Measure.aemeasurable_quantile_restrict_Ioo
end aemeasurable_quantile_restrict_Ioo

namespace map_quantile_volume_Ioo
abbrev arena : Arena where
  signature := Quantile
  Law r := source_law% MeasureTheory.Measure.map_quantile_volume_Ioo replacing (@MeasureTheory.Measure.quantile) with (r.readout ())
theorem source_bridge : (type_of% @MeasureTheory.Measure.map_quantile_volume_Ioo) ↔ arena.Law quantileActual := Iff.rfl
theorem actual_law : arena.Law quantileActual := by
  apply source_bridge.mp
  exact @MeasureTheory.Measure.map_quantile_volume_Ioo
end map_quantile_volume_Ioo


namespace bins_pairwise_disjoint
abbrev arena : Arena where
  signature := Interval
  Law r := source_law% MeasureTheory.Measure.bins_pairwise_disjoint replacing (Set.Ico : ℝ → ℝ → Set ℝ) with (r.readout ())
theorem source_bridge : (type_of% @MeasureTheory.Measure.bins_pairwise_disjoint) ↔ arena.Law intervalActual := Iff.rfl
theorem actual_law : arena.Law intervalActual := by
  apply source_bridge.mp
  exact @MeasureTheory.Measure.bins_pairwise_disjoint
end bins_pairwise_disjoint

namespace iUnion_bins_eq_Ico
abbrev arena : Arena where
  signature := Interval
  Law r := source_law% MeasureTheory.Measure.iUnion_bins_eq_Ico replacing (Set.Ico : ℝ → ℝ → Set ℝ) with (r.readout ())
theorem source_bridge : (type_of% @MeasureTheory.Measure.iUnion_bins_eq_Ico) ↔ arena.Law intervalActual := Iff.rfl
theorem actual_law : arena.Law intervalActual := by
  apply source_bridge.mp
  exact @MeasureTheory.Measure.iUnion_bins_eq_Ico
end iUnion_bins_eq_Ico

namespace countable_not_continuousWithinAt_quantile
abbrev arena : Arena where
  signature := Quantile
  Law r := source_law% MeasureTheory.Measure.countable_not_continuousWithinAt_quantile replacing (@MeasureTheory.Measure.quantile) with (r.readout ())
theorem source_bridge : (type_of% @MeasureTheory.Measure.countable_not_continuousWithinAt_quantile) ↔ arena.Law quantileActual := Iff.rfl
theorem actual_law : arena.Law quantileActual := by
  apply source_bridge.mp
  exact @MeasureTheory.Measure.countable_not_continuousWithinAt_quantile
end countable_not_continuousWithinAt_quantile

namespace tendsto_integral_of_quantile_midpoint
abbrev arena : Arena where
  signature := Quantile
  Law r := source_law% MeasureTheory.Measure.tendsto_integral_of_quantile_midpoint replacing (@MeasureTheory.Measure.quantile) with (r.readout ())
theorem source_bridge : (type_of% @MeasureTheory.Measure.tendsto_integral_of_quantile_midpoint) ↔ arena.Law quantileActual := Iff.rfl
theorem actual_law : arena.Law quantileActual := by
  apply source_bridge.mp
  exact @MeasureTheory.Measure.tendsto_integral_of_quantile_midpoint
end tendsto_integral_of_quantile_midpoint

namespace stopLoss_nonneg
abbrev arena : Arena where
  signature := StopLoss
  Law r := source_law% MeasureTheory.Measure.stopLoss_nonneg replacing (@MeasureTheory.Measure.stopLoss) with (r.readout ())
theorem source_bridge : (type_of% @MeasureTheory.Measure.stopLoss_nonneg) ↔ arena.Law stopLossActual := Iff.rfl
theorem actual_law : arena.Law stopLossActual := by
  apply source_bridge.mp
  exact @MeasureTheory.Measure.stopLoss_nonneg
end stopLoss_nonneg

namespace stopLoss_integrable
abbrev arena : Arena where
  signature := Max
  Law r := source_law% MeasureTheory.Measure.stopLoss_integrable replacing (max : ℝ → ℝ → ℝ) with (r.readout ())
theorem source_bridge : (type_of% @MeasureTheory.Measure.stopLoss_integrable) ↔ arena.Law maxActual := Iff.rfl
theorem actual_law : arena.Law maxActual := by
  apply source_bridge.mp
  exact @MeasureTheory.Measure.stopLoss_integrable
end stopLoss_integrable
end Reg.D5.S3.Analytic.Probability.CompactQuantile
end
