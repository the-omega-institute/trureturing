import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiActual

/-! The actual source is the complete original-host visibility predicate on
all finite labelled subsets, over every original graph parameter. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiActual

open _root_.D5.S3.Combinatorics.Graph.MutualVisibility
open _root_.D5.S3.Combinatorics.Graph.MutualVisibility.Andrasfai
open _root_.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiActual
open _root_.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open PowerSeries

noncomputable section

abbrev visibilitySignature : Signature where
  Params := ℕ
  State m := Finset (Vertex m)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization visibilitySignature :=
  realize visibilitySignature (fun _ m S => Visible (host m) S) (fun e => nomatch e)

def rejected : Realization visibilitySignature :=
  realize visibilitySignature (fun _ _ _ => False) (fun e => nomatch e)

theorem actual_dependence : ObservationalDependence visibilitySignature actual := by
  intro role
  cases role
  refine ⟨1, ∅, Finset.univ, ?_⟩
  change Visible (host 1) ∅ ≠ Visible (host 1) Finset.univ
  intro he
  have hv := he.mp (visible_empty (host 1))
  exact (visible_iff_no_obstruction 1 Finset.univ).mp hv
    ⟨0, 1, by omega, by omega, by simp, by simp, by simp⟩

abbrev countScope := type_of% (@count_eq_trace)

abbrev countArena : Arena where
  signature := visibilitySignature
  Law r := ∀ m : ℕ, 1 ≤ m →
    (Nat.card {S : Finset (Vertex m) // r.readout () m S} : ℚ) =
      Matrix.trace (transfer ^ (3 * m + 2))

theorem count_source_bridge : countScope ↔ countArena.Law actual := by
  dsimp only [countScope, countArena, actual, realize, count, Configuration]
  simp only [← Nat.card_eq_fintype_card]

theorem count_actual_positive : countArena.Law actual :=
  count_source_bridge.mp count_eq_trace

theorem count_rejected_law : ¬ countArena.Law rejected := by
  intro h
  have he := h 1 (by omega)
  change (Nat.card {S : Finset (Vertex 1) // False} : ℚ) = _ at he
  have ht : Matrix.trace (transfer ^ (3 * 1 + 2)) = (21 : ℚ) := by decide +kernel
  simp [ht] at he

def countFamily : Registration countArena countScope where
  actual := actual
  bridge := count_source_bridge
  variation := ⟨count_actual_positive, rejected, count_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, count_rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := actual_dependence

abbrev seriesArena (rhs : PowerSeries ℚ) : Arena where
  signature := visibilitySignature
  Law r := X * PowerSeries.mk (fun m =>
    (Nat.card {S : Finset (Vertex m) // r.readout () m S} : ℚ)) = rhs

abbrev correctionScope := type_of% (@generatingSeries_eq_corrected_trace)
abbrev resultScope := type_of% (@result)

abbrev rationalSeries : PowerSeries ℚ :=
  (X * (4 - 19 * X + 33 * X^2 - 40 * X^3 + 8 * X^4)) *
    (1 - 10 * X + 29 * X^2 - 32 * X^3 + 8 * X^4)⁻¹

theorem correction_source_bridge :
    correctionScope ↔ (seriesArena (traceSeries + X)).Law actual := by
  dsimp only [correctionScope, seriesArena, actual, realize, generatingSeries,
    count, Configuration]
  simp only [← Nat.card_eq_fintype_card]

theorem result_source_bridge : resultScope ↔ (seriesArena rationalSeries).Law actual := by
  dsimp only [resultScope, seriesArena, actual, realize, generatingSeries,
    count, Configuration, rationalSeries]
  simp only [← Nat.card_eq_fintype_card]

theorem correction_actual_positive : (seriesArena (traceSeries + X)).Law actual :=
  correction_source_bridge.mp generatingSeries_eq_corrected_trace

theorem result_actual_positive : (seriesArena rationalSeries).Law actual :=
  result_source_bridge.mp result

theorem series_rejected_law (rhs : PowerSeries ℚ) (hfirst : coeff 1 rhs = 4) :
    ¬ (seriesArena rhs).Law rejected := by
  intro h
  have he := congrArg (coeff 1) h
  change coeff 1 (X * PowerSeries.mk (fun m =>
    (Nat.card {S : Finset (Vertex m) // False} : ℚ))) = coeff 1 rhs at he
  simp [hfirst] at he

theorem correction_first : coeff 1 (traceSeries + X) = (4 : ℚ) := by
  have ht : Matrix.trace (transfer ^ 2) = (3 : ℚ) := by decide +kernel
  norm_num [traceSeries, ht, coeff_X]

theorem rational_first : coeff 1 rationalSeries = (4 : ℚ) := by
  change coeff 1 ((X * (4 - 19 * X + 33 * X^2 - 40 * X^3 + 8 * X^4)) *
    denominator⁻¹) = 4
  rw [← corrected_trace_series]
  exact correction_first

def correctionFamily : Registration (seriesArena (traceSeries + X)) correctionScope where
  actual := actual
  bridge := correction_source_bridge
  variation := ⟨correction_actual_positive, rejected,
    series_rejected_law _ correction_first⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, series_rejected_law _ correction_first⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := actual_dependence

def resultFamily : Registration (seriesArena rationalSeries) resultScope where
  actual := actual
  bridge := result_source_bridge
  variation := ⟨result_actual_positive, rejected, series_rejected_law _ rational_first⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, series_rejected_law _ rational_first⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := actual_dependence

def count_registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@count_eq_trace)
    (type_of% (realize visibilitySignature
      (fun _ m S => Visible (host m) S) (fun e => nomatch e))) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiActual.count_eq_trace
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiActual.countFamily
  realizationSource := none
  generated := false
  arena := .source ⟨countArena⟩
  objectArena := .source ⟨countArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena ⟨countFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize visibilitySignature
    (fun _ m S => Visible (host m) S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def correction_registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@generatingSeries_eq_corrected_trace)
    (type_of% (realize visibilitySignature
      (fun _ m S => Visible (host m) S) (fun e => nomatch e))) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiActual.generatingSeries_eq_corrected_trace
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiActual.correctionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨(seriesArena (traceSeries + X))⟩
  objectArena := .source ⟨(seriesArena (traceSeries + X))⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (seriesArena (traceSeries + X)) ⟨correctionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize visibilitySignature
    (fun _ m S => Visible (host m) S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def result_registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@result)
    (type_of% (realize visibilitySignature
      (fun _ m S => Visible (host m) S) (fun e => nomatch e))) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiActual.result
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiActual.resultFamily
  realizationSource := none
  generated := false
  arena := .source ⟨(seriesArena rationalSeries)⟩
  objectArena := .source ⟨(seriesArena rationalSeries)⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (seriesArena rationalSeries) ⟨resultFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize visibilitySignature
    (fun _ m S => Visible (host m) S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiActual
