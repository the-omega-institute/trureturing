import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiTransfer

/-! The complete series statement is reconstructed from actual matrix rows.
The raw definition-expansion/source-selection certificate remains unresolved. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiTransfer

open _root_.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open PowerSeries
open scoped Matrix

abbrev seriesScope := type_of% (@corrected_trace_series)

abbrev seriesSignature : Signature where
  Params := Unit
  State _ := Fin 4
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 4 → ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def seriesActual : Realization seriesSignature :=
  realize seriesSignature (fun _ _ i => transfer i) (fun e => nomatch e)

noncomputable abbrev seriesArena : Arena where
  signature := seriesSignature
  Law r :=
    let M : Matrix (Fin 4) (Fin 4) ℚ := r.readout () ()
    X * PowerSeries.mk (fun j => Matrix.trace (M^(3*j+2))) + X =
      (X*(4-19*X+33*X^2-40*X^3+8*X^4)) * denominator⁻¹

theorem series_source_bridge : seriesScope ↔ seriesArena.Law seriesActual := by
  unfold seriesScope seriesArena seriesActual realize traceSeries
  rfl

theorem series_actual_positive : seriesArena.Law seriesActual :=
  series_source_bridge.mp corrected_trace_series

/-- Matrix rows, the full rational series and their exact source bridge are preserved.
Variation, sensitivity, actual dependence and raw source reconstruction are not asserted. -/
def seriesCertificate : Option (Registration seriesArena seriesScope) := none

end Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiTransfer
