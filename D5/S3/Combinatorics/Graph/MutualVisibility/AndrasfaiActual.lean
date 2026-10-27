/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual
   mirror-E: none(waiver:no-computational-evidence)
   anchors: []
   utility: none
   digest: Actual labelled mutual-visibility counts satisfy Howroyd's full generating identity. -/

import D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiWords
import D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiEnumeration

/-! The original actual-subset series and its complete rational expression. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiActual

open Andrasfai AndrasfaiWords AndrasfaiLanguage AndrasfaiTransfer PowerSeries
open scoped Classical

/-- Restriction of the actual membership equivalence to visible configurations.
The labels and their origin are unchanged; no rotation quotient is taken. -/
def configurationEquivPeriodicWord (m : ℕ) (hm : 1 ≤ m) :
    Configuration (host m) ≃
      {labels : Fin (3 * m + 2) → Bool // PeriodicAvoidance (List.ofFn labels)} :=
  (subsetLabelsEquiv m).subtypeEquiv (fun X =>
    visible_iff_word_periodic_avoidance m hm X)

/-- Every original graph after the two-vertex graph is counted by its full
labelled transfer trace. -/
theorem count_eq_trace (m : ℕ) (hm : 1 ≤ m) :
    (count m : ℚ) = Matrix.trace (transfer ^ (3 * m + 2)) := by
  unfold count
  rw [Fintype.card_congr (configurationEquivPeriodicWord m hm)]
  exact AndrasfaiEnumeration.periodic_word_card_eq_trace (3 * m + 2)
    (by omega) (by omega)

/-- Coefficient n≥1 is the number of all actual labelled visible subsets of
Cay(Z/(3n−1), {1,4,...,3n−2}); there is no index-zero graph term. -/
noncomputable def generatingSeries : PowerSeries ℚ :=
  X * PowerSeries.mk (fun m => (count m : ℚ))

/-- The sole correction to the trace series is the original first coefficient. -/
theorem generatingSeries_eq_corrected_trace :
    generatingSeries = traceSeries + X := by
  ext n
  cases n with
  | zero => simp [generatingSeries, traceSeries]
  | succ m =>
    simp only [generatingSeries, traceSeries, map_add, coeff_succ_X_mul, coeff_mk]
    cases m with
    | zero =>
      have ht : Matrix.trace (transfer ^ 2) = (3 : ℚ) := by decide +kernel
      norm_num [count_zero, ht, coeff_X]
    | succ m =>
      rw [count_eq_trace (m + 1) (by omega)]
      simp [coeff_X]

/-- Howroyd's full original identity for all labelled original-host
existential shortest-path mutual-visibility subsets, including the empty set
and singletons, with every coefficient starting at original n=1. -/
theorem result :
    generatingSeries =
      (X * (4 - 19 * X + 33 * X^2 - 40 * X^3 + 8 * X^4)) *
        (1 - 10 * X + 29 * X^2 - 32 * X^3 + 8 * X^4)⁻¹ := by
  rw [generatingSeries_eq_corrected_trace]
  exact corrected_trace_series

end D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiActual
