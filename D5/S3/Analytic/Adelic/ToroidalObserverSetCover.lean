/- GID: D5/S3/Analytic/Adelic/ToroidalObserverSetCover
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/ToroidalObserverSetCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite toroidal observer design is a positive-cost weighted set cover. -/

import D5.S3.Analytic.Adelic.ToroidalCechCompletion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.EReal.Basic

/- Library-search audit trail (2026-09-01):
   * Exact D5 hit `nonvanishingDomain` is the canonical nonzero-twist region and
     is reused below. `finite_toroidal_frame_reconstruction` supplies finite
     subcovers under compactness, but it has no cost or optimization objective.
   * `minimum_complete_observer_is_set_cover` and
     `minimum_complete_budget_iff_minimum_cover` optimize covers of state-pair
     separation sets. They do not define a toroidal spectral-window cost or its
     infimum, so neither is an exact owner of the statement below.
   * Pinned Mathlib searches found no weighted-set-cover package. `EReal` supplies
     the complete linear order needed for an infimum that is top when no cover
     exists; `MeasureTheory.Measure.haar.index` uses the same finite-cover `sInf`
     pattern. Searches of the other pinned Lean packages found no exact hit.
   * Lean LSP was not exposed in this worker, so the searches used pinned source
     and declaration text directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Adelic.ToroidalObserverSetCover

open D5.S3.Analytic.Adelic.ToroidalCechCompletion
open scoped BigOperators

universe u

/-- An abstract family of completed quadratic twists with strictly positive
observer costs. The source does not define the L-functions, so `twist` is an
explicit parameter rather than a new analytic construction. -/
structure ToroidalObserverDesign (Index : Type u) where
  twist : Index -> ℂ -> ℂ
  cost : Index -> Real
  cost_pos : ∀ index, 0 < cost index

/-- A finite selection covers the spectral window when its canonical
nonvanishing domains cover every point of the window subtype. -/
def IsFiniteToroidalCover {Index : Type u} (design : ToroidalObserverDesign Index)
    (window : Set ℂ) (selected : Finset Index) : Prop :=
  (Set.univ : Set window) ⊆
    ⋃ index : {candidate // candidate ∈ selected},
      nonvanishingDomain window design.twist index.1

/-- The subtype cover is exactly the source condition that the ambient window
is contained in the union of the selected nonvanishing regions. -/
theorem finite_toroidal_cover_iff_window_subset_iUnion
    {Index : Type u} (design : ToroidalObserverDesign Index)
    (window : Set ℂ) (selected : Finset Index) :
    IsFiniteToroidalCover design window selected ↔
      window ⊆
        ⋃ index : {candidate // candidate ∈ selected},
          {point : ℂ | design.twist index.1 point ≠ 0} := by
  constructor
  · intro covers point pointInWindow
    let windowPoint : window := ⟨point, pointInWindow⟩
    have covered :
        windowPoint ∈
          ⋃ index : {candidate // candidate ∈ selected},
            nonvanishingDomain window design.twist index.1 :=
      covers (Set.mem_univ windowPoint)
    obtain ⟨index, nonzero⟩ := Set.mem_iUnion.mp covered
    exact Set.mem_iUnion.mpr ⟨index, nonzero⟩
  · intro covers point _
    have covered := covers point.2
    obtain ⟨index, nonzero⟩ := Set.mem_iUnion.mp covered
    exact Set.mem_iUnion.mpr ⟨index, nonzero⟩

/-- The total cost of one selected finite toroidal family. -/
def selectedToroidalCost {Index : Type u} (design : ToroidalObserverDesign Index)
    (selected : Finset Index) : Real :=
  ∑ index ∈ selected, design.cost index

/-- The optimal finite toroidal observer cost. `EReal` records an unavailable
finite cover as `⊤`, rather than assigning the misleading real infimum zero. -/
noncomputable def toroidalObserverCost {Index : Type u}
    (design : ToroidalObserverDesign Index) (window : Set ℂ) : EReal :=
  sInf {value : EReal | ∃ selected : Finset Index,
    IsFiniteToroidalCover design window selected ∧
      value = (selectedToroidalCost design selected : EReal)}

/-- The toroidal observer objective is definitionally the weighted set-cover
infimum over finite selections satisfying `K ⊆ ⋃ D, U_D`. -/
theorem toroidal_observer_design_is_weighted_set_cover
    {Index : Type u} (design : ToroidalObserverDesign Index) (window : Set ℂ) :
    toroidalObserverCost design window =
      sInf {value : EReal | ∃ selected : Finset Index,
        (window ⊆
            ⋃ index : {candidate // candidate ∈ selected},
              {point : ℂ | design.twist index.1 point ≠ 0}) ∧
          value = ((∑ index ∈ selected, design.cost index : Real) : EReal)} := by
  unfold toroidalObserverCost
  apply congrArg sInf
  ext value
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨selected, covers, valueEq⟩
    refine ⟨selected,
      (finite_toroidal_cover_iff_window_subset_iUnion design window selected).mp covers, ?_⟩
    simpa [selectedToroidalCost] using valueEq
  · rintro ⟨selected, covers, valueEq⟩
    refine ⟨selected,
      (finite_toroidal_cover_iff_window_subset_iUnion design window selected).mpr covers, ?_⟩
    simpa [selectedToroidalCost] using valueEq

/-- The definition is realizable: one constant nonzero twist of cost one covers
the whole complex plane, and its singleton selection has total cost one. -/
theorem exists_positive_finite_toroidal_cover :
    ∃ (design : ToroidalObserverDesign Unit) (selected : Finset Unit),
      IsFiniteToroidalCover design (Set.univ : Set ℂ) selected ∧
        selectedToroidalCost design selected = 1 := by
  classical
  let design : ToroidalObserverDesign Unit :=
    { twist := fun _ _ => 1
      cost := fun _ => 1
      cost_pos := fun _ => zero_lt_one }
  refine ⟨design, {()}, ?_, ?_⟩
  · intro point _
    apply Set.mem_iUnion.mpr
    refine ⟨⟨(), Finset.mem_singleton_self ()⟩, ?_⟩
    change (1 : ℂ) ≠ 0
    exact one_ne_zero
  · simp [selectedToroidalCost, design]

#print axioms ToroidalObserverDesign
#print axioms IsFiniteToroidalCover
#print axioms finite_toroidal_cover_iff_window_subset_iUnion
#print axioms selectedToroidalCost
#print axioms toroidalObserverCost
#print axioms toroidal_observer_design_is_weighted_set_cover
#print axioms exists_positive_finite_toroidal_cover

end D5.S3.Analytic.Adelic.ToroidalObserverSetCover
