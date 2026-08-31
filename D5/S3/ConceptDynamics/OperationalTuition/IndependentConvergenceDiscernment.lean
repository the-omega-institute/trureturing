/- GID: D5/S3/ConceptDynamics/OperationalTuition/IndependentConvergenceDiscernment
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/OperationalTuition/IndependentConvergenceDiscernment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite independent views have monotone discernment; same-family same-input is zero. -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card

/- Library-search audit trail (2026-08-31):
   * Repository and Mathlib searches for finite-view discernment, independent
     model-family convergence, and the same-family degeneration found no
     covering declaration; the finite Bayesian toy is therefore self-contained.
   * Clause echo: visible-input disjointness and distinct families are
     `Independent`; refinement is the explicit monotonicity order; the
     disagreement-cardinality is the finite evidence value; equal family and
     equal visible inputs select the zero branch.
   * No T1-T5 law is an axiom: this module uses only data structures and
   propositions whose proofs are supplied at each theorem call.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.OperationalTuition.IndependentConvergenceDiscernment

/-- A finite view carries the inputs it can inspect, its model family, and a
Boolean readout on the finite input carrier. -/
structure FiniteView (Input Family : Type*) where
  visibleInput : Finset Input
  family : Family
  readout : Input → Bool

/-- Two views are independent exactly when their visible inputs are disjoint and
their model families differ. -/
def Independent {Input Family : Type*} [DecidableEq Input] [DecidableEq Family]
    (left right : FiniteView Input Family) : Prop :=
  left.visibleInput ∩ right.visibleInput = ∅ ∧ left.family ≠ right.family

instance independentDecidable {Input Family : Type*} [DecidableEq Input]
    [DecidableEq Family] (left right : FiniteView Input Family) :
    Decidable (Independent left right) := by
  unfold Independent
  infer_instance

/-- Inputs on which the two finite readouts give different evidence. -/
def disagreementSet {Input Family : Type*} [DecidableEq Input]
    (left right : FiniteView Input Family) : Finset Input :=
  (left.visibleInput ∪ right.visibleInput).filter
    (fun input => left.readout input ≠ right.readout input)

/-- The toy Bayesian evidence value counts observable input disagreements only
for an independent pair of views. -/
def discernmentPower {Input Family : Type*} [DecidableEq Input] [DecidableEq Family]
    (left right : FiniteView Input Family) : Nat :=
  if Independent left right then (disagreementSet left right).card else 0

/-- A view refinement preserves its model family, adds visible inputs, and keeps
the old readout on every input. -/
def ViewRefinement {Input Family : Type*} [DecidableEq Input]
    (coarse fine : FiniteView Input Family) : Prop :=
  coarse.family = fine.family ∧
    coarse.visibleInput ⊆ fine.visibleInput ∧
      ∀ input, coarse.readout input = fine.readout input

/-- The degeneration hypothesis used by the toy model: both the model family
and the visible input set agree. -/
def SameFamilySameInput {Input Family : Type*} [DecidableEq Input]
    (left right : FiniteView Input Family) : Prop :=
  left.family = right.family ∧ left.visibleInput = right.visibleInput

private theorem disagreementSet_mono
    {Input Family : Type*} [DecidableEq Input]
    {coarse fine right : FiniteView Input Family}
    (visible : coarse.visibleInput ⊆ fine.visibleInput)
    (readout : ∀ input, coarse.readout input = fine.readout input) :
    disagreementSet coarse right ⊆ disagreementSet fine right := by
  intro input inputMem
  simp only [disagreementSet, Finset.mem_filter] at inputMem ⊢
  refine ⟨?_, ?_⟩
  · rcases Finset.mem_union.mp inputMem.1 with h | h
    · exact Finset.mem_union.mpr (Or.inl (visible h))
    · exact Finset.mem_union.mpr (Or.inr h)
  · rw [← readout input]
    exact inputMem.2

/-- T-G: on finite view models, enlarging one view while retaining its readout
and preserving independence can only increase the independent convergence
discernment value. -/
theorem independent_discernment_mono
    {Input Family : Type*} [DecidableEq Input] [DecidableEq Family]
    (coarse fine right : FiniteView Input Family)
    (refinement : ViewRefinement coarse fine)
    (coarseIndependent : Independent coarse right)
    (fineIndependent : Independent fine right) :
    discernmentPower coarse right ≤ discernmentPower fine right := by
  have evidenceSubset : disagreementSet coarse right ⊆ disagreementSet fine right :=
    disagreementSet_mono refinement.2.1 refinement.2.2
  simp only [discernmentPower, if_pos coarseIndependent, if_pos fineIndependent]
  exact Finset.card_le_card evidenceSubset

/-- Same-family, same-visible-input views cannot be an independent pair, so the
toy convergence discernment value is exactly zero. -/
theorem same_family_same_input_discernment_zero
    {Input Family : Type*} [DecidableEq Input] [DecidableEq Family]
    (left right : FiniteView Input Family)
    (same : SameFamilySameInput left right) :
    discernmentPower left right = 0 := by
  have hIndependentFalse : ¬ Independent left right := by
    intro independent
    exact independent.2 same.1
  unfold discernmentPower
  rw [if_neg hIndependentFalse]

#print axioms independent_discernment_mono
#print axioms same_family_same_input_discernment_zero

-- The finite carrier and both branches of the definition are inhabited by a
-- concrete three-input, two-family toy model.
private inductive SampleInput where
  | first
  | second
  | third
deriving DecidableEq

private inductive SampleFamily where
  | structural
  | empirical
deriving DecidableEq

private def coarseView : FiniteView SampleInput SampleFamily where
  visibleInput := {.first}
  family := .structural
  readout := fun input => match input with
    | .first => true
    | .second => false
    | .third => false

private def fineView : FiniteView SampleInput SampleFamily where
  visibleInput := {.first, .second}
  family := .structural
  readout := fun input => match input with
    | .first => true
    | .second => false
    | .third => false

private def otherView : FiniteView SampleInput SampleFamily where
  visibleInput := {.third}
  family := .empirical
  readout := fun input => match input with
    | .first => false
    | .second => true
    | .third => true

example : ViewRefinement coarseView fineView := by
  refine ⟨rfl, ?_, ?_⟩
  · intro input inputMem
    simp only [coarseView, fineView, Finset.mem_singleton, Finset.mem_insert,
      Finset.mem_singleton] at inputMem ⊢
    exact Or.inl inputMem
  · intro input
    rfl

example : Independent coarseView otherView ∧ Independent fineView otherView := by
  constructor <;> simp [Independent, coarseView, fineView, otherView]

example :
    discernmentPower coarseView otherView = 2 ∧
      discernmentPower fineView otherView = 3 := by
  decide

end D5.S3.ConceptDynamics.OperationalTuition.IndependentConvergenceDiscernment
