/- GID: D5/S3/ResourceOrder/PriceCoordinates/ThresholdAccess
   generality: G
   mirror-B: D5/B/S3/ResourceOrder/PriceCoordinates/ThresholdAccess
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Threshold constancy is equivalent to every admissible charge lying below the floor. -/

import Mathlib.Data.Set.Basic
import Mathlib.Order.Lattice

/- Search: the adjacent BudgetSetScaleInvariance concerns simultaneous scaling,
not constancy in wealth. Mathlib supplies sep_ext_iff and standard order laws;
LeanSearch returned convex-sublevel and matroid results, none with this boundary.
The mathematical subject is restricted sublevel sets, with no economic axiom. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ResourceOrder.PriceCoordinates.ThresholdAccess

/-- Nonmonetary admissibility and a payment or resource threshold are separate. -/
def thresholdSet {Item Level : Type*} [LE Level]
    (feasible : Set Item) (charge : Item -> Level) (budget : Level) : Set Item :=
  {item | feasible item /\ charge item <= budget}

/-- Constancy over every higher threshold forces every feasible item to be
admitted already at the floor. The max probe also covers empty feasible sets. -/
theorem threshold_sets_constant_iff {Item Level : Type*} [LinearOrder Level]
    (feasible : Set Item) (charge : Item -> Level) (floor : Level) :
    Iff
      (forall budget, floor <= budget ->
        thresholdSet feasible charge budget = thresholdSet feasible charge floor)
      (forall item, feasible item -> charge item <= floor) := by
  constructor
  · intro constant item feasibleItem
    have admitted : thresholdSet feasible charge (max floor (charge item)) item :=
      And.intro feasibleItem (le_max_right _ _)
    rw [constant _ (le_max_left _ _)] at admitted
    exact admitted.2
  · intro bounded budget floorBudget
    apply Set.sep_ext_iff.mpr
    intro item feasibleItem
    exact Iff.intro (fun _ => bounded item feasibleItem)
      (fun _ => le_trans (bounded item feasibleItem) floorBudget)

/-- An admissible item strictly between two thresholds witnesses genuine growth
of the whole access set, independently of the other items' charges. -/
theorem threshold_set_strict_of_witness {Item Level : Type*} [LinearOrder Level]
    (feasible : Set Item) (charge : Item -> Level)
    {lower upper : Level} {item : Item}
    (feasibleItem : feasible item) (above : lower < charge item)
    (within : charge item <= upper) :
    thresholdSet feasible charge lower < thresholdSet feasible charge upper := by
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · intro other admitted
    exact And.intro admitted.1
      (le_trans admitted.2 (le_trans (le_of_lt above) within))
  · intro same
    have admitted : thresholdSet feasible charge upper item :=
      And.intro feasibleItem within
    rw [<- same] at admitted
    exact (not_le_of_gt above) admitted.2

/-- A second interpretation: extending deadlines changes no eligible jobs
exactly when every eligible job already finishes by the original deadline. -/
example (jobs : Set Nat) (duration : Nat -> Nat) (deadline : Nat) :
    Iff
      (forall later, deadline <= later ->
        thresholdSet jobs duration later = thresholdSet jobs duration deadline)
      (forall job, jobs job -> duration job <= deadline) :=
  threshold_sets_constant_iff jobs duration deadline

#print axioms threshold_sets_constant_iff
#print axioms threshold_set_strict_of_witness

end D5.S3.ResourceOrder.PriceCoordinates.ThresholdAccess
