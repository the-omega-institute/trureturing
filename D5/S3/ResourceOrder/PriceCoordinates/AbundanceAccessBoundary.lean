/- GID: D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary
   generality: G
   mirror-B: D5/B/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.AbundanceMakesWealthIrrelevant; result=D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.not_abundance_makes_wealth_irrelevant; claim=D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.AbundanceMakesWealthIrrelevant
   digest: Unlimited reproducible output permits paid access; free access ignores wealth. -/

import D5.S3.ResourceOrder.PriceCoordinates.ThresholdAccess
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/- Exact applications of ThresholdAccess. Energy balances are hypothetical
model inputs, not a construction of autonomous machinery or infinite energy.
Prices are independent of production cost. The finite slot witnesses refutation;
the two remaining results quantify arbitrary sets or arbitrary capacity bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ResourceOrder.PriceCoordinates.AbundanceAccessBoundary

open D5.S3.ResourceOrder.PriceCoordinates.ThresholdAccess

/-- A bundle specifies reproducible output and reservations of a rival resource. -/
abbrev Bundle := Prod Nat Nat

def singleSlot : Set Bundle := fun bundle => bundle.2 <= 1

def reservationCharge (bundle : Bundle) : Real := bundle.2

def energyRequired (output : Nat) : Nat := output

def energyHarvested (output : Nat) : Nat := output

/-- The universal inference challenged by the countermodel. Energy autonomy and
arbitrary first-good output place no premise on the separately supplied prices. -/
def AbundanceMakesWealthIrrelevant : Prop :=
  forall (feasible : Set Bundle) (charge : Bundle -> Real)
    (required harvested : Nat -> Nat),
    (forall output, required output <= harvested output) ->
    (forall output, feasible (output, 0)) ->
    forall wealth : Real, 0 <= wealth ->
      thresholdSet feasible charge wealth = thresholdSet feasible charge 0

/-- The same model has sufficient harvested energy at every output, arbitrarily
many reproducible goods, one scarce slot, and strictly wealth-dependent access. -/
theorem abundance_preserves_paid_access_difference :
    (forall output, energyRequired output <= energyHarvested output) /\
    (forall output, singleSlot (output, 0)) /\
    Not (singleSlot (0, 2)) /\
    thresholdSet singleSlot reservationCharge (0 : Real) <
      thresholdSet singleSlot reservationCharge (1 : Real) := by
  refine And.intro (fun _ => le_refl _) (And.intro ?_ (And.intro ?_ ?_))
  · intro output
    exact Nat.zero_le _
  · norm_num [singleSlot]
  · apply threshold_set_strict_of_witness singleSlot reservationCharge
      (item := (0, 1))
    all_goals norm_num [singleSlot, reservationCharge]

theorem not_abundance_makes_wealth_irrelevant :
    Not AbundanceMakesWealthIrrelevant := by
  intro implication
  have model := abundance_preserves_paid_access_difference
  have same := implication singleSlot reservationCharge energyRequired energyHarvested
    model.1 model.2.1 1 (by norm_num)
  exact (ne_of_lt model.2.2.2) same.symm

/-- If every admissible choice is actually free, every nonnegative budget gives
exactly those choices. Membership in feasible includes any nonmonetary gate. -/
theorem free_access_ignores_wealth {Choice : Type*}
    (feasible : Set Choice) (charge : Choice -> Real)
    (free : forall choice, feasible choice -> charge choice = 0)
    (wealth : Real) (nonnegative : 0 <= wealth) :
    thresholdSet feasible charge wealth = feasible := by
  have bounded : forall choice, feasible choice -> charge choice <= 0 := by
    intro choice allowed
    exact le_of_eq (free choice allowed)
  have constant := (threshold_sets_constant_iff feasible charge 0).mpr bounded
  have atZero : thresholdSet feasible charge 0 = feasible :=
    Set.sep_eq_self_iff_mem_true.mpr bounded
  exact (constant wealth nonnegative).trans atZero

/-- Removing payment does not remove a physical capacity bound. The capacity and
excess demand remain arbitrary, rather than one fixed positive finite instance. -/
theorem free_rationing_retains_capacity_bound (capacity demand : Nat)
    (excess : capacity < demand) (wealth : Real) (nonnegative : 0 <= wealth) :
    let feasible : Set Bundle := fun bundle => bundle.2 <= capacity
    thresholdSet feasible (fun _ => (0 : Real)) wealth = feasible /\
      Not (thresholdSet feasible (fun _ => (0 : Real)) wealth (0, demand)) := by
  dsimp only
  have freeSet := free_access_ignores_wealth
    (fun bundle : Bundle => bundle.2 <= capacity) (fun _ => (0 : Real))
    (fun _ _ => rfl) wealth nonnegative
  refine And.intro freeSet ?_
  intro admitted
  exact (Nat.not_le_of_gt excess) admitted.1

#print axioms abundance_preserves_paid_access_difference
#print axioms not_abundance_makes_wealth_irrelevant
#print axioms free_access_ignores_wealth
#print axioms free_rationing_retains_capacity_bound

end D5.S3.ResourceOrder.PriceCoordinates.AbundanceAccessBoundary
