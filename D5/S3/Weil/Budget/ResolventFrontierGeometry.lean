/- GID: D5/S3/Weil/Budget/ResolventFrontierGeometry
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/ResolventFrontierGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Convex positive completions give the budget frontier and minimal-cost geometry. -/

import D5.S3.Weil.ZetaAnalytic.FiniteWindowGlobalBoundary
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/- Library-search audit trail (2026-08-29):
   * D5 searches for resolvent frontiers, minimal completion costs, and
     measure-valued convex mixing found no exact theorem or canonical object.
   * `BudgetedEscapeRateAntitone` and `BudgetEnvelopeCompletion` contain only
     adjacent one-sided infimum monotonicity on different carriers.
   * Pinned Mathlib supplies `ConcaveOn`, `ConvexOn`, `convex_iff_add_mem`,
     `concaveOn_iff_forall_pos`, and conditional `sSup`/`sInf` bounds, but no
     theorem lifting a convex completion relation to both extremal functions.
   * Body-shape searches for the two measure-indexed extremal sets missed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Budget.ResolventFrontierGeometry

open MeasureTheory Set

/-- The white-floor frontier and its minimal resolvent cost inherit all order
and convexity laws from positive-measure mixing and nested local readings. -/
theorem resolvent_frontier_basic_properties
    (a : Real) (aPositive : 0 < a)
    (localMatches : Real -> Measure Real -> Prop)
    (resolventBudget whiteFloor : Measure Real -> Real)
    (fullFloor : Real -> Real)
    (mix : Real -> Real -> Measure Real -> Measure Real -> Measure Real)
    (budgetNonnegative : forall nu, 0 <= resolventBudget nu)
    (floorNonnegative : forall nu, 0 <= whiteFloor nu)
    (floorAtMostFull : forall L nu, localMatches L nu ->
      whiteFloor nu <= fullFloor L)
    (whiteBudgetCost : forall nu,
      whiteFloor nu / (2 * a) <= resolventBudget nu)
    (matchingNested : forall {L1 L2 : Real}, L1 <= L2 -> forall nu,
      localMatches L2 nu -> localMatches L1 nu)
    (mixMatches : forall p q : Real, 0 <= p -> 0 <= q -> p + q = 1 ->
      forall L nu1 nu2, localMatches L nu1 -> localMatches L nu2 ->
        localMatches L (mix p q nu1 nu2))
    (mixBudget : forall p q nu1 nu2,
      resolventBudget (mix p q nu1 nu2) =
        p * resolventBudget nu1 + q * resolventBudget nu2)
    (mixFloor : forall p q : Real, 0 <= p -> 0 <= q -> p + q = 1 ->
      forall nu1 nu2,
        p * whiteFloor nu1 + q * whiteFloor nu2 <=
          whiteFloor (mix p q nu1 nu2)) :
    let frontierValues := fun L C : Real =>
      {r : Real | exists nu : Measure Real,
        localMatches L nu /\ resolventBudget nu <= C /\ r = whiteFloor nu}
    let costValues := fun L lambda : Real =>
      {c : Real | exists nu : Measure Real,
        localMatches L nu /\ lambda <= whiteFloor nu /\ c = resolventBudget nu}
    let feasibleBudgets := fun L : Real =>
      {C : Real | (frontierValues L C).Nonempty}
    let feasibleFloors := fun L : Real =>
      {lambda : Real | (costValues L lambda).Nonempty}
    let frontier := fun L C : Real => sSup (frontierValues L C)
    let minimalCost := fun L lambda : Real => sInf (costValues L lambda)
    (forall L C, C ∈ feasibleBudgets L ->
      0 <= frontier L C /\
        frontier L C <= min (fullFloor L) (2 * a * C)) /\
    (forall L, MonotoneOn (frontier L) (feasibleBudgets L)) /\
    (forall L, ConcaveOn Real (feasibleBudgets L) (frontier L)) /\
    (forall C, AntitoneOn (fun L => frontier L C)
      {L : Real | (frontierValues L C).Nonempty}) /\
    (forall L, MonotoneOn (minimalCost L) (feasibleFloors L)) /\
    (forall L, ConvexOn Real (feasibleFloors L) (minimalCost L)) := by
  let frontierValues := fun L C : Real =>
    {r : Real | exists nu : Measure Real,
      localMatches L nu /\ resolventBudget nu <= C /\ r = whiteFloor nu}
  let costValues := fun L lambda : Real =>
    {c : Real | exists nu : Measure Real,
      localMatches L nu /\ lambda <= whiteFloor nu /\ c = resolventBudget nu}
  let feasibleBudgets := fun L : Real =>
    {C : Real | (frontierValues L C).Nonempty}
  let feasibleFloors := fun L : Real =>
    {lambda : Real | (costValues L lambda).Nonempty}
  let frontier := fun L C : Real => sSup (frontierValues L C)
  let minimalCost := fun L lambda : Real => sInf (costValues L lambda)
  have frontierBounded (L C : Real) : BddAbove (frontierValues L C) := by
    refine ⟨fullFloor L, ?_⟩
    rintro r ⟨nu, hMatch, _, rfl⟩
    exact floorAtMostFull L nu hMatch
  have costBounded (L lambda : Real) : BddBelow (costValues L lambda) := by
    refine ⟨0, ?_⟩
    rintro c ⟨nu, _, _, rfl⟩
    exact budgetNonnegative nu
  have budgetCombo
      {C1 C2 p q : Real} (hp : 0 <= p) (hq : 0 <= q)
      {nu1 nu2 : Measure Real}
      (h1 : resolventBudget nu1 <= C1)
      (h2 : resolventBudget nu2 <= C2) :
      resolventBudget (mix p q nu1 nu2) <= p * C1 + q * C2 := by
    rw [mixBudget]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hp)
      (mul_le_mul_of_nonneg_left h2 hq)
  have feasibleBudgetConvex (L : Real) : Convex Real (feasibleBudgets L) := by
    rw [convex_iff_add_mem]
    rintro C1 ⟨r1, nu1, hMatch1, hBudget1, rfl⟩
      C2 ⟨r2, nu2, hMatch2, hBudget2, rfl⟩ p q hp hq hpq
    let nu := mix p q nu1 nu2
    refine ⟨whiteFloor nu, nu, ?_, ?_, rfl⟩
    · exact mixMatches p q hp hq hpq L nu1 nu2 hMatch1 hMatch2
    · exact budgetCombo hp hq hBudget1 hBudget2
  have feasibleFloorConvex (L : Real) : Convex Real (feasibleFloors L) := by
    rw [convex_iff_add_mem]
    rintro lambda1 ⟨c1, nu1, hMatch1, hFloor1, rfl⟩
      lambda2 ⟨c2, nu2, hMatch2, hFloor2, rfl⟩ p q hp hq hpq
    let nu := mix p q nu1 nu2
    refine ⟨resolventBudget nu, nu, ?_, ?_, rfl⟩
    · exact mixMatches p q hp hq hpq L nu1 nu2 hMatch1 hMatch2
    · exact (add_le_add (mul_le_mul_of_nonneg_left hFloor1 hp)
        (mul_le_mul_of_nonneg_left hFloor2 hq)).trans
          (mixFloor p q hp hq hpq nu1 nu2)
  have frontierBounds : forall L C, C ∈ feasibleBudgets L ->
      0 <= frontier L C /\
        frontier L C <= min (fullFloor L) (2 * a * C) := by
    intro L C hFeasible
    constructor
    · rcases hFeasible with ⟨r, hr⟩
      rcases hr with ⟨nu, _, _, rfl⟩
      exact (floorNonnegative nu).trans
        (le_csSup (frontierBounded L C) ⟨nu, ‹_›, ‹_›, rfl⟩)
    · apply csSup_le hFeasible
      rintro r ⟨nu, hMatch, hBudget, rfl⟩
      apply le_min (floorAtMostFull L nu hMatch)
      have denominatorPositive : 0 < 2 * a := mul_pos (by norm_num) aPositive
      have floorLeBudget :
          whiteFloor nu <= (2 * a) * resolventBudget nu :=
        by
          simpa only [mul_comm] using
            (div_le_iff₀ denominatorPositive).mp (whiteBudgetCost nu)
      exact floorLeBudget.trans
        (mul_le_mul_of_nonneg_left hBudget denominatorPositive.le)
  have frontierMonotone (L : Real) :
      MonotoneOn (frontier L) (feasibleBudgets L) := by
    intro C1 hC1 C2 _ hOrder
    apply csSup_le hC1
    intro r hr
    apply le_csSup (frontierBounded L C2)
    rcases hr with ⟨nu, hMatch, hBudget, rfl⟩
    exact ⟨nu, hMatch, hBudget.trans hOrder, rfl⟩
  have frontierAntitone (C : Real) :
      AntitoneOn (fun L => frontier L C)
        {L : Real | (frontierValues L C).Nonempty} := by
    intro L1 _ L2 hL2 hOrder
    apply csSup_le hL2
    intro r hr
    apply le_csSup (frontierBounded L1 C)
    rcases hr with ⟨nu, hMatch, hBudget, rfl⟩
    exact ⟨nu, matchingNested hOrder nu hMatch, hBudget, rfl⟩
  have frontierConcave (L : Real) :
      ConcaveOn Real (feasibleBudgets L) (frontier L) := by
    rw [concaveOn_iff_forall_pos]
    refine ⟨feasibleBudgetConvex L, ?_⟩
    intro C1 hC1 C2 hC2 p q hp hq hpq
    have pairBound : forall r1, r1 ∈ frontierValues L C1 ->
        forall r2, r2 ∈ frontierValues L C2 ->
          p * r1 + q * r2 <= frontier L (p * C1 + q * C2) := by
      rintro r1 ⟨nu1, hMatch1, hBudget1, rfl⟩
        r2 ⟨nu2, hMatch2, hBudget2, rfl⟩
      let nu := mix p q nu1 nu2
      have valueMem : whiteFloor nu ∈
          frontierValues L (p * C1 + q * C2) :=
        ⟨nu, mixMatches p q hp.le hq.le hpq L nu1 nu2 hMatch1 hMatch2,
          budgetCombo hp.le hq.le hBudget1 hBudget2, rfl⟩
      exact (mixFloor p q hp.le hq.le hpq nu1 nu2).trans
        (le_csSup (frontierBounded L (p * C1 + q * C2)) valueMem)
    have firstLift (r2 : Real) (hr2 : r2 ∈ frontierValues L C2) :
        p * frontier L C1 + q * r2 <=
          frontier L (p * C1 + q * C2) := by
      have supBound : frontier L C1 <=
          (frontier L (p * C1 + q * C2) - q * r2) / p := by
        apply csSup_le hC1
        intro r1 hr1
        have := pairBound r1 hr1 r2 hr2
        exact (le_div_iff₀ hp).2 (by linarith)
      have multiplied := (le_div_iff₀ hp).1 supBound
      nlinarith
    have secondBound : frontier L C2 <=
        (frontier L (p * C1 + q * C2) - p * frontier L C1) / q := by
      apply csSup_le hC2
      intro r2 hr2
      exact (le_div_iff₀ hq).2 (by
        have := firstLift r2 hr2
        linarith)
    have result := (le_div_iff₀ hq).1 secondBound
    simp only [smul_eq_mul]
    nlinarith
  have costMonotone (L : Real) :
      MonotoneOn (minimalCost L) (feasibleFloors L) := by
    intro lambda1 _ lambda2 hLambda2 hOrder
    apply csInf_le_csInf (costBounded L lambda1) hLambda2
    rintro c ⟨nu, hMatch, hFloor, rfl⟩
    exact ⟨nu, hMatch, hOrder.trans hFloor, rfl⟩
  have costConvex (L : Real) :
      ConvexOn Real (feasibleFloors L) (minimalCost L) := by
    rw [convexOn_iff_forall_pos]
    refine ⟨feasibleFloorConvex L, ?_⟩
    intro lambda1 hLambda1 lambda2 hLambda2 p q hp hq hpq
    have pairBound : forall c1, c1 ∈ costValues L lambda1 ->
        forall c2, c2 ∈ costValues L lambda2 ->
          minimalCost L (p * lambda1 + q * lambda2) <= p * c1 + q * c2 := by
      rintro c1 ⟨nu1, hMatch1, hFloor1, rfl⟩
        c2 ⟨nu2, hMatch2, hFloor2, rfl⟩
      let nu := mix p q nu1 nu2
      apply csInf_le (costBounded L (p * lambda1 + q * lambda2))
      refine ⟨nu, mixMatches p q hp.le hq.le hpq L nu1 nu2 hMatch1 hMatch2,
        ?_, by simpa only [nu] using (mixBudget p q nu1 nu2).symm⟩
      exact (add_le_add (mul_le_mul_of_nonneg_left hFloor1 hp.le)
        (mul_le_mul_of_nonneg_left hFloor2 hq.le)).trans
          (mixFloor p q hp.le hq.le hpq nu1 nu2)
    have firstLift (c2 : Real) (hc2 : c2 ∈ costValues L lambda2) :
        minimalCost L (p * lambda1 + q * lambda2) <=
          p * minimalCost L lambda1 + q * c2 := by
      have lowerBound :
          (minimalCost L (p * lambda1 + q * lambda2) - q * c2) / p <=
            minimalCost L lambda1 := by
        apply le_csInf hLambda1
        intro c1 hc1
        exact (div_le_iff₀ hp).2 (by
          have := pairBound c1 hc1 c2 hc2
          linarith)
      have multiplied := (div_le_iff₀ hp).1 lowerBound
      nlinarith
    have secondBound :
        (minimalCost L (p * lambda1 + q * lambda2) -
          p * minimalCost L lambda1) / q <= minimalCost L lambda2 := by
      apply le_csInf hLambda2
      intro c2 hc2
      exact (div_le_iff₀ hq).2 (by
        have := firstLift c2 hc2
        linarith)
    have result := (div_le_iff₀ hq).1 secondBound
    simp only [smul_eq_mul]
    nlinarith
  simpa only [frontierValues, costValues, feasibleBudgets, feasibleFloors,
    frontier, minimalCost] using
      And.intro frontierBounds
        (And.intro frontierMonotone
          (And.intro frontierConcave
            (And.intro frontierAntitone
              (And.intro costMonotone costConvex))))

#print axioms resolvent_frontier_basic_properties

end D5.S3.Weil.Budget.ResolventFrontierGeometry
