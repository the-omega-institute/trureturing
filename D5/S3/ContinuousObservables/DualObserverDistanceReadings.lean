/- GID: D5/S3/ContinuousObservables/DualObserverDistanceReadings
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/DualObserverDistanceReadings
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two bounded-function observers give paired zero, finite,
     or infinite distance readings. -/

import D5.S3.Observer.Separation.RefinementDistanceMonotonicity
import Mathlib.Analysis.Normed.Lp.lpSpace

/- Library-search audit trail (2026-08-28):
   * Repository body-shape searches found the canonical general `observerDistance`
     in `RefinementDistanceMonotonicity`, which is imported and instantiated here.
   * No D5 declaration combined its three ENNReal cases with both the unit-ball
     spanning kernel and the zero-cost separation detector for two observers.
   * Mathlib supplies the exact bounded-function carrier `lp (fun _ : X => Real) ∞`,
     the evaluation linear map `lp.eval_l`, `Submodule.span_le`, `eq_top_or_lt_top`,
     and `exists_nat_gt`; no exact theorem states the assembled observer result.
-/

open scoped ENNReal

noncomputable section

namespace D5.S3.ContinuousObservables.DualObserverDistanceReadings

open D5.S3.Observer.Separation.RefinementDistanceMonotonicity

private theorem one_observer_distance_reading
    {X : Type*} (observables : Submodule Real (lp (fun _ : X => Real) ∞))
    (cost : observables -> ENNReal)
    (cost_smul : forall (c : Real) (f : observables),
      cost (c • f) = ENNReal.ofReal |c| * cost f)
    (x y : X) :
    let distance := observerDistance Set.univ cost
      (fun state observable => observable.1 state) x y
    let zeroMeaning :=
      Submodule.span Real {f : observables | cost f <= 1} = ⊤ ->
        (distance = 0 <-> forall f : observables, f.1 x = f.1 y)
    let horizonDetector :=
      (Exists fun f : observables => cost f = 0 ∧ f.1 x ≠ f.1 y) ->
        distance = ⊤
    (distance = 0 ∧ zeroMeaning ∧ horizonDetector) ∨
      ((0 < distance ∧ distance < ⊤) ∧ zeroMeaning ∧ horizonDetector) ∨
      (distance = ⊤ ∧ zeroMeaning ∧ horizonDetector) := by
  dsimp only
  have zeroMeaning :
      Submodule.span Real {f : observables | cost f <= 1} = ⊤ ->
        (observerDistance Set.univ cost
            (fun state observable => observable.1 state) x y = 0 <->
          forall f : observables, f.1 x = f.1 y) := by
    intro spanning
    constructor
    · intro distanceZero
      let evaluationDifference : observables →ₗ[Real] Real :=
        ((lp.evalₗ (fun _ : X => Real) ∞ x).comp observables.subtype) -
          ((lp.evalₗ (fun _ : X => Real) ∞ y).comp observables.subtype)
      have unitAgreement :
          forall f : observables, cost f <= 1 -> f.1 x = f.1 y := by
        intro f hf
        have termLeDistance :
            ENNReal.ofReal |f.1 x - f.1 y| <=
              observerDistance Set.univ cost
                (fun state observable => observable.1 state) x y := by
          unfold observerDistance
          exact le_iSup
            (fun observable :
              {g : observables // g ∈ (Set.univ : Set observables) ∧ cost g <= 1} =>
                ENNReal.ofReal
                  |(fun state observable => observable.1 state) x observable.1 -
                    (fun state observable => observable.1 state) y observable.1|)
            ⟨f, Set.mem_univ f, hf⟩
        have termZero : ENNReal.ofReal |f.1 x - f.1 y| = 0 :=
          le_antisymm (termLeDistance.trans_eq distanceZero) bot_le
        have absoluteZero : |f.1 x - f.1 y| = 0 := by
          apply le_antisymm
          · exact ENNReal.ofReal_eq_zero.mp termZero
          · exact abs_nonneg _
        exact sub_eq_zero.mp (abs_eq_zero.mp absoluteZero)
      have unitInKernel :
          {f : observables | cost f <= 1} <= LinearMap.ker evaluationDifference := by
        intro f hf
        change evaluationDifference f = 0
        change f.1 x - f.1 y = 0
        exact sub_eq_zero.mpr (unitAgreement f hf)
      have spanInKernel :
          Submodule.span Real {f : observables | cost f <= 1} <=
            LinearMap.ker evaluationDifference :=
        Submodule.span_le.mpr unitInKernel
      intro f
      have fInSpan : f ∈ Submodule.span Real {g : observables | cost g <= 1} := by
        rw [spanning]
        exact Submodule.mem_top
      have fInKernel := spanInKernel fInSpan
      change evaluationDifference f = 0 at fInKernel
      change f.1 x - f.1 y = 0 at fInKernel
      exact sub_eq_zero.mp fInKernel
    · intro sameReadout
      unfold observerDistance
      apply le_antisymm
      · apply iSup_le
        intro observable
        simp [sameReadout observable.1]
      · exact bot_le
  have horizonDetector :
      (Exists fun f : observables => cost f = 0 ∧ f.1 x ≠ f.1 y) ->
        observerDistance Set.univ cost
          (fun state observable => observable.1 state) x y = ⊤ := by
    rintro ⟨f, costZero, separates⟩
    unfold observerDistance
    apply iSup_eq_top.mpr
    intro b hb
    let gap : Real := |f.1 x - f.1 y|
    have gapPositive : 0 < gap := abs_pos.mpr (sub_ne_zero.mpr separates)
    obtain ⟨m, hm⟩ := exists_nat_gt (b.toReal / gap)
    refine ⟨⟨(m : Real) • f, Set.mem_univ _, ?_⟩, ?_⟩
    · rw [cost_smul, costZero, mul_zero]
      exact zero_le_one
    · simp only [Submodule.coe_smul_of_tower, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
      apply (ENNReal.lt_ofReal_iff_toReal_lt hb.ne).mpr
      simpa [gap] using (div_lt_iff₀ gapPositive).mp hm
  let distance := observerDistance Set.univ cost
    (fun state observable => observable.1 state) x y
  by_cases distanceZero : distance = 0
  · exact Or.inl ⟨distanceZero, zeroMeaning, horizonDetector⟩
  rcases eq_top_or_lt_top distance with distanceTop | distanceFinite
  · exact Or.inr (Or.inr ⟨distanceTop, zeroMeaning, horizonDetector⟩)
  · exact Or.inr (Or.inl
      ⟨⟨bot_lt_iff_ne_bot.mpr distanceZero, distanceFinite⟩,
        zeroMeaning, horizonDetector⟩)

/-- Each pair of endpoints has one typed distance reading for each of two bounded-function
observers. Unit-ball spanning identifies the zero class with the joint readout fiber, while
a separating zero-cost observable is a sufficient detector of the infinite class. -/
theorem dual_observer_distance_readings
    {X : Type*}
    (firstObservables secondObservables :
      Submodule Real (lp (fun _ : X => Real) ∞))
    (firstCost : firstObservables -> ENNReal)
    (secondCost : secondObservables -> ENNReal)
    (firstCost_smul : forall (c : Real) (f : firstObservables),
      firstCost (c • f) = ENNReal.ofReal |c| * firstCost f)
    (secondCost_smul : forall (c : Real) (f : secondObservables),
      secondCost (c • f) = ENNReal.ofReal |c| * secondCost f)
    (x y : X) :
    let firstDistance := observerDistance Set.univ firstCost
      (fun state observable => observable.1 state) x y
    let secondDistance := observerDistance Set.univ secondCost
      (fun state observable => observable.1 state) x y
    let firstZeroMeaning :=
      Submodule.span Real {f : firstObservables | firstCost f <= 1} = ⊤ ->
        (firstDistance = 0 <->
          forall f : firstObservables, f.1 x = f.1 y)
    let secondZeroMeaning :=
      Submodule.span Real {f : secondObservables | secondCost f <= 1} = ⊤ ->
        (secondDistance = 0 <->
          forall f : secondObservables, f.1 x = f.1 y)
    let firstHorizonDetector :=
      (Exists fun f : firstObservables =>
        firstCost f = 0 ∧ f.1 x ≠ f.1 y) -> firstDistance = ⊤
    let secondHorizonDetector :=
      (Exists fun f : secondObservables =>
        secondCost f = 0 ∧ f.1 x ≠ f.1 y) -> secondDistance = ⊤
    ((firstDistance = 0 ∧ firstZeroMeaning ∧ firstHorizonDetector) ∨
        ((0 < firstDistance ∧ firstDistance < ⊤) ∧
          firstZeroMeaning ∧ firstHorizonDetector) ∨
        (firstDistance = ⊤ ∧ firstZeroMeaning ∧ firstHorizonDetector)) ∧
      ((secondDistance = 0 ∧ secondZeroMeaning ∧ secondHorizonDetector) ∨
        ((0 < secondDistance ∧ secondDistance < ⊤) ∧
          secondZeroMeaning ∧ secondHorizonDetector) ∨
        (secondDistance = ⊤ ∧ secondZeroMeaning ∧ secondHorizonDetector)) := by
  dsimp only
  exact ⟨one_observer_distance_reading firstObservables firstCost firstCost_smul x y,
    one_observer_distance_reading secondObservables secondCost secondCost_smul x y⟩

#print axioms dual_observer_distance_readings

end D5.S3.ContinuousObservables.DualObserverDistanceReadings
