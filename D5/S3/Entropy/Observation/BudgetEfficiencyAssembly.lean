/- GID: D5/S3/Entropy/Observation/BudgetEfficiencyAssembly
   generality: G
   mirror-B: D5/B/S3/Entropy/Observation/BudgetEfficiencyAssembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Assemble refinement information, innovation budgets, and the finite closure-spectrum telescope. -/

import D5.S3.Entropy.Submodularity.RefinementInformationDecomposition
import D5.S3.Observer.Tomography.InnovationCountBound
import D5.S3.Observer.Prediction.StableDepthCardinalityBounds
import D5.S3.Observer.Separation.FiniteHistoryStability
import D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

namespace D5.S3.Entropy.Observation.BudgetEfficiencyAssembly

open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.Submodularity.RefinementInformationDecomposition
open D5.S3.Observer.Tomography.InnovationCountBound
open D5.S3.Observer.Prediction.StableDepthCardinalityBounds
open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.Observer.Separation.FiniteObservationRefinementBound
open D5.S3.Observer.Separation.FiniteHistoryStability
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem stable_class_count_eq_complete
    {X Q : Type*} [Fintype X]
    (update : X -> X) (readout : X -> Q) :
    observationClassCount update readout
        (observationStabilityDepth update readout) =
      infiniteObservationClassCount update readout := by
  let hsetoid : observationSetoid update readout
      (observationStabilityDepth update readout) =
      infiniteObservationSetoid update readout := by
    apply Setoid.ext
    intro x y
    have hstable := (finite_history_stability update readout).2.2.1
    constructor
    · intro h
      have hfinite : (x, y) ∈ finiteFutureRelation update readout
          (observationStabilityDepth update readout) := by
        change ∀ k, k ≤ observationStabilityDepth update readout →
          observedAt update readout k x = observedAt update readout k y
        change futureReadoutWord update readout
            (observationStabilityDepth update readout) x =
          futureReadoutWord update readout
            (observationStabilityDepth update readout) y at h
        intro k hk
        simpa only [futureReadoutWord, observedAt] using
          congrFun h ⟨k, Nat.lt_succ_of_le hk⟩
      have hinfinite : (x, y) ∈ infiniteFutureRelation update readout := by
        rw [← hstable]
        exact hfinite
      change (fun k : Nat => observedAt update readout k x) =
        (fun k : Nat => observedAt update readout k y)
      exact funext hinfinite
    · intro h
      have hinfinite : (x, y) ∈ infiniteFutureRelation update readout := by
        change (fun k : Nat => observedAt update readout k x) =
          (fun k : Nat => observedAt update readout k y) at h
        exact fun k => congrFun h k
      have hfinite : (x, y) ∈ finiteFutureRelation update readout
          (observationStabilityDepth update readout) := by
        rw [hstable]
        exact hinfinite
      change futureReadoutWord update readout
          (observationStabilityDepth update readout) x =
        futureReadoutWord update readout
          (observationStabilityDepth update readout) y
      funext k
      exact hfinite k (Nat.le_of_lt_succ k.isLt)
  exact Fintype.card_congr (Equiv.cast (congrArg Quotient hsetoid))

private theorem initial_class_count_eq_readout_range
    {X Q : Type*} [Fintype X]
    (update : X -> X) (readout : X -> Q) :
    observationClassCount update readout 0 =
      Nat.card (Set.range readout) := by
  letI : Fintype (Set.range readout) := Fintype.ofFinite _
  letI : Fintype (Quotient (Setoid.ker readout)) := Fintype.ofFinite _
  have hsetoid : observationSetoid update readout 0 = Setoid.ker readout := by
    apply Setoid.ext
    intro x y
    constructor
    · intro h
      change readout x = readout y
      change futureReadoutWord update readout 0 x =
        futureReadoutWord update readout 0 y at h
      simpa [futureReadoutWord, observedAt, Function.iterate_zero_apply] using
        congrFun h (0 : Fin 1)
    · intro h
      change readout x = readout y at h
      change futureReadoutWord update readout 0 x =
        futureReadoutWord update readout 0 y
      funext k
      have hk : k = (0 : Fin 1) := Fin.eq_zero k
      subst k
      simpa [futureReadoutWord, observedAt, Function.iterate_zero_apply] using h
  have hquot :
      Fintype.card (Quotient (observationSetoid update readout 0)) =
        Fintype.card (Quotient (Setoid.ker readout)) :=
    Fintype.card_congr (Equiv.cast (congrArg Quotient hsetoid))
  calc
    observationClassCount update readout 0 =
        Nat.card (Quotient (Setoid.ker readout)) := by
      simpa only [observationClassCount, Nat.card_eq_fintype_card] using hquot
    _ = Nat.card (Set.range readout) :=
      Nat.card_congr (Setoid.quotientKerEquivRange readout)

private theorem log_closure_telescope
    {X Q : Type*} [Fintype X]
    (update : X -> X) (readout : X -> Q) :
    ∑ k ∈ Finset.range (observationStabilityDepth update readout),
        (Real.log (observationClassCount update readout (k + 1)) -
          Real.log (observationClassCount update readout k)) =
      Real.log (infiniteObservationClassCount update readout) -
        Real.log (Nat.card (Set.range readout)) := by
  let f : Nat -> Real := fun k =>
    Real.log (observationClassCount update readout k)
  have htelescope : ∀ n, ∑ k ∈ Finset.range n, (f (k + 1) - f k) = f n - f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  rw [show (∑ k ∈ Finset.range (observationStabilityDepth update readout),
      (Real.log (observationClassCount update readout (k + 1)) -
        Real.log (observationClassCount update readout k))) =
      ∑ k ∈ Finset.range (observationStabilityDepth update readout),
        (f (k + 1) - f k) by rfl]
  rw [htelescope]
  change Real.log (observationClassCount update readout
      (observationStabilityDepth update readout)) -
      Real.log (observationClassCount update readout 0) =
    Real.log (infiniteObservationClassCount update readout) -
      Real.log (Nat.card (Set.range readout))
  rw [stable_class_count_eq_complete, initial_class_count_eq_readout_range]

/-- The refinement information identity, the finite innovation count budget, and the
finite closure-spectrum log-resolution telescope hold on their canonical carriers. -/
theorem budget_efficiency_assembly
    {P F Fine Coarse X Q : Type*}
    [Fintype P] [Fintype F] [Fintype Fine] [Fintype Coarse]
    [Fintype X]
    (p : P × F -> Real)
    (hp : (forall z, 0 <= p z) ∧ ∑ z, p z = 1)
    (fine : P -> Fine) (forget : Fine -> Coarse)
    (innovation : Nat -> Real) (H ε : Real)
    (hNonneg : ∀ k, 0 ≤ innovation k)
    (hSummable : Summable innovation)
    (hBudget : ∑' k, innovation k ≤ H)
    (hε : 0 < ε)
    (update : X -> X) (readout : X -> Q) :
    (predictiveMemory p (forget ∘ fine) - predictiveMemory p fine =
        refinementGain p fine forget ∧
      0 ≤ refinementGain p fine forget) ∧
    (({k | ε ≤ innovation k} : Set Nat).ncard : Real) ≤ H / ε ∧
    (∑ k ∈ Finset.range (observationStabilityDepth update readout),
        (Real.log (observationClassCount update readout (k + 1)) -
          Real.log (observationClassCount update readout k)) =
      Real.log (infiniteObservationClassCount update readout) -
        Real.log (Nat.card (Set.range readout))) := by
  refine ⟨deterministic_refinement_information_decomposition p hp fine forget,
    large_innovation_count_le_budget_div innovation H ε hNonneg hSummable hBudget hε,
    log_closure_telescope update readout⟩

#print axioms budget_efficiency_assembly

end D5.S3.Entropy.Observation.BudgetEfficiencyAssembly
