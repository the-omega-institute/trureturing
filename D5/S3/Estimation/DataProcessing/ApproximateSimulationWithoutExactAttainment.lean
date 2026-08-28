/- GID: D5/S3/Estimation/DataProcessing/ApproximateSimulationWithoutExactAttainment
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/ApproximateSimulationWithoutExactAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zero simulation infimum need not have an exact admissible kernel. -/

import D5.S3.Estimation.DecisionRisk.DescentDefectBounds

/- Library-search audit trail (2026-08-26):
   * Repository searches for approximate Blackwell simulation, zero simulator
     defect, infimum attainment, compact kernel families, and exact simulators
     found no theorem with the full positive and contrast clauses below.
   * Body-shape searches found the canonical finite-kernel primitives
     `FiniteMarkovKernel`, `IsRowStochastic`, `channelOutput`, and
     `totalVariation`; they are imported rather than redeclared.
   * Pinned Mathlib supplies exact component hits `exists_nat_gt`,
     `Real.sInf_nonneg`, `csInf_le`, and `le_of_forall_pos_le_add`. No theorem
     packages this nonclosed simulator-family countermodel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DataProcessing.ApproximateSimulationWithoutExactAttainment

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

noncomputable section

/-- For every nonnegative simulation-error cost, zero infimum is equivalent to
the existence of a simulator below every positive tolerance. A concrete
nonclosed family of admissible postprocessing kernels then shows that this
approximate condition need not supply an exact simulator. The experiment,
target law, simulator family, and error are constructed from the repository's
finite-channel primitives. -/
theorem approximate_simulation_without_exact_attainment :
    (forall {Simulator : Type*} [Nonempty Simulator]
        (simulationError : Simulator -> Real),
      (forall M, 0 <= simulationError M) ->
        (sInf (Set.range simulationError) = 0 <->
          forall epsilon : Real, 0 < epsilon ->
            exists M, simulationError M < epsilon)) /\
    (let K : FiniteMarkovKernel Unit Unit :=
        ⟨fun _ _ => 1, by simp [IsRowStochastic]⟩
      let L : FiniteMarkovKernel Unit Bool :=
        ⟨fun _ outcome => if outcome then 0 else 1, by
          constructor
          · intro _ outcome
            cases outcome <;> simp
          · intro _
            simp⟩
      let simulator : Nat -> FiniteMarkovKernel Unit Bool := fun n =>
        ⟨fun _ outcome =>
            if outcome then (1 : Real) / (n + 2) else 1 - 1 / (n + 2), by
          constructor
          · intro _ outcome
            cases outcome
            · simp only [Bool.false_eq_true, ↓reduceIte]
              have hn : (1 : Real) <= (n : Real) + 2 := by
                have hnNat : 1 <= n + 2 := by omega
                exact_mod_cast hnNat
              exact sub_nonneg.mpr
                ((div_le_one (a := (1 : Real)) (b := (n : Real) + 2)
                  (by positivity)).2 hn)
            · exact div_nonneg (by norm_num) (by positivity)
          · intro _
            simp⟩
      let error : Nat -> Real := fun n =>
        totalVariation (L.1 ()) (channelOutput (simulator n).1 (K.1 ()))
      sInf (Set.range error) = 0 /\
        ¬(exists n, L.1 = fun state =>
          channelOutput (simulator n).1 (K.1 state))) := by
  constructor
  · intro Simulator _ simulationError error_nonnegative
    have errors_bddBelow : BddBelow (Set.range simulationError) := by
      refine ⟨0, ?_⟩
      rintro value ⟨M, rfl⟩
      exact error_nonnegative M
    have errors_nonempty : (Set.range simulationError).Nonempty := by
      let M : Simulator := Classical.choice (inferInstance : Nonempty Simulator)
      exact ⟨simulationError M, M, rfl⟩
    constructor
    · intro infimum_zero epsilon hepsilon
      have infimum_lt : sInf (Set.range simulationError) < epsilon := by
        rw [infimum_zero]
        exact hepsilon
      obtain ⟨value, ⟨M, rfl⟩, hvalue⟩ :=
        exists_lt_of_csInf_lt errors_nonempty infimum_lt
      exact ⟨M, hvalue⟩
    · intro arbitrarily_small
      refine le_antisymm ?_ (Real.sInf_nonneg ?_)
      · apply le_of_forall_pos_le_add
        intro epsilon hepsilon
        obtain ⟨M, hM⟩ := arbitrarily_small epsilon hepsilon
        have hinf : sInf (Set.range simulationError) <= simulationError M :=
          csInf_le errors_bddBelow ⟨M, rfl⟩
        linarith
      · intro value hvalue
        rcases hvalue with ⟨M, rfl⟩
        exact error_nonnegative M
  · dsimp only
    have error_eq (n : Nat) :
      totalVariation (fun outcome : Bool => if outcome then 0 else 1)
          (channelOutput
            (fun (_ : Unit) (outcome : Bool) =>
              if outcome then (1 : Real) / (n + 2) else 1 - 1 / (n + 2))
            (fun _ : Unit => (1 : Real))) =
        (1 : Real) / (n + 2) := by
      rw [totalVariation, Fintype.sum_bool]
      norm_num [channelOutput]
      rw [abs_of_pos (show 0 < (n : Real) + 2 by positivity)]
      ring
    have error_nonnegative (n : Nat) :
      0 <= totalVariation (fun outcome : Bool => if outcome then 0 else 1)
        (channelOutput
          (fun (_ : Unit) (outcome : Bool) =>
            if outcome then (1 : Real) / (n + 2) else 1 - 1 / (n + 2))
          (fun _ : Unit => (1 : Real))) :=
      total_variation_nonneg _ _
    have errors_bddBelow : BddBelow (Set.range fun n : Nat =>
      totalVariation (fun outcome : Bool => if outcome then 0 else 1)
        (channelOutput
          (fun (_ : Unit) (outcome : Bool) =>
            if outcome then (1 : Real) / (n + 2) else 1 - 1 / (n + 2))
          (fun _ : Unit => (1 : Real)))) := by
      refine ⟨0, ?_⟩
      rintro value ⟨n, rfl⟩
      exact error_nonnegative n
    have arbitrarily_small : forall epsilon : Real, 0 < epsilon ->
      exists n : Nat,
        totalVariation (fun outcome : Bool => if outcome then 0 else 1)
          (channelOutput
            (fun (_ : Unit) (outcome : Bool) =>
              if outcome then (1 : Real) / (n + 2) else 1 - 1 / (n + 2))
            (fun _ : Unit => (1 : Real))) < epsilon := by
      intro epsilon hepsilon
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / epsilon : Real)
      refine ⟨n, ?_⟩
      rw [error_eq]
      have hdenom : 0 < (n + 2 : Real) := by positivity
      have hinv : 1 / epsilon < (n + 2 : Real) := by
        exact lt_of_lt_of_le hn (by norm_num)
      rw [div_lt_iff₀ hdenom]
      have := (div_lt_iff₀ hepsilon).mp hinv
      nlinarith
    refine ⟨le_antisymm ?_ (Real.sInf_nonneg ?_), ?_⟩
    · apply le_of_forall_pos_le_add
      intro epsilon hepsilon
      obtain ⟨n, hn⟩ := arbitrarily_small epsilon hepsilon
      have hinf : sInf (Set.range fun n : Nat =>
          totalVariation (fun outcome : Bool => if outcome then 0 else 1)
            (channelOutput
              (fun (_ : Unit) (outcome : Bool) =>
                if outcome then (1 : Real) / (n + 2) else 1 - 1 / (n + 2))
              (fun _ : Unit => (1 : Real)))) <=
            totalVariation (fun outcome : Bool => if outcome then 0 else 1)
              (channelOutput
                (fun (_ : Unit) (outcome : Bool) =>
                  if outcome then (1 : Real) / (n + 2) else 1 - 1 / (n + 2))
                (fun _ : Unit => (1 : Real))) :=
        csInf_le errors_bddBelow ⟨n, rfl⟩
      linarith
    · intro value hvalue
      rcases hvalue with ⟨n, rfl⟩
      exact error_nonnegative n
    · rintro ⟨n, exactSimulator⟩
      have htrue := congrFun (congrFun exactSimulator ()) true
      simp [channelOutput] at htrue
      have hpositive : (0 : Real) < (n : Real) + 2 := by positivity
      linarith

#print axioms approximate_simulation_without_exact_attainment

end

end D5.S3.Estimation.DataProcessing.ApproximateSimulationWithoutExactAttainment
