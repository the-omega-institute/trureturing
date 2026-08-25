/- GID: D5/S3/Estimation/DecisionRisk/DescentDefectBounds
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/DescentDefectBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite maxima and an infimum bound descent; TV contraction lifts pairwise to maxima. -/

import D5.S3.TotalVariation.DataProcessing
import D5.S3.TotalVariation.Metric

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'best_descent_error_lower_bound' D5 Golden/Frozen/accepted` and the
     corresponding search for `postprocessed_descent_defect_le` had no hits.
   * The three existing `D5/S3/Estimation/DecisionRisk` digests concern Bayes-risk floors,
     Blackwell garbling, and posterior sufficiency; none defines this total-variation defect.
   * The only nearby descent hit, `ApproximateDescentComposition`, bounds Lipschitz composition
     errors and does not state either fiberwise total-variation estimate proved here.
   * `D5.S3.TotalVariation.Metric.total_variation_triangle` and
     `total_variation_comm` supply the metric steps for the factor-two estimate.
   * `D5.S3.TotalVariation.DataProcessing.total_variation_channel_le` is applied to each
     same-fiber pair and then maximized; the postprocessing result is only this direct lift.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DecisionRisk.DescentDefectBounds

open D5.S3.Divergence.ClassicalDPI
open D5.S3.TotalVariation.DataProcessing
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

/-- A finite real kernel has nonnegative rows of total mass one. -/
def IsRowStochastic {A B : Type*} [Fintype B] (K : A -> B -> Real) : Prop :=
  (forall a b, 0 <= K a b) /\ (forall a, (∑ b, K a b) = 1)

/-- Row-stochastic finite kernels, used as the admissible approximate descents. -/
def FiniteMarkovKernel (A B : Type*) [Fintype B] :=
  {K : A -> B -> Real // IsRowStochastic K}

/-- The maximum total-variation gap between rows whose source states have the same readout.
Rows `K x` already live on `B`, so they model the pushed-forward laws denoted `q_* K_x` in the
source statement. Off-fiber pairs contribute zero and diagonal pairs ensure the maximum is over
a nonempty finite family. -/
noncomputable def descentDefect {X B : Type*} [Fintype X] [Nonempty X] [Fintype B]
    (q : X -> B) (K : X -> B -> Real) : Real := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty fun pair : X × X =>
    if q pair.1 = q pair.2 then totalVariation (K pair.1) (K pair.2) else 0

/-- The uniform error of a proposed quotient kernel along the readout map. -/
noncomputable def uniformDescentError {X B : Type*} [Fintype X] [Nonempty X] [Fintype B]
    (q : X -> B) (K : X -> B -> Real) (Kbar : B -> B -> Real) : Real :=
  Finset.univ.sup' Finset.univ_nonempty fun x => totalVariation (K x) (Kbar (q x))

/-- The infimum uniform error among row-stochastic kernels on the readout space. -/
noncomputable def bestDescentError {X B : Type*} [Fintype X] [Nonempty X] [Fintype B]
    (q : X -> B) (K : X -> B -> Real) : Real :=
  sInf (Set.range fun Kbar : FiniteMarkovKernel B B =>
    uniformDescentError q K Kbar.1)

/-- The deterministic stochastic matrix induced by a finite target postprocessing map. -/
noncomputable def deterministicPostprocess {B C : Type*} (r : B -> C) : B -> C -> Real := by
  classical
  exact fun b c => if r b = c then 1 else 0

/-- The same-fiber defect after applying a deterministic map to every target law. -/
noncomputable def postprocessedDescentDefect {X B C : Type*}
    [Fintype X] [Nonempty X] [Fintype B] [Fintype C]
    (q : X -> B) (K : X -> B -> Real) (r : B -> C) : Real := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty fun pair : X × X =>
    if q pair.1 = q pair.2 then
      totalVariation
        (channelOutput (deterministicPostprocess r) (K pair.1))
        (channelOutput (deterministicPostprocess r) (K pair.2))
    else 0

private theorem total_variation_le_uniform_descent_error
    {X B : Type*} [Fintype X] [Nonempty X] [Fintype B]
    (q : X -> B) (K : X -> B -> Real) (Kbar : B -> B -> Real) (x : X) :
    totalVariation (K x) (Kbar (q x)) <= uniformDescentError q K Kbar := by
  unfold uniformDescentError
  exact Finset.le_sup'
    (fun candidate : X => totalVariation (K candidate) (Kbar (q candidate)))
    (Finset.mem_univ x)

private theorem uniform_descent_error_nonneg
    {X B : Type*} [Fintype X] [Nonempty X] [Fintype B]
    (q : X -> B) (K : X -> B -> Real) (Kbar : B -> B -> Real) :
    0 <= uniformDescentError q K Kbar := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  exact (total_variation_nonneg (K x) (Kbar (q x))).trans
    (total_variation_le_uniform_descent_error q K Kbar x)

private theorem descent_error_range_bddBelow
    {X B : Type*} [Fintype X] [Nonempty X] [Fintype B]
    (q : X -> B) (K : X -> B -> Real) :
    BddBelow (Set.range fun Kbar : FiniteMarkovKernel B B =>
      uniformDescentError q K Kbar.1) := by
  refine ⟨0, ?_⟩
  rintro error ⟨Kbar, rfl⟩
  exact uniform_descent_error_nonneg q K Kbar.1

/-- Every approximate row-stochastic descent has error at least half the fiber defect. -/
theorem best_descent_error_lower_bound
    {X B : Type*} [Fintype X] [Nonempty X] [Fintype B]
    (q : X -> B) (K : X -> B -> Real) (hK : IsRowStochastic K) :
    (1 / 2 : Real) * descentDefect q K <= bestDescentError q K := by
  classical
  let x0 : X := Classical.choice (inferInstance : Nonempty X)
  let constantKernel : FiniteMarkovKernel B B :=
    ⟨fun _ => K x0, by
      constructor
      · intro _ b
        exact hK.1 x0 b
      · intro _
        exact hK.2 x0⟩
  have errorsNonempty :
      (Set.range fun Kbar : FiniteMarkovKernel B B =>
        uniformDescentError q K Kbar.1).Nonempty := by
    exact ⟨uniformDescentError q K constantKernel.1, constantKernel, rfl⟩
  unfold bestDescentError
  refine (le_csInf_iff (descent_error_range_bddBelow q K) errorsNonempty).2 ?_
  intro error herror
  rcases herror with ⟨Kbar, rfl⟩
  have defect_le_twice_error :
      descentDefect q K <= 2 * uniformDescentError q K Kbar.1 := by
    unfold descentDefect
    apply Finset.sup'_le
    intro pair _
    by_cases hfiber : q pair.1 = q pair.2
    · simp only [hfiber, if_true]
      calc
        totalVariation (K pair.1) (K pair.2) <=
            totalVariation (K pair.1) (Kbar.1 (q pair.1)) +
              totalVariation (Kbar.1 (q pair.1)) (K pair.2) :=
          total_variation_triangle _ _ _
        _ = totalVariation (K pair.1) (Kbar.1 (q pair.1)) +
            totalVariation (K pair.2) (Kbar.1 (q pair.2)) := by
          rw [total_variation_comm (Kbar.1 (q pair.1)) (K pair.2), hfiber]
        _ <= uniformDescentError q K Kbar.1 +
            uniformDescentError q K Kbar.1 :=
          add_le_add
            (total_variation_le_uniform_descent_error q K Kbar.1 pair.1)
            (total_variation_le_uniform_descent_error q K Kbar.1 pair.2)
        _ = 2 * uniformDescentError q K Kbar.1 := by ring
    · simp only [hfiber, if_false]
      nlinarith [uniform_descent_error_nonneg q K Kbar.1]
  nlinarith

/-- Chosen representatives give an approximate descent whose error is at most the defect. -/
theorem best_descent_error_upper_bound_of_representatives
    {X B : Type*} [Fintype X] [Nonempty X] [Fintype B]
    (q : X -> B) (K : X -> B -> Real) (hK : IsRowStochastic K)
    (rep : B -> X) (hrep : forall x, q (rep (q x)) = q x) :
    bestDescentError q K <= descentDefect q K := by
  classical
  let representativeKernel : FiniteMarkovKernel B B :=
    ⟨fun b => K (rep b), by
      constructor
      · intro b c
        exact hK.1 (rep b) c
      · intro b
        exact hK.2 (rep b)⟩
  unfold bestDescentError
  calc
    sInf (Set.range fun Kbar : FiniteMarkovKernel B B =>
        uniformDescentError q K Kbar.1) <=
        uniformDescentError q K representativeKernel.1 :=
      csInf_le (descent_error_range_bddBelow q K)
        ⟨representativeKernel, rfl⟩
    _ <= descentDefect q K := by
      unfold uniformDescentError descentDefect
      apply Finset.sup'_le
      intro x _
      have hfiber : q x = q (rep (q x)) := (hrep x).symm
      change totalVariation (K x) (K (rep (q x))) <=
        Finset.univ.sup' Finset.univ_nonempty
          (fun pair : X × X =>
            if q pair.1 = q pair.2 then
              totalVariation (K pair.1) (K pair.2)
            else 0)
      have hpair :=
        Finset.le_sup'
          (fun pair : X × X =>
            if q pair.1 = q pair.2 then
              totalVariation (K pair.1) (K pair.2)
            else 0)
          (Finset.mem_univ (x, rep (q x)))
      rw [if_pos hfiber] at hpair
      exact hpair

/-- Deterministic target postprocessing cannot increase the same-fiber descent defect. -/
theorem postprocessed_descent_defect_le
    {X B C : Type*} [Fintype X] [Nonempty X] [Fintype B] [Fintype C]
    (q : X -> B) (K : X -> B -> Real) (r : B -> C) :
    postprocessedDescentDefect q K r <= descentDefect q K := by
  classical
  have hpostprocess :
      (forall b c, 0 <= deterministicPostprocess r b c) /\
        (forall b, (∑ c, deterministicPostprocess r b c) = 1) := by
    constructor
    · intro b c
      by_cases h : r b = c <;> simp [deterministicPostprocess, h]
    · intro b
      simp [deterministicPostprocess]
  unfold postprocessedDescentDefect descentDefect
  apply Finset.sup'_le
  intro pair _
  by_cases hfiber : q pair.1 = q pair.2
  · simp only [hfiber, if_true]
    calc
      totalVariation
          (channelOutput (deterministicPostprocess r) (K pair.1))
          (channelOutput (deterministicPostprocess r) (K pair.2)) <=
          totalVariation (K pair.1) (K pair.2) :=
        total_variation_channel_le _ _ _ hpostprocess
      _ <= Finset.univ.sup' Finset.univ_nonempty
          (fun candidate : X × X =>
            if q candidate.1 = q candidate.2 then
              totalVariation (K candidate.1) (K candidate.2)
            else 0) :=
        by
          have hsup :=
            (Finset.le_sup'
              (fun candidate : X × X =>
                if q candidate.1 = q candidate.2 then
                  totalVariation (K candidate.1) (K candidate.2)
                else 0)
              (Finset.mem_univ pair))
          have hsup' := hsup
          rw [hfiber] at hsup'
          simpa only [if_true] using hsup'
  · simp only [hfiber, if_false]
    calc
      (0 : Real) =
          (if q pair.1 = q pair.1 then
            totalVariation (K pair.1) (K pair.1)
          else 0) := by
        simp [totalVariation]
      _ <= Finset.univ.sup' Finset.univ_nonempty
          (fun candidate : X × X =>
            if q candidate.1 = q candidate.2 then
              totalVariation (K candidate.1) (K candidate.2)
            else 0) :=
        Finset.le_sup'
          (fun candidate : X × X =>
            if q candidate.1 = q candidate.2 then
              totalVariation (K candidate.1) (K candidate.2)
            else 0)
          (Finset.mem_univ (pair.1, pair.1))

example :
    postprocessedDescentDefect
        (fun x : Bool => x)
        (fun x b : Bool => if x = b then 1 else 0)
        (fun b : Bool => !b) <=
      descentDefect
        (fun x : Bool => x)
        (fun x b : Bool => if x = b then 1 else 0) := by
  exact postprocessed_descent_defect_le _ _ _

#print axioms best_descent_error_lower_bound
#print axioms best_descent_error_upper_bound_of_representatives
#print axioms postprocessed_descent_defect_le

end D5.S3.Estimation.DecisionRisk.DescentDefectBounds
