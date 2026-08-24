/- GID: D5/S3/Observer/DynamicProgramming/BellmanFixedPointIteration
   generality: G
   mirror-B: D5/B/S3/Observer/DynamicProgramming/BellmanFixedPointIteration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A contractive active Bellman operator has one value and geometric iteration. -/

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Data.Fintype.Order

/- Library-search audit trail (2026-08-24):
   * The repository hit `bellman_operator_contracting_unique_fixed_point`
     concerns a fixed deterministic update. The source's own bridge records that
     active observation still requires belief transitions and action minimization,
     so that theorem is not substituted for the operator constructed below.
   * Pinned Mathlib exact hits `ContractingWith.fixedPoint_isFixedPt`,
     `ContractingWith.fixedPoint_unique`, and `LipschitzWith.iterate` supply
     existence, fixed-point uniqueness, and the exact geometric iterate bound.
   * Searches for an existing finite-action `min G (inf_i Q_i V)` Bellman
     operator or a theorem combining all three public clauses found no hit.
     `loogle` and `leansearch` executables are absent from PATH. -/

noncomputable section

namespace D5.S3.Observer.DynamicProgramming.BellmanFixedPointIteration

/-- The active-observation Bellman operator: stop at the current risk, or take
the least continuation value among the available experiments. -/
def activeObservationBellman {Value Experiment : Type*}
    [SemilatticeInf Value] [Fintype Experiment] [Nonempty Experiment]
    (stop : Value) (continuation : Experiment -> Value -> Value) :
    Value -> Value :=
  fun value => stop ⊓
    Finset.univ.inf' Finset.univ_nonempty (fun experiment =>
      continuation experiment value)

/-- Once the source Bellman estimate has established discount-factor
Lipschitzness, the source-constructed active operator is a strict contraction,
has exactly one fixed value, and all value iterations obey the geometric bound. -/
theorem bellman_contraction_unique_fixed_point_and_iteration_bound
    {Value Experiment : Type*}
    [MetricSpace Value] [CompleteSpace Value] [Nonempty Value]
    [SemilatticeInf Value] [Fintype Experiment] [Nonempty Experiment]
    (gamma : NNReal) (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (stop : Value) (continuation : Experiment -> Value -> Value)
    (contractionEstimate : LipschitzWith gamma
      (activeObservationBellman stop continuation)) :
    ContractingWith gamma (activeObservationBellman stop continuation) ∧
      ∃ valueStar : Value,
        Function.IsFixedPt
            (activeObservationBellman stop continuation) valueStar ∧
          (∀ candidate : Value,
            Function.IsFixedPt
                (activeObservationBellman stop continuation) candidate ->
              candidate = valueStar) ∧
          ∀ initial : Value, ∀ n : Nat,
            dist ((activeObservationBellman stop continuation)^[n] initial)
                valueStar ≤
              (gamma : Real) ^ n * dist initial valueStar := by
  let operator := activeObservationBellman stop continuation
  have contracting : ContractingWith gamma operator :=
    ⟨hgamma_lt_one, contractionEstimate⟩
  let valueStar := ContractingWith.fixedPoint operator contracting
  have valueStarFixed : Function.IsFixedPt operator valueStar :=
    contracting.fixedPoint_isFixedPt
  refine ⟨contracting, valueStar, valueStarFixed, ?_, ?_⟩
  · intro candidate candidateFixed
    exact contracting.fixedPoint_unique candidateFixed
  · intro initial n
    have iterateBound :=
      (contracting.toLipschitzWith.iterate n).dist_le_mul initial valueStar
    rw [valueStarFixed.iterate n] at iterateBound
    have bound :
        dist (operator^[n] initial) valueStar ≤
          (gamma : Real) ^ n * dist initial valueStar := by
      simpa only [NNReal.coe_pow] using iterateBound
    have gammaPowerNonnegative : 0 ≤ (gamma : Real) ^ n :=
      pow_nonneg (le_of_lt (by exact_mod_cast hgamma_pos)) n
    exact bound.trans
      (mul_le_mul_of_nonneg_left le_rfl gammaPowerNonnegative)

#print axioms bellman_contraction_unique_fixed_point_and_iteration_bound

end D5.S3.Observer.DynamicProgramming.BellmanFixedPointIteration
