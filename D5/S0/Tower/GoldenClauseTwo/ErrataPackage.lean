/- GID: D5/S0/Tower/GoldenClauseTwo/ErrataPackage
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenClauseTwo/ErrataPackage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden tower clause two as one conjunction that carries its own errata. -/

import D5.S0.Tower.Champions.GoldenPermanentSurvivors
import D5.S0.Tower.ErgodicBridge.Golden
import D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelve
import D5.S0.Tower.GoldenChampionPoint
import D5.S0.Tower.GoldenSubstitution

namespace D5.S0.Tower.GoldenClauseTwo

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Tower.Champions.GoldenSurvivorClassification
open D5.S0.Tower.Champions.GoldenAsymptotic
open D5.S0.Tower.Champions.GoldenPermanentSurvivors
open D5.S0.Tower.MetricGeometry.GoldenSurvivor
open D5.S0.Tower.GoldenNames
open D5.S0.Tower.GoldenGaps
open D5.S0.Tower.GoldenSubstitution
open D5.S0.Tower.GoldenChampionPoint
open D5.S0.Tower.GoldenPeriodicTwelve.EnumerationTwelve
open D5.S0.Tower.ErgodicBridge.Golden
open D5.S0.Conventions

/-- The golden tower section of `theorem/4.2'`, packaged as one conjunction that carries
its own errata rather than silently replacing the refuted sentences. -/
theorem golden_clause_two_errata_package :
    (∀ (Q : Nat),
      goldenNameGrid Q = Set.range (nameValue Q)) ∧
    (∀ (Q : ℕ),
      Fintype.card (GoldenName Q) = Nat.fib (Q + 2)) ∧
    (∀ (Q : ℕ) (hQ : 2 ≤ Q),
      adjacentGapSpectrum Q =
        {Real.goldenRatio ^ (-(Q : ℤ)), Real.goldenRatio ^ (-((Q + 1 : ℕ) : ℤ))}) ∧
    (∀ (Q : ℕ) (hQ : 2 ≤ Q) (i : Fin (Nat.fib (Q + 2) - 1)),
      (indexedNameValue Q
                ⟨i.1 + 1, by have := i.2; have hf : 0 < Nat.fib (Q + 2) := Nat.fib_pos.mpr (by omega); omega⟩ -
              indexedNameValue Q
                ⟨i.1, by have := i.2; have hf : 0 < Nat.fib (Q + 2) := Nat.fib_pos.mpr (by omega); omega⟩ =
            Real.goldenRatio ^ (-((Q + 1 : ℕ) : ℤ)) →
          insertedNameIndices Q i = ∅ ∧
          indexedNameValue (Q + 1)
                (levelEmbedding Q
                  ⟨i.1 + 1, by have := i.2; have hf : 0 < Nat.fib (Q + 2) := Nat.fib_pos.mpr (by omega); omega⟩) -
              indexedNameValue (Q + 1)
                (levelEmbedding Q
                  ⟨i.1, by have := i.2; have hf : 0 < Nat.fib (Q + 2) := Nat.fib_pos.mpr (by omega); omega⟩) =
            Real.goldenRatio ^ (-((Q + 1 : ℕ) : ℤ))) ∧
      (indexedNameValue Q
                ⟨i.1 + 1, by have := i.2; have hf : 0 < Nat.fib (Q + 2) := Nat.fib_pos.mpr (by omega); omega⟩ -
              indexedNameValue Q
                ⟨i.1, by have := i.2; have hf : 0 < Nat.fib (Q + 2) := Nat.fib_pos.mpr (by omega); omega⟩ =
            Real.goldenRatio ^ (-(Q : ℤ)) →
          ∃ j : Fin (Nat.fib (Q + 3)),
            insertedNameIndices Q i = {j} ∧
            indexedNameValue (Q + 1) j -
                indexedNameValue Q
                  ⟨i.1, by have := i.2; have hf : 0 < Nat.fib (Q + 2) := Nat.fib_pos.mpr (by omega); omega⟩ =
              Real.goldenRatio ^ (-((Q + 1 : ℕ) : ℤ)) ∧
            indexedNameValue Q
                  ⟨i.1 + 1, by have := i.2; have hf : 0 < Nat.fib (Q + 2) := Nat.fib_pos.mpr (by omega); omega⟩ -
                indexedNameValue (Q + 1) j =
              Real.goldenRatio ^ (-((Q + 2 : ℕ) : ℤ)))) ∧
    (goldenGridLowerValues = goldenErgodicLowerValues) ∧
    (goldenGridOptimalValue = goldenErgodicOptimalValue) ∧
    (IsGreatest goldenPeriodicOrbitMinimaTwelve goldenThreshold) ∧
    (IsGoldenOrbitGap 6 ((13 / 2 : Real) - 4 * Real.goldenRatio) (1 / 2) (1 / 2)) ∧
    (∀ (k : Nat),
      goldenSurvivor (3 * k + 6) ((13 / 2 : Real) - 4 * Real.goldenRatio) = 1 / 2 ∧
        goldenSurvivor (3 * k + 7) ((13 / 2 : Real) - 4 * Real.goldenRatio) =
          Real.goldenRatio ^ (-2 : Int) / 2 ∧
        goldenSurvivor (3 * k + 8) ((13 / 2 : Real) - 4 * Real.goldenRatio) =
          Real.goldenRatio ^ (-1 : Int) / 2) ∧
    (∀ (F : Set GoldenSurvivorState) (n : Nat),
      goldenBackwardSurvivor F (n + 1) =
        F ∩ goldenTransition ⁻¹' goldenBackwardSurvivor F n) ∧
    (goldenInverse ^ 40 < (5 : Real) / 1000000000) ∧
    (goldenBackwardLimitCore = goldenFourPointSet) ∧
    (Filter.liminf
          (fun Q => goldenSurvivor Q ((13 / 2 : Real) - 4 * Real.goldenRatio)) Filter.atTop =
        Real.goldenRatio ^ (-2 : Int) / 2) ∧
    (((2 - Real.goldenRatio) / 2 : Real) = Real.goldenRatio ^ (-2 : Int) / 2) ∧
    ((13 / 2 : Real) - 4 * Real.goldenRatio =
          (Real.sqrt 5 - 2) ^ 2 / 2 ∧
        (Real.sqrt 5 - 2) ^ 2 / 2 = Real.goldenRatio ^ (-6 : Int) / 2) ∧
    (¬∀ x : Real,
        Filter.liminf (fun Q => goldenSurvivor Q x) Filter.atTop ≤ goldenThreshold) ∧
    (∃ state, (∀ n, state ∈ goldenBackwardSurvivor goldenClosedSurvivorSet n) ∧
        state ∉ goldenFourPointSet) ∧
    (goldenStrictPermanentSet = ∅) :=
  ⟨goldenNameGrid_eq_nameValue_range,
   golden_name_card,
   adjacent_gap_spectrum,
   golden_gap_substitution,
   golden_lower_value_sets_eq,
   golden_optimal_value_eq_ergodic_optimal_value,
   golden_periodic_orbit_maximin_twelve,
   golden_champion_base_gap,
   golden_champion_arm_ring,
   golden_backward_survivor_succ,
   golden_depth_forty_contraction_lt,
   golden_backward_limit_core_eq_four_points,
   golden_champion_liminf,
   golden_asymptotic_value_identity,
   golden_champion_point_identity,
   golden_global_liminf_upper_bound_false,
   golden_closed_permanent_not_four_points,
   golden_strict_permanent_set_eq_empty⟩

end D5.S0.Tower.GoldenClauseTwo
