/- GID: D5/S0/Tower/NonPisotVerdict/SubstitutionTowerClause
   generality: I
   mirror-B: D5/B/S0/Tower/NonPisotVerdict/SubstitutionTowerClause
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The substitution-tower clause, its nine assertions conjoined including the false one. -/

import D5.S0.Tower.DBonacci.Substitution
import D5.S0.Tower.DBonacciGeneral.ChampionLimit
import D5.S0.Tower.ErgodicBridge.General
import D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenAggregate
import D5.S0.Tower.NonPisotVerdict.NotEventuallyPeriodic
import D5.S0.Tower.NonPisot.GapCounts
import D5.S0.Tower.TribonacciSurvivors.StrictFiniteDepth

/- Library-search audit trail (2026-08-18):
   * Nothing new is proved here.  Every conjunct is an existing theorem, located
     by reading the source clause sentence by sentence and searching for the
     object each one names.  Six of the nine were already in the tree before this
     session; three were added during it.
   * The two parameterised conjuncts are quantified rather than instantiated, so
     the package is not weaker than the sentences it stands for.
   * One sentence of the clause is false.  It is represented by the theorem that
     refutes it at the very depth it names, not by a weakened restatement. -/

namespace D5.S0.Tower.NonPisotVerdict.SubstitutionTowerClause

open D5.S0.Tower.DBonacci.Substitution
open D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacci.PerronRoot
open D5.S0.Tower.DBonacci.Values
open D5.S0.Tower.DBonacci.Gaps
open D5.S0.Tower.DBonacciGeneral.ChampionValue
open D5.S0.Tower.DBonacciGeneral.ChampionLimit
open D5.S0.Tower.ErgodicBridge.General
open D5.S0.Tower.NonPisot.GapCounts
open D5.S0.Tower.NonPisot.Beta13Infinite
open D5.S0.Tower.TribonacciSurvivors.TribonacciPermanentSurvivors
open D5.S0.Tower.NonPisotVerdict.NotEventuallyPeriodic
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenAggregate
open D5.S0.Tower.TribonacciSurvivors.StrictFiniteDepth

open Filter Topology

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant
local notation "phi" => Real.goldenRatio

/-- The gap refinement of a d-bonacci tower is that tower's own substitution, at
every arity and window.

The conclusion is transcribed in full from the theorem it quantifies.  Two
shortcuts were tried first and both were wrong in the same direction: replacing
one branch of the `match` with `True`, and stating `id x = x`, which type-checks
while asserting nothing.  A conjunct that is weaker than its sentence, or that is
vacuous, makes the package claim less than the clause it stands for. -/
theorem clause_gap_refinement_is_the_substitution :
    ∀ (d Q : Nat), 2 ≤ d → ∀ i : Fin (dbonacci d (Q + 2) - 1),
      ∃ label ∈ Finset.Ico (d - Q) d,
        indexedNameValue d Q (gapRight d Q i) - indexedNameValue d Q (gapLeft d Q i) =
            dbonacciGapLength d Q label ∧
          match label with
          | 0 =>
              insertedNameIndices d Q i = ∅ ∧
                indexedNameValue d (Q + 1) (levelEmbedding d Q (gapRight d Q i)) -
                    indexedNameValue d (Q + 1) (levelEmbedding d Q (gapLeft d Q i)) =
                  dbonacciGapLength d (Q + 1) (d - 1)
          | fuel + 1 =>
              ∃ j,
                insertedNameIndices d Q i = {j} ∧
                  indexedNameValue d (Q + 1) j -
                      indexedNameValue d Q (gapLeft d Q i) =
                    dbonacciGapLength d (Q + 1) (d - 1) ∧
                    indexedNameValue d Q (gapRight d Q i) -
                        indexedNameValue d (Q + 1) j =
                      dbonacciGapLength d (Q + 1) fuel :=
  fun d Q hd i => dbonacci_gap_substitution d Q hd i

/-- The champion of a d-bonacci tower is the ergodic optimisation solution of the
corresponding piecewise-linear expanding map. -/
theorem clause_champion_is_the_ergodic_optimum :
    ∀ (d : Nat) (hd : 2 ≤ d) (bridge : DBonacciErgodicBridge d hd),
      gridOptimalValue bridge = ergodicOptimalValue bridge :=
  fun _ _ bridge => optimal_value_eq_ergodic_optimal_value bridge

/-- The first-draft formula agrees with the corrected champion value exactly on
roots of the Tribonacci cubic, which is why it survived at arity three and was
judged negative at four and five. -/
theorem clause_initial_formula_holds_only_on_the_cubic :
    ∀ beta : Real, 1 < beta →
      ((1 - beta⁻¹) / 2 = championValue beta ↔ beta ^ 3 = beta ^ 2 + beta + 1) :=
  fun _ hbeta => initialFormula_eq_championValue_iff hbeta

/-- The champion value at the Tribonacci constant, in closed form. -/
theorem clause_champion_value_at_tribonacci : championValue t = (1 - t⁻¹) / 2 :=
  championValue_tribonacciConstant

/-- At arity two the numerator vanishes, so the corrected formula degenerates
exactly there. -/
theorem clause_numerator_vanishes_at_golden : championValue phi = 0 :=
  championValue_goldenRatio

/-- The champion value tends to one third at the integer-tower boundary. -/
theorem clause_boundary_continuity :
    Tendsto (fun d : Nat => championValue (dbonacciPerronRoot d)) atTop (nhds (1 / 3)) :=
  championValue_tendsto_one_third

/-- The clause asserts that the strict forbidden region empties by depth sixty.
It does not: the backward survivor set at that very depth is nonempty. -/
theorem clause_depth_sixty_claim_is_false :
    (tribonacciBackwardSurvivor tribonacciStrictSurvivorSet 60).Nonempty :=
  tribonacci_strict_backward_survivor_sixty_nonempty

/-- Past the Pisot boundary the normalised gap-type count grows with the window,
measured here at window six.

The spectrum is named with its full path deliberately: two modules define
`beta13NormalizedGapSpectrum` with the same signature but different underlying
value maps, `beta13CodeValue` in one and `beta13GapCodeValue` in the other.  A
module that opens both gets an ambiguity error; one that opens only the other
gets a different function under the same name and no warning at all. -/
theorem clause_gap_types_grow_past_the_boundary :
    (D5.S0.Tower.NonPisot.GapCounts.beta13NormalizedGapSpectrum 6).card = 6 :=
  beta13_normalized_gap_type_count_six

/-- And the structural half: the greedy expansion of one at that base is not
eventually periodic, so no finite-type substitution structure describes it. -/
theorem clause_frontier_expansion_is_aperiodic :
    ¬ ∃ p N : Nat, 0 < p ∧
      ∀ n, N ≤ n → beta13GreedyDigit (n + p) = beta13GreedyDigit n :=
  digits_not_eventually_periodic

/-- The substitution-tower clause, its assertions conjoined.

Eight of the nine sentences appear here; the ninth, that the affine fixed-point
enumeration up to period eleven exhibits the optimal cycle, is added once its
aggregate lands.  One conjunct is the refutation of a false sentence rather than
that sentence: the clause claims the strict forbidden region empties by depth
sixty, and it does not.

Nothing in this module is proved for the first time.  Its content is that these
statements, which live in eight different modules, are all true together and
stand for one clause of the source. -/
theorem substitution_tower_clause :
    (∀ (d Q : Nat), 2 ≤ d → ∀ i : Fin (dbonacci d (Q + 2) - 1),
        ∃ label ∈ Finset.Ico (d - Q) d,
          indexedNameValue d Q (gapRight d Q i) - indexedNameValue d Q (gapLeft d Q i) =
              dbonacciGapLength d Q label ∧
            match label with
            | 0 =>
                insertedNameIndices d Q i = ∅ ∧
                  indexedNameValue d (Q + 1) (levelEmbedding d Q (gapRight d Q i)) -
                      indexedNameValue d (Q + 1) (levelEmbedding d Q (gapLeft d Q i)) =
                    dbonacciGapLength d (Q + 1) (d - 1)
            | fuel + 1 =>
                ∃ j,
                  insertedNameIndices d Q i = {j} ∧
                    indexedNameValue d (Q + 1) j -
                        indexedNameValue d Q (gapLeft d Q i) =
                      dbonacciGapLength d (Q + 1) (d - 1) ∧
                      indexedNameValue d Q (gapRight d Q i) -
                          indexedNameValue d (Q + 1) j =
                        dbonacciGapLength d (Q + 1) fuel) ∧
      (∀ (d : Nat) (hd : 2 ≤ d) (bridge : DBonacciErgodicBridge d hd),
          gridOptimalValue bridge = ergodicOptimalValue bridge) ∧
      (∀ beta : Real, 1 < beta →
          ((1 - beta⁻¹) / 2 = championValue beta ↔ beta ^ 3 = beta ^ 2 + beta + 1)) ∧
      championValue t = (1 - t⁻¹) / 2 ∧
      championValue phi = 0 ∧
      Tendsto (fun d : Nat => championValue (dbonacciPerronRoot d)) atTop (nhds (1 / 3)) ∧
      (tribonacciBackwardSurvivor tribonacciStrictSurvivorSet 60).Nonempty ∧
      (D5.S0.Tower.NonPisot.GapCounts.beta13NormalizedGapSpectrum 6).card = 6 ∧
      ¬ ∃ p N : Nat, 0 < p ∧
        ∀ n, N ≤ n → beta13GreedyDigit (n + p) = beta13GreedyDigit n :=
  ⟨clause_gap_refinement_is_the_substitution,
    clause_champion_is_the_ergodic_optimum,
    clause_initial_formula_holds_only_on_the_cubic,
    clause_champion_value_at_tribonacci,
    clause_numerator_vanishes_at_golden,
    clause_boundary_continuity,
    clause_depth_sixty_claim_is_false,
    clause_gap_types_grow_past_the_boundary,
    clause_frontier_expansion_is_aperiodic⟩

end D5.S0.Tower.NonPisotVerdict.SubstitutionTowerClause
