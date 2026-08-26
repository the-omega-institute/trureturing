/- GID: D5/S0/Asymptotics/EscapeProbability/CompletelyRecessiveSelectionOrder
   generality: G
   mirror-B: D5/B/S0/Asymptotics/EscapeProbability/CompletelyRecessiveSelectionOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Completely recessive selection first appears at the ploidy order. -/

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Asymptotics.Lemmas

/- Library-search audit trail (2026-08-27):
   * Current-tree searches for ploidy, recessive selection, mean fitness, and
     selection-order formulas found no matching biological carrier or theorem.
   * Pinned Mathlib's `analyticOrderAt` and
     `AnalyticAt.analyticOrderAt_eq_natCast` provide the canonical exact
     vanishing-order carrier; they are used directly.
   * Pinned Mathlib's `DifferentiableAt.isBigO_sub`, `IsBigO.mul`, and
     `Asymptotics.isLittleO_pow_pow` provide the local asymptotic interface.
   * No new `def` or `abbrev` is introduced. The public local constructions use
     the source's two fitness classes and all-recessive frequency. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Asymptotics.EscapeProbability.CompletelyRecessiveSelectionOrder

open Filter Set
open scoped Topology
open Asymptotics

private theorem mean_fitness_ne_zero
    {ploidy : Nat} (positivePloidy : 1 ≤ ploidy) {selection frequency : Real}
    (selectionRange : selection ∈ Ioc (0 : Real) 1)
    (frequencyRange : frequency ∈ Icc (0 : Real) 1)
    (nondegenerate : selection < 1 ∨ frequency < 1) :
    1 - selection * frequency ^ ploidy ≠ 0 := by
  have ploidyNe : ploidy ≠ 0 := by omega
  have frequencyPowerNonneg : 0 ≤ frequency ^ ploidy :=
    pow_nonneg frequencyRange.1 ploidy
  have frequencyPowerLe : frequency ^ ploidy ≤ 1 :=
    pow_le_one₀ frequencyRange.1 frequencyRange.2
  have selectedPowerLt : selection * frequency ^ ploidy < 1 := by
    rcases nondegenerate with selectionLt | frequencyLt
    · exact mul_lt_one_of_nonneg_of_lt_one_left selectionRange.1.le selectionLt
        frequencyPowerLe
    · exact mul_lt_one_of_nonneg_of_lt_one_right selectionRange.2
        frequencyPowerNonneg
        (pow_lt_one₀ frequencyRange.1 frequencyLt ploidyNe)
  exact (sub_pos.mpr selectedPowerLt).ne'

private theorem selection_change_factorization
    (ploidy : Nat) (positivePloidy : 1 ≤ ploidy) (selection : Real) :
    let change := fun frequency : Real =>
      (frequency - selection * frequency ^ ploidy) /
          (1 - selection * frequency ^ ploidy) - frequency
    let leadingFactor := fun frequency : Real =>
      -selection * (1 - frequency) /
        (1 - selection * frequency ^ ploidy)
    change =ᶠ[𝓝 0] fun frequency => frequency ^ ploidy * leadingFactor frequency := by
  dsimp
  have ploidyNe : ploidy ≠ 0 := by omega
  have denominatorAnalytic :
      AnalyticAt Real (fun frequency : Real =>
        1 - selection * frequency ^ ploidy) 0 := by
    fun_prop
  have denominatorAtZero :
      (1 - selection * (0 : Real) ^ ploidy) ≠ 0 := by
    simp [ploidyNe]
  filter_upwards [denominatorAnalytic.continuousAt.eventually_ne denominatorAtZero]
      with frequency denominatorNe
  field_simp
  ring

private theorem selection_change_analytic_order
    (ploidy : Nat) (positivePloidy : 1 ≤ ploidy) (selection : Real)
    (selectionNe : selection ≠ 0) :
    analyticOrderAt
        (fun frequency : Real =>
          (frequency - selection * frequency ^ ploidy) /
              (1 - selection * frequency ^ ploidy) - frequency)
        0 = ploidy := by
  have ploidyNe : ploidy ≠ 0 := by omega
  let change := fun frequency : Real =>
    (frequency - selection * frequency ^ ploidy) /
        (1 - selection * frequency ^ ploidy) - frequency
  let leadingFactor := fun frequency : Real =>
    -selection * (1 - frequency) /
      (1 - selection * frequency ^ ploidy)
  have denominatorAtZero :
      (1 - selection * (0 : Real) ^ ploidy) ≠ 0 := by
    simp [ploidyNe]
  have changeAnalytic : AnalyticAt Real change 0 := by
    dsimp [change]
    apply AnalyticAt.sub
    · apply AnalyticAt.div
      · fun_prop
      · fun_prop
      · exact denominatorAtZero
    · fun_prop
  have factorAnalytic : AnalyticAt Real leadingFactor 0 := by
    dsimp [leadingFactor]
    apply AnalyticAt.div
    · fun_prop
    · fun_prop
    · exact denominatorAtZero
  apply changeAnalytic.analyticOrderAt_eq_natCast.mpr
  refine ⟨leadingFactor, factorAnalytic, ?_, ?_⟩
  · simp [leadingFactor, ploidyNe, selectionNe]
  · filter_upwards [selection_change_factorization ploidy positivePloidy selection]
      with frequency factorization
    simpa [change, leadingFactor, sub_zero, smul_eq_mul] using factorization

private theorem selection_change_remainder_isBigO
    (ploidy : Nat) (positivePloidy : 1 ≤ ploidy) (selection : Real) :
    (fun frequency : Real =>
      ((frequency - selection * frequency ^ ploidy) /
          (1 - selection * frequency ^ ploidy) - frequency) -
        (-selection * frequency ^ ploidy))
      =O[𝓝 0] fun frequency : Real => frequency ^ (ploidy + 1) := by
  have ploidyNe : ploidy ≠ 0 := by omega
  let change := fun frequency : Real =>
    (frequency - selection * frequency ^ ploidy) /
        (1 - selection * frequency ^ ploidy) - frequency
  let leadingFactor := fun frequency : Real =>
    -selection * (1 - frequency) /
      (1 - selection * frequency ^ ploidy)
  have denominatorAtZero :
      (1 - selection * (0 : Real) ^ ploidy) ≠ 0 := by
    simp [ploidyNe]
  have factorAnalytic : AnalyticAt Real leadingFactor 0 := by
    dsimp [leadingFactor]
    apply AnalyticAt.div
    · fun_prop
    · fun_prop
    · exact denominatorAtZero
  have factorDifference :
      (fun frequency => leadingFactor frequency - leadingFactor 0)
        =O[𝓝 0] fun frequency : Real => frequency - 0 :=
    factorAnalytic.differentiableAt.isBigO_sub
  have productBound :=
    (_root_.Asymptotics.isBigO_refl
      (fun frequency : Real => frequency ^ ploidy) (𝓝 0)).mul
      factorDifference
  have changeFactorization :=
    selection_change_factorization ploidy positivePloidy selection
  refine productBound.congr' ?_ ?_
  · filter_upwards [changeFactorization] with frequency factorization
    rw [factorization]
    simp [leadingFactor, ploidyNe]
    ring
  · filter_upwards [] with frequency
    simp [pow_succ]

private theorem constructed_selection_change_eq
    (ploidy : Nat) (selection : Real) :
    (fun frequency : Real =>
      ((frequency - frequency ^ ploidy) * 1 +
            frequency ^ ploidy * (1 - selection)) /
          ((1 - frequency ^ ploidy) * 1 +
            frequency ^ ploidy * (1 - selection)) - frequency) =
      fun frequency : Real =>
        (frequency - selection * frequency ^ ploidy) /
            (1 - selection * frequency ^ ploidy) - frequency := by
  funext frequency
  congr 1
  ring

/-- In the two-fitness-class completely recessive model, the mean fitness,
selected frequency, exact change, local remainder, and exact selection order
are all determined by the ploidy. Higher ploidy strictly raises that order. -/
theorem completely_recessive_selection_order
    (ploidy : Nat) (positivePloidy : 1 ≤ ploidy)
    (selection frequency : Real)
    (selectionRange : selection ∈ Ioc (0 : Real) 1)
    (frequencyRange : frequency ∈ Icc (0 : Real) 1)
    (nondegenerate : selection < 1 ∨ frequency < 1) :
    let allRecessiveFrequency := fun (level : Nat) (x : Real) => x ^ level
    let meanFitness := fun (level : Nat) (x : Real) =>
      (1 - allRecessiveFrequency level x) * 1 +
        allRecessiveFrequency level x * (1 - selection)
    let selectedAlleleMass := fun (level : Nat) (x : Real) =>
      (x - allRecessiveFrequency level x) * 1 +
        allRecessiveFrequency level x * (1 - selection)
    let updatedFrequency := fun (level : Nat) (x : Real) =>
      selectedAlleleMass level x / meanFitness level x
    let selectionChange := fun (level : Nat) (x : Real) =>
      updatedFrequency level x - x
    meanFitness ploidy frequency = 1 - selection * frequency ^ ploidy /\
      updatedFrequency ploidy frequency =
        (frequency - selection * frequency ^ ploidy) /
          (1 - selection * frequency ^ ploidy) /\
      selectionChange ploidy frequency =
        -(selection * frequency ^ ploidy * (1 - frequency)) /
          (1 - selection * frequency ^ ploidy) /\
      (fun x => selectionChange ploidy x - (-selection * x ^ ploidy))
        =O[𝓝 0] (fun x => x ^ (ploidy + 1)) /\
      analyticOrderAt (selectionChange ploidy) 0 = ploidy /\
      ∀ higherPloidy, ploidy < higherPloidy ->
        analyticOrderAt (selectionChange ploidy) 0 <
          analyticOrderAt (selectionChange higherPloidy) 0 := by
  dsimp
  have denominatorNe : 1 - selection * frequency ^ ploidy ≠ 0 :=
    mean_fitness_ne_zero positivePloidy selectionRange frequencyRange nondegenerate
  refine ⟨by ring, by ring, ?_, ?_, ?_, ?_⟩
  · rw [congrFun (constructed_selection_change_eq ploidy selection) frequency]
    field_simp [denominatorNe]
    ring
  · refine (selection_change_remainder_isBigO ploidy positivePloidy selection).congr' ?_ .rfl
    filter_upwards [] with x
    exact congrArg (fun value => value - (-selection * x ^ ploidy))
      (congrFun (constructed_selection_change_eq ploidy selection) x).symm
  · rw [constructed_selection_change_eq ploidy selection]
    exact selection_change_analytic_order ploidy positivePloidy selection
      selectionRange.1.ne'
  · intro higherPloidy higher
    rw [constructed_selection_change_eq ploidy selection,
      constructed_selection_change_eq higherPloidy selection,
      selection_change_analytic_order ploidy positivePloidy selection
        selectionRange.1.ne',
      selection_change_analytic_order higherPloidy
        (le_trans positivePloidy (Nat.le_of_lt higher)) selection
        selectionRange.1.ne']
    exact_mod_cast higher

#print axioms completely_recessive_selection_order

end D5.S0.Asymptotics.EscapeProbability.CompletelyRecessiveSelectionOrder
