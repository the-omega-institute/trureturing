/- GID: D5/S0/Asymptotics/EscapeProbability/DiploidDominanceSelectionOrder
   generality: G
   mirror-B: D5/B/S0/Asymptotics/EscapeProbability/DiploidDominanceSelectionOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Diploid dominance changes the rare-allele selection signal from second to first order. -/

import D5.S0.Asymptotics.EscapeProbability.CompletelyRecessiveSelectionOrder

/- Library-search audit trail (2026-08-29):
   * The frozen `CompletelyRecessiveSelectionOrder` family constructs the
     all-recessive fitness model and proves the ploidy-order theorem, but it is
     not an exact owner: the present theorem also covers nonzero dominance.
   * Current-tree name and body-shape searches found no existing diploid
     dominance selection-change primitive or theorem. No `def` or `abbrev` is
     introduced here; the public `let` objects are built from genotype
     frequencies, genotype fitnesses, and normalization.
   * Pinned Mathlib's `AnalyticAt.analyticOrderAt_eq_natCast`,
     `DifferentiableAt.isBigO_sub`, and `IsBigO.mul` provide the local order and
     remainder interfaces and are applied directly. No exact Mathlib theorem
     for this population-selection model was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Asymptotics.EscapeProbability.DiploidDominanceSelectionOrder

open Asymptotics Filter
open scoped Topology

private theorem diploid_change_factorization
    (selection dominance : Real) :
    let meanFitness := fun x : Real =>
      (1 - x) ^ 2 + 2 * (1 - x) * x * (1 - dominance * selection) +
        x ^ 2 * (1 - selection)
    let selectedAlleleMass := fun x : Real =>
      x ^ 2 * (1 - selection) + (1 - x) * x * (1 - dominance * selection)
    let selectionChange := fun x : Real => selectedAlleleMass x / meanFitness x - x
    let leadingFactor := fun x : Real =>
      -selection * (1 - x) * (dominance * (1 - x) + (1 - dominance) * x) /
        meanFitness x
    selectionChange =ᶠ[𝓝 0] fun x => x * leadingFactor x := by
  dsimp
  have meanFitnessAnalytic : AnalyticAt Real
      (fun x : Real =>
        (1 - x) ^ 2 + 2 * (1 - x) * x * (1 - dominance * selection) +
          x ^ 2 * (1 - selection)) 0 := by
    fun_prop
  have meanFitnessAtZero :
      (1 - (0 : Real)) ^ 2 +
          2 * (1 - 0) * 0 * (1 - dominance * selection) +
          0 ^ 2 * (1 - selection) ≠ 0 := by
    norm_num
  filter_upwards [meanFitnessAnalytic.continuousAt.eventually_ne meanFitnessAtZero]
      with x meanFitnessNe
  ring_nf at meanFitnessNe ⊢
  field_simp [meanFitnessNe]
  ring

private theorem recessive_change_factorization
    (selection : Real) :
    let meanFitness := fun x : Real =>
      (1 - x) ^ 2 + 2 * (1 - x) * x * (1 - 0 * selection) +
        x ^ 2 * (1 - selection)
    let selectedAlleleMass := fun x : Real =>
      x ^ 2 * (1 - selection) + (1 - x) * x * (1 - 0 * selection)
    let selectionChange := fun x : Real => selectedAlleleMass x / meanFitness x - x
    let leadingFactor := fun x : Real =>
      -selection * (1 - x) / meanFitness x
    selectionChange =ᶠ[𝓝 0] fun x => x ^ 2 * leadingFactor x := by
  dsimp
  have meanFitnessAnalytic : AnalyticAt Real
      (fun x : Real =>
        (1 - x) ^ 2 + 2 * (1 - x) * x * (1 - 0 * selection) +
          x ^ 2 * (1 - selection)) 0 := by
    fun_prop
  have meanFitnessAtZero :
      (1 - (0 : Real)) ^ 2 + 2 * (1 - 0) * 0 * (1 - 0 * selection) +
          0 ^ 2 * (1 - selection) ≠ 0 := by
    norm_num
  filter_upwards [meanFitnessAnalytic.continuousAt.eventually_ne meanFitnessAtZero]
      with x meanFitnessNe
  ring_nf at meanFitnessNe ⊢
  field_simp [meanFitnessNe]
  ring

private theorem recessive_change_remainder_isBigO
    (selection : Real) :
    let meanFitness := fun x : Real =>
      (1 - x) ^ 2 + 2 * (1 - x) * x * (1 - 0 * selection) +
        x ^ 2 * (1 - selection)
    let selectedAlleleMass := fun x : Real =>
      x ^ 2 * (1 - selection) + (1 - x) * x * (1 - 0 * selection)
    let selectionChange := fun x : Real => selectedAlleleMass x / meanFitness x - x
    (fun x => selectionChange x - (-selection * x ^ 2))
      =O[𝓝 0] fun x : Real => x ^ 3 := by
  dsimp
  let meanFitness := fun x : Real =>
    (1 - x) ^ 2 + 2 * (1 - x) * x * (1 - 0 * selection) +
      x ^ 2 * (1 - selection)
  let selectionChange := fun x : Real =>
    (x ^ 2 * (1 - selection) + (1 - x) * x * (1 - 0 * selection)) /
      meanFitness x - x
  let leadingFactor := fun x : Real => -selection * (1 - x) / meanFitness x
  have meanFitnessAtZero : meanFitness 0 ≠ 0 := by
    simp [meanFitness]
  have factorAnalytic : AnalyticAt Real leadingFactor 0 := by
    dsimp [leadingFactor, meanFitness]
    apply AnalyticAt.div
    · fun_prop
    · fun_prop
    · exact meanFitnessAtZero
  have factorDifference :
      (fun x => leadingFactor x - leadingFactor 0)
        =O[𝓝 0] fun x : Real => x - 0 :=
    factorAnalytic.differentiableAt.isBigO_sub
  have productBound :=
    (_root_.Asymptotics.isBigO_refl (fun x : Real => x ^ 2) (𝓝 0)).mul
      factorDifference
  have factorization := recessive_change_factorization selection
  refine productBound.congr' ?_ ?_
  · filter_upwards [factorization] with x factorizationAtX
    have localFactorization : selectionChange x = x ^ 2 * leadingFactor x := by
      simpa [selectionChange, leadingFactor, meanFitness] using factorizationAtX
    change x ^ 2 * (leadingFactor x - leadingFactor 0) =
      selectionChange x - (-selection * x ^ 2)
    rw [localFactorization]
    simp [leadingFactor, meanFitness]
    ring
  · filter_upwards [] with x
    ring

private theorem diploid_change_remainder_isBigO
    (selection dominance : Real) :
    let meanFitness := fun x : Real =>
      (1 - x) ^ 2 + 2 * (1 - x) * x * (1 - dominance * selection) +
        x ^ 2 * (1 - selection)
    let selectedAlleleMass := fun x : Real =>
      x ^ 2 * (1 - selection) + (1 - x) * x * (1 - dominance * selection)
    let selectionChange := fun x : Real => selectedAlleleMass x / meanFitness x - x
    (fun x => selectionChange x - (-(dominance * selection) * x))
      =O[𝓝 0] fun x : Real => x ^ 2 := by
  dsimp
  let meanFitness := fun x : Real =>
    (1 - x) ^ 2 + 2 * (1 - x) * x * (1 - dominance * selection) +
      x ^ 2 * (1 - selection)
  let selectionChange := fun x : Real =>
    (x ^ 2 * (1 - selection) +
          (1 - x) * x * (1 - dominance * selection)) /
      meanFitness x - x
  let leadingFactor := fun x : Real =>
    -selection * (1 - x) * (dominance * (1 - x) + (1 - dominance) * x) /
      meanFitness x
  have meanFitnessAtZero : meanFitness 0 ≠ 0 := by
    simp [meanFitness]
  have factorAnalytic : AnalyticAt Real leadingFactor 0 := by
    dsimp [leadingFactor, meanFitness]
    apply AnalyticAt.div
    · fun_prop
    · fun_prop
    · exact meanFitnessAtZero
  have factorDifference :
      (fun x => leadingFactor x - leadingFactor 0)
        =O[𝓝 0] fun x : Real => x - 0 :=
    factorAnalytic.differentiableAt.isBigO_sub
  have productBound :=
    (_root_.Asymptotics.isBigO_refl (fun x : Real => x) (𝓝 0)).mul
      factorDifference
  have factorization := diploid_change_factorization selection dominance
  refine productBound.congr' ?_ ?_
  · filter_upwards [factorization] with x factorizationAtX
    have localFactorization : selectionChange x = x * leadingFactor x := by
      simpa [selectionChange, leadingFactor, meanFitness] using factorizationAtX
    change x * (leadingFactor x - leadingFactor 0) =
      selectionChange x - (-(dominance * selection) * x)
    rw [localFactorization]
    simp [leadingFactor, meanFitness]
    ring
  · filter_upwards [] with x
    ring

private theorem recessive_change_analytic_order
    (selection : Real) (selectionNe : selection ≠ 0) :
    let meanFitness := fun x : Real =>
      (1 - x) ^ 2 + 2 * (1 - x) * x * (1 - 0 * selection) +
        x ^ 2 * (1 - selection)
    let selectedAlleleMass := fun x : Real =>
      x ^ 2 * (1 - selection) + (1 - x) * x * (1 - 0 * selection)
    let selectionChange := fun x : Real => selectedAlleleMass x / meanFitness x - x
    analyticOrderAt selectionChange 0 = 2 := by
  dsimp
  let meanFitness := fun x : Real =>
    (1 - x) ^ 2 + 2 * (1 - x) * x * (1 - 0 * selection) +
      x ^ 2 * (1 - selection)
  let selectionChange := fun x : Real =>
    (x ^ 2 * (1 - selection) + (1 - x) * x * (1 - 0 * selection)) /
      meanFitness x - x
  let leadingFactor := fun x : Real => -selection * (1 - x) / meanFitness x
  have meanFitnessAtZero : meanFitness 0 ≠ 0 := by
    simp [meanFitness]
  have changeAnalytic : AnalyticAt Real selectionChange 0 := by
    dsimp [selectionChange, meanFitness]
    apply AnalyticAt.sub
    · apply AnalyticAt.div
      · fun_prop
      · fun_prop
      · exact meanFitnessAtZero
    · fun_prop
  have factorAnalytic : AnalyticAt Real leadingFactor 0 := by
    dsimp [leadingFactor, meanFitness]
    apply AnalyticAt.div
    · fun_prop
    · fun_prop
    · exact meanFitnessAtZero
  apply changeAnalytic.analyticOrderAt_eq_natCast.mpr
  refine ⟨leadingFactor, factorAnalytic, ?_, ?_⟩
  · simp [leadingFactor, meanFitness, selectionNe]
  · filter_upwards [recessive_change_factorization selection] with x factorizationAtX
    simpa [selectionChange, leadingFactor, meanFitness, sub_zero, smul_eq_mul]
      using factorizationAtX

private theorem diploid_change_analytic_order
    (selection dominance : Real) (productNe : dominance * selection ≠ 0) :
    let meanFitness := fun x : Real =>
      (1 - x) ^ 2 + 2 * (1 - x) * x * (1 - dominance * selection) +
        x ^ 2 * (1 - selection)
    let selectedAlleleMass := fun x : Real =>
      x ^ 2 * (1 - selection) + (1 - x) * x * (1 - dominance * selection)
    let selectionChange := fun x : Real => selectedAlleleMass x / meanFitness x - x
    analyticOrderAt selectionChange 0 = 1 := by
  dsimp
  let meanFitness := fun x : Real =>
    (1 - x) ^ 2 + 2 * (1 - x) * x * (1 - dominance * selection) +
      x ^ 2 * (1 - selection)
  let selectionChange := fun x : Real =>
    (x ^ 2 * (1 - selection) +
          (1 - x) * x * (1 - dominance * selection)) /
      meanFitness x - x
  let leadingFactor := fun x : Real =>
    -selection * (1 - x) * (dominance * (1 - x) + (1 - dominance) * x) /
      meanFitness x
  have meanFitnessAtZero : meanFitness 0 ≠ 0 := by
    simp [meanFitness]
  have changeAnalytic : AnalyticAt Real selectionChange 0 := by
    dsimp [selectionChange, meanFitness]
    apply AnalyticAt.sub
    · apply AnalyticAt.div
      · fun_prop
      · fun_prop
      · exact meanFitnessAtZero
    · fun_prop
  have factorAnalytic : AnalyticAt Real leadingFactor 0 := by
    dsimp [leadingFactor, meanFitness]
    apply AnalyticAt.div
    · fun_prop
    · fun_prop
    · exact meanFitnessAtZero
  apply changeAnalytic.analyticOrderAt_eq_natCast.mpr
  refine ⟨leadingFactor, factorAnalytic, ?_, ?_⟩
  · have selectionNe : selection ≠ 0 := fun h => productNe (by simp [h])
    have dominanceNe : dominance ≠ 0 := fun h => productNe (by simp [h])
    simp [leadingFactor, meanFitness, selectionNe, dominanceNe]
  · filter_upwards [diploid_change_factorization selection dominance]
      with x factorizationAtX
    simpa [selectionChange, leadingFactor, sub_zero, smul_eq_mul] using factorizationAtX

/-- In the diploid selection model, a completely recessive deleterious allele
has a quadratic rare-frequency signal, while nonzero dominance exposes a
linear signal. -/
theorem diploid_dominance_selection_order
    (selection dominance : Real) (selectionNe : selection ≠ 0) :
    let meanFitness := fun (h x : Real) =>
      (1 - x) ^ 2 + 2 * (1 - x) * x * (1 - h * selection) +
        x ^ 2 * (1 - selection)
    let selectedAlleleMass := fun (h x : Real) =>
      x ^ 2 * (1 - selection) + (1 - x) * x * (1 - h * selection)
    let updatedFrequency := fun (h x : Real) =>
      selectedAlleleMass h x / meanFitness h x
    let selectionChange := fun (h x : Real) => updatedFrequency h x - x
    (∀ x, meanFitness 0 x ≠ 0 ->
      selectionChange 0 x =
        -(selection * (1 - x) * x ^ 2) / (1 - selection * x ^ 2)) /\
    (fun x => selectionChange 0 x - (-selection * x ^ 2))
      =O[𝓝 0] (fun x => x ^ 3) /\
    analyticOrderAt (selectionChange 0) 0 = 2 /\
    (fun x => selectionChange dominance x - (-(dominance * selection) * x))
      =O[𝓝 0] (fun x => x ^ 2) /\
    (dominance * selection ≠ 0 ->
      analyticOrderAt (selectionChange dominance) 0 = 1) := by
  dsimp
  refine ⟨?_, recessive_change_remainder_isBigO selection,
    recessive_change_analytic_order selection selectionNe,
    diploid_change_remainder_isBigO selection dominance, ?_⟩
  · intro x meanFitnessNe
    ring_nf at meanFitnessNe ⊢
    field_simp [meanFitnessNe]
    ring
  · exact diploid_change_analytic_order selection dominance

#print axioms diploid_dominance_selection_order

end D5.S0.Asymptotics.EscapeProbability.DiploidDominanceSelectionOrder
