/- GID: D5/S3/Estimation/DataProcessing/MeasurableDescentErrorBounds
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/MeasurableDescentErrorBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Best measurable descent error lies between half and all of the observable defect. -/

import D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

/- Library-search audit trail (2026-08-28):
   * `DescentDefectBounds` is finite-carrier only: it uses stochastic matrices,
     `Finset.sup'`, and finite half-L1 total variation, so it is not an exact hit.
   * Repository name and body-shape searches found the canonical arbitrary-law
     primitives `measurableTotalVariation` and `observableKernelDefect` in the
     imported measurable postprocessing module. They are reused here.
   * Pinned Mathlib supplies `Kernel.map`, `Kernel.comap`, their Markov instances,
     complete-lattice suprema and infima, and ordered truncated-subtraction laws,
     but no packaged best-descent-error bound at this generality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DataProcessing.MeasurableDescentErrorBounds

open MeasureTheory ProbabilityTheory
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

/-- The uniform error of a candidate measurable Markov descent kernel. -/
noncomputable def measurableDescentError
    {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    (K : Kernel X X) (q : X -> B) (Kbar : Kernel B B) : ENNReal :=
  ⨆ x, measurableTotalVariation ((Kernel.map K q) x) (Kbar (q x))

/-- The infimum of the uniform descent error over Markov kernels on the
observable carrier. -/
noncomputable def bestMeasurableDescentError
    {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    (K : Kernel X X) (q : X -> B) : ENNReal :=
  ⨅ candidate : {Kbar : Kernel B B // IsMarkovKernel Kbar},
    measurableDescentError K q candidate.1

private theorem measurable_total_variation_comm
    {A : Type*} [MeasurableSpace A] (mu nu : Measure A) :
    measurableTotalVariation mu nu = measurableTotalVariation nu mu := by
  simp only [measurableTotalVariation, max_comm]

private theorem measurable_total_variation_triangle
    {A : Type*} [MeasurableSpace A] (mu nu rho : Measure A) :
    measurableTotalVariation mu rho <=
      measurableTotalVariation mu nu + measurableTotalVariation nu rho := by
  unfold measurableTotalVariation
  refine iSup_le fun event => ?_
  have hmunu :
      max (mu event.1 - nu event.1) (nu event.1 - mu event.1) <=
        ⨆ candidate : {event : Set A // MeasurableSet event},
          max (mu candidate.1 - nu candidate.1) (nu candidate.1 - mu candidate.1) :=
    le_iSup (fun candidate : {event : Set A // MeasurableSet event} =>
      max (mu candidate.1 - nu candidate.1) (nu candidate.1 - mu candidate.1)) event
  have hnurho :
      max (nu event.1 - rho event.1) (rho event.1 - nu event.1) <=
        ⨆ candidate : {event : Set A // MeasurableSet event},
          max (nu candidate.1 - rho candidate.1) (rho candidate.1 - nu candidate.1) :=
    le_iSup (fun candidate : {event : Set A // MeasurableSet event} =>
      max (nu candidate.1 - rho candidate.1) (rho candidate.1 - nu candidate.1)) event
  apply max_le
  · calc
      mu event.1 - rho event.1 <=
          (mu event.1 - nu event.1) + (nu event.1 - rho event.1) :=
        tsub_le_tsub_add_tsub
      _ <= _ := add_le_add
        (le_max_left _ _ |>.trans hmunu) (le_max_left _ _ |>.trans hnurho)
  · calc
      rho event.1 - mu event.1 <=
          (rho event.1 - nu event.1) + (nu event.1 - mu event.1) :=
        tsub_le_tsub_add_tsub
      _ <= (⨆ candidate : {event : Set A // MeasurableSet event},
              max (nu candidate.1 - rho candidate.1)
                (rho candidate.1 - nu candidate.1)) +
            ⨆ candidate : {event : Set A // MeasurableSet event},
              max (mu candidate.1 - nu candidate.1)
                (nu candidate.1 - mu candidate.1) := add_le_add
        (le_max_right _ _ |>.trans hnurho) (le_max_right _ _ |>.trans hmunu)
      _ = _ := add_comm _ _

private theorem observable_kernel_defect_le_two_mul_error
    {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    (K : Kernel X X) (q : X -> B) (Kbar : Kernel B B) :
    observableKernelDefect K q <= 2 * measurableDescentError K q Kbar := by
  unfold observableKernelDefect
  refine iSup_le fun pair => ?_
  have hx :
      measurableTotalVariation ((Kernel.map K q) pair.1.1) (Kbar (q pair.1.1)) <=
        measurableDescentError K q Kbar := by
    unfold measurableDescentError
    exact le_iSup (fun x =>
      measurableTotalVariation ((Kernel.map K q) x) (Kbar (q x))) pair.1.1
  have hy :
      measurableTotalVariation ((Kernel.map K q) pair.1.2) (Kbar (q pair.1.2)) <=
        measurableDescentError K q Kbar := by
    unfold measurableDescentError
    exact le_iSup (fun x =>
      measurableTotalVariation ((Kernel.map K q) x) (Kbar (q x))) pair.1.2
  calc
    measurableTotalVariation
        ((Kernel.map K q) pair.1.1) ((Kernel.map K q) pair.1.2) <=
        measurableTotalVariation
            ((Kernel.map K q) pair.1.1) (Kbar (q pair.1.1)) +
          measurableTotalVariation
            (Kbar (q pair.1.1)) ((Kernel.map K q) pair.1.2) :=
      measurable_total_variation_triangle _ _ _
    _ = measurableTotalVariation
            ((Kernel.map K q) pair.1.1) (Kbar (q pair.1.1)) +
          measurableTotalVariation
            ((Kernel.map K q) pair.1.2) (Kbar (q pair.1.1)) := by
      rw [measurable_total_variation_comm
        (Kbar (q pair.1.1)) ((Kernel.map K q) pair.1.2)]
    _ = measurableTotalVariation
            ((Kernel.map K q) pair.1.1) (Kbar (q pair.1.1)) +
          measurableTotalVariation
            ((Kernel.map K q) pair.1.2) (Kbar (q pair.1.2)) := by
      rw [pair.2]
    _ <= measurableDescentError K q Kbar + measurableDescentError K q Kbar :=
      add_le_add hx hy
    _ = 2 * measurableDescentError K q Kbar := by rw [two_mul]

private theorem representative_descent_error_le_defect
    {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    (K : Kernel X X) (q : X -> B) (hq : Measurable q)
    [IsMarkovKernel K]
    (rep : B -> X) (hrep : Measurable rep)
    (hsection : ∀ x, q (rep (q x)) = q x) :
    bestMeasurableDescentError K q <= observableKernelDefect K q := by
  let observed : Kernel X B := Kernel.map K q
  letI : IsMarkovKernel observed := ProbabilityTheory.Kernel.IsMarkovKernel.map K hq
  let candidate : Kernel B B := Kernel.comap observed rep hrep
  letI : IsMarkovKernel candidate :=
    ProbabilityTheory.Kernel.IsMarkovKernel.comap observed hrep
  unfold bestMeasurableDescentError
  refine iInf_le_of_le (⟨candidate, inferInstance⟩) ?_
  unfold measurableDescentError
  refine iSup_le fun x => ?_
  rw [show candidate (q x) = observed (rep (q x)) by
    simp only [candidate, Kernel.comap_apply]]
  exact le_iSup_of_le
    (⟨(x, rep (q x)), (hsection x).symm⟩ :
      {pair : X × X // q pair.1 = q pair.2}) le_rfl

/-- The optimal measurable Markov descent error is at least half the
source-fiber observable defect. A measurable representative of every realized
fiber also constructs a descent kernel whose error is at most that defect. -/
theorem best_measurable_descent_error_bounds
    {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    (K : Kernel X X) [IsMarkovKernel K]
    (q : X -> B) (hq : Measurable q) :
    observableKernelDefect K q / 2 <= bestMeasurableDescentError K q ∧
      ∀ rep : B -> X, Measurable rep ->
        (∀ x, q (rep (q x)) = q x) ->
          bestMeasurableDescentError K q <= observableKernelDefect K q := by
  constructor
  · unfold bestMeasurableDescentError
    refine le_iInf fun candidate => ?_
    apply (ENNReal.div_le_iff' (by norm_num) (by norm_num)).2
    exact observable_kernel_defect_le_two_mul_error K q candidate.1
  · exact fun rep hrep hsection =>
      representative_descent_error_le_defect K q hq rep hrep hsection

#print axioms best_measurable_descent_error_bounds

end D5.S3.Estimation.DataProcessing.MeasurableDescentErrorBounds
