/- GID: D5/S3/Observer/Existence/QubitEmpiricalImageReflexiveGap
   generality: G
   mirror-B: D5/B/S3/Observer/Existence/QubitEmpiricalImageReflexiveGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The qubit density-state readout realizes all predicates but no same-state catalog is exhaustive. -/

import D5.S3.ConceptDynamics.ObservationTopology.LosslessReadoutReflexiveGap
import D5.S3.Observer.Existence.EmpiricalReflexiveSeparation

/-!
# Qubit Empirical-Image Reflexive Gap

This module specializes the abstract lossless-readout theorem to the paper's
existing qubit density-state observer. It strengthens the earlier independent
tomography/diagonal conjunction by placing predicate completeness and catalogue
non-surjectivity on the realized image of the very same injective qubit
readout. Context-subfamily minimality is proved generically in
`RestrictedContextMinimality`; the existing concrete Pauli context is private,
so an immutable downstream module cannot add that concrete conjunct here.
-/

/- Library-search audit trail (2026-09-06):
   * Exact repository hit `empirical_complete_reflexive_incomplete` supplies an
     injective readout on the full `DensityState (Fin 2)` carrier and is applied
     directly; its private Pauli context implementation is not duplicated.
   * Exact repository hit `lossless_observation_strict_reflexive_gap` supplies
     the predicate-space bijection and same-carrier catalogue obstruction on
     the realized image and is specialized directly.
   * Searches for public `qubitTomographyContext`, Pauli-context overlap, and
     restricted density readout declarations found only private definitions in
     the frozen source module, so no public concrete minimality theorem was
     available for import.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Existence.QubitEmpiricalImageReflexiveGap

open D5.S3.ConceptDynamics.ObservationTopology.LosslessReadoutReflexiveGap
open D5.S3.Observer.Existence.EmpiricalReflexiveSeparation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Tomography.ObserverDiagonalSeparation
open D5.S3.Quantum.Tomography.RankOneContextCommutator

/-- There is an injective qubit density-state readout whose realized empirical
image represents every Boolean state predicate uniquely, while no catalogue
indexed by the same density states enumerates all such observable predicates. -/
theorem qubit_empirical_image_reflexive_gap :
    ∃ context : Fin 3 -> RankOneContext 2,
      let R := fun rho : DensityState (Fin 2) =>
        contextReadout context (CStarMatrix.ofMatrix.symm rho.1)
      Function.Injective R ∧
        Function.Bijective (observablePullback R) ∧
        ∀ catalog : DensityState (Fin 2) → Set.range R → Bool,
          ¬ Function.Surjective catalog := by
  obtain ⟨context, hinjective, _⟩ :=
    empirical_complete_reflexive_incomplete
  refine ⟨context, hinjective, ?_⟩
  exact lossless_observation_strict_reflexive_gap hinjective

#print axioms qubit_empirical_image_reflexive_gap

end D5.S3.Observer.Existence.QubitEmpiricalImageReflexiveGap
