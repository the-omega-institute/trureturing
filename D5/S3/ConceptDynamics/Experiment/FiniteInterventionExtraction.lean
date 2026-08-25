/- GID: D5/S3/ConceptDynamics/Experiment/FiniteInterventionExtraction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/FiniteInterventionExtraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite separating intervention subfamily exists. -/

import D5.S3.ConceptDynamics.Interventions.TargetRelativePairUniverse
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Set.Finite.Lattice

/- Library-search audit trail (2026-08-25):
   * Exact repository hit `target_relative_pair_universe` supplies the canonical
     target-disagreement universe and the full-family cover equivalence. It does
     not extract a finite intervention subfamily.
   * The neighboring `finite_cover_laws` extracts a finite family only for a
     baseline-relative defect relation and a dependent readout carrier, so it is
     not an exact statement of this theorem.
   * Exact pinned-Mathlib hit `Set.finite_subset_iUnion` extracts finitely many
     members of an indexed cover of a finite set. No library theorem packages
     the intervention conclusion below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiment.FiniteInterventionExtraction

open D5.S3.ConceptDynamics.Interventions.TargetRelativePairUniverse

universe u v w

/-- If all allowed interventions separate every target-distinct pair in a
finite model class, a finite set of those interventions still separates every
such pair. -/
theorem finite_intervention_extraction {n : Nat}
    {Intervention : Type u} {Response : Type v} {Target : Type w}
    (readout : Intervention → Fin n → Response) (target : Fin n → Target)
    (separates : ∀ i j, target i ≠ target j →
      ∃ intervention, readout intervention i ≠ readout intervention j) :
    ∃ selected : Set Intervention, selected.Finite ∧
      ∀ i j, target i ≠ target j →
        ∃ intervention ∈ selected,
          readout intervention i ≠ readout intervention j := by
  have covers :=
    (target_relative_pair_universe readout target).mp separates
  rcases Set.finite_subset_iUnion
      (Set.finite_univ.subset (Set.subset_univ
        (Sym2.fromRel (r := fun i j : Fin n => target i ≠ target j)
          ⟨fun _ _ different => different.symm⟩)))
      covers with ⟨selected, selectedFinite, selectedCovers⟩
  refine ⟨selected, selectedFinite, ?_⟩
  intro i j targetDifferent
  have pairInUniverse :
      s(i, j) ∈ Sym2.fromRel (r := fun x y : Fin n => target x ≠ target y)
        ⟨fun _ _ different => different.symm⟩ :=
    targetDifferent
  have pairCovered := selectedCovers pairInUniverse
  rcases Set.mem_iUnion.mp pairCovered with ⟨intervention, pairCovered⟩
  rcases Set.mem_iUnion.mp pairCovered with ⟨interventionSelected, separated⟩
  change readout intervention i ≠ readout intervention j at separated
  exact ⟨intervention, interventionSelected, separated⟩

#print axioms finite_intervention_extraction

end D5.S3.ConceptDynamics.Experiment.FiniteInterventionExtraction
