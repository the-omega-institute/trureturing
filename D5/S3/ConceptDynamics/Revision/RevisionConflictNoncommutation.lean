/- GID: D5/S3/ConceptDynamics/Revision/RevisionConflictNoncommutation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Revision/RevisionConflictNoncommutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reset-on-conflict set revision is order-dependent on a three-world model. -/

import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

/- Duplicate-search audit (2026-09-02):
   * Exact and spelling-variant D5 searches for reset-on-conflict revision,
     `Rev_P`, noncommutation, and path dependence found no matching theorem.
   * The formalization-receipt index contains no receipt for the source atom; its
     digest entry is residual-open.
   * The more general search found `EvolutionConditioningNoncommutation`, whose
     arbitrary evolution/conditioning counterexample uses a different operator.
   * No matching declaration occurs on the remote mathematics lane tips.
   * Pinned Mathlib supplies the finite-set and extensionality machinery, but no
     theorem about this source-specific revision operator. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Revision.RevisionConflictNoncommutation

/-- Revision conditions on compatible evidence and resets to the evidence set
when the old state and the evidence are disjoint. -/
noncomputable def revision {X : Type*} (P A : Set X) : Set X :=
  by
    classical
    exact if (A ∩ P).Nonempty then A ∩ P else P

/-- On three worlds, reset-on-conflict revision gives `{1}` in one order and
`{1, 2}` in the other. The `Fin 3` labels `0, 1, 2` encode the source's worlds
`1, 2, 3`, respectively. -/
theorem revision_conflict_noncommutation :
    let A : Set (Fin 3) := {0}
    let P : Set (Fin 3) := {1, 2}
    let Q : Set (Fin 3) := {0, 1}
    revision P A = P ∧
      revision Q A = A ∧
      revision Q (revision P A) = {1} ∧
      revision P (revision Q A) = P ∧
      revision Q (revision P A) ≠ revision P (revision Q A) := by
  dsimp only
  have hPA : revision {1, 2} {0} = ({1, 2} : Set (Fin 3)) := by
    ext x
    fin_cases x <;> simp [revision]
  have hQA : revision {0, 1} {0} = ({0} : Set (Fin 3)) := by
    ext x
    fin_cases x <;> simp [revision]
  have hQP : revision {0, 1} (revision {1, 2} {0}) = ({1} : Set (Fin 3)) := by
    rw [hPA]
    have hMeet : (({1, 2} : Set (Fin 3)) ∩ {0, 1}).Nonempty := by
      exact ⟨1, by simp⟩
    ext x
    fin_cases x <;> simp [revision, hMeet]
  have hPQ : revision {1, 2} (revision {0, 1} {0}) = ({1, 2} : Set (Fin 3)) := by
    rw [hQA]
    ext x
    fin_cases x <;> simp [revision]
  refine ⟨hPA, hQA, hQP, hPQ, ?_⟩
  rw [hQP, hPQ]
  intro h
  have hAtTwo := Set.ext_iff.mp h (2 : Fin 3)
  simp at hAtTwo

#print axioms revision_conflict_noncommutation

end D5.S3.ConceptDynamics.Revision.RevisionConflictNoncommutation
