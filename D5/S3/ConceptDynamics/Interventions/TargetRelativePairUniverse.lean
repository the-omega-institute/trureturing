/- GID: D5/S3/ConceptDynamics/Interventions/TargetRelativePairUniverse
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interventions/TargetRelativePairUniverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Target identification requires covering exactly the target-disagreement pairs. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Sym.Sym2

/- Library-search audit trail (2026-08-25):
   * D5 searches for target-relative universes, target-relevant unordered pairs,
     intervention separation sets, and `Sym2.fromRel` found no exact theorem.
   * `ExperimentIdentifiability.targetKernel` and
     `ExperimentValueIsKernelReduction.residualPairs` are exact adjacent hits on
     ordered state pairs, but neither is the source's unordered finite-model pair
     universe, so no sibling carrier is redeclared here.
   * Exact pinned-Mathlib hits `Sym2.fromRel` and `Sym2.fromRel_prop`
     canonically turn a symmetric disagreement relation into a set of unordered
     pairs with its computation rule. Indexed-union membership supplies the
     intervention-family coverage step. No library theorem packages the full
     target-relative criterion below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Interventions.TargetRelativePairUniverse

universe u v w

/-- A family of interventions identifies a target on finitely indexed models
exactly when its separation sets cover the unordered pairs whose target values
differ. Thus pairs with equal target values are absent from the required
universe. -/
theorem target_relative_pair_universe {n : Nat}
    {Intervention : Type u} {Response : Type v} {Target : Type w}
    (readout : Intervention → Fin n → Response) (target : Fin n → Target) :
    (∀ i j, target i ≠ target j →
        ∃ intervention, readout intervention i ≠ readout intervention j) ↔
      Sym2.fromRel (r := fun i j => target i ≠ target j)
          ⟨fun _ _ different => different.symm⟩ ⊆
        ⋃ intervention,
          Sym2.fromRel
            (r := fun i j => readout intervention i ≠ readout intervention j)
            ⟨fun _ _ different => different.symm⟩ := by
  constructor
  · intro identifies pair targetDifferent
    induction pair using Sym2.inductionOn with
    | _ i j =>
        change target i ≠ target j at targetDifferent
        obtain ⟨intervention, separated⟩ := identifies i j targetDifferent
        apply Set.mem_iUnion.mpr
        refine ⟨intervention, ?_⟩
        change readout intervention i ≠ readout intervention j
        exact separated
  · intro covers i j targetDifferent
    have pairInUniverse :
        s(i, j) ∈ Sym2.fromRel (r := fun x y => target x ≠ target y)
          ⟨fun _ _ different => different.symm⟩ :=
      targetDifferent
    obtain ⟨intervention, separated⟩ := Set.mem_iUnion.mp (covers pairInUniverse)
    change readout intervention i ≠ readout intervention j at separated
    exact ⟨intervention, separated⟩

#print axioms target_relative_pair_universe

end D5.S3.ConceptDynamics.Interventions.TargetRelativePairUniverse
