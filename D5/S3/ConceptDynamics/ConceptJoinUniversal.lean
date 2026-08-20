/- GID: D5/S3/ConceptDynamics/ConceptJoinUniversal
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ConceptJoinUniversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The product readout is the universal join of two concept readouts. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition

/- Library-search audit trail (2026-08-21):
   * `rg -n -F 'concept_join_universal' D5 Golden/Frozen/accepted` found no
     repository declaration or accepted duplicate.
   * Searches for product-readout factorization and universal join declarations
     found `ObserverMemory.Fusion.LeastCommonRefinement`, whose surjective
     setoid-kernel statement is not this readout-factorization theorem; no
     declaration supplies both projection factors and the paired universal factor.
   * The proof uses only product projections, pairing, function composition, and
     function extensionality; no stronger external machinery was found or needed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ConceptJoinUniversal

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- A coarse readout is refined by a finer readout when it factors through it. -/
def Refines {X C D : Type _} (q_C : Concept X C) (q_D : Concept X D) : Prop :=
  ∃ factor : D → C, q_C = factor ∘ q_D

/-- The joint concept records both component readouts. -/
def conceptJoin {X C D : Type _} (q_C : Concept X C) (q_D : Concept X D) :
    Concept X (C × D) :=
  fun x => (q_C x, q_D x)

/-- The product readout is the least common refinement under factorization. -/
theorem concept_join_universal
    {X C D E : Type _} (q_C : Concept X C) (q_D : Concept X D)
    (q_E : Concept X E) :
    Refines q_C (conceptJoin q_C q_D) ∧
      Refines q_D (conceptJoin q_C q_D) ∧
      (Refines q_C q_E → Refines q_D q_E →
        Refines (conceptJoin q_C q_D) q_E) := by
  constructor
  · exact ⟨Prod.fst, by funext x; rfl⟩
  constructor
  · exact ⟨Prod.snd, by funext x; rfl⟩
  · rintro ⟨factor_C, h_C⟩ ⟨factor_D, h_D⟩
    refine ⟨fun e => (factor_C e, factor_D e), ?_⟩
    funext x
    change (q_C x, q_D x) = (factor_C (q_E x), factor_D (q_E x))
    rw [h_C, h_D]
    rfl

example : Refines (fun x : Bool => x) (fun x : Bool => x) :=
  ⟨id, rfl⟩

example : conceptJoin (fun _ : Bool => false) (fun _ : Bool => true) false =
    (false, true) := rfl

#print axioms concept_join_universal

end D5.S3.ConceptDynamics.ConceptJoinUniversal
