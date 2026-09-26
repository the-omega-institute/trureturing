/- GID: D5/S3/ConceptDynamics/Coding/BipartiteOverlapConjugacy
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/BipartiteOverlapConjugacy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shared half-edges give an explicit invertible finite-window path recoding. -/

import Mathlib.Topology.Constructions
import Mathlib.Data.Int.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.BipartiteOverlapConjugacy

universe u v w z

/-- The four endpoint maps of a bipartite directed graph. -/
structure Boundary (U : Type u) (V : Type v) (I : Type w) (J : Type z) where
  sourceU : U → I
  targetU : U → J
  sourceV : V → J
  targetV : V → I

variable {U : Type u} {V : Type v} {I : Type w} {J : Type z}

/-- All legal doubly infinite paths, grouped as U followed by V. -/
abbrev LeftPath (d : Boundary U V I J) :=
  {x : ℤ → U × V // ∀ i : ℤ,
    d.targetU (x i).1 = d.sourceV (x i).2 ∧
    d.targetV (x i).2 = d.sourceU (x (i + 1)).1}

/-- The same alternating paths, grouped as V followed by U. -/
abbrev RightPath (d : Boundary U V I J) :=
  {y : ℤ → V × U // ∀ i : ℤ,
    d.targetV (y i).1 = d.sourceU (y i).2 ∧
    d.targetU (y i).2 = d.sourceV (y (i + 1)).1}

/-- Regroup the shared half-edge at the right boundary. -/
def forward (d : Boundary U V I J) (x : LeftPath d) : RightPath d :=
  ⟨fun i => ((x.val i).2, (x.val (i + 1)).1),
    fun i => ⟨(x.property i).2, (x.property (i + 1)).1⟩⟩

/-- Recover the first half-edge from the preceding output. -/
def backward (d : Boundary U V I J) (y : RightPath d) : LeftPath d :=
  ⟨fun i => ((y.val (i - 1)).2, (y.val i).1), by
    intro i
    constructor
    · simpa only [sub_add_cancel] using (y.property (i - 1)).2
    · simpa only [add_sub_cancel_right] using (y.property i).1⟩

/-- This equivalence contains both recovery proofs on legal histories. -/
def pathEquiv (d : Boundary U V I J) : LeftPath d ≃ RightPath d where
  toFun := forward d
  invFun := backward d
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    simp [backward, forward]
  right_inv := by
    intro y
    apply Subtype.ext
    funext i
    simp [backward, forward]

def leftShift (d : Boundary U V I J) (x : LeftPath d) : LeftPath d :=
  ⟨fun i => x.val (i + 1), fun i => x.property (i + 1)⟩

def rightShift (d : Boundary U V I J) (y : RightPath d) : RightPath d :=
  ⟨fun i => y.val (i + 1), fun i => y.property (i + 1)⟩

section Topology

variable [TopologicalSpace U] [TopologicalSpace V]

/-- No inverse, continuity, or admissibility premise is assumed in this homeomorphism. -/
def pathHomeomorph (d : Boundary U V I J) : LeftPath d ≃ₜ RightPath d where
  toEquiv := pathEquiv d
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (((continuous_apply i).comp continuous_subtype_val).snd).prodMk
      (((continuous_apply (i + 1)).comp continuous_subtype_val).fst)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (((continuous_apply (i - 1)).comp continuous_subtype_val).snd).prodMk
      (((continuous_apply i).comp continuous_subtype_val).fst)

end Topology

#print axioms pathHomeomorph

end D5.S3.ConceptDynamics.Coding.BipartiteOverlapConjugacy
