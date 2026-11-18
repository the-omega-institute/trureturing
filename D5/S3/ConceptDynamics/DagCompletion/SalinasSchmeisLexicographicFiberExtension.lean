/- GID: D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension
   mirror-E: none(waiver:pure-mathematical-argument)
   anchors: []
   utility: none
   digest: Partitions induced lexicographic extensions into inherited fiber copies. -/

/- lexFiberExtension: The literal fibers are exactly the classes of the first-projection kernel.
   To identify the class of each given fiber, the proof uses the induced base embedding as a
   section of first projection. The second-coordinate isomorphisms use the inherited order.
   Escape audit for lexFiberExtension is unfinished. The linked source-family issue is
   https://github.com/the-omega-institute/trureturing/issues/28004 (original result audit).
   A faithful registration would require an enrolled readout and lawful observational variation
   for this construction. The construction supplies neither of those pieces of evidence. -/

import D5.S3.ConceptDynamics.DagCompletion.SalinasSchmeisOmegaChainExtensionRefutation
import Mathlib.Order.Prod.Lex.Basic

/-! Induced extensions with a literal partition by lexicographic fibers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagCompletion.SalinasSchmeisLexicographicFiberExtension

open SalinasSchmeisOmegaChainExtensionRefutation (IsExtension)

universe u v

variable {P : Type u} {A : Type v} [PartialOrder P] [PartialOrder A]

/-- The first-coordinate fiber, with the order induced from the lexicographic product. -/
def lexFiber (p : P) : Set (P ×ₗ A) :=
  {x | (ofLex x).1 = p}

/-- Fixing the second coordinate gives an induced copy of the base order. -/
def lexBaseEmbedding (a₀ : A) : P ↪o (P ×ₗ A) :=
  OrderEmbedding.ofMapLEIff (fun p => toLex (p, a₀)) fun p q => by
    rw [Prod.Lex.toLex_le_toLex']
    exact ⟨And.left, fun h => ⟨h, fun _ => le_rfl⟩⟩

/-- The second coordinate is the inverse of the inclusion into the inherited fiber. -/
def lexFiberOrderIso (p : P) : A ≃o lexFiber (A := A) p where
  toFun a := ⟨toLex (p, a), rfl⟩
  invFun x := (ofLex x.val).2
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext x.property.symm rfl
  map_rel_iff' {a b} := by
    change toLex (p, a) ≤ toLex (p, b) ↔ a ≤ b
    simp [Prod.Lex.toLex_le_toLex]

/-- The literal family of inherited fibers partitions the induced lexicographic extension. -/
theorem lexFiberExtension (a₀ : A) :
    IsExtension P (P ×ₗ A) ∧ Setoid.IsPartition (Set.range (lexFiber (P := P) (A := A))) ∧
      ∀ p : P, Nonempty (A ≃o lexFiber (A := A) p) := by
  let base : P ↪o (P ×ₗ A) := lexBaseEmbedding a₀
  refine ⟨⟨base⟩, ?_, fun p => ⟨lexFiberOrderIso p⟩⟩
  let first : P ×ₗ A → P := fun x => (ofLex x).1
  have classes_eq : (Setoid.ker first).classes = Set.range (lexFiber (A := A)) := by
    refine Set.Subset.antisymm (Setoid.classes_ker_subset_fiber_set first) ?_
    rintro _ ⟨p, rfl⟩
    exact ⟨base p, rfl⟩
  rw [← classes_eq]
  exact Setoid.isPartition_classes _

end D5.S3.ConceptDynamics.DagCompletion.SalinasSchmeisLexicographicFiberExtension
