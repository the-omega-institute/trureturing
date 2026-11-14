/- GID: D5/S3/Combinatorics/Graph/LinearForests/DirectedForestCompletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/DirectedForestCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Basic]
   utility: none
   digest: Actual permutation extensions are classified by their endpoint connectors. -/

import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card
import Mathlib.Order.WellFounded

/-! Exhaustive endpoint classification for actual permutation extensions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
open Equiv Relation
universe u
variable {V : Type u}

/-- Vertices without an incoming edge of the original relation. -/
abbrev Head (E : V → V → Prop) := {y : V // ¬ ∃ x, E x y}

/-- Vertices without an outgoing edge of the original relation. -/
abbrev Tail (E : V → V → Prop) := {x : V // ¬ ∃ y, E x y}

/-- All actual permutation extensions; no orbit restriction is imposed here. -/
abbrev Completion (E : V → V → Prop) :=
  {σ : Perm V // ∀ x y, E x y → σ x = y}

private def edgeMap (E : V → V → Prop) :
    {x : V // ∃ y, E x y} → {y : V // ∃ x, E x y} := fun x =>
  ⟨Classical.choose x.2, x.1, Classical.choose_spec x.2⟩

private theorem edgeMap_edge (E : V → V → Prop) (x : {x : V // ∃ y, E x y}) :
    E x (edgeMap E x) := Classical.choose_spec x.2

private def edgeEquiv (E : V → V → Prop)
    (hout : Relator.RightUnique E) (hin : Relator.LeftUnique E) :
    {x : V // ∃ y, E x y} ≃ {y : V // ∃ x, E x y} :=
  Equiv.ofBijective (edgeMap E) ⟨by
    intro x y h
    apply Subtype.ext
    exact hin (edgeMap_edge E x) (by rw [h]; exact edgeMap_edge E y), by
    rintro ⟨y, x, hxy⟩
    refine ⟨⟨x, y, hxy⟩, Subtype.ext ?_⟩
    exact hout (edgeMap_edge E ⟨x, y, hxy⟩) hxy⟩

private def expand (E : V → V → Prop)
    (hout : Relator.RightUnique E) (hin : Relator.LeftUnique E)
    (e : Tail E ≃ Head E) : Perm V := by
  classical
  exact Equiv.subtypeCongr (edgeEquiv E hout hin) e

private theorem expand_edge (E : V → V → Prop)
    (hout : Relator.RightUnique E) (hin : Relator.LeftUnique E)
    (e : Tail E ≃ Head E) {x y : V} (hxy : E x y) :
    expand E hout hin e x = y := by
  classical
  have hx : ∃ y, E x y := ⟨y, hxy⟩
  have he := hout (edgeMap_edge E ⟨x, hx⟩) hxy
  simpa [expand, Equiv.subtypeCongr, hx, edgeEquiv] using he

private theorem expand_tail (E : V → V → Prop)
    (hout : Relator.RightUnique E) (hin : Relator.LeftUnique E)
    (e : Tail E ≃ Head E) (x : Tail E) : expand E hout hin e x = e x := by
  classical
  simp [expand, Equiv.subtypeCongr, x.2]

private theorem image_tail (E : V → V → Prop) (σ : Completion E) (x : Tail E) :
    ¬ ∃ y, E y (σ.1 x) := by
  rintro ⟨y, hy⟩
  have hyx : y = x := σ.1.injective (σ.2 _ _ hy)
  exact x.2 ⟨σ.1 x, hyx ▸ hy⟩

private def restrict (E : V → V → Prop) (σ : Completion E) : Tail E ≃ Head E :=
  Equiv.ofBijective (fun x => ⟨σ.1 x, image_tail E σ x⟩) ⟨by
    intro x y h
    exact Subtype.ext (σ.1.injective (congrArg Subtype.val h)), by
    rintro ⟨y, hy⟩
    have hx : ¬ ∃ z, E (σ.1.symm y) z := by
      rintro ⟨z, hz⟩
      have hyz : y = z := by simpa using σ.2 _ _ hz
      exact hy ⟨σ.1.symm y, hyz.symm ▸ hz⟩
    exact ⟨⟨σ.1.symm y, hx⟩, Subtype.ext (σ.1.apply_symm_apply y)⟩⟩

/-- Exhaustive classification on the original carrier, with the actual endpoint equation.
The carrier may be infinite and internal directed cycles are allowed. -/
theorem completion_classification (E : V → V → Prop)
    (hout : Relator.RightUnique E) (hin : Relator.LeftUnique E) :
    ∃ Φ : Completion E ≃ (Tail E ≃ Head E),
      ∀ (σ : Completion E) (x : Tail E), σ.1 x = Φ σ x := by
  classical
  let Φ : Completion E ≃ (Tail E ≃ Head E) := {
    toFun := restrict E
    invFun := fun e => ⟨expand E hout hin e, fun _ _ h => expand_edge E hout hin e h⟩
    left_inv := by
      intro σ
      apply Subtype.ext
      apply Equiv.ext
      intro x
      by_cases hx : ∃ y, E x y
      · obtain ⟨y, hxy⟩ := hx
        exact (expand_edge E hout hin (restrict E σ) hxy).trans (σ.2 _ _ hxy).symm
      · exact expand_tail E hout hin (restrict E σ) ⟨x, hx⟩
    right_inv := by
      intro e
      apply Equiv.ext
      intro x
      apply Subtype.ext
      exact expand_tail E hout hin e x }
  exact ⟨Φ, fun _ _ => rfl⟩

end D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
