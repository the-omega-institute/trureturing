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
  simpa [expand, Equiv.subtypeCongr, hx, edgeEquiv, Equiv.ofBijective] using he

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

/-- True weak components on the whole carrier, including isolated vertices. -/
abbrev Component (E : V → V → Prop) := Quotient (EqvGen.setoid E)

/- The normalizable helper adapts `Relation.SN.normalizable` from
leanprover/cslib@6548b846a320a6e7f31db0131cff0d44b6ecc945,
Cslib/Foundations/Relation/Termination.lean. Copyright (c) 2025 Fabrizio Montesi
and Thomas Waring; authors Fabrizio Montesi, Thomas Waring, Chris Henson.
Released under the Apache 2.0 license in LICENSE. The signature uses Mathlib's
Acc directly and spells out normality; the package and its definitions are not imported. -/
private theorem normalizable (E : V → V → Prop) {x : V}
    (hx : Acc (Function.swap E) x) :
    ∃ z, ReflTransGen E x z ∧ ¬ ∃ y, E z y := by
  classical
  induction hx with | intro x _ ih =>
  by_cases hy : ∃ y, E x y
  · obtain ⟨y, hy⟩ := hy
    obtain ⟨z, hz, hnormal⟩ := ih y hy
    exact ⟨z, .head hy hz, hnormal⟩
  · exact ⟨x, .refl, hy⟩

private theorem backward_wf [Finite V] (E : V → V → Prop)
    (ha : ∀ x, ¬ TransGen E x x) : WellFounded (Function.swap E) := by
  letI : Std.Irrefl (TransGen (Function.swap E)) :=
    ⟨fun x h => ha x (transGen_swap.mp h)⟩
  exact Subrelation.wf (fun h => TransGen.single h)
    (Finite.wellFounded_of_trans_of_irrefl (TransGen (Function.swap E)))

private def terminal [Finite V] (E : V → V → Prop)
    (ha : ∀ x, ¬ TransGen E x x) (x : V) : Tail E :=
  ⟨Classical.choose (normalizable E ((backward_wf E ha).apply x)),
    (Classical.choose_spec (normalizable E ((backward_wf E ha).apply x))).2⟩

private theorem terminal_path [Finite V] (E : V → V → Prop)
    (ha : ∀ x, ¬ TransGen E x x) (x : V) : ReflTransGen E x (terminal E ha x) :=
  (Classical.choose_spec (normalizable E ((backward_wf E ha).apply x))).1

private theorem terminal_fixed [Finite V] (E : V → V → Prop)
    (ha : ∀ x, ¬ TransGen E x x) (x : Tail E) : terminal E ha x = x := by
  apply Subtype.ext
  exact (reflTransGen_iff_eq (fun y h => x.2 ⟨y, h⟩)).mp (terminal_path E ha x)

private theorem terminal_edge [Finite V] (E : V → V → Prop)
    (hout : Relator.RightUnique E) (ha : ∀ x, ¬ TransGen E x x)
    {x y : V} (hxy : E x y) : terminal E ha x = terminal E ha y := by
  have hp := (terminal_path E ha x).total_of_right_unique hout
    ((terminal_path E ha y).head hxy)
  apply Subtype.ext
  rcases hp with hp | hp
  · exact ((reflTransGen_iff_eq (fun z hz => (terminal E ha x).2 ⟨z, hz⟩)).mp hp).symm
  · exact (reflTransGen_iff_eq (fun z hz => (terminal E ha y).2 ⟨z, hz⟩)).mp hp

private theorem terminal_component [Finite V] (E : V → V → Prop)
    (hout : Relator.RightUnique E) (ha : ∀ x, ¬ TransGen E x x)
    {x y : V} (h : EqvGen E x y) : terminal E ha x = terminal E ha y := by
  induction h with
  | rel _ _ h => exact terminal_edge E hout ha h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private def tailEquiv [Finite V] (E : V → V → Prop)
    (hout : Relator.RightUnique E) (ha : ∀ x, ¬ TransGen E x x) :
    Component E ≃ Tail E where
  toFun := Quotient.lift (terminal E ha) (fun _ _ h => terminal_component E hout ha h)
  invFun x := Quotient.mk _ x.1
  left_inv := by
    intro A
    induction A using Quotient.inductionOn with | h x =>
    exact Quotient.sound ((EqvGen.reflTransGen_le_eqvGen E x _ (terminal_path E ha x)).symm)
  right_inv := terminal_fixed E ha

private theorem flip_acyclic (E : V → V → Prop)
    (ha : ∀ x, ¬ TransGen E x x) : ∀ x, ¬ TransGen (Function.swap E) x x :=
  fun x h => ha x (transGen_swap.mp h)

private def reverseComponent (E : V → V → Prop) :
    Component E ≃ Component (Function.swap E) :=
  Quotient.congrRight (fun a b => ⟨
    fun h => EqvGen.eqvGen_le (r := E) (r' := EqvGen (Function.swap E))
      (fun x y hxy => EqvGen.symm _ _ (EqvGen.rel y x hxy)) a b h,
    fun h => EqvGen.eqvGen_le (r := Function.swap E) (r' := EqvGen E)
      (fun x y hxy => EqvGen.symm _ _ (EqvGen.rel y x hxy)) a b h⟩)

private theorem flip_unique (E : V → V → Prop) (hin : Relator.LeftUnique E) :
    Relator.RightUnique (Function.swap E) := fun _ _ _ h₁ h₂ => hin h₁ h₂

private def headEquiv [Finite V] (E : V → V → Prop)
    (hin : Relator.LeftUnique E) (ha : ∀ x, ¬ TransGen E x x) :
    Component E ≃ Head E :=
  (reverseComponent E).trans (tailEquiv (Function.swap E) (flip_unique E hin) (flip_acyclic E ha))

/-- Every true weak component has exactly one tail and one head, and all actual
permutation extensions are classified by a permutation of those components.
The endpoint identifications and connector equation are part of the result. -/
theorem component_completion_classification [Finite V] (E : V → V → Prop)
    (hout : Relator.RightUnique E) (hin : Relator.LeftUnique E)
    (ha : ∀ x, ¬ TransGen E x x) :
    ∃ (q : Component E ≃ Tail E) (h : Component E ≃ Head E)
      (Φ : Completion E ≃ Perm (Component E)),
      (∀ A, Quotient.mk (EqvGen.setoid E) (q A).1 = A) ∧
      (∀ A, Quotient.mk (EqvGen.setoid E) (h A).1 = A) ∧
      ∀ σ A, σ.1 (q A) = h (Φ σ A) := by
  classical
  let q := tailEquiv E hout ha
  let h := headEquiv E hin ha
  obtain ⟨Ψ, hΨ⟩ := completion_classification E hout hin
  let K : (Tail E ≃ Head E) ≃ Perm (Component E) := {
    toFun := fun e => q.trans (e.trans h.symm)
    invFun := fun ρ => q.symm.trans (ρ.trans h)
    left_inv := by intro e; ext x; simp
    right_inv := by intro ρ; ext A; simp }
  refine ⟨q, h, Ψ.trans K, ?_, ?_, ?_⟩
  · exact q.symm_apply_apply
  · intro A
    change (reverseComponent E).symm
      ((tailEquiv (Function.swap E) (flip_unique E hin) (flip_acyclic E ha)).symm (h A)) = A
    exact h.symm_apply_apply A
  · intro σ A
    simpa [K] using hΨ σ (q A)

end D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
