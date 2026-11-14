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
import D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
import Mathlib.GroupTheory.Perm.Centralizer

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
private theorem completion_classification (E : V → V → Prop)
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
private theorem component_completion_classification [Finite V] (E : V → V → Prop)
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

private theorem path_to_tail [Finite V] (E : V → V → Prop)
    (hout : Relator.RightUnique E) (ha : ∀ x, ¬ TransGen E x x)
    {x : V} (y : Tail E) (hc : EqvGen E x y) : ReflTransGen E x y := by
  have ht := (terminal_component E hout ha hc).trans (terminal_fixed E ha y)
  simpa only [ht] using terminal_path E ha x

private theorem path_powers (E : V → V → Prop) (σ : Completion E)
    {x y : V} (hp : ReflTransGen E x y) :
    ∃ n : ℕ, (σ.1 ^ n) x = y ∧
      ∀ k, 0 < k → k ≤ n → ∃ z, E z ((σ.1 ^ k) x) := by
  induction hp with
  | refl => exact ⟨0, rfl, by omega⟩
  | @tail y z _ hyz ih =>
    obtain ⟨n, hn, hi⟩ := ih
    have hn₁ : (σ.1 ^ (n + 1)) x = z := by
      rw [pow_succ', Perm.mul_apply, hn, σ.2 _ _ hyz]
    refine ⟨n + 1, hn₁, ?_⟩
    intro k hk hkn
    by_cases he : k = n + 1
    · exact ⟨y, by simpa only [he, hn₁] using hyz⟩
    · exact hi k hk (by omega)

private theorem first_return_data [Finite V] (E : V → V → Prop)
    (hout : Relator.RightUnique E) (ha : ∀ x, ¬ TransGen E x x)
    (σ : Completion E) (x : Head E) (y : Tail E)
    (hc : EqvGen E x y) :
    ∃ n : ℕ,
      D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.FirstVisit
        σ.1 {z | ¬ ∃ w, E w z} x n ∧ (σ.1 ^ n) x = σ.1 y := by
  obtain ⟨n, hn, hi⟩ := path_powers E σ (path_to_tail E hout ha y hc)
  have hn₁ : (σ.1 ^ (n + 1)) x = σ.1 y := by rw [pow_succ', Perm.mul_apply, hn]
  refine ⟨n + 1, ⟨by omega, ?_, ?_⟩, hn₁⟩
  · rw [hn₁]
    exact image_tail E σ y
  · intro k hk hkn hmem
    exact hmem (hi k hk (by omega))

private theorem same_cycle_components (E : V → V → Prop) (σ : Completion E)
    {x y : V} (hc : EqvGen E x y) : σ.1.SameCycle x y := by
  induction hc with
  | rel x y hxy => exact ⟨1, by simpa using σ.2 _ _ hxy⟩
  | refl => exact Perm.SameCycle.refl _ _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem same_cycle_transport {W Z : Type*} (e : W ≃ Z)
    (ρ : Perm W) (x y : W) :
    (e.permCongr ρ).SameCycle (e x) (e y) ↔ ρ.SameCycle x y := by
  unfold Perm.SameCycle
  apply exists_congr
  intro n
  have hn := e.permCongrHom.toMonoidHom.map_zpow ρ n
  change e.permCongr (ρ ^ n) = e.permCongr ρ ^ n at hn
  change (e.permCongr ρ ^ n) (e x) = e y ↔ _
  rw [← hn]
  simp

/-- Actual full-cycle extensions, defined by orbit and extension conditions. -/
abbrev CycleCompletion (E : V → V → Prop) :=
  {σ : Perm V // σ.IsCycleOn Set.univ ∧ ∀ x y, E x y → σ x = y}

/-- Actual full cycles on a carrier. -/
abbrev FullCycle (W : Type*) := {ρ : Perm W // ρ.IsCycleOn Set.univ}

/-- Endpoint-compatible equivalence for actual single-orbit completions of a raw
finite directed linear forest. Isolated vertices belong to their actual components. -/
private theorem full_cycle_completion_equiv [Finite V] (E : V → V → Prop)
    (hout : Relator.RightUnique E) (hin : Relator.LeftUnique E)
    (ha : ∀ x, ¬ TransGen E x x) :
    ∃ (q : Component E ≃ Tail E) (h : Component E ≃ Head E)
      (Φ : CycleCompletion E ≃ FullCycle (Component E)),
      (∀ A, Quotient.mk (EqvGen.setoid E) (q A).1 = A) ∧
      (∀ A, Quotient.mk (EqvGen.setoid E) (h A).1 = A) ∧
      ∀ σ A, σ.1 (q A) = h ((Φ σ).1 A) := by
  classical
  obtain ⟨q, h, Ψ, hq, hh, hΨ⟩ := component_completion_classification E hout hin ha
  let S : Set V := {z | ¬ ∃ w, E w z}
  have jumps (σ : Completion E) (x : Head E) :
      ∃ n : ℕ,
        D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.FirstVisit
          σ.1 S x n ∧ (σ.1 ^ n) x = (h.permCongr (Ψ σ) x : Head E) := by
    let A := h.symm x
    have hc : EqvGen E x (q A) := Quotient.exact (by
      calc
        Quotient.mk (EqvGen.setoid E) x.1 = A := by simpa [A] using hh A
        _ = Quotient.mk (EqvGen.setoid E) (q A).1 := (hq A).symm)
    obtain ⟨n, hn, he⟩ := first_return_data E hout ha σ x (q A) hc
    exact ⟨n, hn, he.trans (hΨ σ A)⟩
  have marked (σ : Completion E) (A B : Component E) :
      σ.1.SameCycle (h A) (h B) ↔ (Ψ σ).SameCycle A B := by
    exact (D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.same_cycle_of_first_visit
      σ.1 S (h.permCongr (Ψ σ)) (jumps σ) (h A) (h B)).trans
        (same_cycle_transport h (Ψ σ) A B)
  have cyc (σ : Completion E) :
      σ.1.IsCycleOn Set.univ ↔ (Ψ σ).IsCycleOn Set.univ := by
    constructor
    · intro hs
      refine ⟨(Ψ σ).bijective.bijOn_univ, ?_⟩
      intro A _ B _
      exact (marked σ A B).mp (hs.2 (Set.mem_univ _) (Set.mem_univ _))
    · intro hs
      refine ⟨σ.1.bijective.bijOn_univ, ?_⟩
      intro x _ y _
      let A : Component E := Quotient.mk _ x
      let B : Component E := Quotient.mk _ y
      have hx : σ.1.SameCycle x (h A) :=
        same_cycle_components E σ (Quotient.exact (hh A).symm)
      have hy : σ.1.SameCycle y (h B) :=
        same_cycle_components E σ (Quotient.exact (hh B).symm)
      exact hx.trans (((marked σ A B).mpr
        (hs.2 (Set.mem_univ _) (Set.mem_univ _))).trans hy.symm)
  let Φ : CycleCompletion E ≃ FullCycle (Component E) := {
    toFun := fun σ => ⟨Ψ ⟨σ.1, σ.2.2⟩, (cyc ⟨σ.1, σ.2.2⟩).mp σ.2.1⟩
    invFun := fun ρ => ⟨(Ψ.symm ρ.1).1,
      (cyc (Ψ.symm ρ.1)).mpr (by simpa using ρ.2), (Ψ.symm ρ.1).2⟩
    left_inv := by
      intro σ
      apply Subtype.ext
      change (Ψ.symm (Ψ ⟨σ.1, σ.2.2⟩)).1 = σ.1
      exact congrArg (fun z : Completion E => z.1) (Ψ.symm_apply_apply ⟨σ.1, σ.2.2⟩)
    right_inv := by intro ρ; apply Subtype.ext; exact Ψ.apply_symm_apply ρ.1 }
  exact ⟨q, h, Φ, hq, hh, fun σ A => hΨ ⟨σ.1, σ.2.2⟩ A⟩

/- Adapted from Liu and Ye, WeightedCycle/Core.lean,
`singleFullCycle_iff_cycle_support`, at immutable revision
4a7568845a361d33b1bbe2872a53f1f0c7d2d38d. Copyright (c) 2026
Xingchen Liu / 刘星辰 and Xiangyu Ye / 叶祥宇. This helper is CC-BY-4.0;
the full license, attribution and modification notice are in
Library/Combinatorics/liuYe2026CycleSupport.md. -/
private theorem full_cycle_support [Fintype V] [DecidableEq V]
    (hV : 2 ≤ Fintype.card V) (σ : Perm V) :
    σ.IsCycleOn Set.univ ↔ σ.IsCycle ∧ σ.support = Finset.univ := by
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  constructor
  · intro h
    refine ⟨Perm.isCycle_iff_exists_isCycleOn.mpr
      ⟨Set.univ, Set.nontrivial_univ, h, by simp⟩, ?_⟩
    apply Finset.eq_univ_of_forall
    intro i
    exact Perm.mem_support.mpr (h.apply_ne Set.nontrivial_univ (Set.mem_univ i))
  · rintro ⟨hc, hs⟩
    have hm : ∀ i, σ i ≠ i := fun i => Perm.mem_support.mp (hs ▸ Finset.mem_univ i)
    have hu : {i | σ i ≠ i} = Set.univ := by ext i; simp [hm]
    simpa only [hu] using hc.isCycleOn

private theorem full_cycle_card [Finite V] (hV : 2 ≤ Nat.card V) :
    Nat.card (FullCycle V) = (Nat.card V - 1).factorial := by
  classical
  letI := Fintype.ofFinite V
  have hn : 2 ≤ Fintype.card V := by simpa only [Nat.card_eq_fintype_card] using hV
  have hp (σ : Perm V) : σ.IsCycleOn Set.univ ↔ σ.cycleType = {Fintype.card V} := by
    rw [full_cycle_support hn]
    constructor
    · rintro ⟨hc, hs⟩
      simpa [hs] using hc.cycleType
    · intro ht
      have hc : σ.IsCycle := Perm.card_cycleType_eq_one.mp (by simp [ht])
      have hs : σ.support.card = Fintype.card V := by
        simpa only [ht, Multiset.sum_singleton] using σ.sum_cycleType.symm
      exact ⟨hc, Finset.eq_univ_of_card _ hs⟩
  let e : FullCycle V ≃ {σ : Perm V // σ.cycleType = {Fintype.card V}} :=
    Equiv.subtypeEquivProp (funext (fun σ => propext (hp σ)))
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa using Perm.card_of_cycleType_singleton hn (le_refl (Fintype.card V))

/-- The complete structural contraction, nonemptiness and exact completion count.
All components and endpoint predicates are derived from the original relation. -/
theorem directed_forest_completion [Finite V] (E : V → V → Prop)
    (hout : Relator.RightUnique E) (hin : Relator.LeftUnique E)
    (ha : ∀ x, ¬ TransGen E x x) (hc : 2 ≤ Nat.card (Component E)) :
    ∃ (q : Component E ≃ Tail E) (h : Component E ≃ Head E)
      (Φ : CycleCompletion E ≃ FullCycle (Component E)),
      (∀ A, Quotient.mk (EqvGen.setoid E) (q A).1 = A) ∧
      (∀ A, Quotient.mk (EqvGen.setoid E) (h A).1 = A) ∧
      (∀ σ A, σ.1 (q A) = h ((Φ σ).1 A)) ∧
      Nonempty (CycleCompletion E) ∧
      Nat.card (CycleCompletion E) = (Nat.card (Component E) - 1).factorial := by
  obtain ⟨q, h, Φ, hq, hh, hΦ⟩ := full_cycle_completion_equiv E hout hin ha
  have hcard := (Nat.card_congr Φ).trans (full_cycle_card hc)
  refine ⟨q, h, Φ, hq, hh, hΦ, ?_, hcard⟩
  exact (Nat.card_pos_iff.mp (by rw [hcard]; exact Nat.factorial_pos _)).1

end D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
