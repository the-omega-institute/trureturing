/- GID: D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/AlternatingMatchingComponents
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Two disjoint perfect matchings identify square components by pointwise commutation. -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Components of two disjoint perfect matchings -/

namespace D5.S3.Combinatorics.Matroids.AlternatingMatchingComponents

open SimpleGraph

/-- Two perfect matchings with distinct partners at each vertex. -/
structure Matchings (V : Type*) where
  first : V → V
  second : V → V
  first_involutive : Function.Involutive first
  second_involutive : Function.Involutive second
  first_ne_self : ∀ x, first x ≠ x
  second_ne_self : ∀ x, second x ≠ x
  partners_ne : ∀ x, first x ≠ second x

namespace Matchings

variable {V : Type*} (M : Matchings V)

/-- The union of the two undirected perfect matchings. -/
def graph : SimpleGraph V where
  Adj x y := M.first x = y ∨ M.second x = y
  symm := ⟨by
    intro x y h
    rcases h with e | e
    · exact Or.inl (e ▸ M.first_involutive x)
    · exact Or.inr (e ▸ M.second_involutive x)⟩
  loopless := ⟨fun x h => h.elim (M.first_ne_self x) (M.second_ne_self x)⟩

private theorem stepFirst (x : V) : M.graph.Reachable x (M.first x) :=
  (show M.graph.Adj x (M.first x) from Or.inl rfl).reachable

private theorem stepSecond (x : V) : M.graph.Reachable x (M.second x) :=
  (show M.graph.Adj x (M.second x) from Or.inr rfl).reachable

private theorem supp_eq_reachable (x : V) :
    (M.graph.connectedComponentMk x).supp = {y | M.graph.Reachable x y} := by
  ext y
  exact ConnectedComponent.eq.trans ⟨Reachable.symm, Reachable.symm⟩

/-- At a commuting vertex the entire connected component consists of the four corners. -/
theorem component_eq_square {x : V} (h : M.first (M.second x) = M.second (M.first x)) :
    (M.graph.connectedComponentMk x).supp =
      {x, M.first x, M.second x, M.first (M.second x)} := by
  let corners : Set V := {x, M.first x, M.second x, M.first (M.second x)}
  have closed {u v : V} (hu : u ∈ corners) (edge : M.graph.Adj u v) : v ∈ corners := by
    change M.first u = v ∨ M.second u = v at edge
    have hf := M.first_involutive
    have hg := M.second_involutive
    have finish : M.second (M.first (M.second x)) = M.first x := by
      rw [h, hg]
    simp only [corners, Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
    rcases hu with rfl | rfl | rfl | rfl <;> rcases edge with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl (hf _)
    · exact Or.inr (Or.inr (Or.inr h.symm))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inl (hg _)
    · exact Or.inr (Or.inr (Or.inl (hf _)))
    · exact Or.inr (Or.inl finish)
  rw [M.supp_eq_reachable x]
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
  · change M.graph.Reachable x y at hy
    rw [SimpleGraph.reachable_iff_reflTransGen] at hy
    induction hy with
    | refl => simp
    | tail _ edge ih => exact closed ih edge
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact Reachable.rfl
    · exact M.stepFirst x
    · exact M.stepSecond x
    · exact (M.stepSecond x).trans (M.stepFirst (M.second x))

private theorem square_card [Finite V] (x : V) :
    ({x, M.first x, M.second x, M.first (M.second x)} : Set V).ncard = 4 := by
  have hf := M.first_involutive
  have hg := M.second_involutive
  have nf := M.first_ne_self
  have ng := M.second_ne_self
  have nd := M.partners_ne
  have h₁ : x ∉ ({M.first x, M.second x, M.first (M.second x)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    grind [Function.Involutive]
  have h₂ : M.first x ∉ ({M.second x, M.first (M.second x)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    grind [Function.Involutive]
  have h₃ : M.second x ∉ ({M.first (M.second x)} : Set V) := by
    simpa using (nf (M.second x)).symm
  rw [Set.ncard_insert_of_notMem h₁, Set.ncard_insert_of_notMem h₂,
    Set.ncard_insert_of_notMem h₃, Set.ncard_singleton]

/-- A failure of commutation exhibits six distinct vertices in the same component. -/
theorem six_le_component_of_noncommute [Finite V] {x : V}
    (h : M.first (M.second x) ≠ M.second (M.first x)) :
    6 ≤ (M.graph.connectedComponentMk x).supp.ncard := by
  let f := M.first
  let g := M.second
  change f (g x) ≠ g (f x) at h
  let six : Set V := {x, f x, g x, f (g x), g (f x), f (g (f x))}
  have hf : Function.Involutive f := M.first_involutive
  have hg : Function.Involutive g := M.second_involutive
  have nf : ∀ y, f y ≠ y := M.first_ne_self
  have ng : ∀ y, g y ≠ y := M.second_ne_self
  have nd : ∀ y, f y ≠ g y := M.partners_ne
  have h₁ : x ∉ ({f x, g x, f (g x), g (f x), f (g (f x))} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    grind [Function.Involutive]
  have h₂ : f x ∉ ({g x, f (g x), g (f x), f (g (f x))} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    grind [Function.Involutive]
  have h₃ : g x ∉ ({f (g x), g (f x), f (g (f x))} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    grind [Function.Involutive]
  have h₄ : f (g x) ∉ ({g (f x), f (g (f x))} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    grind [Function.Involutive]
  have h₅ : g (f x) ∉ ({f (g (f x))} : Set V) := by
    simpa using (nf (g (f x))).symm
  have count : six.ncard = 6 := by
    dsimp [six]
    rw [Set.ncard_insert_of_notMem h₁, Set.ncard_insert_of_notMem h₂,
      Set.ncard_insert_of_notMem h₃, Set.ncard_insert_of_notMem h₄,
      Set.ncard_insert_of_notMem h₅, Set.ncard_singleton]
  rw [← count, M.supp_eq_reachable x]
  refine Set.ncard_le_ncard (fun y hy => ?_) (Set.toFinite _)
  simp only [six, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Reachable.rfl
  · exact M.stepFirst x
  · exact M.stepSecond x
  · exact (M.stepSecond x).trans (M.stepFirst (g x))
  · exact (M.stepFirst x).trans (M.stepSecond (f x))
  · exact ((M.stepFirst x).trans (M.stepSecond (f x))).trans (M.stepFirst (g (f x)))

/-- A vertex fails to commute exactly when its component has at least six vertices. -/
theorem noncommute_iff_six_le_component [Finite V] (x : V) :
    M.first (M.second x) ≠ M.second (M.first x) ↔
      6 ≤ (M.graph.connectedComponentMk x).supp.ncard := by
  refine ⟨M.six_le_component_of_noncommute, fun size h => ?_⟩
  rw [M.component_eq_square h, M.square_card x] at size
  omega

/-- A total vertex count not divisible by four forces a component with at least six vertices. -/
theorem exists_large_component_of_not_dvd [Fintype V] (hcard : ¬ 4 ∣ Fintype.card V) :
    ∃ C : M.graph.ConnectedComponent, 6 ≤ C.supp.ncard := by
  classical
  by_contra! h
  let _ := Fintype.ofFinite M.graph.ConnectedComponent
  have four (C : M.graph.ConnectedComponent) : C.supp.ncard = 4 := by
    induction C using ConnectedComponent.ind with
    | _ x =>
      have hc : M.first (M.second x) = M.second (M.first x) := by
        by_contra nh
        exact (Nat.not_le_of_gt (h _)) ((M.noncommute_iff_six_le_component x).mp nh)
      rw [M.component_eq_square hc, M.square_card x]
  have count : Fintype.card V = ∑ C : M.graph.ConnectedComponent, C.supp.ncard := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
      (f := M.graph.connectedComponentMk) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    exact Finset.sum_congr rfl fun C _ => by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext x
      simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
  rw [count] at hcard
  simp only [four, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hcard
  exact hcard (dvd_mul_left 4 _)

end Matchings

end D5.S3.Combinatorics.Matroids.AlternatingMatchingComponents
