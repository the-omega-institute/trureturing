import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactNormalized
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Finset.Prod

/-! Exterior parity alone forces even axis cuts in the contact graph at a vertex. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactCutParity

open scoped BigOperators
open Finset
open BalancedCriticalSpectrum (Q)
open BalancedCubeGirth (flip_comm)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9SharedContactNormalized (LocalRules)

open Classical in
private theorem even_crossing_of_even_rows {α : Type*} [Fintype α] [LinearOrder α]
    (A : Finset α) (R : α → α → Prop) [DecidableRel R]
    (hsymm : ∀ a b, R a b → R b a) (hloop : ∀ a, ¬ R a a)
    (hrows : ∀ a ∈ A, Even ((univ.filter (R a)).card)) :
    Even (((A.product (univ \ A)).filter fun p => R p.1 p.2).card) := by
  let internal := (A.product A).filter fun p => R p.1 p.2
  let before := internal.filter fun p => p.1 < p.2
  let after := internal.filter fun p => ¬ p.1 < p.2
  have hsplit : before.card + after.card = internal.card :=
    card_filter_add_card_filter_not (s := internal) _
  have hinternal {p : α × α} (hp : p ∈ internal) :
      p.1 ∈ A ∧ p.2 ∈ A ∧ R p.1 p.2 := by
    obtain ⟨hp, hr⟩ := mem_filter.mp hp
    exact ⟨(mem_product.mp hp).1, (mem_product.mp hp).2, hr⟩
  have hswap {p : α × α} (hp : p ∈ internal) : p.swap ∈ internal := by
    obtain ⟨h₁, h₂, hr⟩ := hinternal hp
    exact mem_filter.mpr ⟨mem_product.mpr ⟨h₂, h₁⟩, hsymm _ _ hr⟩
  have hcards : before.card = after.card := by
    apply card_bij (fun p _ => p.swap)
    · intro p hp
      obtain ⟨hp, hlt⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨hswap hp, not_lt_of_ge hlt.le⟩
    · intro p _ q _ he
      exact congrArg Prod.swap he
    · intro p hp
      obtain ⟨hp, hgt⟩ := mem_filter.mp hp
      have hne : p.1 ≠ p.2 := fun he => hloop p.2 (he ▸ (hinternal hp).2.2)
      have hlt : p.2 < p.1 := lt_of_le_of_ne (le_of_not_gt hgt) (Ne.symm hne)
      exact ⟨p.swap, mem_filter.mpr ⟨hswap hp, hlt⟩, Prod.swap_swap _⟩
  have heven : Even internal.card := ⟨before.card, by omega⟩
  have hcard (B : Finset α) :
      ((A.product B).filter fun p => R p.1 p.2).card =
        ∑ a ∈ A, (B.filter (R a)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_product A B _
  have hpartition :
      ((A.product univ).filter fun p => R p.1 p.2).card =
        internal.card + ((A.product (univ \ A)).filter fun p => R p.1 p.2).card := by
    rw [hcard univ, hcard (univ \ A), show internal.card = ∑ a ∈ A,
      (A.filter (R a)).card from hcard A, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext b
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_sdiff]
      tauto
    · exact disjoint_left.mpr (fun b hb hb' =>
        (mem_sdiff.mp (mem_filter.mp hb').1).2 (mem_filter.mp hb).1)
  have htotal : Even (((A.product univ).filter fun p => R p.1 p.2).card) := by
    rw [hcard]
    exact Finset.even_sum _ hrows
  rw [hpartition, Nat.even_add] at htotal
  exact htotal.mp heven

open Classical in
/-- A point separated from a cube support sees an even crossing count in every
axis cut if its one-flip neighbours have even exterior degrees into that support. -/
theorem even_cut_of_exterior_degree {D : Finset (Q 9)} {x : Q 9}
    (A : Finset (Fin 9)) (hD : LocalRules D)
    (hx : x ∉ D) (hsep : ∀ i, BalancedCriticalSpectrum.flip x i ∉ D) :
    Even (((A.product (univ \ A)).filter
      fun p => BalancedCriticalSpectrum.flip (BalancedCriticalSpectrum.flip x p.1) p.2 ∈ D).card) := by
  let R (i j : Fin 9) := BalancedCriticalSpectrum.flip (BalancedCriticalSpectrum.flip x i) j ∈ D
  apply even_crossing_of_even_rows A R
  · intro i j h
    dsimp only [R] at h ⊢
    rwa [flip_comm]
  · intro i
    simpa only [R, BalancedCriticalSpectrum.flip_flip] using hx
  · intro i _
    have heq : univ.filter (R i) = directions D (BalancedCriticalSpectrum.flip x i) := by
      ext j
      simp [R, mem_directions]
    rw [heq]
    exact hD.exterior_degree _ (hsep i)

#print axioms even_cut_of_exterior_degree

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactCutParity
