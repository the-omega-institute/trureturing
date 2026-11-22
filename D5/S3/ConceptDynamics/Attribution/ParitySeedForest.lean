/- GID: D5/S3/ConceptDynamics/Attribution/ParitySeedForest
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParitySeedForest
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Restrict marked parity supports to forests without increasing coordinate costs. -/

import D5.S3.ConceptDynamics.Attribution.ParitySeedSupport
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.ParitySeedForest

private def supportGraph {P Q : Type*} (e : P → Q → Bool) : SimpleGraph (P ⊕ Q) where
  Adj x y := match x, y with
    | .inl p, .inr q | .inr q, .inl p => e p q = true
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> exact id⟩
  loopless := ⟨by intro x; cases x <;> exact id⟩

private theorem cycle_degree {V : Type*} [Fintype V] {G : SimpleGraph V} {x : V}
    {w : G.Walk x x} (hw : w.IsCycle) (v : V) :
    letI := Classical.decEq V
    let C := w.toSubgraph.spanningCoe
    letI : DecidableRel C.Adj := Classical.decRel _
    C.degree v = 0 ∨ C.degree v = 2 := by
  classical
  let C := w.toSubgraph.spanningCoe
  have cyc : C.IsCycles := hw.isCycles_spanningCoe_toSubgraph
  by_cases h : (C.neighborSet v).Nonempty
  · exact Or.inr (by simpa only [SimpleGraph.ncard_neighborSet] using cyc h)
  · left
    apply SimpleGraph.IsIsolated.degree_eq_zero
    change C.IsIsolated v
    simpa [SimpleGraph.IsIsolated, Set.not_nonempty_iff_eq_empty] using h

private theorem sum_bool_add_remove {Q : Type*} [Fintype Q] (e f : Q → Bool)
    (subset : ∀ q, f q = true → e q = true) :
    (∑ q, (e q && !f q).toNat) + (∑ q, (f q).toNat) = ∑ q, (e q).toNat := by
  rw [← sum_add_distrib]
  refine sum_congr rfl fun q _ => ?_
  specialize subset q
  cases he : e q <;> cases hf : f q <;> simp_all

private def markedMass {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (e : P → Q → Bool) (p0 : P) (q0 : Q) (p : P) (q : Q) : ℕ :=
  (e p q).toNat + if p = p0 ∧ q = q0 ∧ e p q = false then 2 else 0

private theorem row_markedMass {P Q : Type*} [Fintype Q] [DecidableEq P] [DecidableEq Q]
    (e : P → Q → Bool) (p0 : P) (q0 : Q) (p : P) :
    (∑ q, markedMass e p0 q0 p q) =
      (∑ q, (e p q).toNat) + if p = p0 ∧ e p q0 = false then 2 else 0 := by
  unfold markedMass
  rw [sum_add_distrib, add_right_inj]
  rw [← sum_erase_add _ _ (mem_univ q0)]
  have zero : (∑ q ∈ univ.erase q0, if p = p0 ∧ q = q0 ∧ e p q = false then 2 else 0) = 0 :=
    sum_eq_zero fun q hq => ite_eq_right fun h => (mem_erase.mp hq).1 h.2.1
  simp [zero]

private theorem row_remove {P Q : Type*} [Fintype Q] [DecidableEq P] [DecidableEq Q]
    (e f : P → Q → Bool) (p0 : P) (q0 : Q) (p : P)
    (sub : ∀ q, f p q = true → e p q = true)
    (rem : (∑ q, (f p q).toNat) = 0 ∨ (∑ q, (f p q).toNat) = 2) :
    let g (p : P) (q : Q) := e p q && !f p q
    (∑ q, markedMass g p0 q0 p q) ≤ (∑ q, markedMass e p0 q0 p q) ∧
    (∑ q, markedMass g p0 q0 p q) % 2 = (∑ q, markedMass e p0 q0 p q) % 2 := by
  dsimp only
  rw [row_markedMass, row_markedMass]
  have sums := sum_bool_add_remove (e p) (f p) sub
  have nonzero : f p q0 = true → 0 < ∑ q, (f p q).toNat := by
    intro h
    have hle := single_le_sum (f := fun q => (f p q).toNat) (fun q _ => Nat.zero_le _) (mem_univ q0)
    simpa [h, Nat.succ_le_iff] using hle
  specialize sub q0
  by_cases hp : p = p0
  · subst p
    rcases rem with rem | rem
    all_goals cases hb : e p0 q0 <;> cases hd : f p0 q0 <;> simp_all
    omega
  · simp [hp]
    omega

private theorem cycle_mask {P Q : Type*} [Fintype P] [Fintype Q]
    (e : P → Q → Bool) {x : P ⊕ Q} {w : (supportGraph e).Walk x x} (hw : w.IsCycle) :
    ∃ f : P → Q → Bool,
      (∀ p q, f p q = true → e p q = true) ∧
      (∀ p, (∑ q, (f p q).toNat) = 0 ∨ (∑ q, (f p q).toNat) = 2) ∧
      (∀ q, (∑ p, (f p q).toNat) = 0 ∨ (∑ p, (f p q).toNat) = 2) ∧
      ∃ p q, f p q = true := by
  classical
  let C := w.toSubgraph.spanningCoe
  let f (p : P) (q : Q) := decide (C.Adj (.inl p) (.inr q))
  have le : C ≤ supportGraph e := w.toSubgraph.spanningCoe_le
  have row (p : P) : C.degree (.inl p) = ∑ q, (f p q).toNat := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, C.neighborFinset_eq_filter,
      card_eq_sum_ones, sum_filter]
    rw [Fintype.sum_sum_type]
    have none (p' : P) : ¬C.Adj (.inl p) (.inl p') := fun h => le h
    simp only [none, ite_false, sum_const_zero, zero_add]
    apply sum_congr rfl
    intro q _
    by_cases h : C.Adj (.inl p) (.inr q) <;> simp [f, h]
  have col (q : Q) : C.degree (.inr q) = ∑ p, (f p q).toNat := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, C.neighborFinset_eq_filter,
      card_eq_sum_ones, sum_filter]
    rw [Fintype.sum_sum_type]
    have none (q' : Q) : ¬C.Adj (.inr q) (.inr q') := fun h => le h
    simp only [none, ite_false, sum_const_zero, add_zero]
    apply sum_congr rfl
    intro p _
    by_cases h : C.Adj (.inl p) (.inr q)
    · simp [f, h, h.symm]
    · have h' : ¬C.Adj (.inr q) (.inl p) := fun hadj => h hadj.symm
      simp [f, h, h']
  refine ⟨f, fun p q h => le (of_decide_eq_true h), ?_, ?_, ?_⟩
  · intro p
    rw [← row]
    exact cycle_degree hw (.inl p)
  · intro q
    rw [← col]
    exact cycle_degree hw (.inr q)
  · let y := w.snd
    have first : C.Adj x y := w.toSubgraph_adj_snd hw.not_nil
    rcases hx : x with p | q <;> rcases hy : y with p' | q'
    · rw [hx, hy] at first
      exact False.elim (le first)
    · exact ⟨p, q', decide_eq_true (by simpa only [hx, hy] using first)⟩
    · exact ⟨p', q, decide_eq_true (by simpa only [hx, hy] using first.symm)⟩
    · rw [hx, hy] at first
      exact False.elim (le first)

private theorem col_markedMass {P Q : Type*} [Fintype P] [DecidableEq P] [DecidableEq Q]
    (e : P → Q → Bool) (p0 : P) (q0 : Q) (q : Q) :
    (∑ p, markedMass e p0 q0 p q) = (∑ p, markedMass (fun q p => e p q) q0 p0 q p) := by
  apply sum_congr rfl
  intro p _
  simp [markedMass, and_left_comm]

private def Within {P Q : Type*} [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
    (p0 : P) (q0 : Q) (k : ℕ) (e : P → Q → Bool) : Prop :=
  (∀ p, let m := ∑ q, markedMass e p0 q0 p q; m ≤ k ∧ m % 2 = 1) ∧
  (∀ q, let m := ∑ p, markedMass e p0 q0 p q; m ≤ k ∧ m % 2 = 1)

private theorem exists_acyclic_marked_support {P Q : Type*}
    [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
    (p0 : P) (q0 : Q) (k : ℕ) (e : P → Q → Bool)
    (he : Within p0 q0 k e) :
    ∃ g : P → Q → Bool,
      (∀ p q, g p q = true → e p q = true) ∧
      Within p0 q0 k g ∧ (supportGraph g).IsAcyclic := by
  classical
  let cards (g : P → Q → Bool) := ∑ p, ∑ q, (g p q).toNat
  let ok (g : P → Q → Bool) : Prop :=
    (∀ p q, g p q = true → e p q = true) ∧ Within p0 q0 k g
  have hex : ∃ n, ∃ g, ok g ∧ cards g = n := ⟨cards e, e, ⟨fun _ _ h => h, he⟩, rfl⟩
  obtain ⟨g, ⟨inc, gr, gc⟩, hcard⟩ := Nat.find_spec hex
  refine ⟨g, inc, ⟨gr, gc⟩, ?_⟩
  intro x w hw
  obtain ⟨f, sub, fr, fc, p, q, chosen⟩ := cycle_mask g hw
  let h (p : P) (q : Q) := g p q && !f p q
  have held : ∀ p q, h p q = true → g p q = true :=
    fun p q hg => (Bool.and_eq_true_iff.mp hg).1
  have hok : ok h := by
    refine ⟨fun p q hh => inc p q (held p q hh), ?_, ?_⟩
    · intro p
      obtain ⟨hm, hp⟩ := row_remove g f p0 q0 p (sub p) (fr p)
      exact ⟨hm.trans (gr p).1, hp.trans (gr p).2⟩
    · intro q
      have hg := gc q
      dsimp only at hg ⊢
      rw [col_markedMass] at hg ⊢
      obtain ⟨hm, hp⟩ := row_remove (fun q p => g p q) (fun q p => f p q)
        q0 p0 q (fun p => sub p q) (fc q)
      exact ⟨hm.trans hg.1, hp.trans hg.2⟩
  have rowAdd (p : P) : (∑ q, (h p q).toNat) + (∑ q, (f p q).toNat) =
      ∑ q, (g p q).toNat := sum_bool_add_remove (g p) (f p) (sub p)
  have cardAdd : cards h + cards f = cards g := by
    dsimp only [cards]
    rw [← sum_add_distrib]
    exact sum_congr rfl fun p _ => rowAdd p
  have positive : 0 < cards f := by
    have inner : (f p q).toNat ≤ ∑ q', (f p q').toNat :=
      single_le_sum (fun q' _ => Nat.zero_le ((f p q').toNat)) (mem_univ q)
    have outer : (∑ q', (f p q').toNat) ≤ cards f :=
      single_le_sum (fun p' _ => Nat.zero_le (∑ q', (f p' q').toNat)) (mem_univ p)
    simpa [chosen, Nat.succ_le_iff] using inner.trans outer
  have min := Nat.find_min' hex ⟨h, hok, rfl⟩
  omega

open D5.S3.ConceptDynamics.Attribution.ParitySeedSupport
open D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
open D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization

private theorem marked_forest_budget (n k : ℕ) (budget : Fin (n + 2) → ℕ)
    (h : markedSupportWithin n k budget) :
    ∃ (even : (n + 2) % 2 = 0)
      (e : EvenSubset (n + 2) → OddSubset (n + 2) → Bool)
      (marked : OddSubset (n + 2)),
      let full : EvenSubset (n + 2) := ⟨univ, by simpa using even⟩
      let base := minimalBase e full marked
      (∀ p, (∑ q, base p q) ≤ k ∧ (∑ q, base p q) % 2 = 1) ∧
      (∀ q, (∑ p, base p q) ≤ k ∧ (∑ p, base p q) % 2 = 1) ∧
      (∀ i, supportCount base full marked i ≤ budget i) ∧ (supportGraph e).IsAcyclic := by
  classical
  obtain ⟨even, e, q0, hr, hc, hb⟩ := h
  let full : EvenSubset (n + 2) := ⟨univ, by simpa using even⟩
  have within : Within full q0 k e := ⟨hr, hc⟩
  obtain ⟨g, inc, ⟨gr, gc⟩, acyclic⟩ := exists_acyclic_marked_support full q0 k e within
  refine ⟨even, g, q0, gr, gc, fun i => le_trans ?_ (hb i), acyclic⟩
  unfold supportCount
  gcongr with p q
  split
  · split
    · rfl
    · simp [minimalBase, *]
      specialize inc p q
      cases he : e p q <;> cases hg : g p q <;> simp_all
  · rfl

/-- A marked support with no cycle among its chosen binary entries. -/
def forestSupportWithin (n k : ℕ) (budget : Fin (n + 2) → ℕ) : Prop :=
  ∃ (even : (n + 2) % 2 = 0)
    (e : EvenSubset (n + 2) → OddSubset (n + 2) → Bool)
    (marked : OddSubset (n + 2)),
    let full : EvenSubset (n + 2) := ⟨univ, by simpa using even⟩
    let base := minimalBase e full marked
    (∀ p, (∑ q, base p q) ≤ k ∧ (∑ q, base p q) % 2 = 1) ∧
    (∀ q, (∑ p, base p q) ≤ k ∧ (∑ p, base p q) % 2 = 1) ∧
    (∀ i, supportCount base full marked i ≤ budget i) ∧ (supportGraph e).IsAcyclic

/-- Restricting the chosen support to a forest preserves simultaneous coordinate feasibility. -/
theorem forest_support_iff (n k : ℕ) (even : (n + 2) % 2 = 0) (odd : k % 2 = 1)
    (budget : Fin (n + 2) → ℕ) :
    (∃ z : Fin (n + 2) → ℕ, RealizableSeedCounts n k z ∧ (∀ i, z i ≤ budget i)) ↔
    forestSupportWithin n k budget := by
  rw [binary_support_iff n k even odd budget]
  constructor
  · exact marked_forest_budget n k budget
  · rintro ⟨even', e, marked, rows, cols, score, _⟩
    exact ⟨even', e, marked, rows, cols, score⟩

end D5.S3.ConceptDynamics.Attribution.ParitySeedForest
