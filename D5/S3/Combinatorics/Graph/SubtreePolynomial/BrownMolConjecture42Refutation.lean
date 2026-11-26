/- GID: D5/S3/Combinatorics/Graph/SubtreePolynomial/BrownMolConjecture42Refutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SubtreePolynomial/BrownMolConjecture42Refutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/SubtreePolynomial/BrownMolConjecture42Refutation.Conjecture42; result=D5/S3/Combinatorics/Graph/SubtreePolynomial/BrownMolConjecture42Refutation.conjecture42_false; claim=D5/S3/Combinatorics/Graph/SubtreePolynomial/BrownMolConjecture42Refutation.Conjecture42
   digest: A subtree root of a 206-vertex tree violates the Brown–Mol inner bound. -/

import OmegaBuild.Commands
import D5.S3.Weil.ZetaAnalytic.RoucheZeroCount
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

compile_only_with_mathlib

/-!
# Brown–Mol Conjecture 4.2

The annulus in Brown and Mol, arXiv:1810.08655v1, Conjecture 4.2 (p. 14),
is violated by a tree with a hub and 41 branches of four leaves each.
The subtree polynomial counts connected induced vertex sets. An exact
Gaussian-integer certificate and the rectangle form of Rouché's theorem
locate a root strictly inside the inner circle. See preregistration #34339.
-/

-- The required single-line utility header contains three qualified GID fields.
set_option linter.style.longLine false

namespace BrownMol

noncomputable section

open Polynomial

private def ConnectedSubsets {V : Type*} (G : SimpleGraph V) :=
  {s : Finset V // (G.induce (↑s : Set V)).Connected}

private instance connectedSubsetsFintype {V : Type*} [Finite V] (G : SimpleGraph V) :
    Fintype (ConnectedSubsets G) :=
  letI := Fintype.ofFinite V
  Fintype.ofFinite {s : Finset V // (G.induce (↑s : Set V)).Connected}

/-- The generating polynomial for nonempty connected induced vertex subsets. -/
def subtreePolynomial {V : Type*} [Finite V] (G : SimpleGraph V) : ℂ[X] :=
  ∑ s : ConnectedSubsets G, X ^ s.val.card

/-- Brown and Mol, Conjecture 4.2, arXiv:1810.08655v1. -/
def Conjecture42 : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), G.IsTree → 2 ≤ Fintype.card V →
    ∀ z : ℂ, (subtreePolynomial G).eval z = 0 →
      let m : ℝ := (Fintype.card V - 1 : ℕ)
      (1 / 2 : ℝ) ≤ ‖z + 1 / 2‖ ∧ ‖z + 1 / 2‖ ≤ 1 / 2 + m ^ (1 / m)

/-! ## The witness tree and its connected induced sets -/

private abbrev Vertex := Unit ⊕ (Fin 41 × (Unit ⊕ Fin 4))

private def hub : Vertex := .inl ()
private def branchCenter (i : Fin 41) : Vertex := .inr (i, .inl ())
private def leaf (i : Fin 41) (j : Fin 4) : Vertex := .inr (i, .inr j)

private inductive Down : Vertex → Vertex → Prop
  | hub_center (i : Fin 41) : Down hub (branchCenter i)
  | center_leaf (i : Fin 41) (j : Fin 4) : Down (branchCenter i) (leaf i j)

/-- The hub has 41 branches, each with one center and four leaves. -/
private def T : SimpleGraph Vertex where
  Adj u v := Down u v ∨ Down v u
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨by rintro u (h | h) <;> cases h⟩

private theorem adj_hub_center (i : Fin 41) : T.Adj hub (branchCenter i) :=
  Or.inl (.hub_center i)

private theorem adj_center_leaf (i : Fin 41) (j : Fin 4) : T.Adj (branchCenter i) (leaf i j) :=
  Or.inl (.center_leaf i j)

private theorem leaf_neighbor {i : Fin 41} {j : Fin 4} {v : Vertex}
    (h : T.Adj (leaf i j) v) : v = branchCenter i := by
  rcases h with h | h
  · cases h
  · cases h
    rfl

private def branchIndex : Vertex → Option (Fin 41)
  | .inl _ => none
  | .inr (i, _) => some i

private theorem vertex_cases (v : Vertex) :
    v = hub ∨ (∃ i, v = branchCenter i) ∨ ∃ i j, v = leaf i j := by
  rcases v with ⟨⟩ | ⟨i, ⟨⟩ | j⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨i, rfl⟩)
  · exact Or.inr (Or.inr ⟨i, j, rfl⟩)

private theorem reachable_label {V A : Type*} {G : SimpleGraph V}
    (f : V → A) (hedge : ∀ ⦃u v⦄, G.Adj u v → f u = f v)
    {u v : V} (h : G.Reachable u v) : f u = f v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hedge hadj).trans ih

private theorem T_connected : T.Connected := by
  have reaches (v : Vertex) : T.Reachable hub v := by
    rcases vertex_cases v with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
    · exact SimpleGraph.Reachable.rfl
    · exact (adj_hub_center i).reachable
    · exact (adj_hub_center i).reachable.trans (adj_center_leaf i j).reachable
  exact @SimpleGraph.Connected.mk _ _ (fun u v => (reaches u).symm.trans (reaches v)) ⟨hub⟩

private theorem T_isTree : T.IsTree := by
  rw [SimpleGraph.isTree_iff_minimal_connected]
  refine ⟨T_connected, ?_⟩
  intro G hG hle
  have hubEdge (i : Fin 41) : G.Adj hub (branchCenter i) := by
    by_contra hn
    let p (v : Vertex) : Prop := branchIndex v = some i
    have step ⦃u v : Vertex⦄ (ha : G.Adj u v) : p u = p v := by
      suffices forward : ∀ ⦃a b⦄, G.Adj a b → Down a b → p a = p b by
        rcases hle ha with hd | hd
        · exact forward ha hd
        · exact (forward ha.symm hd).symm
      intro a b hab hab'
      cases hab' with
      | hub_center k =>
        have hki : k ≠ i := fun eq => hn (eq ▸ hab)
        simp [p, branchIndex, hub, branchCenter, hki]
      | center_leaf k j => rfl
    have eq := reachable_label p step (hG hub (branchCenter i))
    simp [p, branchIndex, hub, branchCenter] at eq
  have leafEdge (i : Fin 41) (j : Fin 4) : G.Adj (branchCenter i) (leaf i j) := by
    by_contra hn
    let p (v : Vertex) : Prop := v = leaf i j
    have step ⦃u v : Vertex⦄ (ha : G.Adj u v) : p u = p v := by
      apply propext
      constructor
      · intro hu
        change u = leaf i j at hu
        subst u
        have hv := leaf_neighbor (hle ha)
        subst v
        exact (hn ha.symm).elim
      · intro hv
        change v = leaf i j at hv
        subst v
        have hu := leaf_neighbor (hle ha.symm)
        subst u
        exact (hn ha).elim
    have eq := reachable_label p step (hG (branchCenter i) (leaf i j))
    simp [p, branchCenter, leaf] at eq
  intro u v ha
  rcases ha with h | h
  · cases h with
    | hub_center i => exact hubEdge i
    | center_leaf i j => exact leafEdge i j
  · cases h with
    | hub_center i => exact (hubEdge i).symm
    | center_leaf i j => exact (leafEdge i j).symm

private theorem card_vertex : Fintype.card Vertex = 206 := by simp [Vertex]

section ConnectedSets

variable {s : Finset Vertex}

private theorem reaches_in (hu : u ∈ s) (hv : v ∈ s) (h : T.Adj u v) :
    (T.induce (↑s : Set Vertex)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ :=
  SimpleGraph.Adj.reachable h

private theorem connected_from (ha : a ∈ s)
    (reaches : ∀ v : (↑s : Set Vertex), (T.induce (↑s : Set Vertex)).Reachable ⟨a, ha⟩ v) :
    (T.induce (↑s : Set Vertex)).Connected :=
  @SimpleGraph.Connected.mk _ _ (fun u v => (reaches u).symm.trans (reaches v)) ⟨⟨a, ha⟩⟩

private theorem center_mem_of_leaf
    (hs : (T.induce (↑s : Set Vertex)).Connected)
    {i : Fin 41} {j : Fin 4} {v : Vertex}
    (hl : leaf i j ∈ s) (hv : v ∈ s) (hne : v ≠ leaf i j) :
    branchCenter i ∈ s := by
  by_contra hc
  let p (w : (↑s : Set Vertex)) : Prop := w.val = leaf i j
  have step ⦃u v⦄ (ha : (T.induce (↑s : Set Vertex)).Adj u v) : p u = p v := by
    have ha' : T.Adj u.val v.val := ha
    apply propext
    constructor
    · intro hu
      have hv' := leaf_neighbor (show T.Adj (leaf i j) v.val from hu ▸ ha')
      exact (hc (hv' ▸ v.property)).elim
    · intro hv'
      have hu := leaf_neighbor (show T.Adj (leaf i j) u.val from hv' ▸ ha'.symm)
      exact (hc (hu ▸ u.property)).elim
  have eq := reachable_label p step (hs ⟨leaf i j, hl⟩ ⟨v, hv⟩)
  exact hne (Eq.mp eq (show p ⟨leaf i j, hl⟩ from rfl))

private theorem same_branch (hs : (T.induce (↑s : Set Vertex)).Connected)
    (hh : hub ∉ s) (hu : u ∈ s) (hv : v ∈ s) : branchIndex u = branchIndex v := by
  apply reachable_label (fun w : (↑s : Set Vertex) => branchIndex w.val) _ (hs ⟨u, hu⟩ ⟨v, hv⟩)
  intro a b ha
  have hadj : T.Adj a.val b.val := ha
  have downStep ⦃x y : Vertex⦄ (hx : x ∈ s) (hd : Down x y) :
      branchIndex x = branchIndex y := by
    cases hd with
    | hub_center i => exact (hh hx).elim
    | center_leaf i j => rfl
  rcases hadj with hd | hd
  · exact downStep a.property hd
  · exact (downStep b.property hd).symm

end ConnectedSets

private abbrev LeafSet := Finset (Fin 4)

private def leafEmbedding (i : Fin 41) : Fin 4 ↪ Vertex :=
  ⟨leaf i, by intro a b h; simpa [leaf] using h⟩

@[simp] private theorem leafEmbedding_apply (i : Fin 41) (j : Fin 4) :
    leafEmbedding i j = leaf i j := rfl

private def branchSet (i : Fin 41) (B : LeafSet) : Finset Vertex :=
  insert (branchCenter i) (B.map (leafEmbedding i))

@[simp] private theorem hub_not_mem_branchSet (i : Fin 41) (B : LeafSet) :
    hub ∉ branchSet i B := by
  simp [branchSet, hub, branchCenter, leaf]

@[simp] private theorem center_mem_branchSet (k i : Fin 41) (B : LeafSet) :
    branchCenter k ∈ branchSet i B ↔ k = i := by
  simp [branchSet, branchCenter, leaf]

@[simp] private theorem leaf_mem_branchSet (k i : Fin 41) (j : Fin 4) (B : LeafSet) :
    leaf k j ∈ branchSet i B ↔ k = i ∧ j ∈ B := by
  constructor
  · simp only [branchSet, Finset.mem_insert, Finset.mem_map, leafEmbedding_apply,
      leaf, branchCenter, Sum.inr.injEq, Prod.mk.injEq,
      reduceCtorEq, and_false, false_or]
    rintro ⟨x, hx, rfl, rfl⟩
    exact ⟨rfl, hx⟩
  · rintro ⟨rfl, hj⟩
    exact Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨j, hj, rfl⟩)

private theorem branch_supported {i : Fin 41} {B : LeafSet} {v : Vertex}
    (hv : v ∈ branchSet i B) : branchIndex v = some i := by
  rcases vertex_cases v with rfl | ⟨k, rfl⟩ | ⟨k, j, rfl⟩
  · exact (hub_not_mem_branchSet i B hv).elim
  · obtain rfl := (center_mem_branchSet k i B).mp hv
    rfl
  · obtain ⟨rfl, _⟩ := (leaf_mem_branchSet k i j B).mp hv
    rfl

private theorem card_branchSet (i : Fin 41) (B : LeafSet) :
    (branchSet i B).card = B.card + 1 := by
  rw [branchSet, Finset.card_insert_of_notMem, Finset.card_map]
  simp [branchCenter, leaf]

private def rootBranch (f : Fin 41 → Option LeafSet) (i : Fin 41) : Finset Vertex :=
  (f i).elim ∅ (branchSet i)

private def rootSet (f : Fin 41 → Option LeafSet) : Finset Vertex :=
  insert hub (Finset.univ.biUnion (rootBranch f))

@[simp] private theorem hub_mem_rootSet (f : Fin 41 → Option LeafSet) :
    hub ∈ rootSet f := Finset.mem_insert_self _ _

private theorem rootBranch_supported {f : Fin 41 → Option LeafSet} {i : Fin 41}
    {v : Vertex} (hv : v ∈ rootBranch f i) : branchIndex v = some i := by
  cases h : f i with
  | none => simp [rootBranch, h] at hv
  | some B =>
    exact branch_supported (show v ∈ branchSet i B by simpa [rootBranch, h] using hv)

private theorem mem_rootSet_of_branchIndex {f : Fin 41 → Option LeafSet} {v : Vertex}
    {i : Fin 41} (hi : branchIndex v = some i) : v ∈ rootSet f ↔ v ∈ rootBranch f i := by
  simp only [rootSet, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | ⟨k, hk⟩)
    · cases hi
    · have eq : some k = some i := (rootBranch_supported hk).symm.trans hi
      obtain rfl := Option.some.inj eq
      exact hk
  · exact fun hv => Or.inr ⟨i, hv⟩

@[simp] private theorem center_mem_rootSet (f : Fin 41 → Option LeafSet) (i : Fin 41) :
    branchCenter i ∈ rootSet f ↔ ∃ B, f i = some B := by
  rw [mem_rootSet_of_branchIndex (f := f) (v := branchCenter i) (i := i) rfl]
  cases h : f i <;> simp [rootBranch, h]

@[simp] private theorem leaf_mem_rootSet (f : Fin 41 → Option LeafSet) (i : Fin 41)
    (j : Fin 4) : leaf i j ∈ rootSet f ↔ ∃ B, f i = some B ∧ j ∈ B := by
  rw [mem_rootSet_of_branchIndex (f := f) (v := leaf i j) (i := i) rfl]
  cases h : f i <;> simp [rootBranch, h]

private theorem card_insert_biUnion {ι α : Type*} [Fintype ι] [DecidableEq α]
    (v : α) (parts : ι → Finset α) (hv : ∀ i, v ∉ parts i)
    (hd : Pairwise fun i k => Disjoint (parts i) (parts k)) :
    (insert v (Finset.univ.biUnion parts)).card = (∑ i, (parts i).card) + 1 := by
  have hnot : v ∉ Finset.univ.biUnion parts := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
    exact hv i hi
  rw [Finset.card_insert_of_notMem hnot, Finset.card_biUnion]
  exact fun i _ k _ hne => hd hne

private theorem card_rootSet (f : Fin 41 → Option LeafSet) :
    (rootSet f).card = (∑ i, (f i).elim 0 (fun B => B.card + 1)) + 1 := by
  have hhub (i : Fin 41) : hub ∉ rootBranch f i := by
    intro hi
    cases rootBranch_supported hi
  have hpair : Pairwise fun i k => Disjoint (rootBranch f i) (rootBranch f k) := by
    intro i k hne
    apply Finset.disjoint_left.mpr
    intro v hi hk
    exact hne (Option.some.inj ((rootBranch_supported hi).symm.trans (rootBranch_supported hk)))
  calc
    (rootSet f).card = (∑ i, (rootBranch f i).card) + 1 :=
      card_insert_biUnion hub (rootBranch f) hhub hpair
    _ = _ := by
      apply congrArg (fun n : ℕ => n + 1)
      apply Finset.sum_congr rfl
      intro i _
      cases h : f i <;> simp [rootBranch, h, card_branchSet]

private theorem branchSet_connected (i : Fin 41) (B : LeafSet) :
    (T.induce (↑(branchSet i B) : Set Vertex)).Connected := by
  have hc : branchCenter i ∈ branchSet i B := by simp
  apply connected_from hc
  rintro ⟨v, hv⟩
  rcases vertex_cases v with rfl | ⟨k, rfl⟩ | ⟨k, j, rfl⟩
  · simp at hv
  · obtain rfl := (center_mem_branchSet k i B).mp hv
    exact SimpleGraph.Reachable.rfl
  · obtain ⟨rfl, _⟩ := (leaf_mem_branchSet k i j B).mp hv
    exact reaches_in hc hv (adj_center_leaf k j)

private theorem rootSet_connected (f : Fin 41 → Option LeafSet) :
    (T.induce (↑(rootSet f) : Set Vertex)).Connected := by
  apply connected_from (hub_mem_rootSet f)
  rintro ⟨v, hv⟩
  rcases vertex_cases v with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · exact SimpleGraph.Reachable.rfl
  · exact reaches_in (hub_mem_rootSet f) hv (adj_hub_center i)
  · obtain ⟨B, hB, _⟩ := (leaf_mem_rootSet f i j).mp hv
    have hc := (center_mem_rootSet f i).mpr ⟨B, hB⟩
    exact (reaches_in (hub_mem_rootSet f) hc (adj_hub_center i)).trans
      (reaches_in hc hv (adj_center_leaf i j))

private theorem singleton_connected (v : Vertex) :
    (T.induce (↑({v} : Finset Vertex) : Set Vertex)).Connected := by
  apply connected_from (show v ∈ ({v} : Finset Vertex) by simp)
  rintro ⟨w, hw⟩
  have : w = v := Finset.mem_singleton.mp hw
  subst w
  exact SimpleGraph.Reachable.rfl

private abbrev Configuration :=
  (Fin 41 → Option LeafSet) ⊕ ((Fin 41 × LeafSet) ⊕ (Fin 41 × Fin 4))

private def encode : Configuration → ConnectedSubsets T
  | .inl f => ⟨rootSet f, rootSet_connected f⟩
  | .inr (.inl (i, B)) => ⟨branchSet i B, branchSet_connected i B⟩
  | .inr (.inr (i, j)) => ⟨{leaf i j}, singleton_connected (leaf i j)⟩

private theorem rootSet_injective : Function.Injective rootSet := by
  intro f g h
  funext i
  have hc : (∃ B, f i = some B) ↔ (∃ B, g i = some B) := by
    rw [← center_mem_rootSet, ← center_mem_rootSet, h]
  have hl (j : Fin 4) : (∃ B, f i = some B ∧ j ∈ B) ↔ (∃ B, g i = some B ∧ j ∈ B) := by
    rw [← leaf_mem_rootSet, ← leaf_mem_rootSet, h]
  cases hf : f i <;> cases hg : g i
  · rfl
  · simp [hf, hg] at hc
  · simp [hf, hg] at hc
  · rename_i B D
    congr 1
    exact Finset.ext fun j => by simpa [hf, hg] using hl j

private theorem eq_of_branchSet_eq {i k : Fin 41} {B D : LeafSet}
    (h : branchSet i B = branchSet k D) : (i, B) = (k, D) := by
  have hi : branchCenter i ∈ branchSet k D := by rw [← h]; simp
  have hik := (center_mem_branchSet i k D).mp hi
  subst k
  congr 1
  ext j
  have heq := Finset.ext_iff.mp h (leaf i j)
  simpa only [leaf_mem_branchSet, true_and] using heq

private theorem encode_injective : Function.Injective encode := by
  rintro (f | (⟨i, B⟩ | ⟨i, j⟩)) (g | (⟨k, D⟩ | ⟨k, l⟩)) h
  all_goals have he := congrArg Subtype.val h
  all_goals dsimp only [encode] at he
  · exact congrArg Sum.inl (rootSet_injective he)
  · have hm : hub ∈ branchSet k D := he ▸ hub_mem_rootSet f
    simp at hm
  · have hm : hub ∈ ({leaf k l} : Finset Vertex) := he ▸ hub_mem_rootSet f
    simp [hub, leaf] at hm
  · have hm : hub ∈ branchSet i B := he.symm ▸ hub_mem_rootSet g
    simp at hm
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (eq_of_branchSet_eq he)
  · have hm : branchCenter i ∈ ({leaf k l} : Finset Vertex) :=
      he ▸ (show branchCenter i ∈ branchSet i B by simp)
    simp [branchCenter, leaf] at hm
  · have hm : hub ∈ ({leaf i j} : Finset Vertex) := he.symm ▸ hub_mem_rootSet g
    simp [hub, leaf] at hm
  · have hm : branchCenter k ∈ ({leaf i j} : Finset Vertex) :=
      he.symm ▸ (show branchCenter k ∈ branchSet k D by simp)
    simp [branchCenter, leaf] at hm
  · have hm : leaf i j ∈ ({leaf k l} : Finset Vertex) :=
      he ▸ (show leaf i j ∈ ({leaf i j} : Finset Vertex) by simp)
    have hp : i = k ∧ j = l := by simpa [leaf] using hm
    obtain ⟨rfl, rfl⟩ := hp
    rfl

private def leavesOf (s : Finset Vertex) (i : Fin 41) : LeafSet :=
  Finset.univ.filter fun j => leaf i j ∈ s

@[simp] private theorem mem_leavesOf {s : Finset Vertex} {i : Fin 41} {j : Fin 4} :
    j ∈ leavesOf s i ↔ leaf i j ∈ s := by simp [leavesOf]

private theorem encode_surjective : Function.Surjective encode := by
  rintro ⟨s, hs⟩
  by_cases hhub : hub ∈ s
  · let f (i : Fin 41) := if branchCenter i ∈ s then some (leavesOf s i) else none
    refine ⟨.inl f, Subtype.ext ?_⟩
    change rootSet f = s
    ext v
    rcases vertex_cases v with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
    · simp [hhub]
    · by_cases hc : branchCenter i ∈ s <;> simp [f, hc]
    · by_cases hc : branchCenter i ∈ s
      · simp [f, hc]
      · have hl : leaf i j ∉ s :=
          fun hl => hc (center_mem_of_leaf hs hl hhub (by simp [hub, leaf]))
        simp [f, hc, hl]
  · by_cases hcenters : ∃ i, branchCenter i ∈ s
    · obtain ⟨i, hi⟩ := hcenters
      refine ⟨.inr (.inl (i, leavesOf s i)), Subtype.ext ?_⟩
      change branchSet i (leavesOf s i) = s
      ext v
      rcases vertex_cases v with rfl | ⟨k, rfl⟩ | ⟨k, j, rfl⟩
      · simp [hhub]
      · rw [center_mem_branchSet]
        exact ⟨fun h => h ▸ hi, fun hk => Option.some.inj (same_branch hs hhub hk hi)⟩
      · rw [leaf_mem_branchSet, mem_leavesOf]
        constructor
        · rintro ⟨rfl, hj⟩
          exact hj
        · intro hk
          have hki := Option.some.inj (same_branch hs hhub hk hi)
          subst k
          exact ⟨rfl, hk⟩
    · have ⟨⟨v, hv⟩⟩ := hs.nonempty
      rcases vertex_cases v with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
      · exact (hhub hv).elim
      · exact (hcenters ⟨i, hv⟩).elim
      · refine ⟨.inr (.inr (i, j)), Subtype.ext ?_⟩
        change ({leaf i j} : Finset Vertex) = s
        ext w
        rw [Finset.mem_singleton]
        refine ⟨fun h => h.symm ▸ hv, fun hw => ?_⟩
        by_contra hne
        exact hcenters ⟨i, center_mem_of_leaf hs hv hw hne⟩

private noncomputable def configurationEquiv : Configuration ≃ ConnectedSubsets T :=
  Equiv.ofBijective encode ⟨encode_injective, encode_surjective⟩

section Weights

variable {R : Type*} [CommSemiring R]

private theorem leafSet_sum (z : R) :
    (∑ B : LeafSet, z ^ B.card) = (1 + z) ^ 4 := by
  simpa [add_comm] using Fintype.sum_pow_mul_eq_add_pow (Fin 4) z 1

private theorem option_sum (z : R) :
    (∑ o : Option LeafSet, z ^ (o.elim 0 (fun B => B.card + 1))) =
      1 + z * (1 + z) ^ 4 := by
  rw [Fintype.sum_option]
  simp only [Option.elim, pow_zero, pow_succ', ← Finset.mul_sum, leafSet_sum]

private theorem rootSet_sum (z : R) :
    (∑ f : Fin 41 → Option LeafSet, z ^ (rootSet f).card) =
      z * (1 + z * (1 + z) ^ 4) ^ 41 := by
  classical
  calc
    _ = ∑ f : Fin 41 → Option LeafSet, z * ∏ i, z ^ (f i).elim 0 (fun B => B.card + 1) := by
      apply Finset.sum_congr rfl
      intro f _
      rw [card_rootSet, pow_succ', Finset.prod_pow_eq_pow_sum]
    _ = _ := by
      rw [← Finset.mul_sum,
        ← Fintype.prod_sum (fun (_ : Fin 41) (o : Option LeafSet) =>
          z ^ (o.elim 0 (fun B => B.card + 1)))]
      simp only [option_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem branchSet_sum (z : R) :
    (∑ p : Fin 41 × LeafSet, z ^ (branchSet p.1 p.2).card) =
      41 * (z * (1 + z) ^ 4) := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ _ : Fin 41, z * (1 + z) ^ 4 := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [card_branchSet, pow_succ', ← Finset.mul_sum, leafSet_sum]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]

private theorem leafSingleton_sum (z : R) :
    (∑ p : Fin 41 × Fin 4, z ^ ({leaf p.1 p.2} : Finset Vertex).card) = 41 * (4 * z) := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.card_singleton, pow_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]

/-- The sum uses every nonempty connected induced vertex set exactly once. -/
private theorem connectedSubset_sum (z : R) :
    (∑ s : ConnectedSubsets T, z ^ s.val.card) =
      z * ((1 + z * (1 + z) ^ 4) ^ 41 + 41 * (4 + (1 + z) ^ 4)) := by
  classical
  calc
    _ = ∑ c : Configuration, z ^ (encode c).val.card :=
      (Fintype.sum_equiv configurationEquiv
        (fun c : Configuration => z ^ (encode c).val.card)
        (fun s : ConnectedSubsets T => z ^ s.val.card) (fun _ => rfl)).symm
    _ = _ := by
      simp only [Configuration, Fintype.sum_sum_type]
      change (∑ f : Fin 41 → Option LeafSet, z ^ (rootSet f).card) +
        ((∑ p : Fin 41 × LeafSet, z ^ (branchSet p.1 p.2).card) +
          (∑ p : Fin 41 × Fin 4, z ^ ({leaf p.1 p.2} : Finset Vertex).card)) = _
      rw [rootSet_sum, branchSet_sum, leafSingleton_sum]
      generalize (1 + z * (1 + z) ^ 4) ^ 41 = a
      generalize (1 + z) ^ 4 = b
      ring

end Weights

/-! ## Exact coefficient bounds for the shifted polynomial -/

private abbrev Gaussian := Int × Int

private def gadd (a b : Gaussian) : Gaussian := (a.1 + b.1, a.2 + b.2)
private def gmul (a b : Gaussian) : Gaussian :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

private def addCoeffs : List Gaussian → List Gaussian → List Gaussian
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => gadd a b :: addCoeffs as bs

private def mulCoeffs : List Gaussian → List Gaussian → List Gaussian
  | [], _ => []
  | a :: as, bs => addCoeffs (bs.map (gmul a)) ((0, 0) :: mulCoeffs as bs)

private def powCoeffs (as : List Gaussian) : Nat → List Gaussian
  | 0 => [(1, 0)]
  | n + 1 => mulCoeffs as (powCoeffs as n)

private def center : Gaussian := (-539, 496)

private def shiftedFourth : List Gaussian := powCoeffs [gadd center (1000, 0), (1, 0)] 4

private def base : List Gaussian :=
  addCoeffs [(1000 ^ 5, 0)] (mulCoeffs [center, (1, 0)] shiftedFourth)

private def coefficients : List Gaussian :=
  addCoeffs (powCoeffs base 41)
    ((addCoeffs [(4 * 1000 ^ 4, 0)] shiftedFourth).map (gmul (41 * 1000 ^ 201, 0)))

private def l1 (a : Gaussian) : Nat := a.1.natAbs + a.2.natAbs
private def linf (a : Gaussian) : Nat := max a.1.natAbs a.2.natAbs

private def weighted : List Gaussian → Nat
  | [] => 0
  | a :: as => l1 a + 2 * weighted as

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Kernel reduction computes the full degree-205 Gaussian-integer convolution.
private theorem coefficient_bounds :
    1000 * l1 coefficients[0]! ≤ 2537 * 1000 ^ 205 ∧
    5225 * 1000 ^ 205 ≤ 1000 * linf coefficients[1]! ∧
    1000 * (4 * weighted (coefficients.drop 2)) ≤ 425 * 1000 ^ 205 := by
  decide +kernel

private def F (z : ℂ) : ℂ := (1 + z * (1 + z) ^ 4) ^ 41 + 41 * (4 + (1 + z) ^ 4)

private def embed (a : Gaussian) : ℂ := ⟨(a.1 : ℝ), (a.2 : ℝ)⟩

@[simp] private theorem embed_add (a b : Gaussian) :
    embed (gadd a b) = embed a + embed b := by
  apply Complex.ext <;> simp [embed, gadd]

@[simp] private theorem embed_mul (a b : Gaussian) :
    embed (gmul a b) = embed a * embed b := by
  apply Complex.ext <;> simp [embed, gmul, Complex.mul_re, Complex.mul_im]

@[simp] private theorem embed_real (a : ℤ) : embed (a, 0) = (a : ℂ) := by
  apply Complex.ext <;> simp [embed]

private def evalCoeffs (z : ℂ) : List Gaussian → ℂ
  | [] => 0
  | a :: as => embed a + z * evalCoeffs z as

@[simp] private theorem eval_add (z : ℂ) (as bs : List Gaussian) :
    evalCoeffs z (addCoeffs as bs) = evalCoeffs z as + evalCoeffs z bs := by
  induction as generalizing bs with
  | nil => simp [addCoeffs, evalCoeffs]
  | cons a as ih =>
    cases bs with
    | nil => simp [addCoeffs, evalCoeffs]
    | cons b bs =>
      simp only [addCoeffs, evalCoeffs, embed_add, ih]
      ring

@[simp] private theorem eval_map_mul (z : ℂ) (a : Gaussian) (bs : List Gaussian) :
    evalCoeffs z (bs.map (gmul a)) = embed a * evalCoeffs z bs := by
  induction bs with
  | nil => simp [evalCoeffs]
  | cons b bs ih =>
    simp only [List.map_cons, evalCoeffs, embed_mul, ih]
    ring

@[simp] private theorem eval_mul (z : ℂ) (as bs : List Gaussian) :
    evalCoeffs z (mulCoeffs as bs) = evalCoeffs z as * evalCoeffs z bs := by
  induction as with
  | nil => simp [mulCoeffs, evalCoeffs]
  | cons a as ih =>
    simp only [mulCoeffs, eval_add, eval_map_mul, evalCoeffs, ih]
    have h : embed (0, 0) = 0 := by simp
    rw [h]
    ring

@[simp] private theorem eval_pow (z : ℂ) (as : List Gaussian) (n : ℕ) :
    evalCoeffs z (powCoeffs as n) = evalCoeffs z as ^ n := by
  induction n with
  | zero => simp [powCoeffs, evalCoeffs]
  | succ n ih => simp [powCoeffs, ih, pow_succ']

set_option maxHeartbeats 1000000 in
-- Normalization checks the two polynomial scaling identities and their powers.
private theorem eval_coefficients (h : ℂ) :
    evalCoeffs h coefficients = (1000 : ℂ) ^ 205 * F ((embed center + h) / 1000) := by
  have fourth : evalCoeffs h shiftedFourth = (embed center + 1000 + h) ^ 4 := by
    simp [shiftedFourth, evalCoeffs]
  have baseEval : evalCoeffs h base =
      (1000 : ℂ) ^ 5 + (embed center + h) * (embed center + 1000 + h) ^ 4 := by
    simp [base, evalCoeffs, fourth]
    norm_num
  have h₁ : 1 + (embed center + h) / 1000 = (embed center + 1000 + h) / 1000 := by
    ring
  have scaleBase :
      (1000 : ℂ) ^ 5 * (1 + ((embed center + h) / 1000) *
          (1 + (embed center + h) / 1000) ^ 4) = evalCoeffs h base := by
    rw [baseEval, h₁]
    ring
  have scaleFourth :
      (1000 : ℂ) ^ 4 * (4 + (1 + (embed center + h) / 1000) ^ 4) =
        evalCoeffs h (addCoeffs [(4 * 1000 ^ 4, 0)] shiftedFourth) := by
    rw [eval_add, fourth, h₁]
    simp [evalCoeffs]
    ring
  have hpow : ((1000 : ℂ) ^ 5) ^ 41 = 1000 ^ 205 := by rw [← pow_mul]
  have hsplit : (1000 : ℂ) ^ 201 * 1000 ^ 4 = 1000 ^ 205 := by rw [← pow_add]
  simp only [coefficients, eval_add, eval_map_mul, eval_pow, embed_real, Int.cast_mul,
    Int.cast_pow, Int.cast_ofNat, F, ← scaleBase, ← scaleFourth,
    mul_pow, hpow]
  conv_rhs => rw [mul_add]
  congr 1
  calc
    _ = 1000 ^ 201 * 1000 ^ 4 *
        (41 * (4 + (1 + (embed center + h) / 1000) ^ 4)) := by ring
    _ = _ := by rw [hsplit]

private theorem cast_natAbs_real (n : ℤ) : (n.natAbs : ℝ) = |(n : ℝ)| := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]

private theorem norm_embed_le (a : Gaussian) : ‖embed a‖ ≤ (l1 a : ℝ) := by
  simpa [embed, l1, cast_natAbs_real] using Complex.norm_le_abs_re_add_abs_im (embed a)

private theorem linf_le_norm_embed (a : Gaussian) : (linf a : ℝ) ≤ ‖embed a‖ := by
  rw [linf, Nat.cast_max, max_le_iff]
  exact ⟨by simpa [embed, cast_natAbs_real] using Complex.abs_re_le_norm (embed a),
    by simpa [embed, cast_natAbs_real] using Complex.abs_im_le_norm (embed a)⟩

private theorem norm_eval_le (h : ℂ) (hh : ‖h‖ ≤ 2) (as : List Gaussian) :
    ‖evalCoeffs h as‖ ≤ (weighted as : ℝ) := by
  induction as with
  | nil => simp [evalCoeffs, weighted]
  | cons a as ih =>
    calc
      ‖evalCoeffs h (a :: as)‖ ≤ ‖embed a‖ + ‖h * evalCoeffs h as‖ := norm_add_le _ _
      _ ≤ (l1 a : ℝ) + 2 * (weighted as : ℝ) := by
        rw [Complex.norm_mul]
        exact add_le_add (norm_embed_le a)
          (mul_le_mul hh ih (norm_nonneg _) (by norm_num))
      _ = (weighted (a :: as) : ℝ) := by simp [weighted]

private theorem coefficients_shape :
    coefficients = coefficients[0]! :: coefficients[1]! :: coefficients.drop 2 := by
  rfl

private theorem eval_coefficients_split (h : ℂ) :
    evalCoeffs h coefficients =
      embed coefficients[0]! + embed coefficients[1]! * h +
      h ^ 2 * evalCoeffs h (coefficients.drop 2) := by
  conv_lhs => rw [coefficients_shape]
  simp only [evalCoeffs]
  ring

private theorem boundary_bound (h : ℂ) (h₁ : 1 ≤ ‖h‖) (h₂ : ‖h‖ ≤ 2) :
    ‖evalCoeffs h coefficients - embed coefficients[1]! * h‖ <
      ‖embed coefficients[1]! * h‖ := by
  obtain ⟨hc, hl, ht⟩ := coefficient_bounds
  have hc' : (1000 : ℝ) * (l1 coefficients[0]! : ℝ) ≤ 2537 * 1000 ^ 205 := by
    exact_mod_cast hc
  have hl' : (5225 : ℝ) * 1000 ^ 205 ≤ 1000 * (linf coefficients[1]! : ℝ) := by
    exact_mod_cast hl
  have ht' : (1000 : ℝ) * (4 * (weighted (coefficients.drop 2) : ℝ)) ≤ 425 * 1000 ^ 205 := by
    exact_mod_cast ht
  have hp : (0 : ℝ) < (1000 : ℝ) ^ 205 := by positivity
  have hsplit : evalCoeffs h coefficients - embed coefficients[1]! * h =
      embed coefficients[0]! + h ^ 2 * evalCoeffs h (coefficients.drop 2) := by
    rw [eval_coefficients_split]
    ring
  rw [hsplit, Complex.norm_mul]
  calc
    _ ≤ ‖embed coefficients[0]!‖ + ‖h ^ 2 * evalCoeffs h (coefficients.drop 2)‖ :=
      norm_add_le _ _
    _ ≤ (l1 coefficients[0]! : ℝ) + 4 * (weighted (coefficients.drop 2) : ℝ) := by
      rw [Complex.norm_mul, Complex.norm_pow]
      refine add_le_add (norm_embed_le _) (mul_le_mul ?_ (norm_eval_le h h₂ _) (norm_nonneg _) (by norm_num))
      convert pow_le_pow_left₀ (norm_nonneg h) h₂ 2 using 1
      norm_num
    _ < (linf coefficients[1]! : ℝ) := by
      change (5225 : ℝ) * 1000 ^ 205 ≤ 1000 * (linf coefficients[1]! : ℝ) at hl'
      generalize (1000 : ℝ) ^ 205 = scale at hc' hl' ht' hp
      norm_num only [Nat.cast_ofNat] at hl'
      linarith only [hc', hl', ht', hp]
    _ ≤ ‖embed coefficients[1]!‖ * ‖h‖ := by
      simpa only [mul_one] using mul_le_mul (linf_le_norm_embed coefficients[1]!) h₁
        (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg _)

private theorem scaled_point_in_disk (h : ℂ) (hh : ‖h‖ ≤ 2) :
    ‖(embed center + h) / 1000 + 1 / 2‖ < (1 / 2 : ℝ) := by
  have hc : ‖embed center + 500‖ < (498 : ℝ) := by
    have hs := Complex.sq_norm (embed center + 500)
    have hre : (embed center + 500).re = -39 := by norm_num [embed, center, Complex.add_re]
    have him : (embed center + 500).im = 496 := by norm_num [embed, center, Complex.add_im]
    rw [Complex.normSq_apply, hre, him] at hs
    nlinarith [norm_nonneg (embed center + 500)]
  have heq : (embed center + h) / 1000 + 1 / 2 = ((embed center + 500) + h) / 1000 := by ring
  rw [heq, Complex.norm_div]
  have hnum : ‖(1000 : ℂ)‖ = (1000 : ℝ) := by norm_num
  rw [hnum]
  have hsum := norm_add_le (embed center + 500) h
  apply (div_lt_iff₀ (by norm_num)).mpr
  linarith

/-! ## Rouché on the square and the strict annulus violation -/

open Complex Set
open D5.S3.Weil.ZetaAnalytic.RoucheZeroCount

private def sw : ℂ := ⟨-1, -1⟩
private def ne : ℂ := ⟨1, 1⟩

private theorem sw_re_lt_ne : sw.re < ne.re := by norm_num [sw, ne]
private theorem sw_im_lt_ne : sw.im < ne.im := by norm_num [sw, ne]

private theorem norm_le_two {h : ℂ} (hh : h ∈ Rectangle sw ne) : ‖h‖ ≤ 2 := by
  have hcoord := (mem_Rect sw_re_lt_ne.le sw_im_lt_ne.le h).mp hh
  change -1 ≤ h.re ∧ h.re ≤ 1 ∧ -1 ≤ h.im ∧ h.im ≤ 1 at hcoord
  have habs := add_le_add
    (abs_le.mpr ⟨hcoord.1, hcoord.2.1⟩) (abs_le.mpr hcoord.2.2)
  exact (Complex.norm_le_abs_re_add_abs_im h).trans (by norm_num at habs; exact habs)

private theorem norm_ge_one {h : ℂ} (hh : h ∈ RectangleBorder sw ne) : 1 ≤ ‖h‖ := by
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
    sw, ne] at hh
  rcases hh with ((⟨_, hi⟩ | ⟨hr, _⟩) | ⟨_, hi⟩) | ⟨hr, _⟩
  · exact (show 1 ≤ |h.im| by rw [hi]; norm_num).trans (abs_im_le_norm h)
  · exact (show 1 ≤ |h.re| by rw [hr]; norm_num).trans (abs_re_le_norm h)
  · exact (show 1 ≤ |h.im| by rw [hi]; norm_num).trans (abs_im_le_norm h)
  · exact (show 1 ≤ |h.re| by rw [hr]; norm_num).trans (abs_re_le_norm h)

private theorem eval_analytic (h : ℂ) (as : List Gaussian) :
    AnalyticAt ℂ (fun z => evalCoeffs z as) h := by
  induction as with
  | nil => exact analyticAt_const
  | cons a as ih =>
    exact analyticAt_const.add (analyticAt_id.mul ih)

private theorem exists_scaled_zero :
    ∃ h ∈ Rectangle sw ne, evalCoeffs h coefficients = 0 := by
  classical
  let a : ℂ := embed coefficients[1]!
  have ha : a ≠ 0 := by
    have h := boundary_bound 1 (by simp) (by simp)
    intro hz
    have hpos := (norm_nonneg _).trans_lt h
    change embed coefficients[1]! = 0 at hz
    rw [hz, zero_mul, norm_zero] at hpos
    exact (lt_irrefl _ hpos)
  have hlinzero (h : ℂ) : a * h = 0 ↔ h = 0 := by simp [ha]
  have hlin (h : ℂ) : AnalyticAt ℂ (fun z => a * z) h :=
    analyticAt_const.mul analyticAt_id
  have hd : HasDerivAt (fun h : ℂ => a * h) a 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul a
  have ho : analyticOrderNatAt (fun h : ℂ => a * h) 0 = 1 := by
    have heq := (hlin 0).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      (by simp) (by rwa [hd.deriv])
    rw [analyticOrderNatAt, heq]
    rfl
  have hzero : (0 : ℂ) ∈ Rectangle sw ne := by
    rw [mem_Rect sw_re_lt_ne.le sw_im_lt_ne.le]
    norm_num [sw, ne]
  by_contra! hno
  have hcount := rectangle_zero_count_eq_of_norm_sub_lt
    (f := fun h => evalCoeffs h coefficients) (g := fun h => a * h)
    sw_re_lt_ne sw_im_lt_ne (fun h _ => eval_analytic h coefficients) (fun h _ => hlin h)
    (fun h hh => boundary_bound h (norm_ge_one hh)
      (norm_le_two (rectangleBorder_subset_rectangle _ _ hh)))
    ∅ {0} (fun h hh => by simp [hno h hh]) (by simp)
    (fun h _ => by simp [hlinzero h]) (by simpa using hzero)
  simp [ho] at hcount

private theorem explicit_F_has_zero :
    ∃ z : ℂ, F z = 0 ∧ ‖z + 1 / 2‖ < (1 / 2 : ℝ) := by
  obtain ⟨h, hh, hzero⟩ := exists_scaled_zero
  refine ⟨(embed center + h) / 1000, ?_, scaled_point_in_disk h (norm_le_two hh)⟩
  rw [eval_coefficients] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ (by norm_num))

private theorem subtreePolynomial_T :
    subtreePolynomial T =
      X * ((1 + X * (1 + X) ^ 4) ^ 41 + 41 * (4 + (1 + X) ^ 4)) :=
  connectedSubset_sum (X : ℂ[X])

private theorem subtreePolynomial_T_eval (z : ℂ) :
    (subtreePolynomial T).eval z = z * F z := by
  rw [subtreePolynomial_T]
  simp [F]

private theorem counterexample :
    T.IsTree ∧ Fintype.card Vertex = 206 ∧
      ∃ z : ℂ, (subtreePolynomial T).eval z = 0 ∧ ‖z + 1 / 2‖ < (1 / 2 : ℝ) := by
  obtain ⟨z, hz, hinner⟩ := explicit_F_has_zero
  exact ⟨T_isTree, card_vertex, z, by simp [subtreePolynomial_T_eval, hz], hinner⟩

/-- The inner annulus bound fails for an actual finite tree. -/
theorem conjecture42_false : ¬ Conjecture42 := by
  intro conjecture
  obtain ⟨ht, hcard, z, hz, hinner⟩ := counterexample
  have horder : 2 ≤ Fintype.card Vertex := by rw [hcard]; decide
  exact (not_le_of_gt hinner) (conjecture T ht horder z hz).1

end

end BrownMol
