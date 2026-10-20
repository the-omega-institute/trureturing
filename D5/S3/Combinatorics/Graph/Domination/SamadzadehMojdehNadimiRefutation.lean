/- GID: D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.claim; result=D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.result; claim=D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.claim
   digest: Five paired-coalition parts at height five refute Conjecture 1. -/

/-
Source: Samadzadeh, Mojdeh and Nadimi, "Paired coalition in graphs",
arXiv:2402.10842v4, Section 1, p. 2, and Conjecture 1, Section 4.2, p. 12.

admission_basis: open-problem-resolution (#19217; Refuted)
escape_witness: none
Direct frozen dependencies: SimpleGraph.IsDominating,
GID D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination.IsDominating,
declaration statement_id sha256:d40412e2ca04d8c91c8ee9b6499ed80d5e9874c1d2269abfd01100dc6f52ffc2.
The domination definition is reused from the Apache-2.0 formal-conjectures
source port in GraphCoverDomination, which retains its attribution and license.
The source predicates and positive-height claim use the expressions recorded
in #19217. PairedCoalitionBinaryTree is a subnamespace of this module.

Every theorem below has proof_shape: bind-only and escape_witness: none.
Same-delivery helpers expand to finite kernel decisions, matching parity,
set and finset bookkeeping, the natural supremum bound, and order reasoning.
Consumers (consumer -> prerequisite):
partition_pc -> parts_nonempty, parts_disjoint, parts_cover, not_paired,
  partner_ne, partner_paired, part_set_injective;
not_paired -> parts_odd;
matching -> matching_data;
union_paired -> matching_isMatching, union_dominating;
partner_paired -> union_paired;
part_set_injective -> part_injective;
partition_card -> part_set_injective;
pc_lower -> partition_pc, partition_card;
result -> pc_lower.
result: proof_shape: bind-only; escape_witness: none.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import D5.S3.ConceptDynamics.GraphColoring.GraphCoverDomination
import Mathlib.Combinatorics.SimpleGraph.Matching

namespace D5.S3.Combinatorics.Graph.Domination.SamadzadehMojdehNadimiRefutation

namespace PairedCoalitionBinaryTree

/-- The perfect binary tree `T(h)` of height `h`: vertex `i : Fin (2^(h+1) − 1)` is the heap label `i + 1`, and the
children of label `v` are `2v` and `2v + 1`. -/
def perfectBinaryTree (h : ℕ) : SimpleGraph (Fin (2 ^ (h + 1) - 1)) :=
  SimpleGraph.fromRel fun x y => y.val + 1 = 2 * (x.val + 1) ∨ y.val + 1 = 2 * (x.val + 1) + 1

/-- A paired dominating set: a dominating set `S` whose induced subgraph `G[S]` contains a perfect matching. -/
def IsPairedDominating {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  G.IsDominating S ∧ ∃ M : G.Subgraph, M.verts = S ∧ M.IsMatching

/-- A paired coalition: disjoint `V₁, V₂`, neither a paired dominating set, whose union is one. -/
def IsPairedCoalition {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ ¬ IsPairedDominating G A ∧ ¬ IsPairedDominating G B ∧ IsPairedDominating G (A ∪ B)

/-- A pc-partition: a vertex partition `π` in which each set is not a paired dominating set but forms a paired
coalition with another set of `π`. -/
def IsPCPartition {V : Type*} (G : SimpleGraph V) (π : Finset (Set V)) : Prop :=
  (∀ A ∈ π, A.Nonempty) ∧ (π : Set (Set V)).PairwiseDisjoint id ∧ (∀ v, ∃ A ∈ π, v ∈ A) ∧
    ∀ A ∈ π, ¬ IsPairedDominating G A ∧ ∃ B ∈ π, B ≠ A ∧ IsPairedCoalition G A B

/-- The paired coalition number `PC(G)`: the maximum order of a pc-partition, `0` if none exists. -/
noncomputable def pcNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sSup {k | ∃ π : Finset (Set V), IsPCPartition G π ∧ π.card = k}

/-- Conjecture 1: "If T(h) is a perfect binary tree with height h, then PC(T(h)) = 5 if h = 2; 3 if h is odd;
0 otherwise", for every positive height `h`. -/
def claim : Prop :=
  ∀ h : ℕ, 1 ≤ h →
    pcNumber (perfectBinaryTree h) = if h = 2 then 5 else if Odd h then 3 else 0

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private def A : Finset (Fin 63) :=
  {0, 1, 2, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}

private def B (j : Fin 4) : Finset (Fin 63) :=
  ![{3, 31, 35, 39, 43, 47, 51, 55, 59},
    {4, 32, 36, 40, 44, 48, 52, 56, 60},
    {5, 33, 37, 41, 45, 49, 53, 57, 61},
    {6, 34, 38, 42, 46, 50, 54, 58, 62}] j

private def part (i : Fin 5) : Finset (Fin 63) := ![A, B 0, B 1, B 2, B 3] i

private theorem parts_nonempty : ∀ i, (part i).Nonempty := by decide +kernel
private theorem parts_disjoint : ∀ i j, i ≠ j → Disjoint (part i) (part j) := by
  decide +kernel
private theorem parts_cover : ∀ v : Fin 63, ∃ i, v ∈ part i := by decide +kernel
private theorem parts_odd : ∀ i, ¬ Even (part i).card := by decide +kernel

private theorem not_paired (i : Fin 5) :
    ¬ IsPairedDominating (perfectBinaryTree 5) (part i) := by
  classical
  rintro ⟨_, M, hM, hm⟩
  have he := hm.even_card
  rw [hM] at he
  simp only [Finset.toFinset_coe] at he
  exact parts_odd i he

private def mate (j : Fin 4) (v : Fin 63) : Fin 63 :=
  ![![2, 3, 0, 1, 4, 5, 6, 16, 18, 20, 22, 24, 26, 28, 30, 31, 7, 35, 8, 39, 9, 43, 10, 47, 11, 51, 12, 55, 13, 59, 14, 15, 32, 33, 34, 17, 36, 37, 38, 19, 40, 41, 42, 21, 44, 45, 46, 23, 48, 49, 50, 25, 52, 53, 54, 27, 56, 57, 58, 29, 60, 61, 62],
    ![2, 4, 0, 3, 1, 5, 6, 16, 18, 20, 22, 24, 26, 28, 30, 32, 7, 36, 8, 40, 9, 44, 10, 48, 11, 52, 12, 56, 13, 60, 14, 31, 15, 33, 34, 35, 17, 37, 38, 39, 19, 41, 42, 43, 21, 45, 46, 47, 23, 49, 50, 51, 25, 53, 54, 55, 27, 57, 58, 59, 29, 61, 62],
    ![1, 0, 5, 3, 4, 2, 6, 15, 17, 19, 21, 23, 25, 27, 29, 7, 33, 8, 37, 9, 41, 10, 45, 11, 49, 12, 53, 13, 57, 14, 61, 31, 32, 16, 34, 35, 36, 18, 38, 39, 40, 20, 42, 43, 44, 22, 46, 47, 48, 24, 50, 51, 52, 26, 54, 55, 56, 28, 58, 59, 60, 30, 62],
    ![1, 0, 6, 3, 4, 5, 2, 15, 17, 19, 21, 23, 25, 27, 29, 7, 34, 8, 38, 9, 42, 10, 46, 11, 50, 12, 54, 13, 58, 14, 62, 31, 32, 33, 16, 35, 36, 37, 18, 39, 40, 41, 20, 43, 44, 45, 22, 47, 48, 49, 24, 51, 52, 53, 26, 55, 56, 57, 28, 59, 60, 61, 30]] j v

private def unionVertices (j : Fin 4) : Finset (Fin 63) := A ∪ B j

private instance decidableAdj : DecidableRel (perfectBinaryTree 5).Adj := by
  unfold perfectBinaryTree
  infer_instance

private theorem matching_data : ∀ j v, v ∈ unionVertices j →
    mate j v ∈ unionVertices j ∧ mate j (mate j v) = v ∧
      (perfectBinaryTree 5).Adj v (mate j v) := by
  decide +kernel

private def matching (j : Fin 4) : (perfectBinaryTree 5).Subgraph where
  verts := unionVertices j
  Adj u v := u ∈ unionVertices j ∧ v = mate j u
  adj_sub := by
    rintro u v ⟨hu, rfl⟩
    exact (matching_data j u hu).2.2
  edge_vert := fun h => h.1
  symm := ⟨by
    rintro u v ⟨hu, rfl⟩
    exact ⟨(matching_data j u hu).1, (matching_data j u hu).2.1.symm⟩⟩

private theorem matching_isMatching (j : Fin 4) : (matching j).IsMatching := by
  intro v hv
  exact ⟨mate j v, ⟨hv, rfl⟩, fun w hw => hw.2⟩

private theorem union_dominating : ∀ j, (perfectBinaryTree 5).IsDominating (unionVertices j) := by
  unfold SimpleGraph.IsDominating
  decide +kernel

private theorem union_paired (j : Fin 4) :
    IsPairedDominating (perfectBinaryTree 5) ((A : Set (Fin 63)) ∪ B j) := by
  exact ⟨by simpa only [unionVertices, Finset.coe_union] using union_dominating j,
    matching j, by simp [matching, unionVertices], matching_isMatching j⟩

private def partner (i : Fin 5) : Fin 5 := if i = 0 then 1 else 0

private theorem partner_ne : ∀ i, partner i ≠ i := by decide +kernel

private theorem part_injective : Function.Injective part := by decide +kernel

private theorem partner_paired (i : Fin 5) :
    IsPairedDominating (perfectBinaryTree 5)
      ((part i : Set (Fin 63)) ∪ part (partner i)) := by
  fin_cases i
  · simpa [part, partner] using union_paired 0
  · simpa [part, partner, Set.union_comm] using union_paired 0
  · simpa [part, partner, Set.union_comm] using union_paired 1
  · simpa [part, partner, Set.union_comm] using union_paired 2
  · simpa [part, partner, Set.union_comm] using union_paired 3

private noncomputable def partition : Finset (Set (Fin 63)) := by
  classical
  exact Finset.univ.image (fun i => (part i : Set (Fin 63)))

private theorem part_set_injective : Function.Injective (fun i => (part i : Set (Fin 63))) := by
  intro i j hij
  exact part_injective (Finset.coe_injective hij)

private theorem partition_pc : IsPCPartition (perfectBinaryTree 5) partition := by
  classical
  have hmem : ∀ i, (part i : Set (Fin 63)) ∈ partition := by
    intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    exact parts_nonempty i
  · intro S hS T hT hST
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hT
    exact Finset.disjoint_coe.mpr (parts_disjoint i j (fun hij => hST (congrArg (fun k => (part k : Set (Fin 63))) hij)))
  · intro v
    obtain ⟨i, hi⟩ := parts_cover v
    exact ⟨part i, hmem i, hi⟩
  · intro S hS
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    refine ⟨not_paired i, part (partner i), hmem _, ?_, ?_⟩
    · exact fun h => partner_ne i (part_set_injective h)
    · exact ⟨Finset.disjoint_coe.mpr (parts_disjoint i (partner i) (partner_ne i).symm),
        not_paired i, not_paired (partner i), partner_paired i⟩

private theorem partition_card : partition.card = 5 := by
  classical
  rw [partition, Finset.card_image_of_injective _ part_set_injective]
  decide +kernel

private theorem pc_lower : 5 ≤ pcNumber (perfectBinaryTree 5) := by
  classical
  unfold pcNumber
  apply le_csSup
  · refine ⟨Fintype.card (Set (Fin 63)), ?_⟩
    rintro k ⟨π, _, rfl⟩
    exact π.card_le_univ
  · exact ⟨partition, partition_pc, partition_card⟩

theorem result : ¬ PairedCoalitionBinaryTree.claim := by
  intro hc
  have h5 := hc 5 NeZero.one_le
  have ho : Odd (5 : ℕ) := Nat.odd_iff.mpr rfl
  simp only [show (5 : ℕ) ≠ 2 from Ne.symm (Nat.ne_of_beq_eq_false rfl), ite_false, ho, ite_true] at h5
  have h := pc_lower
  omega

end PairedCoalitionBinaryTree

end D5.S3.Combinatorics.Graph.Domination.SamadzadehMojdehNadimiRefutation
