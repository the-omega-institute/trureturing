/- GID: D5/S3/Combinatorics/Lattices/FroeseGeorgePathCoverRankRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Lattices/FroeseGeorgePathCoverRankRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Order.Partition.Finpartition]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Lattices/FroeseGeorgePathCoverRankRefutation.claim; result=D5/S3/Combinatorics/Lattices/FroeseGeorgePathCoverRankRefutation.result; claim=D5/S3/Combinatorics/Lattices/FroeseGeorgePathCoverRankRefutation.claim
   digest: A 15-element rooted poset has path-cover rank counts 15, 14, and 17 at ranks 6, 7, and 8. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.Sort
import Mathlib.Order.Atoms.Finite
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.Order.UpperLower.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.SetTheory.Cardinal.Finite

/-! # A rank valley in a rooted path-cover lattice

Matteus Froese and Ian George pose Question 1 in *Path Covering Spaces of Posets*,
arXiv:2610.20890v1. The universal claim uses their rooted partition model,
with rank from Corollary 1.

The counterexample construction is due to the Codex CLI successor-search seat
in issue #33328. The Codex CLI source-qualification seat independently derived
the witness counts. The Codex CLI formal probe implementation supplied the
original Lean proof.
-/

namespace D5.S3.Combinatorics.Lattices.FroeseGeorgePathCoverRankRefutation

open scoped BigOperators

/-- A saturated path from the least element, including the path of length zero. -/
inductive Path (P : Type) [PartialOrder P] [OrderBot P] : P → Type
  | root : Path P ⊥
  | snoc {x y : P} : x ⋖ y → Path P x → Path P y

namespace Path

variable {P : Type} [PartialOrder P] [OrderBot P]

def vertices {p : P} : Path P p → List P
  | .root => [⊥]
  | .snoc (y := y) _ t => y :: t.vertices

private theorem mem_le {p : P} (t : Path P p) : ∀ x ∈ t.vertices, x ≤ p := by
  induction t with
  | root => simp [vertices]
  | @snoc u v h t ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_rfl
    · exact (ih x hx).trans h.le

private theorem sorted {p : P} (t : Path P p) : t.vertices.SortedGT := by
  induction t with
  | root => simp [vertices, List.sortedGT_iff_pairwise]
  | @snoc u v h t ih =>
    rw [vertices, List.sortedGT_iff_pairwise, List.pairwise_cons]
    exact ⟨fun x hx => (t.mem_le x hx).trans_lt h.lt, ih.pairwise⟩

private theorem vertices_injective {p : P} : Function.Injective (vertices (p := p)) := by
  intro t
  induction t with
  | root =>
    intro s h
    cases s with
    | root => rfl
    | snoc edge _ => exact (not_lt_of_ge bot_le edge.lt).elim
  | @snoc u v h t ih =>
    intro s eq
    cases s with
    | root => exact (not_lt_of_ge bot_le h.lt).elim
    | @snoc u' _ h' s =>
      have tail : vertices t = vertices s := (List.cons.inj eq).2
      have head : (vertices t).head? = some u := by cases t <;> rfl
      have head' : (vertices s).head? = some u' := by cases s <;> rfl
      have hu : u = u' := Option.some.inj (head.symm.trans ((congrArg List.head? tail).trans head'))
      subst u'
      cases ih tail
      rfl

instance [Finite P] (p : P) : Finite (Path P p) := by
  classical
  letI : Fintype P := Fintype.ofFinite P
  apply Finite.of_injective (fun t : Path P p => t.vertices.toFinset)
  intro t s h
  change t.vertices.toFinset = s.vertices.toFinset at h
  apply vertices_injective
  apply t.sorted.eq_of_mem_iff s.sorted
  intro a
  simpa only [List.mem_toFinset] using
    (show a ∈ t.vertices.toFinset ↔ a ∈ s.vertices.toFinset by rw [h])

end Path

noncomputable instance pathFintype (P : Type) [PartialOrder P] [OrderBot P] [Finite P]
    (p : P) : Fintype (Path P p) := Fintype.ofFinite _

noncomputable instance pathDecEq (P : Type) [PartialOrder P] [OrderBot P]
    (p : P) : DecidableEq (Path P p) := Classical.decEq _

section Source

variable (P : Type) [PartialOrder P] [OrderBot P] [Fintype P]

abbrev Partition (p : P) := Finpartition (Finset.univ : Finset (Path P p))
abbrev Family := ∀ p : P, Partition P p

def Same {p : P} (A : Partition P p) (s t : Path P p) : Prop := A.part s = A.part t

/-- Definition 2. Extension takes each block at the lower endpoint into a block
at the upper endpoint. -/
def Compatible (A : Family P) : Prop :=
  ∀ ⦃x y : P⦄ (h : x ⋖ y) (C : Finset (Path P x)),
    C ∈ (A x).parts → ∃ D ∈ (A y).parts, ∀ t ∈ C, Path.snoc h t ∈ D

private def CompatiblePairwise (A : Family P) : Prop :=
  ∀ ⦃x y : P⦄ (h : x ⋖ y) (s t : Path P x),
    Same P (A x) s t → Same P (A y) (.snoc h s) (.snoc h t)

/-- A compatible family of rooted path partitions. -/
structure Split where
  family : Family P
  compatible : Compatible P family

private theorem Split.ext {A B : Split P} (h : A.family = B.family) : A = B := by
  cases A
  cases B
  cases h
  rfl

/-- Corollary 1. Each endpoint contributes its number of blocks minus one. -/
noncomputable def sourceRank (A : Split P) : ℕ :=
  ∑ p : P, ((A.1 p).parts.card - 1)

noncomputable def sourceHeight : ℕ := ∑ p : P, (Fintype.card (Path P p) - 1)

noncomputable def rankCount (k : ℕ) : ℕ := Nat.card {A : Split P // sourceRank P A = k}

def LogConcave (r : ℕ → ℕ) (height : ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → k < height → r (k - 1) * r (k + 1) ≤ r k * r k

def Unimodal (r : ℕ → ℕ) (height : ℕ) : Prop :=
  ∃ m : ℕ, m ≤ height ∧
    (∀ i j : ℕ, i ≤ j → j ≤ m → r i ≤ r j) ∧
    (∀ i j : ℕ, m ≤ i → i ≤ j → j ≤ height → r j ≤ r i)

def claim : Prop :=
  ∀ (P : Type) [PartialOrder P] [OrderBot P] [Fintype P],
    LogConcave (rankCount P) (sourceHeight P) ∨ Unimodal (rankCount P) (sourceHeight P)

end Source

inductive Node
  | first | second | third | leaf₁ | leaf₂ | leaf₃
  deriving DecidableEq

instance : Fintype Node where
  elems := {.first, .second, .third, .leaf₁, .leaf₂, .leaf₃}
  complete x := by cases x <;> decide

inductive Vertex
  | root | a | b | branch (side : Bool) (node : Node)
  deriving DecidableEq, Fintype

namespace Node

def level : Node → ℕ
  | .first => 0
  | .second => 1
  | .third => 2
  | _ => 3

def below (x y : Node) : Bool :=
  decide (x = y) || decide (x.level < 3 ∧ x.level < y.level)

instance : PartialOrder Node where
  le x y := below x y = true
  le_refl := show ∀ x : Node, below x x = true by decide
  le_trans := by
    exact (show ∀ x y z : Node, below x y = true → below y z = true → below x z = true by decide)
  le_antisymm := by
    exact (show ∀ x y : Node, below x y = true → below y x = true → x = y by decide)

instance : DecidableLE Node := fun x y => inferInstanceAs (Decidable (below x y = true))

inductive Edge : Node → Node → Prop
  | first : Edge .first .second
  | second : Edge .second .third
  | leaf₁ : Edge .third .leaf₁
  | leaf₂ : Edge .third .leaf₂
  | leaf₃ : Edge .third .leaf₃

def edge : Node → Node → Bool
  | .first, .second | .second, .third
  | .third, .leaf₁ | .third, .leaf₂ | .third, .leaf₃ => true
  | _, _ => false

private theorem edge_iff {x y : Node} : edge x y = true ↔ Edge x y := by
  constructor
  · cases x <;> cases y <;> simp [edge] <;> constructor
  · intro h
    cases h <;> rfl

instance : DecidableLT Node := fun x y => inferInstanceAs (Decidable (x ≤ y ∧ ¬ y ≤ x))
instance (x y : Node) : Decidable (x ⋖ y) :=
  inferInstanceAs (Decidable (x < y ∧ ∀ z : Node, x < z → ¬ z < y))

private theorem covBy_iff {x y : Node} : x ⋖ y ↔ Edge x y := by
  exact (show ∀ x y : Node, x ⋖ y ↔ edge x y = true by decide) x y |>.trans edge_iff

end Node

namespace Vertex

def below : Vertex → Vertex → Bool
  | .root, _ => true
  | .a, .a | .b, .b | .a, .branch _ _ | .b, .branch _ _ => true
  | .branch s x, .branch t y => decide (s = t) && Node.below x y
  | _, _ => false

set_option maxRecDepth 4096 in
instance : PartialOrder Vertex where
  le x y := below x y = true
  le_refl := show ∀ x : Vertex, below x x = true by decide
  le_trans := by
    exact (show ∀ x y z : Vertex, below x y = true → below y z = true → below x z = true by decide)
  le_antisymm := by
    exact (show ∀ x y : Vertex, below x y = true → below y x = true → x = y by decide)

instance : OrderBot Vertex where
  bot := .root
  bot_le _ := rfl

instance : DecidableLE Vertex := fun x y => inferInstanceAs (Decidable (below x y = true))
instance : DecidableLT Vertex := fun x y => inferInstanceAs (Decidable (x ≤ y ∧ ¬ y ≤ x))
instance (x y : Vertex) : Decidable (x ⋖ y) :=
  inferInstanceAs (Decidable (x < y ∧ ∀ z : Vertex, x < z → ¬ z < y))

inductive Edge : Vertex → Vertex → Prop
  | a : Edge .root .a
  | b : Edge .root .b
  | fromA (s : Bool) : Edge .a (.branch s .first)
  | fromB (s : Bool) : Edge .b (.branch s .first)
  | within (s : Bool) {x y : Node} : Node.Edge x y → Edge (.branch s x) (.branch s y)

def edge : Vertex → Vertex → Bool
  | .root, .a | .root, .b | .a, .branch _ .first | .b, .branch _ .first => true
  | .branch s x, .branch t y => decide (s = t) && Node.edge x y
  | _, _ => false

private theorem edge_iff {x y : Vertex} : edge x y = true ↔ Edge x y := by
  constructor
  · cases x <;> cases y <;> simp [edge]
    · exact Edge.a
    · exact Edge.b
    · rename_i s n
      cases n <;> simp <;> exact Edge.fromA s
    · rename_i s n
      cases n <;> simp <;> exact Edge.fromB s
    · rintro rfl he
      exact Edge.within _ (Node.edge_iff.mp he)
  · intro h
    cases h with
    | within _ h => simp [edge, Node.edge_iff.mpr h]
    | _ => rfl

set_option maxRecDepth 4096 in
private theorem covBy_iff {x y : Vertex} : x ⋖ y ↔ Edge x y := by
  exact (show ∀ x y : Vertex, x ⋖ y ↔ edge x y = true by decide) x y |>.trans edge_iff

def rootPath : Path Vertex .root := .root
def aPath : Path Vertex .a := .snoc (covBy_iff.mpr Edge.a) rootPath
def bPath : Path Vertex .b := .snoc (covBy_iff.mpr Edge.b) rootPath

/-- The concrete two routes to each branch vertex, indexed by the first turn. -/
def firstPath (side : Bool) (label : Bool) : Path Vertex (.branch side .first) :=
  if label then .snoc (covBy_iff.mpr (Edge.fromB side)) bPath
  else .snoc (covBy_iff.mpr (Edge.fromA side)) aPath

def branchPath (side : Bool) (label : Bool) (n : Node) : Path Vertex (.branch side n) :=
  let first := firstPath side label
  let second := Path.snoc (covBy_iff.mpr (Edge.within side Node.Edge.first)) first
  let third := Path.snoc (covBy_iff.mpr (Edge.within side Node.Edge.second)) second
  match n with
  | .first => first
  | .second => second
  | .third => third
  | .leaf₁ => .snoc (covBy_iff.mpr (Edge.within side Node.Edge.leaf₁)) third
  | .leaf₂ => .snoc (covBy_iff.mpr (Edge.within side Node.Edge.leaf₂)) third
  | .leaf₃ => .snoc (covBy_iff.mpr (Edge.within side Node.Edge.leaf₃)) third

def route : (v : Vertex) → Bool → Path Vertex v
  | .root, _ => rootPath
  | .a, _ => aPath
  | .b, _ => bPath
  | .branch s n, label => branchPath s label n

def label {v : Vertex} : Path Vertex v → Bool
  | .root => false
  | .snoc (y := y) _ t => decide (y = .b) || label t

private theorem label_branchPath (s b : Bool) (n : Node) :
    label (branchPath s b n) = b := by
  cases b <;> cases n <;> rfl

private theorem within_snoc (s : Bool) {x y : Node} (e : Node.Edge x y) (b : Bool) :
    Path.snoc (covBy_iff.mpr (Edge.within s e)) (branchPath s b x) = branchPath s b y := by
  cases e <;> rfl

private theorem path_eq_route {v : Vertex} (t : Path Vertex v) : t = route v (label t) := by
  induction t with
  | root => rfl
  | @snoc x y h t ih =>
    cases covBy_iff.mp h with
    | a => rw [ih]; rfl
    | b => rw [ih]; rfl
    | fromA s => rw [ih]; rfl
    | fromB s => rw [ih]; rfl
    | within s e =>
      change Path.snoc h t = route _ (label t)
      conv_lhs => rw [ih]
      exact within_snoc s e _

def Labels : Vertex → Type
  | .branch _ _ => Bool
  | _ => Unit

instance (v : Vertex) : Fintype (Labels v) := by
  cases v <;> unfold Labels <;> infer_instance

def pathEquiv (v : Vertex) : Path Vertex v ≃ Labels v := by
  cases v with
  | root | a | b =>
    exact
      { toFun := fun _ => ()
        invFun := fun _ => route _ false
        left_inv := fun t => (path_eq_route t).symm
        right_inv := fun _ => rfl }
  | branch s n =>
    exact
      { toFun := label
        invFun := fun b => branchPath s b n
        left_inv := fun t => (path_eq_route t).symm
        right_inv := fun b => label_branchPath s b n }

private theorem singleton_path {v : Vertex} (h : ∀ s n, v ≠ .branch s n) :
    Subsingleton (Path Vertex v) := by
  cases v with
  | branch s n => exact (h s n rfl).elim
  | root | a | b =>
    exact ⟨fun t u => (path_eq_route t).trans (path_eq_route u).symm⟩

instance : Subsingleton (Path Vertex .root) := singleton_path (fun _ _ h => nomatch h)
instance : Subsingleton (Path Vertex .a) := singleton_path (fun _ _ h => nomatch h)
instance : Subsingleton (Path Vertex .b) := singleton_path (fun _ _ h => nomatch h)

end Vertex

section SourcePartition

variable (P : Type) [PartialOrder P] [OrderBot P] [Fintype P]

instance (p : P) : Nonempty (Path P p) := by
  induction p using WellFoundedLT.induction with
  | ind q ih =>
    by_cases h : q = ⊥
    · subst q
      exact ⟨Path.root⟩
    · obtain ⟨x, _, hcov⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.mpr h)
      obtain ⟨path⟩ := ih x hcov.lt
      exact ⟨Path.snoc hcov path⟩

instance : Finite (Split P) := by
  classical
  exact Finite.of_injective Split.family (fun _ _ => Split.ext P)

private theorem same_iff_mem {p : P} (A : Partition P p) (s t : Path P p) :
    Same P A s t ↔ t ∈ A.part s := by
  rw [A.mem_part_iff_part_eq_part (Finset.mem_univ _) (Finset.mem_univ _), Same, eq_comm]

private theorem compatible_pairwise_iff (A : Family P) :
    CompatiblePairwise P A ↔ Compatible P A := by
  constructor
  · intro hA x y h C hC
    obtain ⟨s, hs⟩ := (A x).nonempty_of_mem_parts hC
    refine ⟨(A y).part (.snoc h s), (A y).part_mem.2 (Finset.mem_univ _), ?_⟩
    intro t ht
    apply (same_iff_mem P _ _ _).mp (hA h s t ?_)
    apply (same_iff_mem P _ _ _).mpr
    rwa [(A x).part_eq_of_mem hC hs]
  · intro hA x y h s t hst
    obtain ⟨D, hD, hDC⟩ := hA h ((A x).part s) ((A x).part_mem.2 (Finset.mem_univ _))
    have hs := hDC s ((A x).mem_part (Finset.mem_univ _))
    have ht := hDC t ((same_iff_mem P _ _ _).mp hst)
    exact ((A y).part_eq_of_mem hD hs).trans ((A y).part_eq_of_mem hD ht).symm

/-- Mathlib orders individual partitions with the finer partition below. -/
private theorem partition_le_iff {p : P} {A B : Partition P p} :
    A ≤ B ↔ ∀ s t : Path P p, Same P A s t → Same P B s t := by
  constructor
  · intro h s t hst
    obtain ⟨D, hD, hCD⟩ := h (A.part_mem.2 (Finset.mem_univ s))
    have hs := hCD (A.mem_part (Finset.mem_univ _))
    have ht := hCD ((same_iff_mem P _ _ _).mp hst)
    exact (B.part_eq_of_mem hD hs).trans (B.part_eq_of_mem hD ht).symm
  · intro h C hC
    obtain ⟨s, hs⟩ := A.nonempty_of_mem_parts hC
    refine ⟨B.part s, B.part_mem.2 (Finset.mem_univ _), ?_⟩
    intro t ht
    apply (same_iff_mem P _ _ _).mp (h s t ?_)
    exact (A.part_eq_of_mem hC hs).trans (A.part_eq_of_mem hC ht).symm

private theorem partition_ext {p : P} {A B : Partition P p}
    (h : ∀ s t : Path P p, Same P A s t ↔ Same P B s t) : A = B :=
  le_antisymm ((partition_le_iff P).mpr fun s t => (h s t).mp)
    ((partition_le_iff P).mpr fun s t => (h s t).mpr)

/-- Theorem 2 orders compatible families from coarser to finer. -/
noncomputable instance : PartialOrder (Split P) :=
  PartialOrder.lift (fun A : Split P => OrderDual.toDual A.family) (fun _ _ => Split.ext P)

noncomputable def merged (p : P) : Partition P p :=
  Finpartition.indiscrete (Finset.univ_nonempty.ne_empty)

private theorem same_merged (p : P) (s t : Path P p) : Same P (merged P p) s t := by
  have hp (u : Path P p) : (merged P p).part u = Finset.univ :=
    (merged P p).part_eq_of_mem (by simp [merged]) (Finset.mem_univ _)
  exact (hp s).trans (hp t).symm

private theorem same_discrete (p : P) (s t : Path P p) :
    Same P (⊥ : Partition P p) s t ↔ s = t := by
  have hp (u : Path P p) : (⊥ : Partition P p).part u = {u} :=
    (⊥ : Partition P p).part_eq_of_mem
      (Finpartition.mem_bot_iff.mpr ⟨u, Finset.mem_univ _, rfl⟩) (Finset.mem_singleton_self _)
  simp [Same, hp]

private theorem partition_eq_merged_of_subsingleton (p : P) [Subsingleton (Path P p)]
    (A : Partition P p) : A = merged P p := by
  apply partition_ext
  intro s t
  rw [Subsingleton.elim t s]
  exact ⟨fun _ => rfl, fun _ => rfl⟩

end SourcePartition

namespace Vertex

private theorem branchPath_injective (side : Bool) (n : Node) :
    Function.Injective (fun b => branchPath side b n) := by
  intro a b h
  simpa only [label_branchPath] using congrArg label h

private theorem card_path_branch (side : Bool) (n : Node) :
    Fintype.card (Path Vertex (.branch side n)) = 2 :=
  (Fintype.card_congr (pathEquiv (.branch side n))).trans Fintype.card_bool

private theorem card_path_singleton {v : Vertex} (h : ∀ s n, v ≠ .branch s n) :
    Fintype.card (Path Vertex v) = 1 := by
  have := singleton_path h
  letI : Unique (Path Vertex v) := ⟨⟨route v false⟩, fun _ => Subsingleton.elim _ _⟩
  exact Fintype.card_unique

end Vertex

namespace Branch

open Vertex (branchPath)

def SplitAt {side : Bool} {n : Node} (A : Partition Vertex (.branch side n)) : Prop :=
  ¬ Same Vertex A (branchPath side false n) (branchPath side true n)

private theorem same_branch_iff {side : Bool} {n : Node} (A : Partition Vertex (.branch side n))
    (i j : Bool) :
    Same Vertex A (branchPath side i n) (branchPath side j n) ↔
      i = j ∨ ¬ SplitAt A := by
  classical
  cases i <;> cases j <;> simp [SplitAt, Same, eq_comm]

private theorem split_discrete (side : Bool) (n : Node) :
    SplitAt (⊥ : Partition Vertex (.branch side n)) := by
  intro h
  exact Bool.false_ne_true (Vertex.branchPath_injective side n ((same_discrete _ _ _ _).mp h))

private theorem not_split_merged (side : Bool) (n : Node) :
    ¬ SplitAt (merged Vertex (.branch side n)) := fun h => h (same_merged _ _ _ _)

private theorem branch_partition_ext {side : Bool} {n : Node} {A B : Partition Vertex (.branch side n)}
    (h : SplitAt A ↔ SplitAt B) : A = B := by
  apply partition_ext
  intro t u
  rw [Vertex.path_eq_route t, Vertex.path_eq_route u]
  change Same Vertex A (branchPath side _ n) (branchPath side _ n) ↔
    Same Vertex B (branchPath side _ n) (branchPath side _ n)
  rw [same_branch_iff, same_branch_iff, h]

private theorem branch_partition_eq {side : Bool} {n : Node} (A : Partition Vertex (.branch side n)) :
    (SplitAt A → A = ⊥) ∧ (¬ SplitAt A → A = merged Vertex (.branch side n)) := by
  constructor
  · intro h
    exact branch_partition_ext ⟨fun _ => split_discrete _ _, fun _ => h⟩
  · intro h
    exact branch_partition_ext ⟨fun h' => (h h').elim, fun h' => (not_split_merged _ _ h').elim⟩

private theorem compatible_iff_edges (A : Family Vertex) :
    Compatible Vertex A ↔ ∀ (side : Bool) ⦃x y : Node⦄, Node.Edge x y →
      SplitAt (A (.branch side y)) → SplitAt (A (.branch side x)) := by
  rw [← compatible_pairwise_iff]
  constructor
  · intro hA side x y e htarget hsource
    let edge := Vertex.covBy_iff.mpr (Vertex.Edge.within side e)
    have hs := hA edge (branchPath side false x) (branchPath side true x) hsource
    rw [Vertex.within_snoc side e false, Vertex.within_snoc side e true] at hs
    exact htarget hs
  · intro hA u v edge p q hpq
    cases Vertex.covBy_iff.mp edge with
    | a | b | fromA | fromB =>
      have hp : p = q := (Vertex.path_eq_route p).trans (Vertex.path_eq_route q).symm
      cases hp
      rfl
    | @within side x y e =>
      rw [Vertex.path_eq_route p, Vertex.path_eq_route q] at hpq ⊢
      change Same Vertex (A (.branch side x)) (branchPath side _ x) (branchPath side _ x) at hpq
      change Same Vertex (A (.branch side y))
        (Path.snoc edge (branchPath side _ x)) (Path.snoc edge (branchPath side _ x))
      rw [Vertex.within_snoc side e, Vertex.within_snoc side e, same_branch_iff]
      exact ((same_branch_iff _ _ _).mp hpq).imp_right fun hc ht => hc (hA side e ht)

end Branch

namespace Branch

private theorem isLowerSet_iff_edges (I : Finset Node) :
    IsLowerSet (I : Set Node) ↔ ∀ ⦃x y : Node⦄, Node.Edge x y → y ∈ I → x ∈ I := by
  constructor
  · intro h x y edge hy
    exact h (Node.covBy_iff.mpr edge).le hy
  · intro h x y hxy hy
    letI : LocallyFiniteOrder Node := Fintype.toLocallyFiniteOrder
    have steps := le_iff_reflTransGen_covBy.mp hxy
    clear hxy
    induction steps with
    | refl => exact hy
    | tail _ hlast ih => exact ih (h (Node.covBy_iff.mp hlast) hy)

abbrev Ideal := {I : Finset Node // IsLowerSet (I : Set Node)}

instance (I : Finset Node) : Decidable (IsLowerSet (I : Set Node)) :=
  decidable_of_iff (∀ x y : Node, x ≤ y → y ∈ I → x ∈ I)
    ⟨fun h _ _ => h _ _, fun h _ _ hxy hy => h hxy hy⟩

def idealAt (I : Ideal × Ideal) : Bool → Ideal
  | false => I.1
  | true => I.2

noncomputable def selected (A : Split Vertex) (side : Bool) : Finset Node := by
  classical
  exact Finset.univ.filter fun n => SplitAt (A.1 (.branch side n))

@[simp] private theorem mem_selected (A : Split Vertex) (side : Bool) (n : Node) :
    n ∈ selected A side ↔ SplitAt (A.1 (.branch side n)) := by
  simp [selected]

noncomputable def toIdeal (A : Split Vertex) (side : Bool) : Ideal :=
  ⟨selected A side, (isLowerSet_iff_edges _).mpr fun x y e hy =>
    (mem_selected A side x).mpr ((compatible_iff_edges A.1).mp A.2 side e
      ((mem_selected A side y).mp hy))⟩

noncomputable def familyOf (I : Ideal × Ideal) : Family Vertex
  | .root => merged Vertex .root
  | .a => merged Vertex .a
  | .b => merged Vertex .b
  | .branch side n => if n ∈ (idealAt I side).1 then ⊥ else merged Vertex (.branch side n)

@[simp] private theorem split_familyOf (I : Ideal × Ideal) (side : Bool) (n : Node) :
    SplitAt (familyOf I (.branch side n)) ↔ n ∈ (idealAt I side).1 := by
  by_cases h : n ∈ (idealAt I side).1 <;>
    simp [familyOf, h, split_discrete, not_split_merged]

noncomputable def splitOf (I : Ideal × Ideal) : Split Vertex :=
  ⟨familyOf I, (compatible_iff_edges _).mpr fun side x y e hy =>
    (split_familyOf I side x).mpr
      ((idealAt I side).2 (Node.covBy_iff.mpr e).le ((split_familyOf I side y).mp hy))⟩

private noncomputable def idealBijection : Split Vertex ≃ Ideal × Ideal where
  toFun A := (toIdeal A false, toIdeal A true)
  invFun := splitOf
  left_inv A := by
    apply Split.ext
    funext v
    cases v with
    | root | a | b =>
      exact (partition_eq_merged_of_subsingleton Vertex _ _).symm
    | branch side n =>
      apply branch_partition_ext
      change SplitAt (familyOf (toIdeal A false, toIdeal A true) (.branch side n)) ↔ _
      rw [split_familyOf]
      cases side <;> exact mem_selected A _ n
  right_inv I := by
    apply Prod.ext <;> apply Subtype.ext <;> apply Finset.ext <;> intro n
    · exact (mem_selected (splitOf I) false n).trans (split_familyOf I false n)
    · exact (mem_selected (splitOf I) true n).trans (split_familyOf I true n)

private theorem branch_refine_iff {side : Bool} {n : Node} (A B : Partition Vertex (.branch side n)) :
    A ≤ B ↔ (SplitAt B → SplitAt A) := by
  rw [partition_le_iff]
  constructor
  · intro h hb ha
    exact hb (h _ _ ha)
  · intro h s t
    rw [Vertex.path_eq_route s, Vertex.path_eq_route t]
    change Same Vertex A (Vertex.branchPath side _ n) (Vertex.branchPath side _ n) →
      Same Vertex B (Vertex.branchPath side _ n) (Vertex.branchPath side _ n)
    rw [same_branch_iff, same_branch_iff]
    exact fun hs => hs.imp_right fun ha hb => ha (h hb)

private theorem idealEquiv_refinement (A B : Split Vertex) :
    A ≤ B ↔
      (idealBijection A).1.1 ⊆ (idealBijection B).1.1 ∧
        (idealBijection A).2.1 ⊆ (idealBijection B).2.1 := by
  have hm (C : Split Vertex) (side : Bool) (n : Node) :
      n ∈ (idealAt (idealBijection C) side).1 ↔ SplitAt (C.1 (.branch side n)) := by
    cases side <;> exact mem_selected C _ n
  have forward (h : A ≤ B) (side : Bool) :
      (idealAt (idealBijection A) side).1 ⊆ (idealAt (idealBijection B) side).1 := by
    intro n hn
    exact (hm B side n).mpr ((branch_refine_iff _ _).mp (h _) ((hm A side n).mp hn))
  refine ⟨fun h => ⟨forward h false, forward h true⟩, ?_⟩
  intro h
  change ∀ v, B.1 v ≤ A.1 v
  intro v
  cases v with
  | root | a | b =>
    rw [partition_eq_merged_of_subsingleton Vertex _ (A.1 _),
      partition_eq_merged_of_subsingleton Vertex _ (B.1 _)]
  | branch side n =>
    apply (branch_refine_iff _ _).mpr
    intro hn
    have hs : (idealAt (idealBijection A) side).1 ⊆ (idealAt (idealBijection B) side).1 := by
      cases side
      · exact h.1
      · exact h.2
    exact (hm B side n).mp (hs ((hm A side n).mpr hn))

/-- Compatible rooted path partitions, ordered from coarser to finer, correspond
to pairs of branch lower ideals ordered by inclusion. -/
noncomputable def idealEquiv : Split Vertex ≃o Ideal × Ideal where
  toEquiv := idealBijection
  map_rel_iff' := fun {A B} => (idealEquiv_refinement A B).symm

end Branch

namespace Vertex

def coordinates : (Unit ⊕ (Unit ⊕ (Unit ⊕ (Bool × Node)))) ≃ Vertex where
  toFun
    | .inl _ => .root
    | .inr (.inl _) => .a
    | .inr (.inr (.inl _)) => .b
    | .inr (.inr (.inr (side, n))) => .branch side n
  invFun
    | .root => .inl ()
    | .a => .inr (.inl ())
    | .b => .inr (.inr (.inl ()))
    | .branch side n => .inr (.inr (.inr (side, n)))
  left_inv := by
    rintro (_ | (_ | (_ | ⟨_, _⟩))) <;> rfl
  right_inv := by intro v; cases v <;> rfl

private theorem sum_vertices (f : Vertex → ℕ) :
    ∑ v : Vertex, f v =
      f .root + f .a + f .b +
        (∑ n : Node, f (.branch false n)) + ∑ n : Node, f (.branch true n) := by
  rw [← coordinates.sum_comp]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [coordinates, add_assoc, add_left_comm, add_comm]

end Vertex

namespace Branch

private theorem single_contribution {v : Vertex} [Subsingleton (Path Vertex v)]
    (A : Partition Vertex v) : A.parts.card - 1 = 0 := by
  rw [partition_eq_merged_of_subsingleton Vertex v A]
  simp [merged]

private theorem branch_contribution {side : Bool} {n : Node}
    (A : Partition Vertex (.branch side n))
    [Decidable (SplitAt A)] : A.parts.card - 1 = if SplitAt A then 1 else 0 := by
  by_cases h : SplitAt A
  · rw [ite_eq_left h, (branch_partition_eq A).1 h, Finpartition.card_bot, Finset.card_univ,
      Vertex.card_path_branch]
  · rw [ite_eq_right h, (branch_partition_eq A).2 h]
    simp [merged]

def idealRank (I : Ideal × Ideal) : ℕ := I.1.1.card + I.2.1.card

theorem idealEquiv_preserves_rank (A : Split Vertex) :
    sourceRank Vertex A = idealRank (idealEquiv A) := by
  classical
  unfold sourceRank
  rw [Vertex.sum_vertices]
  simp only [single_contribution, Nat.zero_add]
  have branch_sum (side : Bool) :
      (∑ n : Node, ((A.1 (.branch side n)).parts.card - 1)) = (selected A side).card := by
    calc
      _ = ∑ n : Node, (if SplitAt (A.1 (.branch side n)) then 1 else 0) :=
        Finset.sum_congr rfl fun _ _ => branch_contribution _
      _ = (selected A side).card := Finset.sum_boole _ _
  rw [branch_sum false, branch_sum true]
  rfl

private theorem witness_height : sourceHeight Vertex = 12 := by
  unfold sourceHeight
  rw [Vertex.sum_vertices,
    Vertex.card_path_singleton (v := .root) (fun _ _ h => nomatch h),
    Vertex.card_path_singleton (v := .a) (fun _ _ h => nomatch h),
    Vertex.card_path_singleton (v := .b) (fun _ _ h => nomatch h)]
  simp only [Vertex.card_path_branch, Nat.reduceSub, Nat.zero_add]
  decide

noncomputable def rankFiberEquiv (k : ℕ) :
    {A : Split Vertex // sourceRank Vertex A = k} ≃ {I : Ideal × Ideal // idealRank I = k} :=
  idealEquiv.toEquiv.subtypeEquiv fun A => by
    change sourceRank Vertex A = k ↔ idealRank (idealEquiv A) = k
    rw [idealEquiv_preserves_rank]

private theorem rankCount_eq_ideal (k : ℕ) :
    rankCount Vertex k = Nat.card {I : Ideal × Ideal // idealRank I = k} :=
  Nat.card_congr (rankFiberEquiv k)

instance (k : ℕ) : Fintype {I : Ideal × Ideal // idealRank I = k} :=
  Subtype.fintype _

set_option maxRecDepth 4096 in
/-- The certificate enumerates pairs of lower ideals after the rank-fiber equivalence. -/
private theorem ideal_rank_counts :
    Fintype.card {I : Ideal × Ideal // idealRank I = 6} = 15 ∧
    Fintype.card {I : Ideal × Ideal // idealRank I = 7} = 14 ∧
    Fintype.card {I : Ideal × Ideal // idealRank I = 8} = 17 := by decide

theorem witness_rank_counts :
    rankCount Vertex 6 = 15 ∧ rankCount Vertex 7 = 14 ∧ rankCount Vertex 8 = 17 := by
  simpa only [rankCount_eq_ideal, Nat.card_eq_fintype_card] using ideal_rank_counts

private theorem not_logConcave : ¬ LogConcave (rankCount Vertex) (sourceHeight Vertex) := by
  intro h
  obtain ⟨h6, h7, h8⟩ := witness_rank_counts
  have hh : 7 < sourceHeight Vertex := by rw [witness_height]; decide
  have hc := h 7 (by decide) hh
  change rankCount Vertex 6 * rankCount Vertex 8 ≤ rankCount Vertex 7 * rankCount Vertex 7 at hc
  rw [h6, h7, h8] at hc
  exact (by decide : ¬ (15 * 17 ≤ (14 * 14 : ℕ))) hc

private theorem not_unimodal : ¬ Unimodal (rankCount Vertex) (sourceHeight Vertex) := by
  rintro ⟨m, _, hinc, hdec⟩
  obtain ⟨h6, h7, h8⟩ := witness_rank_counts
  by_cases hm : 7 ≤ m
  · have h := hinc 6 7 (by decide) hm
    rw [h6, h7] at h
    exact (by decide : ¬ (15 ≤ (14 : ℕ))) h
  · have hh : 8 ≤ sourceHeight Vertex := by rw [witness_height]; decide
    have h := hdec 7 8 (Nat.le_of_lt (Nat.lt_of_not_ge hm)) (by decide) hh
    rw [h7, h8] at h
    exact (by decide : ¬ (17 ≤ (14 : ℕ))) h

end Branch

/-- The same rooted poset refutes both properties in Question 1. -/
theorem result : ¬ claim := by
  intro h
  exact (h Vertex).elim Branch.not_logConcave Branch.not_unimodal

end D5.S3.Combinatorics.Lattices.FroeseGeorgePathCoverRankRefutation
