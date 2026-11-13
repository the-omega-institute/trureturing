/- GID: D5/S3/Combinatorics/Partitions/LyudogovskiySimplex
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/LyudogovskiySimplex
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram]
   utility: none
   digest: Integer-partition unit transfers and exact local clique layers. -/

import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Combinatorics.Partitions.LyudogovskiySimplex

/-- A zero row is omitted; a positive row contributes one occurrence. -/
def part (k : ℕ) : Multiset ℕ := if k = 0 then 0 else {k}

/-- The two displayed slots are distinct occurrences, even when their sizes agree.
The first slot donates one unit; the second may be the virtual zero recipient. -/
def UnitTransfer {n : ℕ} (p q : Nat.Partition n) : Prop :=
  p ≠ q ∧ ∃ (s : Multiset ℕ) (a b : ℕ),
    p.parts = {a + 1} + part b + s ∧
    q.parts = part a + {b + 1} + s

private theorem transfer_symm {n : ℕ} {p q : Nat.Partition n}
    (h : UnitTransfer p q) : UnitTransfer q p := by
  obtain ⟨hne, s, a, b, hp, hq⟩ := h
  refine ⟨hne.symm, s, b, a, ?_, ?_⟩
  · simpa [add_comm, add_left_comm, add_assoc] using hq
  · simpa [add_comm, add_left_comm, add_assoc] using hp

/-- The source simple graph on all integer partitions of n. -/
def graph (n : ℕ) : SimpleGraph (Nat.Partition n) where
  Adj := UnitTransfer
  symm := fun _ _ h => transfer_symm h
  loopless := fun _ h => h.1 rfl

/-- All actual finite cliques, including singletons and the empty clique. -/
def cliques (n : ℕ) : Finset (Finset (Nat.Partition n)) :=
  Finset.univ.powerset.filter (fun s => (graph n).IsClique (s : Set (Nat.Partition n)))

/-- Maximum clique cardinality containing p, minus one. -/
def localDimension {n : ℕ} (p : Nat.Partition n) : ℕ :=
  ((cliques n).filter (p ∈ ·)).sup (fun s => s.card - 1)

/-- This is the exact local-dimension level, rather than a superlevel. -/
def layer (r n : ℕ) : Finset (Nat.Partition n) :=
  Finset.univ.filter (fun p => localDimension p = r)

def maxDimension (n : ℕ) : ℕ := Finset.univ.sup (fun p : Nat.Partition n => localDimension p)

/-- The infimum convention has value zero if the set is empty.
The threshold assertion includes existence and positive leastness. -/
def threshold (r : ℕ) : ℕ := sInf {n : ℕ | 0 < n ∧ (layer r n).Nonempty}

def triangular (r : ℕ) : ℕ := r * (r + 1) / 2

/-- The finite Young ideal of the staircase (r,r-1,...,1), including r=0. -/
def staircase (r : ℕ) : YoungDiagram where
  cells := ((Finset.range r).product (Finset.range r)).filter (fun c => c.1 + c.2 < r)
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at *
    exact ⟨⟨lt_of_le_of_lt hxy.1 hy.1.1, lt_of_le_of_lt hxy.2 hy.1.2⟩,
      lt_of_le_of_lt (Nat.add_le_add hxy.1 hxy.2) hy.2⟩

/-- A genuine one-cell Young extension of the staircase. -/
def firstFamily (r n : ℕ) : Finset (Nat.Partition n) :=
  Finset.univ.filter (fun p => (staircase r).cells ⊆ (YoungDiagram.ofPartition p).cells ∧
    ((YoungDiagram.ofPartition p).cells \ (staircase r).cells).card = 1)

/-- The complete threshold and global-maximum question, with existence explicit. -/
def ThresholdClaim : Prop :=
  (∀ r : ℕ, threshold r = triangular r + 1 ∧
    IsLeast {n : ℕ | 0 < n ∧ (layer r n).Nonempty} (triangular r + 1)) ∧
  (∀ n : ℕ, 0 < n → maxDimension n =
    ((Finset.range (n + 1)).filter (fun r => triangular r + 1 ≤ n)).sup id)

/-- Both inclusions at the literal threshold, and the exact distinct-family count. -/
def FirstOccurrenceClaim : Prop := ∀ r : ℕ, 2 ≤ r →
  layer r (threshold r) = firstFamily r (threshold r) ∧
  layer r (triangular r + 1) = firstFamily r (triangular r + 1) ∧
  (firstFamily r (threshold r)).card = r + 1

private theorem column_count (d : YoungDiagram) (j : ℕ) :
    (d.rowLens : Multiset ℕ).countP (fun k => j < k) = d.colLen j := by
  have hf : (Finset.range (d.colLen 0)).filter (fun i => j < d.rowLen i) =
      Finset.range (d.colLen j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_colLen]
    constructor
    · exact And.right
    · intro hi
      exact ⟨lt_of_lt_of_le hi (d.colLen_anti 0 j (Nat.zero_le j)), hi⟩
  have hc := congrArg Finset.card hf
  simpa [YoungDiagram.rowLens, Multiset.countP_map, Multiset.countP_eq_card_filter,
    Finset.filter_val, Finset.range_val] using hc

private theorem partition_column_count {n : ℕ} (p : Nat.Partition n) (j : ℕ) :
    p.parts.countP (fun k => j < k) = (YoungDiagram.ofPartition p).colLen j := by
  have h := column_count (YoungDiagram.ofPartition p) j
  simpa using h

end D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
