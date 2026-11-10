# FiniteCyclicNoncoverGreedyBranches

## Abstract

Actual original s2 no/yes branches and their later-round restrictions, without altering ambient labels.

The actual original s2 branches, exact free interval predicates, native no/yes restrictions and later-round separation. The interval conjugacy and critical-family formulas are developed in the interval, native and survivor modules. Lexical section variables are recorded faithfully. Lean may omit unused variables.

**Definition 1.1 (branchA).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchA`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.branchA.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def branchA {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) : Finset (Finset V)

**Definition 1.2 (branchB).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchB`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.branchB.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def branchB {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) : Finset (Finset V)

**Theorem 1.3 (second_round).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.second_round`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.second_round` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.second_round.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem second_round {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :

    remaining (tailFaces (by omega) s) (s ⟨1, by omega⟩) = branchA hn s ∪ branchB hn s

**Theorem 1.4 (second_original).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.second_original`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.second_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.second_original.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem second_original {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :

    remaining (remaining (FiniteVertexDominationCollapse.faceSet

      (noncover (show 0 < n by omega) s)) (point (by omega) s)) (s ⟨1, by omega⟩) =

      insert {point (by omega) s} (branchA hn s ∪ branchB hn s)

**Theorem 1.5 (branchA_fixed).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchA_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchA_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.branchA_fixed.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem branchA_fixed {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V)

    {a : Finset V} (ha : a ∈ branchA hn s) :

    point (by omega) s ∉ a ∧ s ⟨1, by omega⟩ ∉ a ∧

      s ⟨2, by omega⟩ ∈ a ∧ s ⟨n-1, by omega⟩ ∈ a

**Theorem 1.6 (branchB_fixed).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchB_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchB_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.branchB_fixed.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem branchB_fixed {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V)

    {a : Finset V} (ha : a ∈ branchB hn s) :

    point (by omega) s ∉ a ∧ s ⟨n-1, by omega⟩ ∉ a ∧ s ⟨2, by omega⟩ ∉ a ∧

      s ⟨1, by omega⟩ ∈ a ∧ s ⟨3, by omega⟩ ∈ a ∧ s ⟨n-2, by omega⟩ ∈ a

**Definition 1.7 (IntervalIndependent).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.IntervalIndependent`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.IntervalIndependent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.IntervalIndependent.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def IntervalIndependent {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V)

    (lo hi : Nat) (a : Finset V) : Prop

**Theorem 1.8 (branchA_iff).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchA_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchA_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.branchA_iff.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem branchA_iff {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) (a : Finset V) :

    a ∈ branchA hn s ↔ a ⊆ ground s ∧ point (by omega) s ∉ a ∧

      s ⟨1, by omega⟩ ∉ a ∧ s ⟨2, by omega⟩ ∈ a ∧ s ⟨n-1, by omega⟩ ∈ a ∧

        IntervalIndependent hn s 3 (n-1) a

**Theorem 1.9 (branchB_iff).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchB_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchB_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.branchB_iff.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem branchB_iff {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) (a : Finset V) :

    a ∈ branchB hn s ↔ a ⊆ ground s ∧ point (by omega) s ∉ a ∧

      s ⟨n-1, by omega⟩ ∉ a ∧ s ⟨2, by omega⟩ ∉ a ∧ s ⟨1, by omega⟩ ∈ a ∧

        s ⟨3, by omega⟩ ∈ a ∧ s ⟨n-2, by omega⟩ ∈ a ∧

          IntervalIndependent hn s 4 (n-2) a

**Theorem 1.10 (second_noBranch_faces).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.second_noBranch_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.second_noBranch_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.second_noBranch_faces.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem second_noBranch_faces {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :

    (((nativeRelative (noncover (show 0 < n by omega) s)).noBranch

      (point (by omega) s)).noBranch (s ⟨1, by omega⟩)).F = branchA hn s

**Theorem 1.11 (second_yesBranch_faces).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.second_yesBranch_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.second_yesBranch_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.second_yesBranch_faces.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem second_yesBranch_faces {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :

    (((nativeRelative (noncover (show 0 < n by omega) s)).noBranch

      (point (by omega) s)).yesBranch (s ⟨1, by omega⟩)).F = branchB hn s

**Theorem 1.12 (branch_survivors).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branch_survivors`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branch_survivors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.branch_survivors.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem branch_survivors {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) (vs : List V)

    (hvs : s ⟨1, by omega⟩ ∉ vs) :

    survivors (remaining (tailFaces (by omega) s) (s ⟨1, by omega⟩)) vs =

      survivors (branchA hn s) vs ∪ survivors (branchB hn s) vs

## References

- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.IntervalIndependent`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchA`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchA_fixed`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchA_iff`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchB`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchB_fixed`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branchB_iff`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.branch_survivors`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.second_noBranch_faces`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.second_original`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.second_round`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.second_yesBranch_faces`
- Dependency: [D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction](FiniteCyclicNoncoverGreedyReduction.md)
