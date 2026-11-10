# FiniteCyclicNoncoverIntervalPaths

## Abstract

Exact original-index interval images and every ordered greedy round commute with fixed pins and original-ground complementation.

The declaration handles name the paired Lean source owners. The displayed section variables give lexical scope; unused variables need not become declaration parameters.

**Definition 1.1 (intervalEmbedding).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.intervalEmbedding`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.intervalEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def intervalEmbedding {n : Nat} (lo m : Nat) (h : lo+m ≤ n) : Fin m ↪ Fin n

**Definition 1.2 (intervalList).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.intervalList`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.intervalList` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def intervalList {n : Nat} (hn : 0 < n) (lo m : Nat) : List (Fin n)

**Theorem 1.3 (intervalList_source).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.intervalList_source`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.intervalList_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem intervalList_source {n : Nat} (hn : 0 < n) (lo m : Nat) (h : lo+m ≤ n) :

    intervalList hn lo m = ((List.finRange n).drop lo).take m ∧

    intervalList hn lo m = (List.finRange m).map (intervalEmbedding lo m h)

**Theorem 1.4 (mem_paths_interval).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.mem_paths_interval`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.mem_paths_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem mem_paths_interval {n : Nat} (hn : 0 < n) (lo m : Nat) (h : lo+m ≤ n)

    (a : Finset (Fin n)) :

    a ∈ paths (intervalList hn lo m) ↔

      (∀ i ∈ a, lo ≤ i.val ∧ i.val < lo+m) ∧

      (∀ i : Fin n, lo ≤ i.val → i.val+1 < lo+m → i ∉ a ∨ successor hn i ∉ a)

**Theorem 1.5 (mem_pathChosen_interval).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.mem_pathChosen_interval`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.mem_pathChosen_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem mem_pathChosen_interval {n : Nat} (hn : 0 < n) (lo m : Nat)

    (h : lo+m ≤ n) (i : Fin n) :

    i ∈ pathChosen (intervalList hn lo m) ↔

      lo+1 ≤ i.val ∧ i.val < lo+m ∧ (i.val-lo) % 3 = 1

**Definition 1.6 (pinnedImage).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.pinnedImage`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.pinnedImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def pinnedImage {n : Nat} (hn : 0 < n) (s : Fin n ↪ V) (lo m : Nat)

    (S : Finset (Fin n)) : Finset (Finset V)

**Theorem 1.7 (pinnedImage_iff).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.pinnedImage_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.pinnedImage_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem pinnedImage_iff {n : Nat} (hn : 0 < n) (s : Fin n ↪ V) (lo m : Nat)

    (h : lo+m ≤ n) (S : Finset (Fin n))

    (hS : ∀ i ∈ S, i.val < lo ∨ lo+m ≤ i.val) (a : Finset V) :

    a ∈ pinnedImage hn s lo m S ↔ a ⊆ ground s ∧

      (∀ i : Fin n, (i.val < lo ∨ lo+m ≤ i.val) → (s i ∉ a ↔ i ∈ S)) ∧

      (∀ i : Fin n, lo ≤ i.val → i.val+1 < lo+m →

        s i ∈ a ∨ s (successor hn i) ∈ a)

**Theorem 1.8 (survivors_pinnedImage).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.survivors_pinnedImage`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.survivors_pinnedImage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lexical declaration below retains its original parameters and hypotheses.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem survivors_pinnedImage {n : Nat} (hn : 0 < n) (s : Fin n ↪ V)

    (k lo m : Nat) (hk : k ≤ lo) (h : lo+m ≤ n) (S : Finset (Fin n))

    (hS : ∀ i ∈ S, i.val < lo ∨ lo+m ≤ i.val) :

    survivors (pinnedImage hn s lo m S) (((List.finRange n).drop k).map s) =

      if m % 3 = 1 then ∅ else

        {complementMap s (S ∪ pathChosen (intervalList hn lo m))}

## References

- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.intervalEmbedding`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.intervalList`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.intervalList_source`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.mem_pathChosen_interval`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.mem_paths_interval`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.pinnedImage`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.pinnedImage_iff`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.survivors_pinnedImage`
- Dependency: [D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches](FiniteCyclicNoncoverGreedyBranches.md)
