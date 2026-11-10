# FiniteCyclicNoncoverCollapse

## Abstract

Cyclic noncovers and their prescribed critical faces retain the original injective spoke labels and ghosts.

The source section has V : Type*, Fintype V and DecidableEq V; each raw statement retains its lexical source binders and namespace. Lean may omit unused section variables. Structures and the Walk inductive include their full explicit field/constructor contracts. This matching module supplies finite source extraction; the cyclic recurrence is proved in its separate owner. The collapse consumers use the same native face and coordinate types.

**Definition 1.1 (successor).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.successor`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.successor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.successor.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def successor {n : Nat} (hn : 0 < n) (i : Fin n) : Fin n

**Definition 1.2 (ground).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.ground`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.ground` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.ground.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def ground {n : Nat} (s : Fin n ↪ V) : Finset V

**Definition 1.3 (noncover).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.noncover`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.noncover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A face misses the two ORIGINAL endpoints of at least one cyclic rim edge.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def noncover {n : Nat} (hn : 0 < n) (s : Fin n ↪ V) : PreAbstractSimplicialComplex V

**Theorem 1.4 (mem_noncover).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.mem_noncover`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.mem_noncover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.mem_noncover.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem mem_noncover {n : Nat} (hn : 0 < n) (s : Fin n ↪ V) (a : Finset V) :

    a ∈ noncover hn s ↔ a.Nonempty ∧

      ∃ i : Fin n, a ⊆ ground s \ {s i, s (successor hn i)}

**Definition 1.5 (pointIndex).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.pointIndex`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.pointIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.pointIndex.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def pointIndex {n : Nat} (hn : 3 ≤ n) : Fin n

**Definition 1.6 (point).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.point`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.point` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.point.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def point {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) : V

**Theorem 1.7 (point_mem).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.point_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.point_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual native vertex, not VOID, UNIT, or a selected point in no space.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem point_mem {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :

    ({point hn s} : Finset V) ∈ noncover (by omega) s

**Theorem 1.8 (has_vertex).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.has_vertex`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.has_vertex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.has_vertex.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem has_vertex {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :

    ∃ p : V, ({p} : Finset V) ∈ noncover (by omega) s

**Definition 1.9 (matching).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.matching`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.matching` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cyclic greedy matching uses the given original-label order.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def matching {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :

    Pairing (noncover (show 0 < n by omega) s)

**Theorem 1.10 (matching_acyclic).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.matching_acyclic`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.matching_acyclic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.matching_acyclic.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem matching_acyclic {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :

    (matching hn s).IsAcyclic

**Definition 1.11 (remainingFaces).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.remainingFaces`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.remainingFaces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.remainingFaces.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def remainingFaces {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) : Finset (Finset V)

**Theorem 1.12 (unmatched_iff_remaining).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.unmatched_iff_remaining`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.unmatched_iff_remaining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.unmatched_iff_remaining.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem unmatched_iff_remaining {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V)

    (a : Finset V) (ha : a ∈ noncover (show 0 < n by omega) s) :

    (matching hn s).Unmatched a ↔ a ∈ remainingFaces hn s

**Definition 1.13 (blockIndex).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.blockIndex`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.blockIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Equally spaced two-vertex blocks, expressed by an injective ORIGINAL index map. The parameter start is zero based; the public membership formula below adds one to recover exactly s1,...,sn.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def blockIndex {n r : Nat} (start : Nat)

    (h : ∀ j : Fin r, ∀ b : Fin 2, start + 3 * j.val + b.val < n) :

    (Fin r × Fin 2) ↪ Fin n

**Definition 1.14 (blocks).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.blocks`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.blocks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.blocks.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def blocks {n r : Nat} (s : Fin n ↪ V) (start : Nat)

    (h : ∀ j : Fin r, ∀ b : Fin 2, start + 3 * j.val + b.val < n) : Finset V

**Theorem 1.15 (blocks_card).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.blocks_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.blocks_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.blocks_card.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem blocks_card {n r : Nat} (s : Fin n ↪ V) (start : Nat)

    (h : ∀ j : Fin r, ∀ b : Fin 2, start + 3 * j.val + b.val < n) :

    (blocks s start h).card = 2 * r

**Theorem 1.16 (mem_blocks).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.mem_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.mem_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.mem_blocks.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem mem_blocks {n r : Nat} (s : Fin n ↪ V) (start : Nat)

    (h : ∀ j : Fin r, ∀ b : Fin 2, start + 3 * j.val + b.val < n) (i : Fin n) :

    s i ∈ blocks s start h ↔

      ∃ j : Fin r, ∃ b : Fin 2, i.val = start + 3 * j.val + b.val

**Theorem 1.17 (blocks_subset_ground).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.blocks_subset_ground`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.blocks_subset_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.blocks_subset_ground.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem blocks_subset_ground {n r : Nat} (s : Fin n ↪ V) (start : Nat)

    (h : ∀ j : Fin r, ∀ b : Fin 2, start + 3 * j.val + b.val < n) :

    blocks s start h ⊆ ground s

**Definition 1.18 (criticalA).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalA.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def criticalA (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) : Finset V

**Definition 1.19 (criticalB).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalB.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def criticalB (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) : Finset V

**Definition 1.20 (criticalOne).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalOne.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def criticalOne (q : Nat) (s : Fin (3*q+1) ↪ V) : Finset V

**Definition 1.21 (criticalTwo).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalTwo.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def criticalTwo (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) : Finset V

**Theorem 1.22 (criticalA_card).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalA_card.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalA_card (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    (criticalA q hq s).card = 2*q-1

**Theorem 1.23 (criticalB_card).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalB_card.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalB_card (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    (criticalB q hq s).card = 2*q-1

**Theorem 1.24 (criticalOne_card).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalOne_card.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalOne_card (q : Nat) (s : Fin (3*q+1) ↪ V) :

    (criticalOne q s).card = 2*q

**Theorem 1.25 (criticalTwo_card).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalTwo_card.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalTwo_card (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :

    (criticalTwo q hq s).card = 2*q

**Theorem 1.26 (criticalA_formula).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact approved ORIGINAL one-based formula, not just a cardinality.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalA_formula (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) (i : Fin (3*q)) :

    s i ∈ criticalA q hq s ↔ i.val+1 = 2 ∨

      ∃ j : Nat, 1 ≤ j ∧ j < q ∧ (i.val+1 = 3*j+1 ∨ i.val+1 = 3*j+2)

**Theorem 1.27 (criticalB_formula).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalB_formula.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalB_formula (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) (i : Fin (3*q)) :

    s i ∈ criticalB q hq s ↔ i.val+1 = 3*q ∨

      ∃ j : Nat, 1 ≤ j ∧ j < q ∧ (i.val+1 = 3*j ∨ i.val+1 = 3*j+1)

**Theorem 1.28 (criticalOne_formula).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalOne_formula.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalOne_formula (q : Nat) (s : Fin (3*q+1) ↪ V) (i : Fin (3*q+1)) :

    s i ∈ criticalOne q s ↔

      ∃ j : Nat, 1 ≤ j ∧ j ≤ q ∧ (i.val+1 = 3*j ∨ i.val+1 = 3*j+1)

**Theorem 1.29 (criticalTwo_formula).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalTwo_formula.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalTwo_formula (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) (i : Fin (3*q+2)) :

    s i ∈ criticalTwo q hq s ↔ i.val+1 = 2 ∨ i.val+1 = 3*q+1 ∨

      ∃ j : Nat, 1 ≤ j ∧ j < q ∧ (i.val+1 = 3*j+1 ∨ i.val+1 = 3*j+2)

**Theorem 1.30 (spoke_mem_ground).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.spoke_mem_ground`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.spoke_mem_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.spoke_mem_ground.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem spoke_mem_ground {n : Nat} (s : Fin n ↪ V) (i : Fin n) : s i ∈ ground s

**Theorem 1.31 (criticalA_supported).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_supported`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalA_supported.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalA_supported (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    criticalA q hq s ⊆ ground s

**Theorem 1.32 (criticalB_supported).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB_supported`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalB_supported.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalB_supported (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    criticalB q hq s ⊆ ground s

**Theorem 1.33 (criticalOne_supported).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne_supported`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalOne_supported.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalOne_supported (q : Nat) (s : Fin (3*q+1) ↪ V) :

    criticalOne q s ⊆ ground s

**Theorem 1.34 (criticalTwo_supported).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo_supported`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalTwo_supported.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalTwo_supported (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :

    criticalTwo q hq s ⊆ ground s

**Theorem 1.35 (criticalA_avoids_zero).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_avoids_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_avoids_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalA_avoids_zero.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalA_avoids_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    s ⟨0, by omega⟩ ∉ criticalA q hq s

**Theorem 1.36 (criticalB_avoids_zero).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB_avoids_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB_avoids_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalB_avoids_zero.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalB_avoids_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    s ⟨0, by omega⟩ ∉ criticalB q hq s

**Theorem 1.37 (criticalOne_avoids_zero).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne_avoids_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne_avoids_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalOne_avoids_zero.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalOne_avoids_zero (q : Nat) (s : Fin (3*q+1) ↪ V) :

    s ⟨0, by omega⟩ ∉ criticalOne q s

**Theorem 1.38 (criticalTwo_avoids_zero).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo_avoids_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo_avoids_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalTwo_avoids_zero.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalTwo_avoids_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :

    s ⟨0, by omega⟩ ∉ criticalTwo q hq s

**Theorem 1.39 (successor_last).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.successor_last`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.successor_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.successor_last.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem successor_last {n : Nat} (hn : 0 < n) :

    successor hn ⟨n-1, by omega⟩ = (⟨0, hn⟩ : Fin n)

**Theorem 1.40 (successor_zero).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.successor_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.successor_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.successor_zero.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem successor_zero {n : Nat} (hn : 1 < n) :

    successor (show 0 < n by omega) ⟨0, by omega⟩ = (⟨1, hn⟩ : Fin n)

**Theorem 1.41 (criticalA_mem).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalA_mem.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalA_mem (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    criticalA q hq s ∈ noncover (by omega) s

**Theorem 1.42 (criticalB_mem).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalB_mem.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalB_mem (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    criticalB q hq s ∈ noncover (by omega) s

**Theorem 1.43 (criticalOne_mem).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalOne_mem.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalOne_mem (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :

    criticalOne q s ∈ noncover (by omega) s

**Theorem 1.44 (criticalTwo_mem).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalTwo_mem.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalTwo_mem (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :

    criticalTwo q hq s ∈ noncover (by omega) s

**Theorem 1.45 (criticalA_ne_B).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_ne_B`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_ne_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.criticalA_ne_B.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem criticalA_ne_B (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    criticalA q hq s ≠ criticalB q hq s

**Theorem 1.46 (critical_pair_antichain).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.critical_pair_antichain`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.critical_pair_antichain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.critical_pair_antichain.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem critical_pair_antichain (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :

    ¬ criticalA q hq s ⊆ criticalB q hq s ∧ ¬ criticalB q hq s ⊆ criticalA q hq s

**Theorem 1.47 (base_three_A).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.base_three_A`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.base_three_A` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Small critical-face bases are equations on the actual original labels. They do not stand in for the missing universal greedy-survivor recurrence.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem base_three_A (s : Fin 3 ↪ V) (i : Fin 3) :

    s i ∈ criticalA 1 (by omega) s ↔ i.val = 1

**Theorem 1.48 (base_three_B).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.base_three_B`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.base_three_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.base_three_B.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem base_three_B (s : Fin 3 ↪ V) (i : Fin 3) :

    s i ∈ criticalB 1 (by omega) s ↔ i.val = 2

**Theorem 1.49 (base_four).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.base_four`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.base_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.base_four.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem base_four (s : Fin 4 ↪ V) (i : Fin 4) :

    s i ∈ criticalOne 1 s ↔ i.val = 2 ∨ i.val = 3

**Theorem 1.50 (base_five).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.base_five`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.base_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.base_five.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem base_five (s : Fin 5 ↪ V) (i : Fin 5) :

    s i ∈ criticalTwo 1 (by omega) s ↔ i.val = 1 ∨ i.val = 3

**Theorem 1.51 (ghost_coordinate).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.ghost_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.ghost_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Explicit ghosts on the original ambient type, never globally retired.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem ghost_coordinate {n : Nat} (hn : 0 < n) (s : Fin n ↪ V)

    (x : Space (noncover hn s)) (v : V) (hv : v ∉ ground s) : x.val v = 0

**Theorem 1.52 (inclusion_coordinates).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.inclusion_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.inclusion_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCyclicNoncoverCollapse.inclusion_coordinates.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem inclusion_coordinates {n : Nat} (hn : 0 < n) (s : Fin n ↪ V)

    (L : PreAbstractSimplicialComplex V) (hL : L ≤ noncover hn s)

    (x : Space L) : (realizationInclusion hL x).val = x.val

## References

- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.base_five`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.base_four`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.base_three_A`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.base_three_B`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.blockIndex`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.blocks`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.blocks_card`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.blocks_subset_ground`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_avoids_zero`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_card`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_formula`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_mem`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_ne_B`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalA_supported`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB_avoids_zero`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB_card`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB_formula`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB_mem`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalB_supported`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne_avoids_zero`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne_card`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne_formula`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne_mem`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalOne_supported`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo_avoids_zero`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo_card`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo_formula`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo_mem`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.criticalTwo_supported`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.critical_pair_antichain`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.ghost_coordinate`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.ground`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.has_vertex`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.inclusion_coordinates`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.matching`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.matching_acyclic`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.mem_blocks`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.mem_noncover`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.noncover`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.point`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.pointIndex`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.point_mem`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.remainingFaces`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.spoke_mem_ground`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.successor`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.successor_last`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.successor_zero`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverCollapse.unmatched_iff_remaining`
- Dependency: [D5/S3/Geometry/FiniteAcyclicMatchingCollapse](FiniteAcyclicMatchingCollapse.md)
- Dependency: [D5/S3/Geometry/FiniteGreedyMatchingAcyclicity](FiniteGreedyMatchingAcyclicity.md)
