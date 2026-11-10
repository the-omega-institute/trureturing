# FiniteGreedyMatchingAcyclicity

## Abstract

The literal coordinate-greedy matching is acyclic by incomparable relative branches and a no-return three-region potential.

The source section has V : Type*, Fintype V and DecidableEq V; each raw statement retains its lexical source binders and namespace. Lean may omit unused section variables. Structures and the Walk inductive include their full explicit field/constructor contracts. This matching module supplies finite source extraction; the cyclic recurrence is proved in its separate owner. The collapse consumers use the same native face and coordinate types.

**Definition 1.1 (Separated).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.Separated`

*Formalization.* `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.Separated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.Separated.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def Separated (A B : Finset (Finset V)) : Prop

**Theorem 1.2 (separated_disjoint).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.separated_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.separated_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.separated_disjoint.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem separated_disjoint {A B : Finset (Finset V)} (h : Separated A B) : Disjoint A B

**Theorem 1.3 (separated_mono).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.separated_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.separated_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.separated_mono.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem separated_mono {A B C D : Finset (Finset V)} (h : Separated A B)

    (hC : C ⊆ A) (hD : D ⊆ B) : Separated C D

**Theorem 1.4 (lowers_union).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.lowers_union`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.lowers_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.lowers_union.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem lowers_union {A B : Finset (Finset V)} (h : Separated A B) (v : V) :

    lowers (A ∪ B) v = lowers A v ∪ lowers B v

**Theorem 1.5 (roundPairs_union).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.roundPairs_union`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.roundPairs_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.roundPairs_union.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem roundPairs_union {A B : Finset (Finset V)} (h : Separated A B) (v : V) :

    roundPairs (A ∪ B) v = roundPairs A v ∪ roundPairs B v

**Theorem 1.6 (pairedFaces_union).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pairedFaces_union`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pairedFaces_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.pairedFaces_union.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem pairedFaces_union {A B : Finset (Finset V)} (h : Separated A B) (v : V) :

    pairedFaces (A ∪ B) v = pairedFaces A v ∪ pairedFaces B v

**Theorem 1.7 (remaining_union).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.remaining_union`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.remaining_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.remaining_union.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem remaining_union {A B : Finset (Finset V)} (h : Separated A B) (v : V) :

    remaining (A ∪ B) v = remaining A v ∪ remaining B v

**Theorem 1.8 (greedy_union).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.greedy_union`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.greedy_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The split recursion is EXACTLY the original greedy algorithm.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem greedy_union {A B : Finset (Finset V)} (h : Separated A B) (vs : List V) :

    greedy (A ∪ B) vs = greedy A vs ∪ greedy B vs

**Definition 1.9 (HasPair).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.HasPair`

*Formalization.* `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.HasPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.HasPair.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def HasPair (P : Finset (Finset V × V)) (a b : Finset V) : Prop

**Definition 1.10 (Edge).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.Edge`

*Formalization.* `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.Edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.Edge.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def Edge (F : Finset (Finset V)) (P : Finset (Finset V × V))

    (a b : Finset V) : Prop

**Theorem 1.11 (walk_potential).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.walk_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.walk_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.walk_potential.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem walk_potential {α : Type*} {r : α → α → Prop} (f : α → ℤ)

    (hf : ∀ a b, r a b → f a < f b) {a b : α} (h : Walk r a b) : f a < f b

**Theorem 1.12 (acyclic_potential).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.acyclic_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.acyclic_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.acyclic_potential.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem acyclic_potential {α : Type*} {r : α → α → Prop} (f : α → ℤ)

    (hf : ∀ a b, r a b → f a < f b) : Acyclic r

**Theorem 1.13 (walk_nondecreasing).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.walk_nondecreasing`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.walk_nondecreasing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.walk_nondecreasing.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem walk_nondecreasing {α : Type*} {r : α → α → Prop} (z : α → Nat)

    (hz : ∀ a b, r a b → z a ≤ z b) {a b : α} (h : Walk r a b) : z a ≤ z b

**Theorem 1.14 (walk_one_zone).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.walk_one_zone`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.walk_one_zone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.walk_one_zone.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem walk_one_zone {α : Type*} {r : α → α → Prop} (z : α → Nat)

    (hz : ∀ a b, r a b → z a ≤ z b) {a b : α} (h : Walk r a b)

    (k : Nat) (ha : z a = k) (hb : z b = k) :

    Walk (fun a b => r a b ∧ z a = k ∧ z b = k) a b

**Theorem 1.15 (acyclic_zones).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.acyclic_zones`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.acyclic_zones` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A no-return partition reduces a cycle to one region.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem acyclic_zones {α : Type*} {r : α → α → Prop} (z : α → Nat)

    (hz : ∀ a b, r a b → z a ≤ z b)

    (hk : ∀ k, Acyclic (fun a b => r a b ∧ z a = k ∧ z b = k)) : Acyclic r

**Theorem 1.16 (RelativeFamily.separated_branches).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.separated_branches`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.separated_branches` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.separated_branches.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem separated_branches : Separated (R.A v) (R.B v)

**Theorem 1.17 (RelativeFamily.greedy_cons).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.greedy_cons`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.greedy_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.greedy_cons.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem greedy_cons (vs : List V) : greedy R.F (v :: vs) =

    roundPairs R.F v ∪ (greedy (R.A v) vs ∪ greedy (R.B v) vs)

**Definition 1.18 (RelativeFamily.zone).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone`

*Formalization.* `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.zone.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

def zone (s : Finset V) : Nat

**Theorem 1.19 (RelativeFamily.zone_A).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_A`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_A` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.zone_A.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem zone_A {s : Finset V} (hs : s ∈ R.A v) : R.zone v s = 0

**Theorem 1.20 (RelativeFamily.zone_B).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_B`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.zone_B.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem zone_B {s : Finset V} (hs : s ∈ R.B v) : R.zone v s = 2

**Theorem 1.21 (RelativeFamily.zone_A_iff).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_A_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_A_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.zone_A_iff.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem zone_A_iff (s : Finset V) : R.zone v s = 0 ↔ s ∈ R.A v

**Theorem 1.22 (RelativeFamily.zone_B_iff).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_B_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_B_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.zone_B_iff.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem zone_B_iff (s : Finset V) : R.zone v s = 2 ↔ s ∈ R.B v

**Theorem 1.23 (RelativeFamily.paired_not_A).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.paired_not_A`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.paired_not_A` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.paired_not_A.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem paired_not_A {s : Finset V} (hs : s ∈ pairedFaces R.F v) : s ∉ R.A v

**Theorem 1.24 (RelativeFamily.paired_not_B).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.paired_not_B`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.paired_not_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.paired_not_B.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem paired_not_B {s : Finset V} (hs : s ∈ pairedFaces R.F v) : s ∉ R.B v

**Theorem 1.25 (RelativeFamily.zone_P).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_P`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_P` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.zone_P.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem zone_P {s : Finset V} (hs : s ∈ pairedFaces R.F v) : R.zone v s = 1

**Theorem 1.26 (RelativeFamily.paired_of_zone_one).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.paired_of_zone_one`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.paired_of_zone_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.paired_of_zone_one.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem paired_of_zone_one {s : Finset V} (hs : s ∈ R.F) (hz : R.zone v s = 1) :

    s ∈ pairedFaces R.F v

**Theorem 1.27 (RelativeFamily.pair_same_zone).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pair_same_zone`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pair_same_zone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.pair_same_zone.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem pair_same_zone (vs : List V) {e : Finset V × V}

    (he : e ∈ greedy R.F (v::vs)) : R.zone v e.1 = R.zone v (upper e)

**Theorem 1.28 (RelativeFamily.zone_nondecreasing).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_nondecreasing`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_nondecreasing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.zone_nondecreasing.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem zone_nondecreasing (vs : List V) {a b : Finset V}

    (hab : Edge R.F (greedy R.F (v::vs)) a b) : R.zone v a ≤ R.zone v b

**Theorem 1.29 (RelativeFamily.pair_in_A).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pair_in_A`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pair_in_A` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.pair_in_A.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem pair_in_A (vs : List V) {a b : Finset V} (ha : a ∈ R.A v)

    (hp : HasPair (greedy R.F (v::vs)) a b) : HasPair (greedy (R.A v) vs) a b

**Theorem 1.30 (RelativeFamily.pair_in_B).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pair_in_B`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pair_in_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.pair_in_B.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem pair_in_B (vs : List V) {a b : Finset V} (ha : a ∈ R.B v)

    (hp : HasPair (greedy R.F (v::vs)) a b) : HasPair (greedy (R.B v) vs) a b

**Theorem 1.31 (RelativeFamily.edge_in_A).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.edge_in_A`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.edge_in_A` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.edge_in_A.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem edge_in_A (vs : List V) {a b : Finset V}

    (ha : a ∈ R.A v) (hb : b ∈ R.A v)

    (he : Edge R.F (greedy R.F (v::vs)) a b) :

    Edge (R.A v) (greedy (R.A v) vs) a b

**Theorem 1.32 (RelativeFamily.edge_in_B).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.edge_in_B`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.edge_in_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.edge_in_B.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem edge_in_B (vs : List V) {a b : Finset V}

    (ha : a ∈ R.B v) (hb : b ∈ R.B v)

    (he : Edge R.F (greedy R.F (v::vs)) a b) :

    Edge (R.B v) (greedy (R.B v) vs) a b

**Definition 1.33 (RelativeFamily.pRank).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pRank`

*Formalization.* `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.pRank.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

def pRank (_R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V) (s : Finset V) : ℤ

**Theorem 1.34 (RelativeFamily.paired_region_increases).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.paired_region_increases`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.paired_region_increases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.RelativeFamily.paired_region_increases.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

Definitions and proofs are in the paired Lean module.

theorem paired_region_increases (vs : List V) {a b : Finset V}

    (haP : a ∈ pairedFaces R.F v) (hbP : b ∈ pairedFaces R.F v)

    (he : Edge R.F (greedy R.F (v::vs)) a b) : R.pRank v a < R.pRank v b

**Theorem 1.35 (greedy_acyclic).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.greedy_acyclic`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.greedy_acyclic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Full acyclicity of the ACTUAL coordinate greedy algorithm on any relative complex, proved by induction on the coordinate list and the A/P/B partition.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem greedy_acyclic (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V))

    (vs : List V) : Acyclic (Edge R.F (greedy R.F vs))

**Theorem 1.36 (pairing_edge).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pairing_edge`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pairing_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteGreedyMatchingAcyclicity.pairing_edge.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem pairing_edge (K : PreAbstractSimplicialComplex V) (vs : List V) (a b : Finset V) :

    (pairing K vs).Edge a b ↔ Edge (FiniteVertexDominationCollapse.faceSet K)

      (greedy (FiniteVertexDominationCollapse.faceSet K) vs) a b

**Theorem 1.37 (pairing_acyclic).**

Lean statement: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pairing_acyclic`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pairing_acyclic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic native pairing has genuine acyclicity with no input certificate.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem pairing_acyclic (K : PreAbstractSimplicialComplex V) (vs : List V) :

    (pairing K vs).IsAcyclic

## References

- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.Edge`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.HasPair`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.Separated`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.acyclic_potential`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.acyclic_zones`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.edge_in_A`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.edge_in_B`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.greedy_acyclic`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.greedy_cons`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.greedy_union`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.lowers_union`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pRank`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pair_in_A`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pair_in_B`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pair_same_zone`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pairedFaces_union`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.paired_not_A`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.paired_not_B`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.paired_of_zone_one`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.paired_region_increases`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pairing_acyclic`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.pairing_edge`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.remaining_union`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.roundPairs_union`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.separated_branches`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.separated_disjoint`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.separated_mono`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.walk_nondecreasing`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.walk_one_zone`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.walk_potential`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_A`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_A_iff`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_B`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_B_iff`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_P`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyMatchingAcyclicity.zone_nondecreasing`
- Dependency: [D5/S3/Geometry/FiniteCoordinateGreedyMatching](FiniteCoordinateGreedyMatching.md)
