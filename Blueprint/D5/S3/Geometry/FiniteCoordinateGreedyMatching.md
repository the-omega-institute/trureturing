# FiniteCoordinateGreedyMatching

## Abstract

Coordinate rounds give disjoint original-label face pairs and explicit relative A and B branches.

The source section has V : Type*, Fintype V and DecidableEq V; each raw statement retains its lexical source binders and namespace. Lean may omit unused section variables. Structures and the Walk inductive include their full explicit field/constructor contracts. This matching module supplies finite source extraction; the cyclic recurrence is proved in its separate owner. The collapse consumers use the same native face and coordinate types.

**Definition 1.1 (lowers).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.lowers`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateGreedyMatching.lowers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.lowers.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def lowers (F : Finset (Finset V)) (v : V) : Finset (Finset V)

**Definition 1.2 (roundPairs).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.roundPairs`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateGreedyMatching.roundPairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.roundPairs.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def roundPairs (F : Finset (Finset V)) (v : V) : Finset (Finset V × V)

**Definition 1.3 (pairedFaces).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.pairedFaces`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateGreedyMatching.pairedFaces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.pairedFaces.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def pairedFaces (F : Finset (Finset V)) (v : V) : Finset (Finset V)

**Definition 1.4 (remaining).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.remaining`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateGreedyMatching.remaining` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.remaining.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def remaining (F : Finset (Finset V)) (v : V) : Finset (Finset V)

**Definition 1.5 (greedy).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.greedy`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateGreedyMatching.greedy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.greedy.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def greedy (F : Finset (Finset V)) : List V → Finset (Finset V × V)

**Definition 1.6 (survivors).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.survivors`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateGreedyMatching.survivors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.survivors.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def survivors (F : Finset (Finset V)) : List V → Finset (Finset V)

**Definition 1.7 (rounds).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.rounds`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateGreedyMatching.rounds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.rounds.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def rounds (F : Finset (Finset V)) : List V → List (Finset (Finset V × V))

**Theorem 1.8 (mem_lowers).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.mem_lowers`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.mem_lowers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.mem_lowers.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

@[simp] theorem mem_lowers (F : Finset (Finset V)) (v : V) (s : Finset V) :

    s ∈ lowers F v ↔ s ∈ F ∧ v ∉ s ∧ insert v s ∈ F

**Theorem 1.9 (mem_roundPairs).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.mem_roundPairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.mem_roundPairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.mem_roundPairs.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

@[simp] theorem mem_roundPairs (F : Finset (Finset V)) (v : V) (e : Finset V × V) :

    e ∈ roundPairs F v ↔ e.2 = v ∧ e.1 ∈ lowers F v

**Theorem 1.10 (paired_subset).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.paired_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.paired_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.paired_subset.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem paired_subset (F : Finset (Finset V)) (v : V) : pairedFaces F v ⊆ F

**Theorem 1.11 (round_incident).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.round_incident`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.round_incident` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.round_incident.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem round_incident {F : Finset (Finset V)} {v : V}

    {e : Finset V × V} (he : e ∈ roundPairs F v) {s : Finset V}

    (hs : Incident s e) : s ∈ pairedFaces F v

**Theorem 1.12 (round_disjoint).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.round_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.round_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.round_disjoint.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem round_disjoint {F : Finset (Finset V)} {v : V}

    {e f : Finset V × V} (he : e ∈ roundPairs F v) (hf : f ∈ roundPairs F v)

    {s : Finset V} (hse : Incident s e) (hsf : Incident s f) : e = f

**Theorem 1.13 (remaining_subset).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.remaining_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.remaining_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.remaining_subset.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem remaining_subset (F : Finset (Finset V)) (v : V) : remaining F v ⊆ F

**Theorem 1.14 (greedy_endpoints).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.greedy_endpoints`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.greedy_endpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.greedy_endpoints.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem greedy_endpoints (F : Finset (Finset V)) (vs : List V)

    {e : Finset V × V} (he : e ∈ greedy F vs) :

    e.1 ∈ F ∧ upper e ∈ F ∧ e.2 ∉ e.1

**Theorem 1.15 (greedy_disjoint).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.greedy_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.greedy_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.greedy_disjoint.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem greedy_disjoint (F : Finset (Finset V)) (vs : List V)

    {e f : Finset V × V} (he : e ∈ greedy F vs) (hf : f ∈ greedy F vs)

    {s : Finset V} (hse : Incident s e) (hsf : Incident s f) : e = f

**Theorem 1.16 (survivors_subset).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.survivors_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.survivors_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.survivors_subset.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem survivors_subset (F : Finset (Finset V)) (vs : List V) :

    survivors F vs ⊆ F

**Theorem 1.17 (mem_survivors).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.mem_survivors`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.mem_survivors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.mem_survivors.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem mem_survivors (F : Finset (Finset V)) (vs : List V) (s : Finset V) :

    s ∈ survivors F vs ↔ s ∈ F ∧ ∀ e ∈ greedy F vs, ¬ Incident s e

**Definition 1.18 (pairing).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.pairing`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateGreedyMatching.pairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual pairing on the NONEMPTY native faces, without any acyclicity field.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def pairing (K : PreAbstractSimplicialComplex V) (vs : List V) : Pairing K

**Definition 1.19 (Down).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.Down`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateGreedyMatching.Down` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.Down.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def Down (F : Finset (Finset V)) : Prop

**Definition 1.20 (RelativeFamily).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.RelativeFamily`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateGreedyMatching.RelativeFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Augmented complexes represented literally as finite downward families. The empty family and the family containing only empty are distinct.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

structure RelativeFamily where

  E : Finset (Finset V)

  D : Finset (Finset V)

  downE : Down E

  downD : Down D

  inclusion : D ⊆ E

**Definition 1.21 (RelativeFamily.F).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.F`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateGreedyMatching.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.RelativeFamily.F.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def F (R : RelativeFamily (V := V)) : Finset (Finset V)

**Definition 1.22 (RelativeFamily.A).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.A`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateGreedyMatching.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.RelativeFamily.A.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def A (R : RelativeFamily (V := V)) (v : V) : Finset (Finset V)

**Definition 1.23 (RelativeFamily.B).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.B`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateGreedyMatching.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.RelativeFamily.B.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def B (R : RelativeFamily (V := V)) (v : V) : Finset (Finset V)

**Theorem 1.24 (RelativeFamily.mem_A).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.mem_A`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.mem_A` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.RelativeFamily.mem_A.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

@[simp] theorem mem_A (R : RelativeFamily (V := V)) (v : V) (s : Finset V) :

    s ∈ R.A v ↔ s ∈ R.F ∧ v ∉ s ∧ insert v s ∉ R.E

**Theorem 1.25 (RelativeFamily.mem_B).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.mem_B`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.mem_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.RelativeFamily.mem_B.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

@[simp] theorem mem_B (R : RelativeFamily (V := V)) (v : V) (s : Finset V) :

    s ∈ R.B v ↔ s ∈ R.F ∧ v ∈ s ∧ s.erase v ∈ R.D

**Theorem 1.26 (RelativeFamily.A_upper).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.A_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.A_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.RelativeFamily.A_upper.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem A_upper (R : RelativeFamily (V := V)) (v : V)

    {s t : Finset V} (hs : s ∈ R.A v) (ht : t ∈ R.F) (hst : s ⊆ t) : t ∈ R.A v

**Theorem 1.27 (RelativeFamily.B_lower).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.B_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.B_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.RelativeFamily.B_lower.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem B_lower (R : RelativeFamily (V := V)) (v : V)

    {s t : Finset V} (hs : s ∈ R.B v) (ht : t ∈ R.F) (hts : t ⊆ s) : t ∈ R.B v

**Theorem 1.28 (RelativeFamily.branches_incomparable).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.branches_incomparable`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.branches_incomparable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.RelativeFamily.branches_incomparable.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem branches_incomparable (R : RelativeFamily (V := V)) (v : V)

    {s t : Finset V} (hs : s ∈ R.A v) (ht : t ∈ R.B v) :

    ¬ s ⊆ t ∧ ¬ t ⊆ s

**Theorem 1.29 (RelativeFamily.remaining_eq).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.remaining_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.remaining_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact residual decomposition, including the empty face if it is available.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem remaining_eq (R : RelativeFamily (V := V)) (v : V) :

    remaining R.F v = R.A v ∪ R.B v

**Definition 1.30 (RelativeFamily.noBranch).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.noBranch`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateGreedyMatching.noBranch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A as a relative difference on the SAME original coordinate type.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def noBranch (R : RelativeFamily (V := V)) (v : V) : RelativeFamily (V := V)

**Definition 1.31 (RelativeFamily.yesBranch).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.yesBranch`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateGreedyMatching.yesBranch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B as a relative difference without relabelling or dropping its fixed v. All no-v faces of the upper family are put in the lower family.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def yesBranch (R : RelativeFamily (V := V)) (v : V) : RelativeFamily (V := V)

**Theorem 1.32 (RelativeFamily.noBranch_faces).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.noBranch_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.noBranch_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.RelativeFamily.noBranch_faces.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem noBranch_faces (R : RelativeFamily (V := V)) (v : V) :

    (R.noBranch v).F = R.A v

**Theorem 1.33 (RelativeFamily.yesBranch_faces).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.yesBranch_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.yesBranch_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.RelativeFamily.yesBranch_faces.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem yesBranch_faces (R : RelativeFamily (V := V)) (v : V) :

    (R.yesBranch v).F = R.B v

**Definition 1.34 (nativeRelative).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.nativeRelative`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateGreedyMatching.nativeRelative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact augmented/native bridge used by the nonempty greedy algorithm.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def nativeRelative (K : PreAbstractSimplicialComplex V) : RelativeFamily (V := V)

**Theorem 1.35 (nativeRelative_faces).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.nativeRelative_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateGreedyMatching.nativeRelative_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteCoordinateGreedyMatching.nativeRelative_faces.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem nativeRelative_faces (K : PreAbstractSimplicialComplex V) :

    (nativeRelative K).F = faceSet K

## References

- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.A`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.A_upper`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.B`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.B_lower`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.Down`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.F`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.RelativeFamily`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.branches_incomparable`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.greedy`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.greedy_disjoint`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.greedy_endpoints`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.lowers`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.mem_A`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.mem_B`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.mem_lowers`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.mem_roundPairs`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.mem_survivors`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.nativeRelative`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.nativeRelative_faces`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.noBranch`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.noBranch_faces`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.pairedFaces`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.paired_subset`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.pairing`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.remaining`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.remaining_eq`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.remaining_subset`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.roundPairs`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.round_disjoint`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.round_incident`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.rounds`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.survivors`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.survivors_subset`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.yesBranch`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateGreedyMatching.yesBranch_faces`
- Dependency: [D5/S3/Geometry/FiniteAcyclicFaceMatching](FiniteAcyclicFaceMatching.md)
