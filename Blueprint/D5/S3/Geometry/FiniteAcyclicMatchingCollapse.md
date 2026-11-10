# FiniteAcyclicMatchingCollapse

## Abstract

Same-dimensional critical faces give an actual main collapse and a separate core-to-vertex collapse.

The source section has V : Type*, Fintype V and DecidableEq V; each raw statement retains its lexical source binders and namespace. Lean may omit unused section variables. Structures and the Walk inductive include their full explicit field/constructor contracts. This matching module supplies finite source extraction; the cyclic recurrence is proved in its separate owner. The collapse consumers use the same native face and coordinate types.

**Theorem 1.1 (CriticalData.unmatched_in_X).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.unmatched_in_X`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.unmatched_in_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.unmatched_in_X.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem unmatched_in_X {s : Finset V} (hs : s ∈ K) (hu : M.Unmatched s) : s ∈ A.X

**Definition 1.2 (CriticalData.mainSequence).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.mainSequence`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.mainSequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.mainSequence.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

def mainSequence (hacyc : M.IsAcyclic) : Sequence K A.X

**Definition 1.3 (CriticalData.coreSequence).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.coreSequence`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.coreSequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.coreSequence.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

def coreSequence (hacyc : M.IsAcyclic) : Sequence A.C (vertexComplex A.p)

**Definition 1.4 (CriticalData.mainPairs).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.mainPairs`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.mainPairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.mainPairs.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

def mainPairs (hacyc : M.IsAcyclic) : List (Finset V × Finset V)

**Definition 1.5 (CriticalData.corePairs).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.corePairs`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.corePairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.corePairs.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

def corePairs (hacyc : M.IsAcyclic) : List (Finset V × Finset V)

**Theorem 1.6 (CriticalData.main_pair_original).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_pair_original`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_pair_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.main_pair_original.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem main_pair_original (hacyc : M.IsAcyclic) (P : CollapsePair V)

    (hP : P ∈ (A.mainSequence hacyc).pairs) : (P.lower, P.apex) ∈ M.pairs

**Theorem 1.7 (CriticalData.core_pair_original).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_pair_original`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_pair_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.core_pair_original.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem core_pair_original (hacyc : M.IsAcyclic) (P : CollapsePair V)

    (hP : P ∈ (A.coreSequence hacyc).pairs) : (P.lower, P.apex) ∈ M.pairs

**Theorem 1.8 (CriticalData.main_lowers_nodup).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_lowers_nodup`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_lowers_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.main_lowers_nodup.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem main_lowers_nodup (hacyc : M.IsAcyclic) :

    ((A.mainSequence hacyc).pairs.map CollapsePair.lower).Nodup

**Theorem 1.9 (CriticalData.core_lowers_nodup).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_lowers_nodup`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_lowers_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.core_lowers_nodup.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem core_lowers_nodup (hacyc : M.IsAcyclic) :

    ((A.coreSequence hacyc).pairs.map CollapsePair.lower).Nodup

**Theorem 1.10 (CriticalData.main_pair_complete).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_pair_complete`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_pair_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.main_pair_complete.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem main_pair_complete (hacyc : M.IsAcyclic) (e : Finset V × V)

    (he : e ∈ M.pairs) :

    (∃ P ∈ (A.mainSequence hacyc).pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ A.X

**Theorem 1.11 (CriticalData.core_pair_complete).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_pair_complete`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_pair_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.core_pair_complete.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem core_pair_complete (hacyc : M.IsAcyclic) (e : Finset V × V)

    (he : e ∈ M.pairs) (hl : e.1 ∈ A.C) :

    (∃ P ∈ (A.coreSequence hacyc).pairs, (P.lower, P.apex) = e) ↔

      e.1 ∉ vertexComplex A.p

**Theorem 1.12 (CriticalData.main_frames).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_frames`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_frames` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.main_frames.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem main_frames (hacyc : M.IsAcyclic) (i : Nat)

    (hi : i ≤ (A.mainSequence hacyc).pairs.length) (s : Finset V) :

    s ∈ (A.mainSequence hacyc).frames.getD i A.X ↔ s ∈ K ∧

      ∀ P ∈ (A.mainSequence hacyc).pairs.take i, s ≠ P.lower ∧ s ≠ P.upper

**Theorem 1.13 (CriticalData.core_frames).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_frames`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_frames` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.core_frames.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem core_frames (hacyc : M.IsAcyclic) (i : Nat)

    (hi : i ≤ (A.coreSequence hacyc).pairs.length) (s : Finset V) :

    s ∈ (A.coreSequence hacyc).frames.getD i (vertexComplex A.p) ↔ s ∈ A.C ∧

      ∀ P ∈ (A.coreSequence hacyc).pairs.take i, s ≠ P.lower ∧ s ≠ P.upper

**Theorem 1.14 (CriticalData.main_frames_count).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_frames_count`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_frames_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.main_frames_count.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem main_frames_count (hacyc : M.IsAcyclic) :

    (A.mainSequence hacyc).frames.length = (A.mainPairs hacyc).length + 1

**Theorem 1.15 (CriticalData.core_frames_count).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_frames_count`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_frames_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.core_frames_count.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem core_frames_count (hacyc : M.IsAcyclic) :

    (A.coreSequence hacyc).frames.length = (A.corePairs hacyc).length + 1

**Theorem 1.16 (CriticalData.main_endpoint).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.main_endpoint.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem main_endpoint (hacyc : M.IsAcyclic) :

    (A.mainSequence hacyc).frames.getD (A.mainPairs hacyc).length A.X = A.X

**Theorem 1.17 (CriticalData.core_endpoint).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.core_endpoint.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem core_endpoint (hacyc : M.IsAcyclic) :

    (A.coreSequence hacyc).frames.getD (A.corePairs hacyc).length (vertexComplex A.p) =

      vertexComplex A.p

**Theorem 1.18 (CriticalData.closure_face_count).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.closure_face_count`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.closure_face_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.closure_face_count.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem closure_face_count :

    (faceSet A.X).card = (faceSet A.C).card + A.critical.card

**Theorem 1.19 (CriticalData.vertex_face_count).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.vertex_face_count`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.vertex_face_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.vertex_face_count.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem vertex_face_count : (faceSet (vertexComplex A.p)).card = 1

**Theorem 1.20 (CriticalData.main_count).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_count`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.main_count.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem main_count (hacyc : M.IsAcyclic) :

    (faceSet K).card = (faceSet A.X).card + 2 * (A.mainPairs hacyc).length

**Theorem 1.21 (CriticalData.core_count).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_count`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.core_count.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem core_count (hacyc : M.IsAcyclic) :

    (faceSet A.C).card = 1 + 2 * (A.corePairs hacyc).length

**Theorem 1.22 (CriticalData.total_count).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.total_count`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.total_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.total_count.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem total_count (hacyc : M.IsAcyclic) :

    (faceSet K).card = 1 + A.critical.card +

      2 * ((A.mainPairs hacyc).length + (A.corePairs hacyc).length)

**Definition 1.23 (CriticalData.mainSDR).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.mainSDR`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.mainSDR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.mainSDR.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

def mainSDR (hacyc : M.IsAcyclic) : RelativeSDR K A.X A.X_le

**Definition 1.24 (CriticalData.coreSDR).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.coreSDR`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.coreSDR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Standalone C-to-point SDR, never claimed relative to the retained cells.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

def coreSDR (hacyc : M.IsAcyclic) : RelativeSDR A.C (vertexComplex A.p) A.vertex_le_C

**Theorem 1.25 (CriticalData.main_fixed).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.main_fixed.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem main_fixed (hacyc : M.IsAcyclic) (t : I)

    (x : FiniteSimplicialJoin.Space K) (hx : x.val ∈ FiniteConeCollapse.realization A.X) :

    (A.mainSDR hacyc).homotopy (t, x) = x

**Theorem 1.26 (CriticalData.core_fixed).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.core_fixed.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem core_fixed (hacyc : M.IsAcyclic) (t : I)

    (x : FiniteSimplicialJoin.Space A.C)

    (hx : x.val ∈ FiniteConeCollapse.realization (vertexComplex A.p)) :

    (A.coreSDR hacyc).homotopy (t, x) = x

**Theorem 1.27 (CriticalData.discrete_core).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.discrete_core`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.discrete_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.discrete_core.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem discrete_core (hD : A.D = 1) : A.C = vertexComplex A.p

**Theorem 1.28 (CriticalData.discrete_X_equation).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.discrete_X_equation`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.discrete_X_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.discrete_X_equation.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem discrete_X_equation (hD : A.D = 1) (s : Finset V) :

    s ∈ A.X ↔ s = {A.p} ∨ s ∈ A.critical

**Theorem 1.29 (CriticalData.discrete_core_pairs).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.discrete_core_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.discrete_core_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicMatchingCollapse.CriticalData.discrete_core_pairs.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K}

    (A : FiniteMatchingCoreClosure.CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem discrete_core_pairs (hD : A.D = 1) (hacyc : M.IsAcyclic) :

    A.corePairs hacyc = []

## References

- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.closure_face_count`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.corePairs`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.coreSDR`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.coreSequence`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_count`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_endpoint`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_fixed`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_frames`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_frames_count`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_lowers_nodup`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_pair_complete`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.core_pair_original`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.discrete_X_equation`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.discrete_core`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.discrete_core_pairs`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.mainPairs`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.mainSDR`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.mainSequence`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_count`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_endpoint`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_fixed`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_frames`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_frames_count`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_lowers_nodup`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_pair_complete`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.main_pair_original`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.total_count`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.unmatched_in_X`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicMatchingCollapse.vertex_face_count`
- Dependency: [D5/S3/Geometry/FiniteMatchingCoreClosure](FiniteMatchingCoreClosure.md)
