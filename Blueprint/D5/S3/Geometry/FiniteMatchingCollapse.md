# FiniteMatchingCollapse

## Abstract

Finite acyclic face matchings construct native collapse sequences to saturated subcomplexes.

The source section has V : Type*, Fintype V and DecidableEq V; each raw statement retains its lexical source binders and namespace. Lean may omit unused section variables. Structures and the Walk inductive include their full explicit field/constructor contracts. This matching module supplies finite source extraction; the cyclic recurrence is proved in its separate owner. The collapse consumers use the same native face and coordinate types.

**Theorem 1.1 (frame_mem).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCollapse.frame_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCollapse.frame_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replay an arbitrary native sequence by deleting its actual pair prefix.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem frame_mem {K L : PreAbstractSimplicialComplex V} (S : Sequence K L)

    (i : Nat) (hi : i ≤ S.pairs.length) (s : Finset V) :

    s ∈ S.frames.getD i L ↔ s ∈ K ∧

      ∀ P ∈ S.pairs.take i, s ≠ P.lower ∧ s ≠ P.upper

**Theorem 1.2 (frames_terminal).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCollapse.frames_terminal`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCollapse.frames_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCollapse.frames_terminal.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem frames_terminal {K L : PreAbstractSimplicialComplex V}

    (S : Sequence K L) : S.frames.getD S.pairs.length L = L

**Theorem 1.3 (elementary_face_count).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCollapse.elementary_face_count`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCollapse.elementary_face_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCollapse.elementary_face_count.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem elementary_face_count (P : CollapsePair V) :

    (faceSet P.ambient).card = (faceSet P.retained).card + 2

**Theorem 1.4 (sequence_face_count).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCollapse.sequence_face_count`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCollapse.sequence_face_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual step removes two distinct nonempty faces.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem sequence_face_count {K L : PreAbstractSimplicialComplex V}

    (S : Sequence K L) :

    (faceSet K).card = (faceSet L).card + 2 * S.pairs.length

**Theorem 1.5 (pair_ambient_le_source).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCollapse.pair_ambient_le_source`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCollapse.pair_ambient_le_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCollapse.pair_ambient_le_source.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem pair_ambient_le_source {K L : PreAbstractSimplicialComplex V}

    (S : Sequence K L) (P : CollapsePair V) (hP : P ∈ S.pairs) : P.ambient ≤ K

**Theorem 1.6 (sequence_lowers_nodup).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCollapse.sequence_lowers_nodup`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCollapse.sequence_lowers_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCollapse.sequence_lowers_nodup.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem sequence_lowers_nodup {K L : PreAbstractSimplicialComplex V}

    (S : Sequence K L) : (S.pairs.map CollapsePair.lower).Nodup

**Theorem 1.7 (matching_pair_occurs).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCollapse.matching_pair_occurs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCollapse.matching_pair_occurs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCollapse.matching_pair_occurs.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem matching_pair_occurs {K L T : PreAbstractSimplicialComplex V}

    (M : Pairing K) (S : Sequence L T)

    (hS : ∀ P ∈ S.pairs, (P.lower, P.apex) ∈ M.pairs)

    (e : Finset V × V) (he : e ∈ M.pairs) (hl : e.1 ∈ L) :

    (∃ P ∈ S.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ T

**Theorem 1.8 (frames_supported).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCollapse.frames_supported`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCollapse.frames_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCollapse.frames_supported.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem frames_supported {K L : PreAbstractSimplicialComplex V} (S : Sequence K L)

    (W : Finset V) (hW : ∀ s ∈ K, s ⊆ W)

    (J : PreAbstractSimplicialComplex V) (hJ : J ∈ S.frames) :

    ∀ s ∈ J, s ⊆ W

**Theorem 1.9 (Pairing.sequence_exists).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCollapse.sequence_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCollapse.sequence_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual finite extraction, including its integration invariant: every pair in the native sequence is one of the original matching pairs.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem sequence_exists (hacyc : M.IsAcyclic)

    (T : PreAbstractSimplicialComplex V) (hTK : T ≤ K) (hT : M.Saturated T)

    (L : PreAbstractSimplicialComplex V) (hLK : L ≤ K) (hTL : T ≤ L)

    (hL : M.Saturated L) (hcrit : ∀ s ∈ L, M.Unmatched s → s ∈ T) :

    ∃ S : Sequence L T, ∀ P ∈ S.pairs,

      (P.lower, P.apex) ∈ M.pairs

**Definition 1.10 (Pairing.collapseBetween).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCollapse.collapseBetween`

*Formalization.* `D5/S3/Geometry/FiniteMatchingCollapse.collapseBetween` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A definite finite native sequence, chosen from the construction above.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

def collapseBetween (hacyc : M.IsAcyclic)

    (T : PreAbstractSimplicialComplex V) (hTK : T ≤ K) (hT : M.Saturated T)

    (L : PreAbstractSimplicialComplex V) (hLK : L ≤ K) (hTL : T ≤ L)

    (hL : M.Saturated L) (hcrit : ∀ s ∈ L, M.Unmatched s → s ∈ T) : Sequence L T

**Theorem 1.11 (Pairing.collapseBetween_pairs).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCollapse.collapseBetween_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCollapse.collapseBetween_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCollapse.Pairing.collapseBetween_pairs.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem collapseBetween_pairs (hacyc : M.IsAcyclic)

    (T : PreAbstractSimplicialComplex V) (hTK : T ≤ K) (hT : M.Saturated T)

    (L : PreAbstractSimplicialComplex V) (hLK : L ≤ K) (hTL : T ≤ L)

    (hL : M.Saturated L) (hcrit : ∀ s ∈ L, M.Unmatched s → s ∈ T) (P : CollapsePair V)

    (hP : P ∈ (M.collapseBetween hacyc T hTK hT L hLK hTL hL hcrit).pairs) :

    (P.lower, P.apex) ∈ M.pairs

**Definition 1.12 (Pairing.sdrBetween).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCollapse.sdrBetween`

*Formalization.* `D5/S3/Geometry/FiniteMatchingCollapse.sdrBetween` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Native original-coordinate SDR, fixing ALL of the target.

### Source text

Exact attempted Lean contract: Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

def sdrBetween (hacyc : M.IsAcyclic)

    (T : PreAbstractSimplicialComplex V) (hTK : T ≤ K) (hT : M.Saturated T)

    (L : PreAbstractSimplicialComplex V) (hLK : L ≤ K) (hTL : T ≤ L)

    (hL : M.Saturated L) (hcrit : ∀ s ∈ L, M.Unmatched s → s ∈ T) : RelativeSDR L T hTL

## References

- Truth anchor: `D5/S3/Geometry/FiniteMatchingCollapse.collapseBetween`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCollapse.collapseBetween_pairs`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCollapse.elementary_face_count`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCollapse.frame_mem`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCollapse.frames_supported`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCollapse.frames_terminal`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCollapse.matching_pair_occurs`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCollapse.pair_ambient_le_source`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCollapse.sdrBetween`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCollapse.sequence_exists`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCollapse.sequence_face_count`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCollapse.sequence_lowers_nodup`
- Dependency: [D5/S3/Geometry/FiniteAcyclicFaceMatching](FiniteAcyclicFaceMatching.md)
