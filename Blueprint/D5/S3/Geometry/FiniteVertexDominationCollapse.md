# Finite dominated-vertex free-face deletion

## Abstract

A dominated vertex admits a complete original-label finite free-face deletion certificate.

The raw headers below are written in the section V : Type*, Fintype V, DecidableEq V.Unused section instances need not occur in the compiled telescope.K is a native PreAbstractSimplicialComplex, with nonempty faces only.No carrier, purity, connectedness, or realization-nonempty hypothesis is hidden.Canonical finite relative and elementary owners supply the native Sequence and SDR.This is the classical decreasing-face pairing proof, credited to the releasedCLI79532 ordinary verification, constructive_restricted_result.K_elementary_foldand actual_Ind_F_certificate.graph_fold; no novelty is claimed.

**Definition 1.1 (Extends).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.Extends`

*Formalization.* `D5/S3/Geometry/FiniteVertexDominationCollapse.Extends` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every face s of K containing v, insert u s is again a face. This is the sole combinatorial extension hypothesis and contains no collapse or geometric endpoint.

Exact attempted Lean contract:def Extends (K : PreAbstractSimplicialComplex V) (u v : V) : Prop

**Definition 1.2 (badFaces).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.badFaces`

*Formalization.* `D5/S3/Geometry/FiniteVertexDominationCollapse.badFaces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite family consists exactly of original faces containing v and omitting u; the empty face is absent.

Exact attempted Lean contract:def badFaces (K : PreAbstractSimplicialComplex V) (u v : V) : Finset (Finset V)

**Theorem 1.3 (mem_badFaces).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.mem_badFaces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.mem_badFaces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership is exactly the three stated original-face conditions.

### Source text

Exact attempted Lean contract:@[simp] theorem mem_badFaces (K : PreAbstractSimplicialComplex V) (u v : V)

    (s : Finset V) : s ∈ badFaces K u v ↔ s ∈ K ∧ v ∈ s ∧ u ∉ s

**Definition 1.4 (faceSet).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.faceSet`

*Formalization.* `D5/S3/Geometry/FiniteVertexDominationCollapse.faceSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All actual nonempty faces of K on V, collected as a finite set.

Exact attempted Lean contract:def faceSet (K : PreAbstractSimplicialComplex V) : Finset (Finset V)

**Theorem 1.5 (mem_faceSet).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.mem_faceSet`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.mem_faceSet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite face family has exactly the original complex membership.

### Source text

Exact attempted Lean contract:@[simp] theorem mem_faceSet (K : PreAbstractSimplicialComplex V) (s : Finset V) :

    s ∈ faceSet K ↔ s ∈ K

**Theorem 1.6 (badFaces_empty_iff).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.badFaces_empty_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.badFaces_empty_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct u and v, the lower-face family is empty exactly when v is a ghost of K. A singleton v witnesses the converse direction whenever v occurs in any face.

### Source text

Exact attempted Lean contract:theorem badFaces_empty_iff (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) : badFaces K u v = ∅ ↔ Fresh v K

**Definition 1.7 (sequence).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.sequence`

*Formalization.* `D5/S3/Geometry/FiniteVertexDominationCollapse.sequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For distinct u and v under Extends, construct a genuine native Sequence from K to its literal deletion of v. Strong induction on the current lower-face count selects a maximum-cardinality lower face. The proof checks its sole strict coface, retained extension invariant, and exact decrement before recursing.

### Source text

Exact attempted Lean contract:def sequence (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) : Sequence K (deletion K v)

**Definition 1.8 (orderedLowers).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedLowers`

*Formalization.* `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedLowers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native sequence lower faces, in their actual removal order.

### Source text

Exact attempted Lean contract:def orderedLowers (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) : List (Finset V)

**Definition 1.9 (orderedPairs).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedPairs`

*Formalization.* `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedPairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete native sequence list of literal lower and upper faces, in removal order.

### Source text

Exact attempted Lean contract:def orderedPairs (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) : List (Finset V × Finset V)

**Theorem 1.10 (sequence_pair_spec).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.sequence_pair_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.sequence_pair_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every pair has a nonempty lower containing v, omitting u, and apex exactly u, so its upper is insert u lower. Labels are never replaced by a subtype.

### Source text

Exact attempted Lean contract:theorem sequence_pair_spec (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) (P : CollapsePair V)

    (hP : P ∈ (sequence K u v huv hExt).pairs) :

    P.lower.Nonempty ∧ v ∈ P.lower ∧ u ∉ P.lower ∧

      P.apex = u ∧ P.upper = insert u P.lower

**Theorem 1.11 (orderedLowers_nodup).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedLowers_nodup`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedLowers_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No original lower face occurs twice.

### Source text

Exact attempted Lean contract:theorem orderedLowers_nodup (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) :

    (orderedLowers K u v huv hExt).Nodup

**Theorem 1.12 (orderedLowers_mem).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedLowers_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedLowers_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original face of K containing v and omitting u occurs, and only such faces occur. The conditions refer to the ORIGINAL K, not to an assumed current matching.

### Source text

Exact attempted Lean contract:theorem orderedLowers_mem (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) (s : Finset V) :

    s ∈ orderedLowers K u v huv hExt ↔ s ∈ K ∧ v ∈ s ∧ u ∉ s

**Theorem 1.13 (orderedLowers_decreasing).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedLowers_decreasing`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedLowers_decreasing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each earlier and later lower face in the list, the later cardinality is at most the earlier cardinality; ties may be resolved by classical maximum choice.

### Source text

Exact attempted Lean contract:theorem orderedLowers_decreasing (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) :

    (orderedLowers K u v huv hExt).Pairwise (fun s t => t.card ≤ s.card)

**Theorem 1.14 (orderedPairs_eq).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedPairs_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedPairs_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete pair list is exactly the ordered lower list mapped to (s, insert u s).

### Source text

Exact attempted Lean contract:theorem orderedPairs_eq (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) :

    orderedPairs K u v huv hExt =

      (orderedLowers K u v huv hExt).map (fun s => (s, insert u s))

**Theorem 1.15 (orderedPairs_nodup).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedPairs_nodup`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedPairs_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No ordered lower-upper pair occurs twice, since its first coordinate determines its lower face.

### Source text

Exact attempted Lean contract:theorem orderedPairs_nodup (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) :

    (orderedPairs K u v huv hExt).Nodup

**Theorem 1.16 (orderedPairs_mem).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedPairs_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedPairs_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A pair (a,b) occurs exactly when a is an original face containing v and omitting u, and b is exactly insert u a.

### Source text

Exact attempted Lean contract:theorem orderedPairs_mem (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) (a b : Finset V) :

    (a, b) ∈ orderedPairs K u v huv hExt ↔

      a ∈ K ∧ v ∈ a ∧ u ∉ a ∧ b = insert u a

**Theorem 1.17 (sequence_length).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.sequence_length`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.sequence_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number of actual native free-pair steps equals the cardinality of the complete original lower-face family.

### Source text

Exact attempted Lean contract:theorem sequence_length (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) :

    (sequence K u v huv hExt).pairs.length = (badFaces K u v).card

**Theorem 1.18 (deletion_le_each_retained).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.deletion_le_each_retained`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.deletion_le_each_retained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every deletion face survives every retained stage, with no connectedness or dimension restriction.

### Source text

Exact attempted Lean contract:theorem deletion_le_each_retained (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) (P : CollapsePair V)

    (hP : P ∈ (sequence K u v huv hExt).pairs) : deletion K v ≤ P.retained

**Theorem 1.19 (frames_length).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.frames_length`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.frames_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frames list has n+1 entries for n original lower faces, including the final deletion frame.

### Source text

Exact attempted Lean contract:theorem frames_length (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) :

    (sequence K u v huv hExt).frames.length = (badFaces K u v).card + 1

**Theorem 1.20 (frames_initial).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.frames_initial`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.frames_initial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frame at index zero is literally K.

### Source text

Exact attempted Lean contract:theorem frames_initial (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) :

    (sequence K u v huv hExt).frames.getD 0 (deletion K v) = K

**Theorem 1.21 (frames_terminal).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.frames_terminal`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.frames_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frame at index n is literally deletion K v; the getD default is also explicitly that deletion.

### Source text

Exact attempted Lean contract:theorem frames_terminal (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) :

    (sequence K u v huv hExt).frames.getD (badFaces K u v).card (deletion K v) =

      deletion K v

**Theorem 1.22 (frame_mem_iff).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.frame_mem_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.frame_mem_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every valid index i including n, membership in the actual ith complex is original K membership with precisely the lower and upper faces of the first i native pairs removed. This is a replay statement about the evolving complexes.

### Source text

Exact attempted Lean contract:theorem frame_mem_iff (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) (i : Nat)

    (hi : i ≤ (badFaces K u v).card) (s : Finset V) :

    s ∈ (sequence K u v huv hExt).frames.getD i (deletion K v) ↔

      s ∈ K ∧ ∀ P ∈ (sequence K u v huv hExt).pairs.take i,

        s ≠ P.lower ∧ s ≠ P.upper

**Theorem 1.23 (face_count).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.face_count`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.face_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number of original nonempty faces is the number of deletion faces plus twice the complete lower-face count. Each genuine elementary pair removes exactly two different nonempty faces.

### Source text

Exact attempted Lean contract:theorem face_count (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) :

    (faceSet K).card = (faceSet (deletion K v)).card + 2 * (badFaces K u v).card

**Theorem 1.24 (ghost_pairs).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.ghost_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.ghost_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If v is a ghost, the chosen certificate has the empty pair list. No empty-lower augmented collapse and no point in an empty realization is manufactured.

### Source text

Exact attempted Lean contract:theorem ghost_pairs (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) (hf : Fresh v K) :

    (sequence K u v huv hExt).pairs = []

**Theorem 1.25 (ghost_frames).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.ghost_frames`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.ghost_frames` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the ghost case the complete frames list is [K], including its terminal frame. Empty complexes are allowed.

### Source text

Exact attempted Lean contract:theorem ghost_frames (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) (hf : Fresh v K) :

    (sequence K u v huv hExt).frames = [K]

**Definition 1.26 (sdr).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.sdr`

*Formalization.* `D5/S3/Geometry/FiniteVertexDominationCollapse.sdr` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use native Sequence.realize to obtain a strong deformation retraction with the literal original-coordinate inclusion from the entire deletion. No alternative model is substituted.

### Source text

Exact attempted Lean contract:def sdr (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) :

    RelativeSDR K (deletion K v) (deletion_le K v)

**Definition 1.27 (retraction).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.retraction`

*Formalization.* `D5/S3/Geometry/FiniteVertexDominationCollapse.retraction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The continuous retraction is the native finite composition of elementary-pair retractions.

### Source text

Exact attempted Lean contract:def retraction (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) : C(Space K, Space (deletion K v))

**Theorem 1.28 (retraction_inclusion).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.retraction_inclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.retraction_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every point of the full deletion realization, retraction after the literal realizationInclusion is exactly the point.

### Source text

Exact attempted Lean contract:theorem retraction_inclusion (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) (y : Space (deletion K v)) :

    retraction K u v huv hExt (realizationInclusion (deletion_le K v) y) = y

**Definition 1.29 (collapseHomotopy).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.collapseHomotopy`

*Formalization.* `D5/S3/Geometry/FiniteVertexDominationCollapse.collapseHomotopy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native relative homotopy runs from the actual identity to the literal inclusion after the sequence retraction. Its fixed set is the entire realized deletion.

### Source text

Exact attempted Lean contract:def collapseHomotopy (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) :

    (ContinuousMap.id (Space K)).HomotopyRel

      ((realizationInclusion (deletion_le K v)).comp (retraction K u v huv hExt))

      {x | x.val ∈ realization (deletion K v)}

**Theorem 1.30 (collapseHomotopy_fixed).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.collapseHomotopy_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.collapseHomotopy_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every time and every ambient point whose vector lies in the deletion realization, the homotopy fixes that point, including arbitrary retained faces and components.

### Source text

Exact attempted Lean contract:theorem collapseHomotopy_fixed (K : PreAbstractSimplicialComplex V) (u v : V)

    (huv : u ≠ v) (hExt : Extends K u v) (t : I) (x : Space K)

    (hx : x.val ∈ realization (deletion K v)) :

    collapseHomotopy K u v huv hExt (t, x) = x

**Theorem 1.31 (inclusion_coordinates).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.inclusion_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.inclusion_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inclusion has exactly the same coordinate vector on the original finite label type, including ghost coordinates.

### Source text

Exact attempted Lean contract:theorem inclusion_coordinates (K : PreAbstractSimplicialComplex V) (v : V)

    (y : Space (deletion K v)) :

    (realizationInclusion (deletion_le K v) y).val = y.val

**Theorem 1.32 (deletion_coordinate_zero).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.deletion_coordinate_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.deletion_coordinate_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A point of the literal deletion has zero coordinate at the original label v, which remains in V.

### Source text

Exact attempted Lean contract:theorem deletion_coordinate_zero (K : PreAbstractSimplicialComplex V) (v : V)

    (y : Space (deletion K v)) : y.val v = 0

**Theorem 1.33 (restricted_coordinate_zero).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.restricted_coordinate_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.restricted_coordinate_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every point of the actual restricted independence realization has coordinate zero at every label not satisfying the allowed-ground predicate, including excluded ghosts.

### Source text

Exact attempted Lean contract:theorem restricted_coordinate_zero (G : SimpleGraph V) (p : V → Prop)

    (x : Space (restricted G p)) (a : V) (ha : ¬ p a) : x.val a = 0

**Theorem 1.34 (graph_extends).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.graph_extends`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.graph_extends` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For actual restricted independence faces, if survivor u is allowed and every allowed neighbor of u is a neighbor of v, adjoining u to a face containing v preserves independence and allowed ground membership. No graph subtype is introduced.

### Source text

Exact attempted Lean contract:theorem graph_extends (G : SimpleGraph V) (p : V → Prop) (u v : V)

    (huv : u ≠ v) (hpu : p u)

    (hdom : ∀ a, p a → G.Adj u a → G.Adj v a) :

    Extends (restricted G p) u v

**Theorem 1.35 (restricted_deletion).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.restricted_deletion`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.restricted_deletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal deletion of v from restricted G p is exactly restricted G (a maps to p a and a not equal to v), on the SAME V.

### Source text

Exact attempted Lean contract:theorem restricted_deletion (G : SimpleGraph V) (p : V → Prop) (v : V) :

    deletion (restricted G p) v = restricted G (fun a => p a ∧ a ≠ v)

**Definition 1.36 (graphSequence).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.graphSequence`

*Formalization.* `D5/S3/Geometry/FiniteVertexDominationCollapse.graphSequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the proved extension lemma to construct the genuine original-label elementary certificate for the actual restricted independence complex, with literal deletion endpoint.

### Source text

Exact attempted Lean contract:def graphSequence (G : SimpleGraph V) (p : V → Prop) (u v : V)

    (huv : u ≠ v) (hpu : p u)

    (hdom : ∀ a, p a → G.Adj u a → G.Adj v a) :

    Sequence (restricted G p) (deletion (restricted G p) v)

**Definition 1.37 (graphRestrictedSequence).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.graphRestrictedSequence`

*Formalization.* `D5/S3/Geometry/FiniteVertexDominationCollapse.graphRestrictedSequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

View the same certificate at the exactly equal restriction-excluding-v endpoint, using equality transport only.

### Source text

Exact attempted Lean contract:def graphRestrictedSequence (G : SimpleGraph V) (p : V → Prop) (u v : V)

    (huv : u ≠ v) (hpu : p u)

    (hdom : ∀ a, p a → G.Adj u a → G.Adj v a) :

    Sequence (restricted G p) (restricted G (fun a => p a ∧ a ≠ v))

**Definition 1.38 (graphSDR).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.graphSDR`

*Formalization.* `D5/S3/Geometry/FiniteVertexDominationCollapse.graphSDR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Realize that actual graph certificate through the native relative API, fixing the whole deletion realization. This is not a claim of equality to the existing simultaneous coordinate fold.

### Source text

Exact attempted Lean contract:def graphSDR (G : SimpleGraph V) (p : V → Prop) (u v : V)

    (huv : u ≠ v) (hpu : p u)

    (hdom : ∀ a, p a → G.Adj u a → G.Adj v a) :

    RelativeSDR (restricted G p) (deletion (restricted G p) v)

      (deletion_le (restricted G p) v)

**Definition 1.39 (independenceSequence).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.independenceSequence`

*Formalization.* `D5/S3/Geometry/FiniteVertexDominationCollapse.independenceSequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the actual unrestricted independenceComplex of a simple graph, distinct u and v and open-neighborhood containment N(u) subset N(v) yield the original-label elementary deletion certificate.

### Source text

Exact attempted Lean contract:def independenceSequence (G : SimpleGraph V) (u v : V) (huv : u ≠ v)

    (hdom : G.neighborSet u ⊆ G.neighborSet v) :

    Sequence (independenceComplex G).toPreAbstractSimplicialComplex

      (deletion (independenceComplex G).toPreAbstractSimplicialComplex v)

**Theorem 1.40 (independence_deletion).**

Lean statement: `D5/S3/Geometry/FiniteVertexDominationCollapse.independence_deletion`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexDominationCollapse.independence_deletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Deleting v from the actual unrestricted independenceComplex is literally the same complex on V as restricting to labels different from v.

### Source text

Exact attempted Lean contract:theorem independence_deletion (G : SimpleGraph V) (v : V) :

    deletion (independenceComplex G).toPreAbstractSimplicialComplex v =

      restricted G (fun a => a ≠ v)

The existing coordinate transfer/foldHomotopy/foldEquiv and forestleafEquiv are not re-proved or renamed here. The new content is the actual finiteelementary Sequence with original-label pair data and literal deletion fixedness.The simultaneous fold need not equal the successive pairwise homotopy.No universal root-K supplier, unrestricted critical-face construction, spherequotient, disk collar, or attached-cell branch is discharged by this module.Kernel and axiom-closure checks, faithful Reg source observation, Scribe coverage,all native gates, remote checks, publication and cleanup remain integration work.

## References

- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.Extends`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.badFaces`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.badFaces_empty_iff`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.collapseHomotopy`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.collapseHomotopy_fixed`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.deletion_coordinate_zero`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.deletion_le_each_retained`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.faceSet`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.face_count`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.frame_mem_iff`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.frames_initial`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.frames_length`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.frames_terminal`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.ghost_frames`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.ghost_pairs`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.graphRestrictedSequence`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.graphSDR`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.graphSequence`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.graph_extends`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.inclusion_coordinates`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.independenceSequence`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.independence_deletion`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.mem_badFaces`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.mem_faceSet`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedLowers`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedLowers_decreasing`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedLowers_mem`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedLowers_nodup`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedPairs`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedPairs_eq`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedPairs_mem`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.orderedPairs_nodup`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.restricted_coordinate_zero`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.restricted_deletion`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.retraction`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.retraction_inclusion`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.sdr`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.sequence`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.sequence_length`
- Truth anchor: `D5/S3/Geometry/FiniteVertexDominationCollapse.sequence_pair_spec`
- Dependency: [D5/S3/Geometry/FiniteGraphVertexSubstitution](FiniteGraphVertexSubstitution.md)
- Dependency: [D5/S3/Geometry/FiniteRelativeSimplicialCollapse](FiniteRelativeSimplicialCollapse.md)
