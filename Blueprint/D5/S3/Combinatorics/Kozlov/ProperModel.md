# The literal proper f-vectors and their repeated sums

## Abstract

A proper family is a downset containing the empty face and every singleton. Its cardinalities by face size give the vectors in the equal-shift sumset.

**Definition 1.1 (Families of faces).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.Family`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ProperModel.Family` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

A family on the ground set of size n is a finite set of subsets of Fin n, the carrier used in Spine/Complexes.lean, line 38.

**Definition 1.2 (The face-size coordinate space).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.FVector`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ProperModel.FVector` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

An f-vector assigns a natural number to each of the n+1 face sizes, starting at zero. See the codomain in Counting/Stats.lean, line 45.

**Definition 1.3 (Proper downsets).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.IsComplex`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ProperModel.IsComplex` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Every subset of a face is a face. The family contains the empty face and the singleton of every ground element. See Spine/Complexes.lean, line 44.

**Definition 1.4 (Face counts in one degree).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.fEntry`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ProperModel.fEntry` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Filter the family to faces of size k and take its cardinality. In degree zero the empty face contributes one. See Spine/Complexes.lean, line 57.

**Definition 1.5 (Face counts in all degrees).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.fVector`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ProperModel.fVector` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The coordinate indexed by k counts the faces of size k. See Counting/Stats.lean, line 45.

**Definition 1.6 (The proper f-vector set).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.SnF`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ProperModel.SnF` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Take the image of all proper downsets under the f-vector map. See Counting/Duality.lean, lines 309–314.

**Definition 1.7 (Repeated summation).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.sumTuple`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ProperModel.sumTuple` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Sum all entries of a tuple componentwise. The indexing by Fin r permits equal summands. This is Part II's summation map at zero shifts, equation (4).

**Definition 1.8 (The literal equal-shift sumset).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.properSumset`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ProperModel.properSumset` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Take the image of the coordinate sum over tuples whose entries all belong to the proper f-vector set. Distinct tuples with the same total contribute one vector. See Counting/Proper.lean, line 509, at zero shifts and Part II, Theorem 41.

**Definition 1.9 (Largest occupied degree).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.top`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ProperModel.top` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Take the largest degree having a positive count, with value minus one if all counts vanish. See Counting/Stats.lean, lines 105–108.

**Definition 1.10 (First missing degree).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.indeg`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ProperModel.indeg` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Take the least degree whose count is below the full binomial layer. Use n+1 when no degree is deficient. See Counting/Stats.lean, lines 112–115.

**Definition 1.11 (Adjacent degree separation).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.Chained`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ProperModel.Chained` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

In each adjacent pair of vectors the last occupied degree of the preceding vector is strictly below the first missing degree of its successor. This is the equal-shift case of Counting/Chaining.lean, line 361.

**Theorem 1.12 (The top lies in the face window).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.top_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ProperModel.top_le` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

All occupied degrees lie between zero and n. The empty support sentinel is also at most n. See Counting/Stats.lean, line 122.

**Theorem 1.13 (Vanishing above a threshold bounds the top).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.top_lt_of_vanish`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ProperModel.top_lt_of_vanish` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

If all degrees from k onward vanish, any maximum occupied degree lies below k. Empty support uses the sentinel.

**Theorem 1.14 (The minimum is deficient unless it is the sentinel).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.indeg_eq_sentinel_or_missing`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ProperModel.indeg_eq_sentinel_or_missing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

A nonempty set of deficient degrees supplies its minimum. When the set is empty the designated value is n+1.

**Definition 1.15 (A uniform layer of faces).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.layer`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ProperModel.layer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

This is the set of all k-element subsets of the n-element ground set.

**Theorem 1.16 (Membership in the full layer).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.mem_layer`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ProperModel.mem_layer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

A ground-set subset belongs to the selected layer exactly when its cardinality is the degree.

**Theorem 1.17 (The binomial layer capacity).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.card_layer`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ProperModel.card_layer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Counting k-subsets of an n-element set gives the binomial coefficient.

**Definition 1.18 (Missing faces of one size).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.missing`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ProperModel.missing` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Remove the faces of the family from the full layer of the selected size.

**Theorem 1.19 (Present and missing faces partition a layer).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.fEntry_add_card_missing`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ProperModel.fEntry_add_card_missing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The filter of present k-faces and the missing k-faces are disjoint and exhaust the uniform layer.

**Theorem 1.20 (Missing layers are closed under upper shadows).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.missing_upShadow_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ProperModel.missing_upShadow_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

If a missing face is contained in a face one element larger, downwards closure forces the larger face to be missing.

**Theorem 1.21 (The empty face is present).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.missing_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ProperModel.missing_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

In degree zero the layer consists only of the empty face, which properness requires.

**Theorem 1.22 (Every singleton is present).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.missing_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ProperModel.missing_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Every degree-one face is a singleton and belongs to a proper downset.

**Definition 1.23 (Reconstruction from missing layers).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.fromMissing`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ProperModel.fromMissing` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Keep every subset whose own cardinality layer does not mark it as missing.

**Theorem 1.24 (Reconstructed families are proper downsets).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.fromMissing_isComplex`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ProperModel.fromMissing_isComplex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Repeatedly add one element to propagate missing status upwards through the shadow inclusions. The vanishing missing layers in degrees zero and one supply the two properness conditions.

**Theorem 1.25 (Recovery of the missing layer).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ProperModel.missing_fromMissing`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ProperModel.missing_fromMissing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

If every prescribed missing family belongs to its degree layer, reconstructing and then taking missing faces recovers it.

## References

- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.Chained`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.FVector`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.Family`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.IsComplex`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.SnF`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.card_layer`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.fEntry`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.fEntry_add_card_missing`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.fVector`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.fromMissing`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.fromMissing_isComplex`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.indeg`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.indeg_eq_sentinel_or_missing`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.layer`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.mem_layer`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.missing`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.missing_fromMissing`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.missing_one`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.missing_upShadow_subset`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.missing_zero`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.properSumset`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.sumTuple`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.top`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.top_le`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ProperModel.top_lt_of_vanish`
