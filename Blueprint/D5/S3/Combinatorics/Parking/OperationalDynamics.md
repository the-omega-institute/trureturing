# Operational Dynamics of Circular Two-Choice Parking

## Abstract

The literal ordered circular process, its bounded scanner, unique vacancy, and rotation laws.

**Definition 1.1 (Circular spots).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.Spot`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.Spot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

For n cars, the parking circle is ZMod(n+1). Addition is clockwise translation, so every scan and rotation is performed on exactly n+1 spots.

**Definition 1.2 (Positive clockwise increments).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.Increment`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.Increment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

An increment is a natural number k with hypotheses 1 <= k and k <= n. These inequalities make the second choice distinct from the anchor and cover every admissible second choice when n is positive.

**Definition 1.3 (Literal ordered choices).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.ActualChoice`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.ActualChoice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

Each car carries an anchor, a second spot, and evidence that the two spots are distinct. The field order is operational: the anchor is tried first and the second spot starts the fallback scan.

**Definition 1.4 (Actual preferences).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.ActualPreferences`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.ActualPreferences` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

An actual preference assigns one ordered ActualChoice to every car in Fin n. Nothing is quotiented by rotation or by the increment encoding.

**Definition 1.5 (One-choice anchors).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.Anchors`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.Anchors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The comparison input assigns one circular anchor to each of the n cars.

**Definition 1.6 (Per-car increment matrices).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.IncrementMatrix`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.IncrementMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

An increment matrix retains one positive clockwise increment for every car. It is the fixed parameter of the source-level anchor classes.

**Definition 1.7 (Anchor priority and second-origin scanning).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.actualStep`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.actualStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

Given the occupied list and an ordered choice q, the step returns q.anchor when that spot is free. Only when the anchor is occupied does it inspect offsets 0 through n clockwise from q.second; offset zero therefore selects a free second choice before any later spot.

**Definition 1.8 (The comparison scanner).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.oneStep`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.oneStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The one-choice process uses the same bounded circular scanner, beginning at its single anchor with offset zero.

**Definition 1.9 (Parking from an occupied state).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.parkFrom`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.parkFrom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

For an arbitrary step function, cars are processed in list order. Each selected spot is prepended to the occupied state before the remaining cars run, while the returned list stays in car order.

**Definition 1.10 (Actual landing spots).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.actualSpots`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.actualSpots` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The literal ordered choices are listed in car order and run from an empty occupied state using actualStep.

**Definition 1.11 (One-choice landing spots).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.oneSpots`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.oneSpots` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The anchor vector is listed in car order and run from an empty occupied state using the comparison step.

**Theorem 1.12 (Every actual prefix is fresh).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.actual_prefix_fresh`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/OperationalDynamics.actual_prefix_fresh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

For any list of actual choices with length at most n, the landing list has exactly the same length and has no duplicate spot. The proof first shows that the finite offset set contains a free position, characterizes its minimum, and then carries freshness through the recursive occupied state.

**Definition 1.13 (The actual vacancy).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.actualEmpty`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.actualEmpty` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

After all n actual choices run, the vacancy is the first circular spot absent from the landing list, scanning from zero.

**Definition 1.14 (The comparison vacancy).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.oneEmpty`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.oneEmpty` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The one-choice vacancy uses the identical complement selector on the one-choice landing list.

**Theorem 1.15 (The actual vacancy is unique).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.actual_unique_vacancy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/OperationalDynamics.actual_unique_vacancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

For every spot x, x is absent from the n actual landings if and only if x equals actualEmpty. Prefix freshness gives n distinct elements of a type with n+1 elements; adjoining two different missing spots would exceed that cardinality.

**Theorem 1.16 (The comparison vacancy is unique).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.one_unique_vacancy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/OperationalDynamics.one_unique_vacancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

For every spot x, x is absent from the one-choice landings if and only if x equals oneEmpty. The proof uses the same finite-complement argument as the literal run.

**Definition 1.17 (Rotate an ordered choice).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.rotateChoice`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.rotateChoice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

A common circular displacement is added to both the anchor and the second choice. Translation preserves their inequality.

**Definition 1.18 (Rotate an actual preference).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.rotateActual`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.rotateActual` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The same displacement is applied pointwise to every car's ordered choice.

**Definition 1.19 (Rotate a one-choice preference).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.rotateAnchors`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.rotateAnchors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The same displacement is applied pointwise to every one-choice anchor.

**Theorem 1.20 (Actual landings commute with rotation).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.actualSpots_rotate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/OperationalDynamics.actualSpots_rotate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

Rotating all ordered choices rotates the complete landing list by the same amount. The proof transports membership through translated occupied lists, proves that the minimum free offset is unchanged, and inducts through parkFrom.

**Theorem 1.21 (The actual vacancy commutes with rotation).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.actualEmpty_rotate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/OperationalDynamics.actualEmpty_rotate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The vacancy of the rotated actual input is the original vacancy plus the common displacement. Uniqueness identifies it from the rotated landing complement.

**Definition 1.22 (Circular offset enumeration).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.orbitEquiv`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.orbitEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

For each starting spot, offsets in Fin(n+1) are identified bijectively with all circular spots in clockwise order.

**Definition 1.23 (Available offsets).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.freeOffsets`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.freeOffsets` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The available-offset finset retains exactly those bounded offsets whose circular images are absent from the occupied finset.

**Definition 1.24 (Least available offset).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFreeOffset`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFreeOffset` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The scanner selects the minimum available offset, with zero used only in the unreachable empty-set branch later excluded by the capacity theorem.

**Definition 1.25 (Bounded first-free scanner).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFree`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The sole scanner inspects offsets zero through n from its start and returns the spot at the least free offset.

**Theorem 1.26 (A free start is selected at offset zero).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFree_of_not_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFree_of_not_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

When the scan origin is absent from the occupied list, offset zero is available and minimal, so the bounded scanner returns that origin exactly.

**Theorem 1.27 (The selected spot is fresh).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFree_fresh`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFree_fresh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

For a duplicate-free occupied list of length at most n, the bounded scan returns a spot not already occupied.

**Theorem 1.28 (Earlier offsets are occupied).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFree_skipped`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFree_skipped` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

Every offset strictly below the selected first-free offset maps to a spot already present in the occupied list.

**Definition 1.29 (Rotate an occupied state).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.rotateList`

*Formalization.* `D5/S3/Combinatorics/Parking/OperationalDynamics.rotateList` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

A common circular displacement is added to every occupied spot while preserving the list order used by the operational recursion.

**Theorem 1.30 (Rotation preserves occupied membership).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.mem_rotateList_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/OperationalDynamics.mem_rotateList_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

A translated spot belongs to the translated occupied list exactly when its untranslated spot belongs to the original list.

**Theorem 1.31 (The scanner commutes with rotation).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFree_rotate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFree_rotate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

Translating the occupied state and scan origin leaves the chosen offset unchanged and translates the selected spot by the same displacement.

**Theorem 1.32 (The comparison vacancy commutes with rotation).**

Lean statement: `D5/S3/Combinatorics/Parking/OperationalDynamics.oneEmpty_rotate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/OperationalDynamics.oneEmpty_rotate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The unique empty spot of a translated one-choice run is the original comparison vacancy plus the common displacement.

## References

- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.ActualChoice`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.ActualPreferences`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.Anchors`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.Increment`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.IncrementMatrix`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.Spot`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.actualEmpty`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.actualEmpty_rotate`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.actualSpots`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.actualSpots_rotate`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.actualStep`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.actual_prefix_fresh`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.actual_unique_vacancy`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFree`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFreeOffset`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFree_fresh`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFree_of_not_mem`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFree_rotate`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.firstFree_skipped`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.freeOffsets`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.mem_rotateList_iff`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.oneEmpty`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.oneEmpty_rotate`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.oneSpots`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.oneStep`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.one_unique_vacancy`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.orbitEquiv`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.parkFrom`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.rotateActual`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.rotateAnchors`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.rotateChoice`
- Truth anchor: `D5/S3/Combinatorics/Parking/OperationalDynamics.rotateList`
- Dependency: [D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata](../../../S0/Certificates/Combinatorics/UnitIntervalParkingFoata.md)
