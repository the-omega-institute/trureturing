# The Operational Circular Two-Choice Parking Construction

## Abstract

A literal circular two-choice parking process, its vacancy and rotation laws, and explicit fixed-increment normalization and cutting operations.

**Definition 1.1 (Circular spots).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.Spot`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.Spot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

For n cars, the parking circle is ZMod(n+1). Addition is clockwise translation, so every scan and rotation is performed on exactly n+1 spots.

**Definition 1.2 (Positive clockwise increments).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.Increment`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.Increment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

An increment is a natural number k with hypotheses 1 <= k and k <= n. These inequalities make the second choice distinct from the anchor and cover every admissible second choice when n is positive.

**Definition 1.3 (Literal ordered choices).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.ActualChoice`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.ActualChoice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

Each car carries an anchor, a second spot, and evidence that the two spots are distinct. The field order is operational: the anchor is tried first and the second spot starts the fallback scan.

**Definition 1.4 (Actual preferences).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.ActualPreferences`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.ActualPreferences` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

An actual preference assigns one ordered ActualChoice to every car in Fin n. Nothing is quotiented by rotation or by the increment encoding.

**Definition 1.5 (One-choice anchors).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.Anchors`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.Anchors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The comparison input assigns one circular anchor to each of the n cars.

**Definition 1.6 (Per-car increment matrices).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.IncrementMatrix`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.IncrementMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

An increment matrix retains one positive clockwise increment for every car. It is the fixed parameter of the source-level anchor classes.

**Definition 1.7 (Anchor priority and second-origin scanning).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualStep`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

Given the occupied list and an ordered choice q, the step returns q.anchor when that spot is free. Only when the anchor is occupied does it inspect offsets 0 through n clockwise from q.second; offset zero therefore selects a free second choice before any later spot.

**Definition 1.8 (The comparison scanner).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.oneStep`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.oneStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The one-choice process uses the same bounded circular scanner, beginning at its single anchor with offset zero.

**Definition 1.9 (Parking from an occupied state).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.parkFrom`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.parkFrom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

For an arbitrary step function, cars are processed in list order. Each selected spot is prepended to the occupied state before the remaining cars run, while the returned list stays in car order.

**Definition 1.10 (Actual landing spots).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualSpots`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualSpots` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The literal ordered choices are listed in car order and run from an empty occupied state using actualStep.

**Definition 1.11 (One-choice landing spots).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.oneSpots`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.oneSpots` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The anchor vector is listed in car order and run from an empty occupied state using the comparison step.

**Theorem 1.12 (Every actual prefix is fresh).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actual_prefix_fresh`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actual_prefix_fresh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

For any list of actual choices with length at most n, the landing list has exactly the same length and has no duplicate spot. The proof first shows that the finite offset set contains a free position, characterizes its minimum, and then carries freshness through the recursive occupied state.

**Definition 1.13 (The actual vacancy).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualEmpty`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualEmpty` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

After all n actual choices run, the vacancy is the first circular spot absent from the landing list, scanning from zero.

**Definition 1.14 (The comparison vacancy).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.oneEmpty`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.oneEmpty` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The one-choice vacancy uses the identical complement selector on the one-choice landing list.

**Theorem 1.15 (The actual vacancy is unique).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actual_unique_vacancy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actual_unique_vacancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

For every spot x, x is absent from the n actual landings if and only if x equals actualEmpty. Prefix freshness gives n distinct elements of a type with n+1 elements; adjoining two different missing spots would exceed that cardinality.

**Theorem 1.16 (The comparison vacancy is unique).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.one_unique_vacancy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.one_unique_vacancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

For every spot x, x is absent from the one-choice landings if and only if x equals oneEmpty. The proof uses the same finite-complement argument as the literal run.

**Definition 1.17 (Rotate an ordered choice).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.rotateChoice`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.rotateChoice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

A common circular displacement is added to both the anchor and the second choice. Translation preserves their inequality.

**Definition 1.18 (Rotate an actual preference).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.rotateActual`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.rotateActual` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The same displacement is applied pointwise to every car's ordered choice.

**Definition 1.19 (Rotate a one-choice preference).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.rotateAnchors`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.rotateAnchors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The same displacement is applied pointwise to every one-choice anchor.

**Theorem 1.20 (Actual landings commute with rotation).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualSpots_rotate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualSpots_rotate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

Rotating all ordered choices rotates the complete landing list by the same amount. The proof transports membership through translated occupied lists, proves that the minimum free offset is unchanged, and inducts through parkFrom.

**Theorem 1.21 (The actual vacancy commutes with rotation).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualEmpty_rotate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualEmpty_rotate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The vacancy of the rotated actual input is the original vacancy plus the common displacement. Uniqueness identifies it from the rotated landing complement.

**Definition 1.22 (Read the positive clockwise increment).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualIncrement`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualIncrement` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The increment is the canonical value of second minus anchor in ZMod(n+1). Distinctness rules out zero, and the canonical value bound gives the upper bound n.

**Definition 1.23 (Rebuild an ordered choice).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.choiceOfAnchorIncrement`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.choiceOfAnchorIncrement` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

Given an anchor and k in 1 through n, the second choice is anchor+k. The strict canonical-value bound proves that this spot cannot equal the anchor.

**Definition 1.24 (Read every car's increment).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualIncrements`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualIncrements` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The increment decoder is applied pointwise, retaining the original per-car order.

**Definition 1.25 (Fixed increments and fixed actual vacancy).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.FixedActualFiber`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.FixedActualFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

This subtype contains exactly the literal actual preferences whose decoded increment matrix equals the supplied matrix and whose actual vacancy equals the supplied spot.

**Definition 1.26 (Fixed one-choice vacancy).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.OneChoiceFiber`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.OneChoiceFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

This subtype contains exactly the one-choice anchor vectors whose vacancy is the supplied spot.

**Definition 1.27 (Normalize an actual fiber).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.fixedFiberToOneChoice`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.fixedFiberToOneChoice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The map forgets neither a car nor its position. It extracts all anchors and rotates them by target vacancy minus their one-choice vacancy. The rotation law proves that the normalized anchor vector lies in OneChoiceFiber n j.

**Definition 1.28 (Reconstruct the literal fixed fiber).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.oneChoiceToFixedFiber`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.oneChoiceToFixedFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The inverse first rotates the anchors so that rebuilding with the fixed increment matrix has vacancy j, then rebuilds every ordered pair. The increment proof is pointwise, and actual vacancy equivariance proves membership in the target fiber.

**Definition 1.29 (The fixed-fiber orbit equivalence).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.fixedFiberOneChoiceEquiv`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.fixedFiberOneChoiceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The forward and reverse normalizations form an explicit equivalence. For the left inverse, subtraction recovers the increment of each original pair and rebuilding recovers both its anchor and second choice; the two compensating rotations cancel. For the right inverse, the vacancy equation makes the corresponding rotations cancel on every anchor.

**Definition 1.30 (Cut the circle at a vacancy).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.cutSpot`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.cutSpot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The linear coordinate of x relative to vacancy j is the canonical natural value of x-j, ranging from zero through n.

**Definition 1.31 (Restore a cut coordinate).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.uncutSpot`

*Formalization.* `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.uncutSpot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

A natural linear coordinate p is placed back on the circle as j+p.

**Theorem 1.32 (Cutting identifies the two scanners).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.firstFree_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.firstFree_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

Assume the occupied list has no duplicates, its length is at most n, j is unoccupied, and the circular scanner does not land at j. Cutting at j sends the circular first-free result to the supplier's linear parkStep. The proof rotates j to zero, orders every skipped offset before the cut, and applies the supplier's vacancy and skipped-position specification.

**Theorem 1.33 (The reverse scanner does not cross the vacancy).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.firstFree_ne_vacancy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.firstFree_ne_vacancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

Let 1 <= p <= q <= n and suppose uncutSpot j q is free. The first circular free spot from uncutSpot j p cannot be j: the free offset q-p occurs strictly before the offset n+1-p that returns to the cut.

**Theorem 1.34 (Cutting simulates the complete one-choice run).**

Lean statement: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.cut_run`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.cut_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

Assume a duplicate-free occupied state, enough remaining capacity, an unoccupied cut j, and a future one-choice run that never lands at j. Then supplier parkFrom on the cut occupied list and cut anchors equals the cut circular landing list. The same induction also proves that every input anchor differs from j.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.ActualChoice`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.ActualPreferences`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.Anchors`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.FixedActualFiber`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.Increment`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.IncrementMatrix`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.OneChoiceFiber`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.Spot`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualEmpty`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualEmpty_rotate`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualIncrement`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualIncrements`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualSpots`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualSpots_rotate`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actualStep`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actual_prefix_fresh`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.actual_unique_vacancy`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.choiceOfAnchorIncrement`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.cutSpot`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.cut_run`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.firstFree_cut`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.firstFree_ne_vacancy`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.fixedFiberOneChoiceEquiv`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.fixedFiberToOneChoice`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.oneChoiceToFixedFiber`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.oneEmpty`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.oneSpots`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.oneStep`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.one_unique_vacancy`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.parkFrom`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.rotateActual`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.rotateAnchors`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.rotateChoice`
- Truth anchor: `D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.uncutSpot`
- Dependency: [D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata](../../S0/Certificates/Combinatorics/UnitIntervalParkingFoata.md)
