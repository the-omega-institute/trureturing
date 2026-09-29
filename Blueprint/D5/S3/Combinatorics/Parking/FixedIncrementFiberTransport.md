# Fixed-Increment Fiber Transport

## Abstract

Positive-increment encoding and explicit vacancy-normalized transport between actual and one-choice fibers.

**Definition 1.1 (Read the positive clockwise increment).**

Lean statement: `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.actualIncrement`

*Formalization.* `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.actualIncrement` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The increment is the canonical value of second minus anchor in ZMod(n+1). Distinctness rules out zero, and the canonical value bound gives the upper bound n.

**Definition 1.2 (Rebuild an ordered choice).**

Lean statement: `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.choiceOfAnchorIncrement`

*Formalization.* `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.choiceOfAnchorIncrement` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

Given an anchor and k in 1 through n, the second choice is anchor+k. The strict canonical-value bound proves that this spot cannot equal the anchor.

**Definition 1.3 (Read every car's increment).**

Lean statement: `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.actualIncrements`

*Formalization.* `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.actualIncrements` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The increment decoder is applied pointwise, retaining the original per-car order.

**Definition 1.4 (Fixed increments and fixed actual vacancy).**

Lean statement: `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.FixedActualFiber`

*Formalization.* `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.FixedActualFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

This subtype contains exactly the literal actual preferences whose decoded increment matrix equals the supplied matrix and whose actual vacancy equals the supplied spot.

**Definition 1.5 (Fixed one-choice vacancy).**

Lean statement: `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.OneChoiceFiber`

*Formalization.* `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.OneChoiceFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

This subtype contains exactly the one-choice anchor vectors whose vacancy is the supplied spot.

**Definition 1.6 (Normalize an actual fiber).**

Lean statement: `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.fixedFiberToOneChoice`

*Formalization.* `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.fixedFiberToOneChoice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The map forgets neither a car nor its position. It extracts all anchors and rotates them by target vacancy minus their one-choice vacancy. The rotation law proves that the normalized anchor vector lies in OneChoiceFiber n j.

**Definition 1.7 (Reconstruct the literal fixed fiber).**

Lean statement: `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.oneChoiceToFixedFiber`

*Formalization.* `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.oneChoiceToFixedFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The inverse first rotates the anchors so that rebuilding with the fixed increment matrix has vacancy j, then rebuilds every ordered pair. The increment proof is pointwise, and actual vacancy equivariance proves membership in the target fiber.

**Definition 1.8 (The fixed-fiber orbit equivalence).**

Lean statement: `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.fixedFiberOneChoiceEquiv`

*Formalization.* `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.fixedFiberOneChoiceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The forward and reverse normalizations form an explicit equivalence. For the left inverse, subtraction recovers the increment of each original pair and rebuilding recovers both its anchor and second choice; the two compensating rotations cancel. For the right inverse, the vacancy equation makes the corresponding rotations cancel on every anchor.

## References

- Truth anchor: `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.FixedActualFiber`
- Truth anchor: `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.OneChoiceFiber`
- Truth anchor: `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.actualIncrement`
- Truth anchor: `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.actualIncrements`
- Truth anchor: `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.choiceOfAnchorIncrement`
- Truth anchor: `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.fixedFiberOneChoiceEquiv`
- Truth anchor: `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.fixedFiberToOneChoice`
- Truth anchor: `D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.oneChoiceToFixedFiber`
- Dependency: [D5/S3/Combinatorics/Parking/OperationalDynamics](OperationalDynamics.md)
