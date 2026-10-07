# Levy Maximal

## Abstract

Gaussian moments, independence and operator norm tails.

Gaussian moments, independence and operator norm tails. The results below relate levy maximal to the stochastic ellipsoid construction.

**Theorem 1.1 (measure le two mul of reflection).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.measure_le_two_mul_of_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.measure_le_two_mul_of_reflection` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The reflection step. If R preserves P, fixes E, and pulls F back to G, and F ∪ G covers E, then P E ≤ 2 · P (E ∩ F). This is the entire content of the reflection principle, with no probability theory in it.

**Theorem 1.2 (measure le two mul of reflection family).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.measure_le_two_mul_of_reflection_family`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.measure_le_two_mul_of_reflection_family` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

First-passage decomposition plus reflection. E k is {τ = k}, a disjoint family; R k is the reflection attached to time k; target absorbs every E k ∩ F k. Then the hitting event has measure at most 2 · P target. Both hlevy (here) and hsym (Padding.lean) are instances of this one lemma.

**Definition 1.3 (flip Coords).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.flipCoords`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.flipCoords` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Flip the sign of the coordinates satisfying p.

**Theorem 1.4 (measure Preserving flip Coords).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.measurePreserving_flipCoords`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.measurePreserving_flipCoords` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A product of symmetric laws is invariant under flipping any set of coordinates.

**Definition 1.5 (walk Sum).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.walkSum`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.walkSum` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

walkSum k ω = ∑_{i < k} ω i, the partial sums of the coordinate increments.

**Theorem 1.6 (walk Sum total).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.walkSum_total`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.walkSum_total` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

walkSum N is the total sum.

**Definition 1.7 (flip Tail).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.flipTail`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.flipTail` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The reflection attached to time k: flip every increment of index ≥ k.

**Theorem 1.8 (walk Sum flip Tail le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.walkSum_flipTail_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.walkSum_flipTail_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

flipTail k does not move the partial sums up to time k.

**Theorem 1.9 (walk Sum flip Tail total).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.walkSum_flipTail_total`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.walkSum_flipTail_total` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

flipTail k reflects the increment from k to N.

**Theorem 1.10 (tail flip Tail).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.tail_flipTail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.tail_flipTail` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The reflected tail increment is the negative of the original.

**Definition 1.11 (first Hit).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.firstHit`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.firstHit` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

{τ = k}: the walk first reaches r at time k.

**Theorem 1.12 (bi Union first Idx).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.biUnion_firstIdx`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.biUnion_firstIdx` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

First-passage decomposition, for an arbitrary family of predicates: the events "p first holds at time k", k ≤ N, partition {∃ k ≤ N, p k x}. Used for both hlevy (here) and hsym (Padding.lean).

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.biUnion_firstIdx`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.firstHit`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.flipCoords`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.flipTail`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.measurePreserving_flipCoords`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.measure_le_two_mul_of_reflection`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.measure_le_two_mul_of_reflection_family`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.tail_flipTail`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.walkSum`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.walkSum_flipTail_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.walkSum_flipTail_total`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.walkSum_total`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail](../Tail/PaddedTail.md)
