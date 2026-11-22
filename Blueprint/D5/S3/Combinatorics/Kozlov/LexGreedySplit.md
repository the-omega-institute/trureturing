# Greedy placement minimizes upper-shadow cost

## Abstract

The exchange inequality reduces the minimization over component sizes to filling the components from left to right.

**Definition 1.1 (Greedy allocation).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.greedy`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexGreedySplit.greedy` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Give each component the lesser of its capacity and the available mass, then recurse on what remains.

**Definition 1.2 (Total component cost).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.cost`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexGreedySplit.cost` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Apply the component cost to each degree and its allocated size and sum over the paired lists.

**Definition 1.3 (Capacity constraints on allocations).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.Feasible`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexGreedySplit.Feasible` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Pair each component with one size and bound that size by its capacity.

**Definition 1.4 (Two-component cost comparison).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.Exchange`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexGreedySplit.Exchange` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

For an ordered pair, fill the first component as far as possible with the two masses. The resulting combined cost is at most the initial combined cost.

**Lemma 1.5 (Cost with no components).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.cost_nil`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexGreedySplit.cost_nil` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Pairing an empty degree list gives an empty sum.

**Lemma 1.6 (Remove the first cost term).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.cost_cons`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexGreedySplit.cost_cons` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The cost of paired nonempty lists is the first component cost plus the remaining cost.

**Lemma 1.7 (Greedy sizes respect all capacities).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.greedy_feasible`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexGreedySplit.greedy_feasible` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Each recursive head is bounded by its capacity and the tails have matched lengths.

**Lemma 1.8 (Total greedy allocation).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.greedy_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexGreedySplit.greedy_sum` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The assigned mass is the lesser of the requested mass and the total capacity.

**Lemma 1.9 (Absorb tail mass into the first component).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.absorb`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexGreedySplit.absorb` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Apply the exchange to move mass from successive tail positions into the first component until it is full or the tail is exhausted.

**Theorem 1.10 (Greedy allocation minimizes cost).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.greedy_le_of_exchange`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexGreedySplit.greedy_le_of_exchange` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Absorb as much tail mass as possible into the first component. Induct on the remaining list at its unchanged residual total.

**Definition 1.11 (Capacity in an integer degree).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.capZ`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexGreedySplit.capZ` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Use the binomial capacity at nonnegative degrees and zero at negative degrees.

**Definition 1.12 (Shadow cost in an integer degree).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.costZ`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexGreedySplit.costZ` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Use the recursive shadow count at nonnegative degrees and zero at negative degrees.

**Lemma 1.13 (Upper-shadow cost admits the block exchange).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.exchange_sig`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexGreedySplit.exchange_sig` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Apply the two numerical inequalities on either side of the first capacity. Negative degrees have zero admissible mass.

**Theorem 1.14 (Minimum shadow cost for ordered degrees).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.prop_greedy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexGreedySplit.prop_greedy` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Apply the greedy exchange principle to binomial capacities and upper-shadow costs with the degrees in nonincreasing order.

## References

- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.Exchange`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.Feasible`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.absorb`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.capZ`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.cost`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.costZ`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.cost_cons`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.cost_nil`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.exchange_sig`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.greedy`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.greedy_feasible`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.greedy_le_of_exchange`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.greedy_sum`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexGreedySplit.prop_greedy`
- Dependency: [D5/S3/Combinatorics/Kozlov/LexShadowSize](LexShadowSize.md)
