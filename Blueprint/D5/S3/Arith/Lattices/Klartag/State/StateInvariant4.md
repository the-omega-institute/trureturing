# State Invariant4

## Abstract

Symmetric matrix state invariants and padded driving laws.

Symmetric matrix state invariants and padded driving laws. The results below relate state invariant4 to the stochastic ellipsoid construction.

**Theorem 1.1 (measurable refl Step).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.measurable_reflStep`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.measurable_reflStep` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The reflected increment is measurable.

**Definition 1.2 (refl Sum Past).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.reflSumPast`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.reflSumPast` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The partial sum of reflected increments, read as a function of the past sequence.

**Theorem 1.3 (map refl Step).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.map_reflStep`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.map_reflStep` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The per-step law of the reflected increment: the frozen rotation preserves N(0, c²·Id).

**Theorem 1.4 (indep Fun sum refl Step).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.indepFun_sum_reflStep`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.indepFun_sum_reflStep` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

…and it stays independent of the partial sum before it. The partial sum is reflSumPast ∘ past, a measurable function of the past, so IndepFun.comp applies.

**Definition 1.5 (count Good).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.countGood`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.countGood` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The count event. Route M's lift bound is |C_k| · η; this is the event that buys |C_N|, and Chain.chain_snd_mono makes the terminal count dominate every earlier one.

**Theorem 1.6 (card le of count Good).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.card_le_of_countGood`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.card_le_of_countGood` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The contact set only grows, so one bound at N bounds every k ≤ N.

**Theorem 1.7 (measure Real compl count Good le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.measureReal_compl_countGood_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.measureReal_compl_countGood_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Markov. The count event fails with probability at most (∫ |C_N|)/c₃.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.card_le_of_countGood`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.countGood`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.indepFun_sum_reflStep`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.map_reflStep`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.measurable_reflStep`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.measureReal_compl_countGood_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.reflSumPast`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ContactIntegrated](../Contact/ContactIntegrated.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/ReflStep2](../Drift/ReflStep2.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainDataInst](../Walk/ChainDataInst.md)
