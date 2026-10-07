# Tail At Step RW2

## Abstract

Lattice tail bounds along the matrix walk.

Lattice tail bounds along the matrix walk. The results below relate tail at step rw2 to the stochastic ellipsoid construction.

**Theorem 1.1 (tail at step RW2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepRW2.tail_at_stepRW2`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepRW2.tail_at_stepRW2` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Proposition 4.1 at step k, in the profile's language. From the Φ form of the padded tail at horizon k·h to the profileAt form ContactIntegrated.integrated_count_le consumes.

**Definition 1.2 (prof Step RW2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepRW2.profStepRW2`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepRW2.profStepRW2` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The per-step profile: Proposition 4.1's value at step time k·h, zero at k = 0.

**Theorem 1.3 (tail of steps RW2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepRW2.tail_of_stepsRW2`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepRW2.tail_of_stepsRW2` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

ChainRaw2RW2.tail, discharged. The per-step tail of §1, summed by §2 and §3, at the adopted e = 7 discretisation.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepRW2.profStepRW2`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepRW2.tail_at_stepRW2`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepRW2.tail_of_stepsRW2`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/WindowR2](../Completion/WindowR2.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep](TailAtStep.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainInputDom](../Walk/ChainInputDom.md)
