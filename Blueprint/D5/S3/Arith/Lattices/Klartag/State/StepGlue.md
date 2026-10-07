# Step Glue

## Abstract

Symmetric matrix state invariants and padded driving laws.

Symmetric matrix state invariants and padded driving laws. The results below relate step glue to the stochastic ellipsoid construction.

**Theorem 1.1 (std Gaussian coord law).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StepGlue.stdGaussian_coord_law`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StepGlue.stdGaussian_coord_law` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Each coordinate of a standard Gaussian on EuclideanSpace ℝ ι is N(0,1).

**Theorem 1.2 (coord law).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StepGlue.coord_law`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StepGlue.coord_law` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A random variable with the standard Gaussian law has N(0,1) coordinates.

**Theorem 1.3 (coord indep).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StepGlue.coord_indep`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StepGlue.coord_indep` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

…and independent coordinates.

**Theorem 1.4 (coord law smul).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StepGlue.coord_law_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StepGlue.coord_law_smul` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain's increment is r • ξ with ξ standard, so its coordinates are N(0, r²).

**Theorem 1.5 (coord indep smul).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StepGlue.coord_indep_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StepGlue.coord_indep_smul` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

…and they stay independent.

**Theorem 1.6 (measure Real compl chain Good le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StepGlue.measureReal_compl_chainGood_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StepGlue.measureReal_compl_chainGood_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The failure probability of the full good event, the two costs added.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StepGlue.coord_indep`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StepGlue.coord_indep_smul`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StepGlue.coord_law`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StepGlue.coord_law_smul`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StepGlue.measureReal_compl_chainGood_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StepGlue.stdGaussian_coord_law`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/StepInputs](../Walk/StepInputs.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2](../Walk/StepInputs2.md)
