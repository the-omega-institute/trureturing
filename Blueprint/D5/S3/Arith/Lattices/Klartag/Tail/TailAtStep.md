# Tail At Step

## Abstract

Lattice tail bounds along the matrix walk.

Lattice tail bounds along the matrix walk. The results below relate tail at step to the stochastic ellipsoid construction.

**Theorem 1.1 (tail arg eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep.tail_arg_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep.tail_arg_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Klartag's tail argument is yOf: with M₀ = a₀ − (α·r)⁻² (eq. 61 at the scaled radius) and q = 1, the argument of Φ in padded_tail_of_increments is yOf a₀ t (α·r).

**Theorem 1.2 (measure Real le of le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep.measureReal_le_of_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep.measureReal_le_of_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

An ℝ≥0∞ tail bound read as a real one.

**Theorem 1.3 (dom of tail2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep.dom_of_tail2`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep.dom_of_tail2` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Params.dom against c · profile. dom_of_tail rescaled; c ≥ 0 is all that is used.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep.dom_of_tail2`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep.measureReal_le_of_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep.tail_arg_eq`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2](../Completion/ParamsAdopted2.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ContactIntegrated](../Contact/ContactIntegrated.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainInputDom](../Walk/ChainInputDom.md)
