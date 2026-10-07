# Tail Transport

## Abstract

Lattice tail bounds along the matrix walk.

Lattice tail bounds along the matrix walk. The results below relate tail transport to the stochastic ellipsoid construction.

**Theorem 1.1 (measure hit Set fst).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailTransport.measure_hitSet_fst`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailTransport.measure_hitSet_fst` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The transport. hitSet M N does not read the padding coordinates, so its probability under the padded measure is its probability under the chain's measure.

**Theorem 1.2 (hit tail y Of).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailTransport.hit_tail_yOf`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailTransport.hit_tail_yOf` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Proposition 4.1 at horizon t, about the chain's measure alone. Klartag's M₀ is the initial gap a₀ − (α·r)⁻² and q = 1, so the tail's argument is yOf a₀ t (α·r) — the profile's own argument, by TailAtStep.tail_arg_eq.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailTransport.hit_tail_yOf`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailTransport.measure_hitSet_fst`
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/Padding](../State/Padding.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/StepGlue](../State/StepGlue.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep](TailAtStep.md)
