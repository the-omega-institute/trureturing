# State Invariant3

## Abstract

Symmetric matrix state invariants and padded driving laws.

Symmetric matrix state invariants and padded driving laws. The results below relate state invariant3 to the stochastic ellipsoid construction.

**Theorem 1.1 (reflection congr).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant3.reflection_congr`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant3.reflection_congr` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Submodule.reflection carries a HasOrthogonalProjection instance argument depending on the subspace, so rw on the subspace fails ("motive is not type correct"). subst does not.

**Theorem 1.2 (map sum xi).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant3.map_sum_xi`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant3.map_sum_xi` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

(B1) Σ_{j<k} ξ_j ~ N(0, k c² · Id).

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant3.map_sum_xi`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant3.reflection_congr`
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/StateInvariant2](StateInvariant2.md)
