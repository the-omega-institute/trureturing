# Padding Map

## Abstract

Symmetric matrix state invariants and padded driving laws.

Symmetric matrix state invariants and padded driving laws. The results below relate padding map to the stochastic ellipsoid construction.

**Theorem 1.1 (norm pad Unit).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/PaddingMap.norm_padUnit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/PaddingMap.norm_padUnit` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The padding direction is a unit vector. w is the projected drift direction π_k v_k, e a fresh direction orthogonal to it; √(1 − ‖w‖²) is Klartag's padding amplitude, and the Pythagorean identity is exactly the statement that the padded conditional variance is h.

**Theorem 1.2 (map scaled inner).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/PaddingMap.map_scaled_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/PaddingMap.map_scaled_inner` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The padded increment's law at a *fixed* unit direction: N(0, r²).

**Theorem 1.3 (map frozen).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/PaddingMap.map_frozen`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/PaddingMap.map_frozen` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The frozen law. Increments.map_frozen_isometry with the isometry hypothesis weakened to constancy of the fibre law.

**Theorem 1.4 (indep Fun frozen).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/PaddingMap.indepFun_frozen`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/PaddingMap.indepFun_frozen` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The frozen independence. The padded increment is independent of the past it was read against.

**Theorem 1.5 (map pi of step Indep).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/PaddingMap.map_pi_of_stepIndep`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/PaddingMap.map_pi_of_stepIndep` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hincl at every horizon. The induction is on the horizon: the pair (X k, (X i)_{i<k}) has law ν ⊗ πν by independence, and Fin.insertNthEquiv at Fin.last k turns ν ⊗ πν into π ν on Fin (k+1).

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/PaddingMap.indepFun_frozen`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/PaddingMap.map_frozen`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/PaddingMap.map_pi_of_stepIndep`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/PaddingMap.map_scaled_inner`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/PaddingMap.norm_padUnit`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailTransport](../Tail/TailTransport.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/Increments](../Walk/Increments.md)
