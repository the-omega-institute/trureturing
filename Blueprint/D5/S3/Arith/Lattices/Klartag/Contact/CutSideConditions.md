# Cut Side Conditions

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate cut side conditions to the stochastic ellipsoid construction.

**Theorem 1.1 (card new Active le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/CutSideConditions.card_newActive_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/CutSideConditions.card_newActive_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

card (newActive j) ≤ c₃ on goodCut, for j < K: the newly frozen constraints at step j all sit in C_{j+1}.

**Definition 1.2 (rr At).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/CutSideConditions.rrAt`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Contact/CutSideConditions.rrAt` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

rr := 5/⁴√n — the ceiling the increment actually needs, and it decays. At n₁ it is 0.132; the resulting coefficient (1/2 + 2rr)/m² is 0.92 there and tends to 1/2.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/CutSideConditions.card_newActive_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/CutSideConditions.rrAt`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds](../Completion/GoodPathBounds.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower](../Drift/LogDetChainLower.md)
