# Lift Bound

## Abstract

Construction A lattices, covolumes and ellipsoid transfer.

Construction A lattices, covolumes and ellipsoid transfer. The results below relate lift bound to the stochastic ellipsoid construction.

**Theorem 1.1 (sum card new Active).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/LiftBound.sum_card_newActive`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/LiftBound.sum_card_newActive` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The freezes partition the active set. A step never breaks an already-active constraint (Chain.newActive_disjoint), so the counts add.

**Theorem 1.2 (norm lift Sum le card).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/LiftBound.norm_liftSum_le_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/LiftBound.norm_liftSum_le_card` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The accumulated lift, with no per-step count and no dim.

**Theorem 1.3 (state Bounds of chain count).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/LiftBound.stateBounds_of_chain_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/LiftBound.stateBounds_of_chain_count` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The per-path core with the accumulated lift bound (StateInvariantGlue.stateBounds_of_chain takes the per-step one and pays a factor dim).

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/LiftBound.norm_liftSum_le_card`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/LiftBound.stateBounds_of_chain_count`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/LiftBound.sum_card_newActive`
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/StateInvariant3](../State/StateInvariant3.md)
