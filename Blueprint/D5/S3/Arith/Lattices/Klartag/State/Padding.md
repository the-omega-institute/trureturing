# Padding

## Abstract

Symmetric matrix state invariants and padded driving laws.

Symmetric matrix state invariants and padded driving laws. The results below relate padding to the stochastic ellipsoid construction.

**Definition 1.1 (pad Sum).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/Padding.padSum`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/Padding.padSum` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The accumulated padding P_k = ∑_{i<k} c_i(ω₁)·η_i.

**Definition 1.2 (padded Proc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/Padding.paddedProc`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/Padding.paddedProc` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The padded process S̃_k = (M_k − M₀) + P_k.

**Definition 1.3 (neg Pad).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/Padding.negPad`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/Padding.negPad` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Negate every padding coordinate, leaving the chain alone.

**Theorem 1.4 (pad Sum neg Pad).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/Padding.padSum_negPad`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/Padding.padSum_negPad` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The accumulated padding is odd in the padding coordinates.

**Theorem 1.5 (measure Preserving neg Pad).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/Padding.measurePreserving_negPad`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/Padding.measurePreserving_negPad` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

negPad is measure preserving when the padding law is symmetric.

**Definition 1.6 (hit Set).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/Padding.hitSet`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/Padding.hitSet` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

{∃ k ≤ N, M_k ≤ 0} — the chain reaches the boundary. Depends only on the chain.

**Definition 1.7 (lev Set).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/Padding.levSet`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/Padding.levSet` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

{∃ k ≤ N, S̃_k ≤ −M₀} — the padded process reaches −M₀.

**Theorem 1.8 (hsym of symmetric).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/Padding.hsym_of_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/Padding.hsym_of_symmetric` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hsym: the padded process reaches −M₀ with at least half the probability that the chain reaches the boundary. P(∃ k ≤ N, M_k ≤ 0) ≤ 2 · P(∃ k ≤ N, S̃_k ≤ −M₀). This is the first of the two factors of 2 in padded_increment_tail's constant 4. It needs only that the padding law is symmetric; the chain M is completely arbitrary.

**Theorem 1.9 (map finset Sum gaussian).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/Padding.map_finsetSum_gaussian`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/Padding.map_finsetSum_gaussian` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The sum over a Finset of i.i.d. centred Gaussian coordinates is centred Gaussian.

**Theorem 1.10 (map walk Sum gaussian).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/Padding.map_walkSum_gaussian`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/Padding.map_walkSum_gaussian` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The terminal law. The walk's final value under i.i.d. N(0,δ) increments is N(0, N·δ).

**Theorem 1.11 (hlaw of hincl).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/Padding.hlaw_of_hincl`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/Padding.hlaw_of_hincl` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hlaw from hincl. If the increment vector is i.i.d. N(0,δ), the terminal value is N(0, N·δ) — so padded_tail_assembled's last premise is free.

**Theorem 1.12 (measure Preserving neg gaussian Real).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/Padding.measurePreserving_neg_gaussianReal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/Padding.measurePreserving_neg_gaussianReal` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A centred real Gaussian is symmetric.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/Padding.hitSet`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/Padding.hlaw_of_hincl`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/Padding.hsym_of_symmetric`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/Padding.levSet`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/Padding.map_finsetSum_gaussian`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/Padding.map_walkSum_gaussian`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/Padding.measurePreserving_negPad`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/Padding.measurePreserving_neg_gaussianReal`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/Padding.negPad`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/Padding.padSum`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/Padding.padSum_negPad`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/Padding.paddedProc`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal](../Gaussian/LevyMaximal.md)
