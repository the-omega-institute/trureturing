# Packing

## Abstract

One positive packing constant for every natural dimension.

Construction A provides the lattice point-count profile. A stopped Gaussian walk deforms its quadratic form while controlling contact counts, determinant drift and shortfall. A good realization excludes every nonzero lattice point. Transfer to integer coordinates and scaling then fix the volume exactly, with one constant in every dimension and the zero map at n=0.

**Definition 1.1 (Bfam).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Packing.Bfam`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/Packing.Bfam` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The terminal counting weight is B(m)=140/(m+1)^2. Its dimension dependence balances the contact and drift estimates.

**Theorem 1.2 (Bfam nonneg).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Packing.Bfam_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/Packing.Bfam_nonneg` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The terminal counting weight is nonnegative in every natural dimension.

**Definition 1.3 (Kcut).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Packing.Kcut`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/Packing.Kcut` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The cut index: one step short of the horizon.

**Theorem 1.4 (Kcut lt).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Packing.Kcut_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/Packing.Kcut_lt` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Above the dimension threshold the walk horizon is positive, so its predecessor is a strictly earlier cut index.

**Theorem 1.5 (Kcut succ).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Packing.Kcut_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/Packing.Kcut_succ` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Above the dimension threshold, adding one to the cut index recovers the full walk horizon.

**Definition 1.6 (rr At).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Packing.rrAt`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/Packing.rrAt` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The shortfall's free parameter rr, chosen so that rr·mAt ≥ (1+c₃)·η with mAt ≥ 1/2.

**Definition 1.7 (eps At).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Packing.epsAt`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/Packing.epsAt` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The perturbation allowance is the reciprocal fourth root of the dimension.

**Theorem 1.8 (klartag packing).**

$$\exists c: \mathbb{R}, 0 < c \land \forall n: \mathbb{N}, \exists phi: \operatorname{LinearEnd}\left(\mathbb{R}^{n+1}\right), \operatorname{volume}\left(\operatorname{image}\left(phi, \operatorname{openUnitBall}\left(\mathbb{R}^{n+1}\right)\right)\right) = c \cdot n^{2} \land \operatorname{IntegerPoints}\left(\operatorname{image}\left(phi, \operatorname{openUnitBall}\left(\mathbb{R}^{n+1}\right)\right)\right) = \{0\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/Packing.klartag_packing` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

There is one positive real constant c such that, for every natural n, a real linear map on Euclidean space of dimension n+1 sends the open unit ball to a set of volume exactly c*n^2. Its points with integer coordinates are exactly zero. The constant is uniform in n, including n=0. Construction A averaging supplies the lattice, the stopped Gaussian matrix walk supplies the determinant bound, and linear transfer followed by homothetic shrinking gives exact volume.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Packing.Bfam`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Packing.Bfam_nonneg`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Packing.Kcut`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Packing.Kcut_lt`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Packing.Kcut_succ`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Packing.epsAt`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Packing.klartag_packing`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Packing.rrAt`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds](PackingBounds.md)
