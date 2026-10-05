# Chain Setup

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate chain setup to the stochastic ellipsoid construction.

**Definition 1.1 (gauss Path).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.gaussPath`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.gaussPath` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The path space: one standard Gaussian per step, for infinitely many steps.

**Definition 1.2 (coord).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.coord`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.coord` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The k-th driving increment.

**Theorem 1.3 (map coord).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.map_coord`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.map_coord` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The law of each coordinate is the standard Gaussian.

**Theorem 1.4 (i Indep Fun coord).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.iIndepFun_coord`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.iIndepFun_coord` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The coordinates are independent.

**Definition 1.5 (restr).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.restr`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.restr` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The first k increments.

**Definition 1.6 (nat Fil).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.natFil`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.natFil` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The natural filtration of the driving sequence.

**Definition 1.7 (filtration).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.filtration`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.filtration` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The filtration, bundled.

**Theorem 1.8 (measurable coord nat Fil).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.measurable_coord_natFil`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.measurable_coord_natFil` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

ξ k is ℱ (k+1)-measurable — the sequence is adapted.

**Theorem 1.9 (indep Fun coord restr).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.indepFun_coord_restr`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.indepFun_coord_restr` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

ξ k is independent of the first k increments.

**Theorem 1.10 (mem Lp coord apply).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.memLp_coord_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.memLp_coord_apply` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

All moments of every coordinate are finite, from memLp_id_gaussianReal.

**Theorem 1.11 (integrable norm sq coord).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.integrable_norm_sq_coord`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.integrable_norm_sq_coord` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

‖ξ_k‖² is integrable — the second moment that dominates hintquad, since ‖π x‖ ≤ ‖x‖.

**Definition 1.12 (step).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.step`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.step` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain's increment: the standard coordinate scaled by c = √h.

**Theorem 1.13 (map step).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.map_step`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.map_step` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

ξ_k ~ N(0, c²·Id) — the currency StateInvariant4's half-laws take.

**Theorem 1.14 (step coord law).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.step_coord_law`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.step_coord_law` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hlaw of driftInputs_step_chain, at v = c².

**Theorem 1.15 (step coord indep).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.step_coord_indep`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.step_coord_indep` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hindep of driftInputs_step_chain.

**Theorem 1.16 (indep step nat Fil).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.indep_step_natFil`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.indep_step_natFil` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hind of driftInputs_step_chain: each increment is independent of its own past.

**Theorem 1.17 (integrable step apply).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.integrable_step_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.integrable_step_apply` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hintxi of driftInputs_step_chain.

**Theorem 1.18 (integrable step mul).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.integrable_step_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.integrable_step_mul` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hintprod of driftInputs_step_chain.

**Theorem 1.19 (integrable bdd Coeff mul).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.integrable_bddCoeff_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.integrable_bddCoeff_mul` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hintK: a coefficient bounded by C times a product of two coordinates is integrable as soon as the coefficient is a.e. strongly measurable. For driftInputs_step_chain the coefficient is (π_k e_p) q, bounded by ‖π_k e_p‖ ≤ ‖e_p‖ = 1.

**Theorem 1.20 (norm coord le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.norm_coord_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.norm_coord_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A coordinate is bounded by the norm.

**Theorem 1.21 (abs star Projection single le one).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.abs_starProjection_single_le_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.abs_starProjection_single_le_one` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The bound integrable_bddCoeff_mul is applied at: an orthogonal projection's matrix entries are at most 1 in absolute value.

**Definition 1.22 (chain Dir).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.chainDir`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.chainDir` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain direction, in the first summand.

**Definition 1.23 (fresh Dir).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.freshDir`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.freshDir` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The fresh direction: the second summand's unit vector.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.abs_starProjection_single_le_one`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.chainDir`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.coord`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.filtration`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.freshDir`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.gaussPath`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.iIndepFun_coord`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.indepFun_coord_restr`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.indep_step_natFil`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.integrable_bddCoeff_mul`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.integrable_norm_sq_coord`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.integrable_step_apply`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.integrable_step_mul`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.map_coord`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.map_step`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.measurable_coord_natFil`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.memLp_coord_apply`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.natFil`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.norm_coord_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.restr`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.step`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.step_coord_indep`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.step_coord_law`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ContactIntegrated](../Contact/ContactIntegrated.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/StateInvariant4](../State/StateInvariant4.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep](../Tail/TailAtStep.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk](ChainWalk.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/WalkTelescope](WalkTelescope.md)
