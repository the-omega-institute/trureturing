# Tail Side Setup

## Abstract

Lattice tail bounds along the matrix walk.

Lattice tail bounds along the matrix walk. The results below relate tail side setup to the stochastic ellipsoid construction.

**Theorem 1.1 (prod map middle four).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.prod_map_middle_four`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.prod_map_middle_four` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The middle-four interchange for product measures. Not in Mathlib; proved on rectangles by Fubini twice.

**Theorem 1.2 (indep Fun prod Mk prod Mk).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.indepFun_prodMk_prodMk`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.indepFun_prodMk_prodMk` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Two independent pairs of blocks, one pair per factor.

**Theorem 1.3 (indep Fun fst prod).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.indepFun_fst_prod`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.indepFun_fst_prod` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A block on the first factor against a block on the first factor together with all of the second.

**Theorem 1.4 (std Gaussian real).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.stdGaussian_real`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.stdGaussian_real` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

stdGaussian ℝ is N(0,1) — the bridge between the value type's second summand and the external factor's law.

**Definition 1.5 (Pad Space).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.PadSpace`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.PadSpace` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The space of the external-padding route: the chain's path space times the k fresh Gaussians TailTransport.hit_tail_yOf asks for.

**Definition 1.6 (Zed).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.Zed`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.Zed` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The past at step i: the first i chain coordinates and the first i fresh ones.

**Definition 1.7 (Xi).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.Xi`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.Xi` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The combined increment below the horizon, rescaled so that it is a *standard* Gaussian on the two-factor value type: the chain coordinate and the fresh coordinate divided by r.

**Theorem 1.8 (map Xi).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.map_Xi`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.map_Xi` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Its law is standard: map_pair_prod, with the fresh coordinate rescaled.

**Theorem 1.9 (indep Fun Zed Xi).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.indepFun_Zed_Xi`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.indepFun_Zed_Xi` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The past is independent of the increment — the four blocks straddle the two factors, which is what §1 is for.

**Definition 1.10 (trunc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.trunc`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.trunc` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The past, truncated further — used to say that the earlier increments are functions of the past at step i.

**Definition 1.11 (Xfam).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.Xfam`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.Xfam` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The increment family. Below the horizon it is the padded increment — the chain coordinate and the fresh one read in a past-measurable unit direction. At and above the horizon there is no fresh coordinate, so the increment is an unused chain coordinate read in a fixed unit direction; that completion is exactly what PaddingMap.map_pi_of_stepIndep's ∀ i hypotheses need.

**Theorem 1.12 (map Xfam).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.map_Xfam`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.map_Xfam` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Every increment is N(0, r²) — below the horizon by the frozen-direction argument on the two-factor value type, above it by map_scaled_inner at the unused chain coordinate.

**Definition 1.13 (Gfam).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.Gfam`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.Gfam` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The earlier increments, as a function of the past at step i.

**Theorem 1.14 (indep Fun Xfam).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.indepFun_Xfam`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.indepFun_Xfam` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Each increment is independent of all the earlier ones.

**Theorem 1.15 (hincl external).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.hincl_external`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.hincl_external` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hincl at every horizon on the external-padding route.

**Theorem 1.16 (inner to Lp pad Unit).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.inner_toLp_padUnit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.inner_toLp_padUnit` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The completed unit direction, written out at the two-factor carrier.

**Theorem 1.17 (hincl of increments).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.hincl_of_increments`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.hincl_of_increments` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hincl for an adapted increment family — TailTransport.hit_tail_yOf's law, with the chain entering only through hM: its increment at step i is r⟪ω i, w_i(past)⟫, and the padding amplitude is the completing √(1 − ‖w_i‖²).

**Theorem 1.18 (tail of increments).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.tail_of_increments`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.tail_of_increments` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The transported per-step tail for an adapted increment family, on the chain's own path space, with no probabilistic hypothesis left.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.Gfam`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.PadSpace`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.Xfam`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.Xi`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.Zed`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.hincl_external`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.hincl_of_increments`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.indepFun_Xfam`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.indepFun_Zed_Xi`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.indepFun_fst_prod`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.indepFun_prodMk_prodMk`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.inner_toLp_padUnit`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.map_Xfam`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.map_Xi`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.prod_map_middle_four`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.stdGaussian_real`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.tail_of_increments`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.trunc`
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetup](../State/PaddedLawSetup.md)
