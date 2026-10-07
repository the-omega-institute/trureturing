# Tail At Step R5W2

## Abstract

Lattice tail bounds along the matrix walk.

Lattice tail bounds along the matrix walk. The results below relate tail at step r5w2 to the stochastic ellipsoid construction.

**Definition 1.1 (Chain Raw3).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.ChainRaw3`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.ChainRaw3` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The raw datum with a terminal weight. ChainRaw2RW2 plus the single-time bound the count event needs.

**Theorem 1.2 (prof Step le horizon).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.profStep_le_horizon`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.profStep_le_horizon` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The terminal step's bound is below the horizon's, by monotonicity of profile in t.

**Definition 1.3 (w Prof).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.wProf`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.wProf` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The t-integrated profile bound, as the weight. ChainRaw2RW2.tail at it is le_refl.

**Definition 1.4 (w Prof T).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.wProfT`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.wProfT` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The terminal profile bound, as the weight. ChainRaw3.tailT at it is le_refl.

**Definition 1.5 (chain Raw3 of raw2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.chainRaw3_of_raw2`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.chainRaw3_of_raw2` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The weight swap (route note). Any ChainRaw2RW2 becomes a ChainRaw3 whose two weights are the profile bounds themselves: every arithmetic field is carried over untouched and both tail fields are le_refl, so the record is g-free and chain-free.

**Theorem 1.6 (integrable profile euclidean).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.integrable_profile_euclidean`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.integrable_profile_euclidean` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Params.integrable for a single-time profile. integrable_radial_euclidean without the t-integral: bounded by 1/2, supported in closedBall 0 W.

**Theorem 1.7 (dom of tail T).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.dom_of_tailT`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.dom_of_tailT` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Params.dom for a single-time profile. dom_of_tail2 without the t-integral; the shift in profileAt is again exactly the cube radius √n/2.

**Definition 1.8 (comb W).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.combW`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.combW` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The combined contact weight: A·w_int + B·w_T, in ℝ≥0∞.

**Definition 1.9 (comb F).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.combF`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.combF` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Its radial profile. The 4s of ChainRaw3.tail and ChainRaw3.tailT sit inside, so the second coefficient is 4·B; that is the b of Lemma43R3.radial_bound_combined_le.

**Definition 1.10 (C3).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.C3`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.C3` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The combined radial estimate uses the scaled sum of the integrated-contact coefficient and the terminal-contact coefficient.

**Theorem 1.11 (comb F nonneg).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.combF_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.combF_nonneg` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

combF is nonnegative.

**Theorem 1.12 (of Real comb le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.ofReal_comb_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.ofReal_comb_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The ℝ≥0∞ arithmetic of Params.dom for a sum of two weights, isolated so the record below does not carry it inline.

**Theorem 1.13 (params Producer3).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.paramsProducer3`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.paramsProducer3` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

paramsProducer3. Theorem2R3.ParamsProducerR2's five equalities, with ChainRaw3 in the binder and the combined weight in the fourth — all five are rfl on the record above.

**Theorem 1.14 (sums split).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.sums_split`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.sums_split` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The split, at a general §5 threshold. TerminalCount.sums_of_combined asks for ∑ < 1; the §5 output is ∑ < θ, so the coefficients passed to it are divided by θ, and the two admissibility facts become θ ≤ A·θ₁ and θ ≤ B·θ₂. That pair is scale-invariant in (A, B), which is why no normalisation of the combined weight is needed.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.C3`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.ChainRaw3`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.chainRaw3_of_raw2`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.combF`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.combF_nonneg`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.combW`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.dom_of_tailT`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.integrable_profile_euclidean`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.ofReal_comb_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.paramsProducer3`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.profStep_le_horizon`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.sums_split`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.wProf`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2.wProfT`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/GoodPathLight](../Completion/GoodPathLight.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/TerminalCount](../Completion/TerminalCount.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/Theorem2](../Completion/Theorem2.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/WindowR](../Completion/WindowR.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Construction/LatticeData](../Construction/LatticeData.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Construction/LatticeDataR](../Construction/LatticeDataR.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR2](../Contact/Lemma43UniformR2.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR3](../Contact/Lemma43UniformR3.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ThetaTight](../Contact/ThetaTight.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8](../Drift/Stopped/DriftStopped8.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8R5](../Drift/Stopped/DriftStopped8R5.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep](TailAtStep.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR2W2](TailAtStepR2W2.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup3](TailSideSetup3.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup3W2](TailSideSetup3W2.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainInputDom](../Walk/ChainInputDom.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainWalkRW2](../Walk/ChainWalkRW2.md)
