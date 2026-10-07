# Params Adopted2

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate params adopted2 to the stochastic ellipsoid construction.

**Definition 1.1 (num Steps Adopted2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2.numStepsAdopted2`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2.numStepsAdopted2` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

N = ⌈16 n⁷ log n⌉ — the adopted number of steps at h = n⁻⁹.

**Definition 1.2 (step Size Adopted2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2.stepSizeAdopted2`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2.stepSizeAdopted2` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

h = T / N ≤ n⁻⁹ — the adopted step size.

**Theorem 1.3 (num Steps Adopted2 mul step Size Adopted2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The horizon is hit exactly: N · h = T.

**Theorem 1.4 (eta2 le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2.eta2_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2.eta2_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

η ≤ √2 · n⁻³ — the per-step threshold √(2 h d n) at h ≤ n⁻⁹, d ≤ n². (Discharge.eta_le gives √2 · n⁻² at h ≤ n⁻⁷.)

**Theorem 1.5 (step Good cost2 le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2.stepGood_cost2_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2.stepGood_cost2_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The union-bound cost at the new N: ≤ 33 n⁹ log n. (Discharge.stepGood_cost_le gives 33 n⁷ log n at N = ⌈16 n⁵ log n⌉.)

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2.eta2_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2.numStepsAdopted2`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2.stepGood_cost2_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2.stepSizeAdopted2`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/Discharge](Discharge.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/StepGlue](../State/StepGlue.md)
