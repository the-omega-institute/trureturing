# Haar fidelity under single-axis dephasing

## Abstract

Strict asymptotic deficit in the Haar mean of iterative Petz recovery.

**Theorem 1.1 (The limiting Haar mean is strictly below one).**

Lean statement: `D5/S3/Quantum/Recovery/IterativePetz/IterativePetzHaar.meanFidelity_tendsto_lt_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/IterativePetz/IterativePetzHaar.meanFidelity_tendsto_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lea Lautenbacher, Felix Ahnefeld, Susana F. Huelga, and Martin B. Plenio (2026). *Iterative Petz Protocols for Quantum State Recovery*. DOI: [10.48550/arXiv.2611.32995](https://doi.org/10.48550/arXiv.2611.32995). URL: <https://arxiv.org/abs/2611.32995v1>.

*Commentary.*

The axial distribution for a Haar-random pure qubit is uniform on the interval from minus one to one. Each finite-depth fidelity is measurable and bounded by one. Dominated convergence yields the limiting mean, and the positive pointwise gap on a set of positive measure makes this limit strictly smaller than one for every nontrivial multiplier.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/IterativePetz/IterativePetzHaar.meanFidelity_tendsto_lt_one`
- Dependency: [D5/S3/Quantum/Recovery/IterativePetz/IterativePetzDephasing](IterativePetzDephasing.md)
