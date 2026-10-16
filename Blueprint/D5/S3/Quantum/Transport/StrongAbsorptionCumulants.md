# StrongAbsorptionCumulants

## Abstract

StrongAbsorptionCumulants for the strong-absorption cumulant expansion.

Natural-number subtraction is truncated. Unmarked integrals use volume; real-number powers and division use the real field.

**Definition 1.1 (claim).**

$$claim = (\forall M : \mathbb{N} , 1 \le M \to \forall n : \mathbb{N} , 2 \le n \to \exists C \gamma_{0} : \mathbb{R} , 0 < \gamma_{0} \land \forall \gamma : \mathbb{R} , \gamma_{0} \le \gamma \to |  (- 1 : \mathbb{R})^{n} \cdot kappa M n \gamma - ((n - 1) . factorial / ((M : \mathbb{R})^{2 \cdot n - 2} \cdot  \gamma^{2 \cdot n}) - (2 \cdot n - 1) \cdot n \cdot (n - 1) . factorial / ((M : \mathbb{R})^{2 \cdot n - 2} \cdot  \gamma^{2 \cdot n + 1})) | \le C /  \gamma^{2 \cdot n + 2})$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.claim` (`✓ std3`).

*Citation.* M. Novaes (2023). *Time delay statistics for chaotic cavities with absorption*. DOI: [10.1007/s10955-023-03183-7](https://doi.org/10.1007/s10955-023-03183-7). URL: <https://arxiv.org/abs/2305.18235>.

*Commentary.*

Novaes, Section 5, p. 7: “we conjecture that, for n > 1,” followed by Eq. (58). Natural n ≥ 2 expresses n > 1. The two coefficients and the absolute remainder bound refer to every M ≥ 1. The constants may depend on M and n.

**Theorem 1.2 (result).**

$$\forall M : \mathbb{N} , 1 \le M \to \forall n : \mathbb{N} , 2 \le n \to \exists C \gamma_{0} : \mathbb{R} , 0 < \gamma_{0} \land \forall \gamma : \mathbb{R} , \gamma_{0} \le \gamma \to |  (- 1 : \mathbb{R})^{n} \cdot kappa M n \gamma - ((n - 1) . factorial / ((M : \mathbb{R})^{2 \cdot n - 2} \cdot  \gamma^{2 \cdot n}) - (2 \cdot n - 1) \cdot n \cdot (n - 1) . factorial / ((M : \mathbb{R})^{2 \cdot n - 2} \cdot  \gamma^{2 \cdot n + 1})) | \le C /  \gamma^{2 \cdot n + 2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Novaes (2023). *Time delay statistics for chaotic cavities with absorption*. DOI: [10.1007/s10955-023-03183-7](https://doi.org/10.1007/s10955-023-03183-7). URL: <https://arxiv.org/abs/2305.18235>.

*Commentary.*

For every positive channel number and every cumulant order at least two, the normalized law has the two strong-absorption coefficients of Novaes, Eq. (58).

## References

- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.claim`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.result`
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/Density](StrongAbsorption/Density.md)
