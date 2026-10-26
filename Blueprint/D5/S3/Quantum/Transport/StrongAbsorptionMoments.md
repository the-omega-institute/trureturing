# StrongAbsorptionMoments

## Abstract

StrongAbsorptionMoments for strong-absorption moments.

Real arithmetic is used in all coefficients. Integrals without an explicit measure use volume. M is the channel count; n is the moment order.

**Definition 1.1 (traceQPow).**

$$\forall (M : (\mathbb{N})) , ((\forall (n : (\mathbb{N})) , ((\forall (\gamma : (\mathbb{R})) , ((\forall (p : (((Fin M) \to (\mathbb{R})) \times ((Fin M) \to (\mathbb{R})))) , ((traceQPow M n \gamma p = (((M : (\mathbb{R})))^{-1} \cdot \sum i , ((1 / (\gamma + p . 1 i)))^{n})))))))))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorptionMoments.traceQPow` (`✓ std3`).

*Citation.* M. Novaes (2023). *Time delay statistics for chaotic cavities with absorption*. DOI: [10.1007/s10955-023-03183-7](https://doi.org/10.1007/s10955-023-03183-7). URL: <https://arxiv.org/abs/2305.18235v1>.

*Commentary.*

The normalized spectral power sum uses proper delay times 1 / (γ + xᵢ).

**Definition 1.2 (claim54).**

$$claim54 = (\forall M : (\mathbb{N}) , ((1 \le M) \to (\forall n : (\mathbb{N}) , ((1 \le n) \to (\exists C \gamma_{0} : (\mathbb{R}) , ((0 < \gamma_{0}) \land (\forall \gamma : (\mathbb{R}) , ((\gamma_{0} \le \gamma) \to (| (\int p , traceQPow M n \gamma p \,d (law M \gamma)) - (1 / (\gamma)^{n} - (n : (\mathbb{R})) / (\gamma)^{n + 1} + ((n : (\mathbb{R})))^{2} / (\gamma)^{n + 2} - ((n : (\mathbb{R})) + 1) \cdot ((n : (\mathbb{R})) \cdot (5 \cdot (n : (\mathbb{R})) - 2) \cdot ((M : (\mathbb{R})))^{2} + (n : (\mathbb{R})) \cdot ((n : (\mathbb{R})) + 2)) / (6 \cdot ((M : (\mathbb{R})))^{2} \cdot (\gamma)^{n + 3})) | \le C / (\gamma)^{n + 4})))))))))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorptionMoments.claim54` (`✓ std3`).

*Citation.* M. Novaes (2023). *Time delay statistics for chaotic cavities with absorption*. DOI: [10.1007/s10955-023-03183-7](https://doi.org/10.1007/s10955-023-03183-7). URL: <https://arxiv.org/abs/2305.18235v1>.

*Commentary.*

Novaes, arXiv v1, p. 7: “We conjecture that (1/M)⟨Tr(Qⁿ)⟩ is given by 1/γⁿ − n/γⁿ⁺¹ + n²/γⁿ⁺² − (n + 1)[n(5n − 2)M² + n(n + 2)]/(6M²γⁿ⁺³) + O(γ^{−n−4}) (54) and that (1/Mⁿ)⟨[Tr(Q)]ⁿ⟩ is given by 1/γⁿ − n/γⁿ⁺¹ + n[(n + 1)M² + (n − 1)]/(2M²γⁿ⁺²) + O(γ^{−n−3}), (55) for every positive integer n.” The channel count M and the order n are positive natural numbers. Expectations use law M γ. Each remainder has a constant and a positive threshold depending on M and n.

**Definition 1.3 (claim55).**

$$claim55 = (\forall M : (\mathbb{N}) , ((1 \le M) \to (\forall n : (\mathbb{N}) , ((1 \le n) \to (\exists C \gamma_{0} : (\mathbb{R}) , ((0 < \gamma_{0}) \land (\forall \gamma : (\mathbb{R}) , ((\gamma_{0} \le \gamma) \to (| (\int p , (tauW M \gamma p)^{n} \,d (law M \gamma)) - (1 / (\gamma)^{n} - (n : (\mathbb{R})) / (\gamma)^{n + 1} + (n : (\mathbb{R})) \cdot (((n : (\mathbb{R})) + 1) \cdot ((M : (\mathbb{R})))^{2} + ((n : (\mathbb{R})) - 1)) / (2 \cdot ((M : (\mathbb{R})))^{2} \cdot (\gamma)^{n + 2})) | \le C / (\gamma)^{n + 3})))))))))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorptionMoments.claim55` (`✓ std3`).

*Citation.* M. Novaes (2023). *Time delay statistics for chaotic cavities with absorption*. DOI: [10.1007/s10955-023-03183-7](https://doi.org/10.1007/s10955-023-03183-7). URL: <https://arxiv.org/abs/2305.18235v1>.

*Commentary.*

Novaes, arXiv v1, p. 7: “We conjecture that (1/M)⟨Tr(Qⁿ)⟩ is given by 1/γⁿ − n/γⁿ⁺¹ + n²/γⁿ⁺² − (n + 1)[n(5n − 2)M² + n(n + 2)]/(6M²γⁿ⁺³) + O(γ^{−n−4}) (54) and that (1/Mⁿ)⟨[Tr(Q)]ⁿ⟩ is given by 1/γⁿ − n/γⁿ⁺¹ + n[(n + 1)M² + (n − 1)]/(2M²γⁿ⁺²) + O(γ^{−n−3}), (55) for every positive integer n.” The channel count M and the order n are positive natural numbers. Expectations use law M γ. Each remainder has a constant and a positive threshold depending on M and n.

**Definition 1.4 (claim).**

$$claim = ((claim54) \land (claim55))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorptionMoments.claim` (`✓ std3`).

*Citation.* M. Novaes (2023). *Time delay statistics for chaotic cavities with absorption*. DOI: [10.1007/s10955-023-03183-7](https://doi.org/10.1007/s10955-023-03183-7). URL: <https://arxiv.org/abs/2305.18235v1>.

*Commentary.*

Novaes, arXiv v1, p. 7: “We conjecture that (1/M)⟨Tr(Qⁿ)⟩ is given by 1/γⁿ − n/γⁿ⁺¹ + n²/γⁿ⁺² − (n + 1)[n(5n − 2)M² + n(n + 2)]/(6M²γⁿ⁺³) + O(γ^{−n−4}) (54) and that (1/Mⁿ)⟨[Tr(Q)]ⁿ⟩ is given by 1/γⁿ − n/γⁿ⁺¹ + n[(n + 1)M² + (n − 1)]/(2M²γⁿ⁺²) + O(γ^{−n−3}), (55) for every positive integer n.” The channel count M and the order n are positive natural numbers. Expectations use law M γ. Each remainder has a constant and a positive threshold depending on M and n.

**Theorem 1.5 (result).**

$$((\forall M : (\mathbb{N}) , ((1 \le M) \to (\forall n : (\mathbb{N}) , ((1 \le n) \to (\exists C \gamma_{0} : (\mathbb{R}) , ((0 < \gamma_{0}) \land (\forall \gamma : (\mathbb{R}) , ((\gamma_{0} \le \gamma) \to (| (\int p , traceQPow M n \gamma p \,d (law M \gamma)) - (1 / (\gamma)^{n} - (n : (\mathbb{R})) / (\gamma)^{n + 1} + ((n : (\mathbb{R})))^{2} / (\gamma)^{n + 2} - ((n : (\mathbb{R})) + 1) \cdot ((n : (\mathbb{R})) \cdot (5 \cdot (n : (\mathbb{R})) - 2) \cdot ((M : (\mathbb{R})))^{2} + (n : (\mathbb{R})) \cdot ((n : (\mathbb{R})) + 2)) / (6 \cdot ((M : (\mathbb{R})))^{2} \cdot (\gamma)^{n + 3})) | \le C / (\gamma)^{n + 4})))))))))) \land ((\forall M : (\mathbb{N}) , ((1 \le M) \to (\forall n : (\mathbb{N}) , ((1 \le n) \to (\exists C \gamma_{0} : (\mathbb{R}) , ((0 < \gamma_{0}) \land (\forall \gamma : (\mathbb{R}) , ((\gamma_{0} \le \gamma) \to (| (\int p , (tauW M \gamma p)^{n} \,d (law M \gamma)) - (1 / (\gamma)^{n} - (n : (\mathbb{R})) / (\gamma)^{n + 1} + (n : (\mathbb{R})) \cdot (((n : (\mathbb{R})) + 1) \cdot ((M : (\mathbb{R})))^{2} + ((n : (\mathbb{R})) - 1)) / (2 \cdot ((M : (\mathbb{R})))^{2} \cdot (\gamma)^{n + 2})) | \le C / (\gamma)^{n + 3}))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorptionMoments.result` (`✓ std3`). ∎

*Resolves.* `Problems/novaes-2023-strong-absorption-spectral-moments` (proved) by `D5/S3/Quantum/Transport/StrongAbsorptionMoments.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"novaes-2023-strong-absorption-spectral-moments","declaration_gid":"D5/S3/Quantum/Transport/StrongAbsorptionMoments.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. Novaes (2023). *Time delay statistics for chaotic cavities with absorption*. DOI: [10.1007/s10955-023-03183-7](https://doi.org/10.1007/s10955-023-03183-7). URL: <https://arxiv.org/abs/2305.18235v1>.

*Commentary.*

Both moment expansions hold for every positive channel count and order.

## References

- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorptionMoments.claim`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorptionMoments.claim54`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorptionMoments.claim55`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorptionMoments.result`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorptionMoments.traceQPow`
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/Density](StrongAbsorption/Density.md)
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/Foundations](StrongAbsorption/Foundations.md)
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments](StrongAbsorption/LaguerreMoments.md)
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/SecondOrderDensity](StrongAbsorption/SecondOrderDensity.md)
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorptionCumulants](StrongAbsorptionCumulants.md)
