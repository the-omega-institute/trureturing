# Actual Density Strong Subadditivity

## Abstract

Strong subadditivity for actual finite density matrices, including singular states.

The supplier is Physlib at immutable revision 2725b6f621901d4cd330869e9b77105045c1582e. Its original Apache-2.0 copyright notices and proof bodies are retained in the consumed D5 closure. The receiving carrier is the project's PSD trace-one CStarMatrix. toMState keeps exactly the same complex matrix. Both actual partial traces agree entry by entry, including after the tensor associator. This is an integration of an existing theorem, with no novelty claim. Library/Quantum/meiburg2026ssa.md records all 32 consumed modules, their immutable upstream source mapping and adaptations, the original Meiburg/Lessa/Soldati attribution, and the full Apache-2.0 license retained in the supplier ForMathlib/Misc.lean.

**Theorem 1.1 (The entropy normalization agrees).**

$$\operatorname{Svn}\left(\operatorname{toMState}\left(\rho\right)\right) = \operatorname{S}\left(\rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/StrongSubadditivity.entropy_toMState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuous functional calculus transports through the CStarMatrix star algebra equivalence. Both entropies are the natural-logarithm trace of negative x log x. Zero eigenvalues contribute zero, so no positive-definite or support condition is added.

**Theorem 1.2 (Strong subadditivity on actual marginals).**

$$\operatorname{S}\left(ABC\right) + \operatorname{S}\left(B\right) \le \operatorname{S}\left(AB\right) + \operatorname{S}\left(BC\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/StrongSubadditivity.strong_subadditivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite A, B, C and every DensityState on A tensor B tensor C, S(ABC)+S(B) is at most S(AB)+S(BC). marginalLeft traces the left factor; marginalRight traces the right factor. The AB state is the actual right partial trace after the associator, and B is the actual right trace of BC. No SSA, DPI, invertibility, or entropy-equality hypothesis is supplied.

## References

- Truth anchor: `D5/S3/Quantum/Information/StrongSubadditivity.entropy_toMState`
- Truth anchor: `D5/S3/Quantum/Information/StrongSubadditivity.strong_subadditivity`
- Dependency: [D5/S3/Quantum/Foundation/FiniteDensityPurification](../Foundation/FiniteDensityPurification.md)
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](OrthogonalRecordEntropy.md)
