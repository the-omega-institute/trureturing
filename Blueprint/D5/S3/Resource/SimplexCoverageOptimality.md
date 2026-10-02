# The Original Simplex Coverage Optimizer

## Abstract

The q-ary simplex code minimizes actual uniform physical iid expected full-span retrieval time among every full-rank generator of the exact simplex length.

**Theorem 1.1 (Bertuzzo–Ravagnani–Yaakobi Conjecture 3.2).**

Lean statement: `D5/S3/Resource/SimplexCoverageOptimality.result`

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SimplexCoverageOptimality.result` (`✓ std3`). ∎

*Resolves.* `Problems/bertuzzo-2026-simplex-coverage-optimality` (proved) by `D5/S3/Resource/SimplexCoverageOptimality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bertuzzo-2026-simplex-coverage-optimality","declaration_gid":"D5/S3/Resource/SimplexCoverageOptimality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Matteo Bertuzzo, Alberto Ravagnani, Eitan Yaakobi (2026). *The DNA Coverage Depth Problem: Duality, Weight Distributions, and Applications*. DOI: [10.48550/arXiv.2603.06489](https://doi.org/10.48550/arXiv.2603.06489). URL: <https://arxiv.org/html/2603.06489v1>.

*Commentary.*

For every finite field K of cardinality q, every dimension k at least two, n=(q^k-1)/(q-1), every rank-k Matrix (Fin k) (Fin n) K generator G, and every actual physical simplex matrix S whose columns give exactly one nonzero representative of each projective line, E[T_S] is at most E[T_G]. Both expectations are the original real integral of MinimumRetrievalTime.retrievalTime toReal under MinimumRetrievalTime.uniformSamples (Fin n). There are no additional mass, invariance, concavity, finiteness or integrability premises. The nonempty sampling instance is derived inside the statement, not required as an assumption.

This is arXiv:2603.06489v1 Section 3 Conjecture 3.2, solving Problem B at the simplex parameters; the predecessor is arXiv:2507.20639v1 Section III's unnumbered optimizer paragraph. All zero, repeated and scalar-parallel competitor positions remain in the same iid uniform-with-replacement physical sample space. The result is not a uniqueness statement, a prime-field or nonzero-only subcase, a projective-only competitor comparison, a rank-deficient expectation or a changed sampling law.

Only zero columns are replaced by a fixed nonzero vector. Submodule containment couples every original prefix with its replacement on the identical positions and also preserves full span. Local GL span invariance and finite orbit Jensen use the represented root-concavity theorem. Local physical ray fiber sums preserve multiplicity. An actual alphabet bijection and the pinned projective cardinality identify uniform ray recovery with physical simplex recovery. Measurable complements compare every failure tail, including horizon zero; the original probability bridge gives finite ENNReal tail sums, integrability and both real-integral conversions.

The sole new public declaration is result. All averaging, coupling, transport, cardinality and measure arguments are theorem-local. The published closed-form simplex expectation supplies context for this optimizer theorem.

## References

- Truth anchor: `D5/S3/Resource/SimplexCoverageOptimality.result`
- Dependency: [D5/S3/Resource/SimplexCoverageProbability](SimplexCoverageProbability.md)
- Dependency: [D5/S3/Resource/SimplexCoverageRoot](SimplexCoverageRoot.md)
- Dependency: [D5/S3/Resource/SimplexCoverageWords](SimplexCoverageWords.md)
