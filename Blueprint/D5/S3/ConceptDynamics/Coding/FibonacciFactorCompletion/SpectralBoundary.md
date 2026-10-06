# Original weighted spectral convergence boundary

## Abstract

The total series of actual retained weighted paths converges exactly below complex spectral radius one, and the full positive-cap scope includes a closed root at one.

The matrix uses exactly the original retained finite-past vertices and allowed c/u labels. Its two edge weights are z to twenty and z to six, summed even when labels have the same endpoints. ComplexAdjacency is the coefficientwise complex image of this real matrix, so every power is the complex image of the original power. WeightedRadius is its complex spectral radius. No replacement graph or assumed exponential-growth law is introduced.

**Theorem 1.1 (original weighted series boundary).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real, z \in Real,\; \operatorname{le}\left(0, z\right) \Rightarrow \left(\operatorname{Summable}\left(\left(\operatorname{sum}\left(\left(\operatorname{sum}\left(\left(\operatorname{coreMonomial}\left(side, K, d, z, k, v, choices\right)\right)_{choices \in \operatorname{Fin}\left(k\right) \to \operatorname{Product}\left(CuLetter, \operatorname{CoreVertex}\left(side, n, K, d\right)\right)}\right)\right)_{v \in \operatorname{CoreVertex}\left(side, n, K, d\right)}\right)\right)_{k \in Nat}\right) \Leftrightarrow \operatorname{lt}\left(\operatorname{weightedRadius}\left(side, n, K, d, z\right), 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary.original_weighted_series_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative real z, both memory sides, every n and K, and every real threshold d, summing all original path monomials over their letter length is convergent exactly when the radius is strictly below one. The exact matrix-power row-sum identity identifies these monomials with the original paths. Nonnegative entries give a sandwich: the operator norm of a power is at most its total entry sum, and that sum is at most the number of retained vertices times the norm. A radius gap gives a summable geometric bound. Conversely convergence forces the powers to tend to zero; a sufficiently late power has norm below one, which forces the spectral radius below one. The empty carrier is handled separately. Thus radius one also gives divergence, and reducible graphs and paths crossing transient bridges remain included.

For the endpoint statement, oneStepCeiling is the maximum of zero, the original high-side u intercept, chi times the high-side fixed point, and that fixed point. These are exactly the two one-letter images of the zero and high seeds. A threshold strictly above this ceiling disables every c edge at K=n=1 under both the strict lower and the closed upper conventions.

**Theorem 1.2 (original closed root boundary).**

$$\forall side \in MemorySide, d \in Real,\; \operatorname{lt}\left(oneStepCeiling, d\right) \Rightarrow \left(\operatorname{MemoryLanguage}\left(side, 1, 1, d\right) = \operatorname{singleton}\left(\left(u\right)_{i \in Int}\right) \land \left(\left(\forall z \in Real,\; \operatorname{le}\left(0, z\right) \Rightarrow \operatorname{weightedRadius}\left(side, 1, 1, d, z\right) = \operatorname{ENNRealOfReal}\left(\operatorname{power}\left(z, 6\right)\right)\right) \land \left(\left(\forall z \in Real,\; \operatorname{le}\left(0, z\right) \Rightarrow \left(\operatorname{weightedRadius}\left(side, 1, 1, d, z\right) = 1 \Leftrightarrow z = 1\right)\right) \land \operatorname{weightedFactorRate}\left(\operatorname{MemoryLanguage}\left(side, 1, 1, d\right)\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary.original_closed_root_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At these thresholds the complete bilateral language is the singleton all-u sequence. Reconstruction forces every retained vertex to be the one-letter u memory, while the actual all-u path supplies a vertex. The adjacency is therefore the scalar z to six times the identity on this nonempty singleton carrier. Its radius is z to six for nonnegative z, and radius one occurs precisely at z=1. At each actual total weight, at most one different factor occurs: every factor is a u repetition and weight six times its length determines that repetition. Thus the original weightedFactorRate, including its max-one convention at unsupported weights, is zero, equal to minus log base two of the closed root. This positive-K endpoint supplements the original section's K at least two regime.

Existence and uniqueness of a spectral root for general thresholds, equality with the original weighted factor rate, memory nesting, auxiliary intersections and inclusions, fixed-graph margins, convergence of graph rates, and eventual even-length asymptotics require further conclusions. The convergence criterion alone does not establish them.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary.original_closed_root_boundary`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary.original_weighted_series_boundary`
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph](MemoryGraph.md)
