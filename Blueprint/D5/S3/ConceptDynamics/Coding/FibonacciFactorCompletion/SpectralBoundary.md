# Original weighted spectral convergence boundary

## Abstract

The total series of actual retained weighted paths converges exactly below complex spectral radius one, and the full positive-cap scope includes a closed root at one.

The matrix uses exactly the original retained finite-past vertices and allowed c/u labels. Its two edge weights are z to twenty and z to six, summed even when labels have the same endpoints. ComplexAdjacency is the coefficientwise complex image of this real matrix, so every power is the complex image of the original power. WeightedRadius is its complex spectral radius. No replacement graph or assumed exponential-growth law is introduced.

**Theorem 1.1 (geometric bound supplier).**

$$\forall A \in Type, a \in A, rate \in NNReal,\; \left(\operatorname{NormedRing}\left(A\right) \land \left(\operatorname{CompleteSpace}\left(A\right) \land \left(\operatorname{NormedAlgebra}\left(Complex, A\right) \land \operatorname{lt}\left(\operatorname{spectralRadius}\left(Complex, a\right), \operatorname{toENNReal}\left(rate\right)\right)\right)\right)\right) \Rightarrow \operatorname{exists}\left(\left(\operatorname{lt}\left(0, C\right) \land \left(\forall k \in Nat,\; \operatorname{le}\left(\operatorname{norm}\left(\operatorname{power}\left(a, k\right)\right), \operatorname{multiply}\left(C, \operatorname{power}\left(\operatorname{toReal}\left(rate\right), k\right)\right)\right)\right)\right)_{C \in Real}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary.geometric_bound_supplier` (`✓ std3`). ∎

*Citation.* TNLean contributors (2026). *Power decay below spectral radius one*. URL: <https://github.com/LionSR/QICLean/blob/c61daa23f385237a4d992a602c94812ca9f909b8/QICLean/Analysis/SpectralRadiusPowerDecay.lean>.

*Commentary.*

For an element a of a complete complex normed algebra and a nonnegative rate strictly above its spectral radius, one positive constant bounds every power norm by that constant times the rate to k. Gelfand's formula gives the eventual estimate; a finite initial sum gives the same bound at every earlier k. This geometric estimate supplies the u-cycle positivity and actual spectral scaling arguments.

**Theorem 1.2 (path mass norm bounds).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real, z \in Real, k \in Nat,\; \operatorname{le}\left(0, z\right) \Rightarrow \left(\operatorname{le}\left(0, \operatorname{pathMass}\left(side, n, K, d, z, k\right)\right) \land \left(\operatorname{le}\left(\operatorname{norm}\left(\operatorname{power}\left(\operatorname{complexAdjacency}\left(side, n, K, d, z\right), k\right)\right), \operatorname{pathMass}\left(side, n, K, d, z, k\right)\right) \land \operatorname{le}\left(\operatorname{pathMass}\left(side, n, K, d, z, k\right), \operatorname{multiply}\left(\operatorname{toReal}\left(\operatorname{FintypeCard}\left(\operatorname{CoreVertex}\left(side, n, K, d\right)\right)\right), \operatorname{norm}\left(\operatorname{power}\left(\operatorname{complexAdjacency}\left(side, n, K, d, z\right), k\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary.path_mass_norm_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonnegative parameter, the total original k-step path mass is nonnegative and bounds the operator norm of the actual matrix power from above. The same mass is bounded by the retained vertex count times that norm. Nonnegative rows and the operator row-sum norm give both comparisons, including an empty retained carrier. These comparisons pass actual monomial scaling to spectral scaling.

**Theorem 1.3 (original weighted series boundary).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real, z \in Real,\; \operatorname{le}\left(0, z\right) \Rightarrow \left(\operatorname{Summable}\left(\left(\operatorname{sum}\left(\left(\operatorname{sum}\left(\left(\operatorname{coreMonomial}\left(side, K, d, z, k, v, choices\right)\right)_{choices \in \operatorname{Fin}\left(k\right) \to \operatorname{Product}\left(CuLetter, \operatorname{CoreVertex}\left(side, n, K, d\right)\right)}\right)\right)_{v \in \operatorname{CoreVertex}\left(side, n, K, d\right)}\right)\right)_{k \in Nat}\right) \Leftrightarrow \operatorname{lt}\left(\operatorname{weightedRadius}\left(side, n, K, d, z\right), 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary.original_weighted_series_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative real z, both memory sides, every n and K, and every real threshold d, summing all original path monomials over their letter length is convergent exactly when the radius is strictly below one. The exact matrix-power row-sum identity identifies these monomials with the original paths. Nonnegative entries give a sandwich: the operator norm of a power is at most its total entry sum, and that sum is at most the number of retained vertices times the norm. A radius gap gives a summable geometric bound. Conversely convergence forces the powers to tend to zero; a sufficiently late power has norm below one, which forces the spectral radius below one. The empty carrier is handled separately. Thus radius one also gives divergence, and reducible graphs and paths crossing transient bridges remain included.

For the endpoint statement, oneStepCeiling is the maximum of zero, the original high-side u intercept, chi times the high-side fixed point, and that fixed point. These are exactly the two one-letter images of the zero and high seeds. A threshold strictly above this ceiling disables every c edge at K=n=1 under both the strict lower and the closed upper conventions.

**Theorem 1.4 (original closed root boundary).**

$$\forall side \in MemorySide, d \in Real,\; \operatorname{lt}\left(oneStepCeiling, d\right) \Rightarrow \left(\operatorname{MemoryLanguage}\left(side, 1, 1, d\right) = \operatorname{singleton}\left(\left(u\right)_{i \in Int}\right) \land \left(\left(\forall z \in Real,\; \operatorname{le}\left(0, z\right) \Rightarrow \operatorname{weightedRadius}\left(side, 1, 1, d, z\right) = \operatorname{ENNRealOfReal}\left(\operatorname{power}\left(z, 6\right)\right)\right) \land \left(\left(\forall z \in Real,\; \operatorname{le}\left(0, z\right) \Rightarrow \left(\operatorname{weightedRadius}\left(side, 1, 1, d, z\right) = 1 \Leftrightarrow z = 1\right)\right) \land \operatorname{weightedFactorRate}\left(\operatorname{MemoryLanguage}\left(side, 1, 1, d\right)\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary.original_closed_root_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At these thresholds the complete bilateral language is the singleton all-u sequence. Reconstruction forces every retained vertex to be the one-letter u memory, while the actual all-u path supplies a vertex. The adjacency is therefore the scalar z to six times the identity on this nonempty singleton carrier. Its radius is z to six for nonnegative z, and radius one occurs precisely at z=1. At each actual total weight, at most one different factor occurs: every factor is a u repetition and weight six times its length determines that repetition. Thus the original weightedFactorRate, including its max-one convention at unsupported weights, is zero, equal to minus log base two of the closed root. This positive-K endpoint supplements the original section's K at least two regime.

InteriorRoot supplies the general K at least two interior roots, their actual weighted rates, memory nesting and the closed upper intersection. Fixed-graph margins, convergence of graph rates and eventual even-length asymptotics require further conclusions. The convergence criterion alone does not establish them.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary.geometric_bound_supplier`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary.original_closed_root_boundary`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary.original_weighted_series_boundary`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary.path_mass_norm_bounds`
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph](MemoryGraph.md)
