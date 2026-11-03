# Fourth maxima on the native command grid

## Abstract

Uniform fourth maxima on normal grid windows of the actual native command triple.

A raw model B determines the original command triple (a,b,j), where j is its chronological area. Put delta=1/n squared. A complete word is a function from Fin(n cubed) to the four sign pairs. Every word has mass 4 to the power minus n cubed, including every unused suffix after a wall contact.

gridFourthMaximum(B,n,w,k,m) is the maximum, over the nonempty set of integers j from zero through m, of the fourth power of the norm of command(B,n,w,(k+j)delta)-command(B,n,w,k delta). The norm is the maximum coordinate norm on the joint triple. gridFourthExpectation is its sum over all complete words multiplied by their original common mass.

**Theorem 1.1 (A common fourth bound for every normal grid window).**

$$\forall B: Model, \exists C: \mathbb{R}, (0 \le C) \land (\forall n: \mathbb{N}, (0 < n) \Rightarrow (\forall k: \mathbb{N}, \forall m: \mathbb{N}, (k + m \le n^{3}) \Rightarrow ((m \cdot \operatorname{mesh}\left(n\right) \le 2) \Rightarrow (\operatorname{gridFourthExpectation}\left(B, n, k, m\right) \le C \cdot \left(m \cdot \operatorname{mesh}\left(n\right)\right)^{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/NativeCommandGridMaximal.actual_grid_maximal_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite nonempty maximum includes j=0. The condition k+m<=n cubed keeps every observed point on the normal grid; the distinct forced final upper-wall leg is excluded. The same constant depends only on B, independently of n, k, m, the word and whether the path survives. The case m=0 has expectation zero.

From each alive endpoint, take the full original increment and its chronological area increment; after the first endpoint outside the height walls, hold this auxiliary endpoint chain fixed. The actual stopped command at any normal grid point differs from this chain by at most the length of one chord. The clipping parameter is the original sign-dependent first-wall fraction, and the actual path holds at that clipped point.

Compactness in height and periodicity in phase bound the original drift and noise coefficients. Consequently there are nonnegative constants D and J such that the four-sign mean endpoint increment has norm at most D delta, every endpoint jump has norm at most J sqrt(delta), and each full chord has Lipschitz bound J sqrt(delta) in its interpolation parameter. The area-coordinate mean uses the original product of the two horizontal increments; it is bounded by the same coefficient estimates.

Use the finite complete-word history law with constant innovation mass one fourth. Its exact next-prefix conditional expectation shows that the endpoint chain minus its accumulated four-sign means is a martingale. For any window, its centered coordinate jumps have absolute value at most (J+D)sqrt(delta). The finite even maximal inequality at exponent four bounds the expected fourth coordinate maximum by 262144 times (J+D) to the fourth power times T squared, where T=m delta.

The accumulated mean over the window has norm at most D T. The endpoint comparison contributes at most 2 J sqrt(delta) to an increment. The five-term fourth-power sum bound combines the three centered coordinate maxima, 3 D T and this comparison error. For m positive, delta<=T; for T<=2, T to the fourth power is at most 4 T squared. Thus C=125 times the sum of 3 times 262144 times (J+D) to the fourth power, 324 D to the fourth power and 16 J to the fourth power suffices.

The expectation is exactly the original finite complete-word sum. No survival conditioning or change of word masses is used. Arbitrary real windows, the fourth estimate on all scales and tightness in continuous path space require additional arguments.

## References

- Truth anchor: `D5/S3/Analytic/Probability/NativeCommandGridMaximal.actual_grid_maximal_estimate`
- Dependency: [D5/S3/Analytic/Probability/NativeCommandPathTightness](NativeCommandPathTightness.md)
- Dependency: [D5/S3/Estimation/DataProcessing/FiniteHistoryConditionalExpectation](../../Estimation/DataProcessing/FiniteHistoryConditionalExpectation.md)
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/StoppedLikelihoodAbsorption](../../Estimation/SequentialDecisionRisk/StoppedLikelihoodAbsorption.md)
