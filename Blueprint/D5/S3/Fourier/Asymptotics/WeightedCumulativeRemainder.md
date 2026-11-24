# Weighted transfer of a cumulative error

## Abstract

A logarithmic cumulative error gives a weighted bound uniform in the upper height.

**Theorem 1.1 (Error bound for a weighted finite tail).**

$$\begin{aligned}&|\operatorname{C}\left(t\right)-\operatorname{G}\left(t\right)| \le A\operatorname{log}\left(ct\right)^{2}+B\operatorname{log}\left(2t\right)\quad(t \in [X,T]),\\&|\sum_{j \in S} \operatorname{w}\left(\operatorname{h}\left(j\right)\right)\operatorname{a}\left(j\right)-\int_{X}^{T} \operatorname{w}\left(t\right)\operatorname{g}\left(t\right) dt| \le \frac{2A(\operatorname{log}\left(cX\right)^{2}+\operatorname{log}\left(cX\right)+1)+B(2\operatorname{log}\left(2X\right)+1)}{X}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/WeightedCumulativeRemainder.weighted_tail_error_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The interval has 1 ≤ X ≤ T. The finite set S indexes complex jumps a(j) at heights h(j) in (X,T]. Multiple indices can have equal height. The cumulative value C(t) adds the jumps at heights at most t to the arbitrary complex baseline C₀. The complex main term G has continuous derivative g.

The real weight w has continuous derivative and satisfies 0 ≤ w(t) ≤ 1/t and w′(t) ≤ 0 on the interval. The error profile uses c ≥ 1 and A,B ≥ 0. The displayed hypothesis on the cumulative error holds for each t in [X,T].

For an individual jump, integrate the weight derivative from its height to T. Summing these identities gives finite partial summation. Apply integration by parts to the main term. For an envelope E, the two endpoint errors and the integrated error are bounded by 2 w(X) E(X) plus the integral of w E′. Integration by parts for the product w E cancels the right endpoint. Bound the remaining integral by replacing w with 1/t and evaluating the logarithmic primitive.

For Ford and Zaharescu's Lemma 1, on the Riemann hypothesis, take the literal ordinate phases with multiplicity and use the prime-power main term divided by the square root of the frequency parameter x. For an explicit-formula error constant K the parameters are c=2x, A=K sqrt(x), and B=K/(sqrt(x) log(x)). The estimate is uniform in T for fixed x. Control of the full frequency range for growing moments remains open. https://arxiv.org/pdf/math/0405459

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/WeightedCumulativeRemainder.weighted_tail_error_le`
