# Golden Horizon Matching

## Abstract

Rank-one horizon channel laws make seven golden matching conditions equivalent.

**Theorem 1.1 (Seven golden horizon conditions are equivalent).**

$$\begin{gathered}\forall H, sigma, alphaSq, betaSq, K, omega, delta \in \mathbb{R},\\{}(((((((0 < delta) \land (0 \leq omega)) \land (omega < delta)) \land (H = {1 - sigma^{2}}^{-1})) \land (sigma = omega / delta)) \land (alphaSq = H)) \land (betaSq = alphaSq - 1)) \land (K = \operatorname{log}\left(H\right)) \Rightarrow\\{}\operatorname{ListTFAE}\left({[H = \varphi^{2}, 1 - sigma^{2} = {\varphi^{2}}^{-1}, sigma^{2} = \varphi^{-1}, alphaSq = \varphi^{2}, betaSq = \varphi, K = 2 \operatorname{log}\left(\varphi\right), omega / delta = \operatorname{sqrt}\left(\varphi^{-1}\right)]}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenHorizonMatching.golden_horizon_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The external channel laws identify the horizon index with the inverse complement of the sampling square, the sampling ratio with omega over delta, the two squared amplitudes with successive index values, and the entropy cost with the logarithm of the index.

Strict positivity of delta, nonnegativity of omega, and strict contractivity exclude division by zero, the negative square-root branch, and the singular horizon boundary.

Under those laws, the golden horizon index, complementary transmission, sampling square, squared amplitudes, logarithmic cost, and positive sampling ratio are seven equivalent descriptions of one channel.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenHorizonMatching.golden_horizon_matching`
