# Entropy Derivative Equals the Modular Gap

## Abstract

For a positive observation scale below the defect depth, rank-one thermal entropy has derivative and full differential equal to the local modular gap.

**Theorem 1.1 (The local modular first law).**

$$\begin{gathered}\forall delta, omega: \mathbb{R},\\{}0 < omega \land omega < delta \Rightarrow\\{}[\operatorname{HasDerivAt}\left(S, \log (\frac{N+1}{N}), N\right) \land\\{}\log (\frac{N+1}{N}) = -\log (q) \land\\{}-\log (q) = epsilon] \land\\{}[(\forall dN: \mathbb{R}, \operatorname{fderiv}\left(\mathbb{R}, S, N\right)(dN) = epsilon dN) \land\\{}epsilon = 2 \log (\frac{delta}{omega})].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DefectModularFirstLaw/EntropyDerivativeEqualsModularGap.entropy_derivative_equals_modular_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let delta and omega be real scales with 0 < omega < delta. The Lean definitions localModularWeight, rankOneThermalOccupation, rankOneThermalEntropy, and defectModularGap carry respectively q = (omega/delta)^2, the externally visible occupation N = q/(1-q), S(N) = (N+1) log(N+1) - N log N, and epsilon = 2 log(delta/omega).

The first displayed group mirrors (1388.3): S has derivative log((N+1)/N) at N, this coefficient is -log q, and -log q is epsilon. HasDerivAt records both the derivative value and the differentiability implicit in dS/dN.

The second displayed group mirrors (1388.4): for every real increment dN, the Frechet derivative sends dN to epsilon*dN, and epsilon equals 2 log(delta/omega). These are the theorem's five public conclusion leaves in the same two groups as the source.

This is the local rank-one modular thermodynamic law. It neither asserts the existence of an off-critical zeta zero nor states the physical black-hole first law.

## References

- Truth anchor: `D5/S3/Observer/DefectModularFirstLaw/EntropyDerivativeEqualsModularGap.entropy_derivative_equals_modular_gap`
