# Symmetric Bernoulli Second-Order Evidence

## Abstract

The symmetric two-point signal has quadratic Hellinger, log-affinity, and KL evidence with quartic remainders.

**Theorem 1.1 (Weak symmetric bias produces quadratic evidence).**

$$\forall b \in \operatorname{Bool},\\{}P_{\delta}(b) := \operatorname{ite}(b, \frac{1}{2} + \delta, \frac{1}{2} - \delta), Q_{\delta}(b) := \operatorname{ite}(b, \frac{1}{2} - \delta, \frac{1}{2} + \delta);\\{}\delta \to 0:\\{}(\operatorname{H}(P_{\delta}, Q_{\delta})^{2} = 4 \delta^{2} + \operatorname{O}(\delta^{4})) \land\\{}(-\log \rho(P_{\delta}, Q_{\delta}) = 2 \delta^{2} + \operatorname{O}(\delta^{4})) \land\\{}(D_{KL}(P_{\delta}, Q_{\delta}) = 8 \delta^{2} + \operatorname{O}(\delta^{4})).$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliSecondOrder.symmetric_bernoulli_second_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Bool, the positive-bias mass assigns one half plus delta to true and one half minus delta to false. The negative-bias mass swaps those two values. Thus the source laws are constructed directly from the two-point carrier rather than introduced through the claimed asymptotic coefficients.

The frozen squared Hellinger distance, Bhattacharyya affinity, and real-valued finite KL divergence evaluate on this pair to the source closed forms. Rationalizing the square root controls the first remainder, while the pinned local logarithm estimate controls the other two.

Each displayed remainder is bounded by a constant multiple of delta to the fourth in a neighborhood of zero. The three clauses are independent public conjuncts and use the exact Bool laws shown before the asymptotic statement.

## References

- Truth anchor: `D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliSecondOrder.symmetric_bernoulli_second_order`
- Dependency: [D5/S3/TotalVariation/HellingerDivergence](../HellingerDivergence.md)
