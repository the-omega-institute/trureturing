# Finite Support Selection Bayes and Minimax Bridge

## Abstract

Finite Support Selection Bayes and Minimax Bridge.

**Theorem 1.1 (Finite Support Selection Bayes and Minimax Bridge).**

$$\forall M, q, s: Nat, r: Real, e: Experiment, 1\leq q<M \land 0<r<1 \land 0\leq\operatorname{compensation}(M, q, r)<1 \Rightarrow \operatorname{Conclusion}(M, q, s, r, e)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportSelectionMinimax.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural M, q and s, assume 1<=q<M, 0<r<1 and 0<=a<1, where a=rq/(M-q). The conclusion holds for both complete finite experiments: independent uniform-start ordered pairs and a consecutive path with one uniform start. The support is a single unknown q-element subset throughout all observations.

The conclusion includes stochastic compensated transitions and complete observation laws, strict positivity, the full uniform-reference and support-product likelihood factorizations, positive exponential weights, the normalized posterior, the exact elementary-symmetric inclusion-difference identity, and equivalence of inclusion and weight ordering.

Every permutation of the first-copy coordinates fixes the second copy and acts on every vertex in the complete observation. Mapping every support coordinate gives a bijection on supports; mapping both endpoints of every ordered pair, or every vertex of a path, gives a bijection on complete observations. Applying these explicit maps preserves the actual probability, relabels every weight, and transports the uniform cutoff decision mass. Any two supports of cardinality q are connected by one such permutation.

There exist measurable stochastic decision kernels equal to the uniform top-q rule and its extension by zero to other subsets. The q-element kernel has the exact cutoff description: H={i:t<w(i)}, E={i:w(i)=t}, |H|<q<=|H|+|E|, with uniform mass 1/binomial(|E|,q-|H|) on precisely those T between H and H union E.

For normalized Hamming loss, competitors output exactly q elements. For exact-recovery loss, competitors may output any subset. In each action class the constructed kernel minimizes uniform-prior Bayes cost among all randomized competitors, has equal frequentist risk at all true supports, and its risk at every support is at most the supremum risk of every competitor. Its supremum risk equals the infimum, over all randomized competitors, of their supremum risks.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportSelectionMinimax.result`
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportSelectionBayes](FiniteSupportSelectionBayes.md)
