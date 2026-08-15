# Equality in Total-Variation Data Processing

## Abstract

Total-variation channel contraction is exact precisely when each output column avoids mixing the two strict sign supports of the input discrepancy.

**Theorem 1.1 (Channel equality is absence of sign mixing).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to \mathbb{R}, W: X\to Y\to \mathbb{R},\\((\forall x, y, 0\le W(x, y)) \land (\forall x, \sum_{y} W(x, y)= 1)) \Rightarrow \\\operatorname{TV}(\operatorname{channelOutput}(W, p), \operatorname{channelOutput}(W, q))= \operatorname{TV}(p, q) \Leftrightarrow \\\forall y, ((\forall x, p(x)< q(x) \Rightarrow W(x, y)= 0) \lor \\(\forall x, q(x)< p(x) \Rightarrow W(x, y)= 0)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Equality/DataProcessingEquality.total_variation_channel_eq_iff_no_sign_mixing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p and q be arbitrary real functions on a finite input carrier, and let W be a nonnegative row-stochastic channel. The channel preserves their total variation exactly when every output y kills all inputs from one of the two strict sign supports of p - q.

The strict inequalities are essential at the boundary. Inputs with p(x) = q(x) impose no condition, and a zero channel weight contributes to neither sign. Thus a column may meet both strict supports as sets, but it cannot give positive weight to both; an identically zero output column satisfies both alternatives.

The contraction proof is a sum of one triangle inequality for each output column. Row normalization preserves the total absolute input mass across all columns, so global equality holds exactly when every columnwise triangle inequality is an equality. A private finite signed-mass lemma identifies that equality with sign coherence, and channel nonnegativity converts coherence into the displayed support condition.

No normalization, nonnegativity, or equal-mass assumption is placed on p and q. The result classifies equality for the fixed triple (p, q, W); it does not classify channels that preserve total variation for every input pair, and it states no measure-theoretic analogue.

## References

- Truth anchor: `D5/S3/TotalVariation/Equality/DataProcessingEquality.total_variation_channel_eq_iff_no_sign_mixing`
- Dependency: [D5/S3/TotalVariation/DataProcessing](../DataProcessing.md)
