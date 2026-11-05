# Stable Recovery from Opposite-Channel Singleton Fibres

## Abstract

Local singleton fibres control the inverse error of two finite observation channels.

Let X, U and V be finite types and let f:X->U and g:X->V be the actual deterministic observations. A point x is an f-leaf if every y with f(y)=f(x) equals x. OppositeLeaves(f,g) means that whenever x is not a leaf in either channel, every different y in its f-fibre is a g-leaf. Both channel orientations are assumed. These are conditions on the complete fibres of the supplied maps, independent of any weights or desired inverse estimate.

In the formulas, Weights(X) is X->Real, L1(h) is the sum over X of abs(h(x)), pushMass(f,h)(u) is the sum of h over the actual fibre f(x)=u, and TV(p,q) is one half of L1(p-q). Empty finite types and signed weights are allowed; no normalization, positivity, or zero-total-mass assumption is used.

**Theorem 1.1 (Uniform signed inverse estimate).**

$$\forall X \in \mathrm{FiniteType},\; \forall U \in \mathrm{FiniteType},\; \forall V \in \mathrm{FiniteType},\; \forall f \in \mathrm{Function}\left(X, U\right),\; \forall g \in \mathrm{Function}\left(X, V\right),\; \forall h \in \mathrm{Weights}\left(X\right),\; ((\mathrm{OppositeLeaves}\left(f, g\right)) \land (\mathrm{OppositeLeaves}\left(g, f\right))) \Rightarrow (\mathrm{L1}\left(h\right) \le \frac{3}{2} \cdot \left(\mathrm{L1}\left(\mathrm{pushMass}\left(f, h\right)\right) + \mathrm{L1}\left(\mathrm{pushMass}\left(g, h\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/LocalLeafInverse.signed_l1_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Call a point a centre if neither observation identifies it alone. At most one centre uses each output coordinate: a second centre in that fibre would have to be an opposite-channel leaf. Partners of distinct centres therefore occupy disjoint singleton fibres in the other channel. The fibre triangle inequality bounds twice the centre mass by the two centre-output norms plus the two leaf masses. Every noncentre is a leaf in at least one channel. Leaf and centre outputs are disjoint, so no observed coordinate is charged twice. The resulting signed L1 bound has coefficient three halves.

**Theorem 1.2 (Total-variation error bound).**

$$\forall X \in \mathrm{FiniteType},\; \forall U \in \mathrm{FiniteType},\; \forall V \in \mathrm{FiniteType},\; \forall f \in \mathrm{Function}\left(X, U\right),\; \forall g \in \mathrm{Function}\left(X, V\right),\; \forall p \in \mathrm{Weights}\left(X\right),\; \forall q \in \mathrm{Weights}\left(X\right),\; ((\mathrm{OppositeLeaves}\left(f, g\right)) \land (\mathrm{OppositeLeaves}\left(g, f\right))) \Rightarrow (\mathrm{TV}\left(p, q\right) \le \frac{3}{2} \cdot \left(\mathrm{TV}\left(\mathrm{pushMass}\left(f, p\right), \mathrm{pushMass}\left(f, q\right)\right) + \mathrm{TV}\left(\mathrm{pushMass}\left(g, p\right), \mathrm{pushMass}\left(g, q\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/LocalLeafInverse.total_variation_le_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the signed estimate to p-q, use linearity of the actual pushforward, and divide by two. Probability mass functions are included. If both observed TV errors are at most epsilon, the source TV is at most three epsilon. The bound uses the sum of the separate errors and does not assume a joint law for the two channel outputs.

The local condition permits double-star incidence components with degrees larger than two. Consequently, it does not require a global enumeration of graph components, a path partition, or a degree-two hypothesis. The coefficient is an upper bound under the stated local condition; optimality in a particular observation model requires its own witnesses.

## References

- Truth anchor: `D5/S3/TotalVariation/LocalLeafInverse.signed_l1_le`
- Truth anchor: `D5/S3/TotalVariation/LocalLeafInverse.total_variation_le_sum`
- Dependency: [D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope](../Estimation/DataProcessing/FiniteSimplexFiberPolytope.md)
- Dependency: [D5/S3/TotalVariation/Metric](Metric.md)
