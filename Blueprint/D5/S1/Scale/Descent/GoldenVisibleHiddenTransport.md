# Golden Visible-Hidden Transport

## Abstract

Golden inflation expands its visible projection while its conjugate residual contracts.

**Theorem 1.1 (Golden inflation transports visible and hidden projections).**

$$\forall W: Type, (\operatorname{AddCommGroup}(W) \land \operatorname{Module}(\mathbb{R}, W)) \Rightarrow \forall J: \operatorname{LinearMap}(\mathbb{R}, W, W), J \circ J = 5 \cdot I_{W} \Rightarrow\\{}\text{let } Phi := \frac{1}{2}{I_{W} + J}; pi_{vis} := \frac{1}{2}{I_{W} + \frac{1}{\sqrt{5}}J};\\{}pi_{hid} := \frac{1}{2}{I_{W} - \frac{1}{\sqrt{5}}J}; epsilon:\mathbb{N}\to\mathbb{R} := (n: \mathbb{N} \mapsto \Vert \operatorname{goldenConj} \Vert^{n});\\{}(\forall x: W, pi_{vis}(Phi(x)) = \operatorname{goldenRatio} \cdot pi_{vis}(x)) \land 1 < \operatorname{goldenRatio} \land\\{}(\forall x: W, pi_{hid}(Phi(x)) = \operatorname{goldenConj} \cdot pi_{hid}(x)) \land \operatorname{goldenConj} < 0 \land\\{}\Vert \operatorname{goldenConj} \Vert = \operatorname{goldenRatio}^{-1} \land \operatorname{goldenRatio}^{-1} < 1 \land\\{}(\forall n: \mathbb{N}, epsilon(n) = {\operatorname{goldenRatio}^{-1}}^{n}) \land \operatorname{Tendsto}(epsilon, \operatorname{atTop}, \operatorname{nhds}(0)).$$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/Descent/GoldenVisibleHiddenTransport.golden_visible_hidden_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be a real-linear endomorphism whose square is five times the identity. The inflation operator and its visible and hidden projections are constructed explicitly from J and the square root of five. The two projections are therefore source objects rather than an assumed eigenspace decomposition.

The visible projection scales by the golden ratio, which is greater than one. The hidden projection scales by the negative golden conjugate. Its magnitude is exactly the reciprocal golden ratio, strictly less than one, so the intrinsic sequence epsilon n is that geometric power and converges to zero.

Current D5 and pinned-Mathlib searches found no exact theorem packaging this carrier, construction, and all transport clauses. Mathlib's golden-ratio identities and geometric-power convergence theorem are applied directly. The existing two-coordinate renormalization result was rejected as a surrogate for the source's module construction.

## References

- Truth anchor: `D5/S1/Scale/Descent/GoldenVisibleHiddenTransport.golden_visible_hidden_transport`
