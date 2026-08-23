# Factor-Invariant Observables

## Abstract

A readout admits factor dynamics exactly when pullback preserves every observable that passes through it.

**Lemma 1.1 (Factor dynamics transport pulled-back observables).**

$$\begin{gathered}\forall Y, Z, V: \operatorname{Type},\\{}phi: Y \to Z, tau: Y \to Y, sigma: Z \to Z,\\{}phi \circ tau = sigma \circ phi \Rightarrow \forall g: Z \to V,\\{}g \circ phi \circ tau = g \circ sigma \circ phi.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Factor/FactorInvariantObservables.factor_pullback_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the readout intertwines the state dynamics with a dynamics on the readout space. Pulling back any value-valued observable through the state dynamics then agrees with first transporting that observable by the factor dynamics and then reading out.

Thus every observable obtained from the readout remains an observable of the same readout after one state update, with the transported observable given by composition with the factor dynamics.

**Theorem 1.2 (Factor dynamics are equivalent to observable invariance).**

$$\begin{gathered}\forall Y, Z: \operatorname{Type},\\{}phi: Y \to Z, tau: Y \to Y,\\{}(\exists sigma: Z \to Z, phi \circ tau = sigma \circ phi) \iff (\forall V: \operatorname{Type}, \forall g: Z \to V,\\{}\exists h: Z \to V, g \circ phi \circ tau = h \circ phi).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Factor/FactorInvariantObservables.factor_iff_observable_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A dynamics on the readout space makes the readout equivariant exactly when every observable through the readout remains expressible through that readout after pullback by the state dynamics.

The forward direction transports each observable by composition with the factor dynamics. Conversely, applying invariance to the identity observable on the readout space produces the factor dynamics itself and its intertwining equation.

**Lemma 1.3 (Surjective readouts have unique factor dynamics).**

$$\begin{gathered}\forall Y, Z: \operatorname{Type},\\{}phi: Y \to Z, tau: Y \to Y,\\{}(\forall z: Z, \exists y: Y, phi\left(y\right) = z) \Rightarrow \forall sigma1, sigma2: Z \to Z,\\{}(phi \circ tau = sigma1 \circ phi \land phi \circ tau = sigma2 \circ phi) \Rightarrow sigma1 = sigma2.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Factor/FactorInvariantObservables.factor_unique_of_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every readout value is represented by some state, two dynamics on the readout space that both intertwine the same state dynamics must agree everywhere.

For any readout value, choose a state mapping to it. Both factor equations evaluate the two candidate dynamics there to the same updated readout, so surjectivity upgrades pointwise agreement on represented values to equality of the dynamics.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Factor/FactorInvariantObservables.factor_iff_observable_invariance`
- Truth anchor: `D5/S3/ConceptDynamics/Factor/FactorInvariantObservables.factor_pullback_formula`
- Truth anchor: `D5/S3/ConceptDynamics/Factor/FactorInvariantObservables.factor_unique_of_surjective`
