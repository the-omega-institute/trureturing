# Static and Dynamic Projection Diagnostics Are Independent

## Abstract

Unread-measurement coherence loss and residual-to-visible generator return are independent quantitative diagnostics.

**Definition 1.1 (Pinching is packaged as a linear endomorphism).**

$$\forall \rho: QubitMatrix, \operatorname{pinchingEnd}\left(\rho\right) = \operatorname{pinching}\left(\rho\right).$$

*Formalization.* `D5/S3/QuantumChannels/ProjectionDiagnostics/StaticDynamicScalarSeparation.pinchingEnd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The endomorphism applies the repository's standard-basis pinching channel. Its linear laws follow entrywise from the existing channel formula.

**Definition 1.2 (The generator returns one residual coordinate to the visible diagonal).**

$$\forall A: QubitMatrix, i, j: \operatorname{Fin}\left(2\right), \operatorname{residualReturnGenerator}\left(A, i, j\right) = A_{01}, \operatorname{if} (i,j)=(0,0); 0, \operatorname{otherwise}.$$

*Formalization.* `D5/S3/QuantumChannels/ProjectionDiagnostics/StaticDynamicScalarSeparation.residualReturnGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This explicit complex-linear generator reads the upper off-diagonal entry and writes it into the first diagonal entry. It therefore transports a discarded residual coordinate back into the visible block.

**Theorem 1.3 (Static coherence loss and dynamic return vary independently).**

$$[\forall lower\in \mathbb{R}, \exists \rho\in QubitMatrix, lower < \Re \operatorname{hilbertSchmidtInner}\left((\rho - \operatorname{pinching}\left(\rho\right)), (\rho - \operatorname{pinching}\left(\rho\right))\right) \land pinchingEnd \circ I \circ (I - pinchingEnd) = 0] \land [\forall upper\in \mathbb{R}, 0 < upper \Rightarrow \exists \rho\in QubitMatrix, 0 < \Re \operatorname{hilbertSchmidtInner}\left((\rho - \operatorname{pinching}\left(\rho\right)), (\rho - \operatorname{pinching}\left(\rho\right))\right) \land \Re \operatorname{hilbertSchmidtInner}\left((\rho - \operatorname{pinching}\left(\rho\right)), (\rho - \operatorname{pinching}\left(\rho\right))\right) < upper \land pinchingEnd \circ residualReturnGenerator \circ (I - pinchingEnd) \neq 0].$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/ProjectionDiagnostics/StaticDynamicScalarSeparation.static_loss_and_dynamic_return_are_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real lower bound, scaling a single off-diagonal matrix entry makes the Hilbert--Schmidt mass discarded by pinching exceed that bound. The identity generator still has zero residual-to-visible block because pinching is idempotent.

For every positive real upper bound, a smaller positive off-diagonal entry gives discarded mass strictly between zero and that bound. The explicit residual-return generator nevertheless has a nonzero visible return block. Both contrast clauses use the same pinching channel on the complex qubit-matrix carrier.

## References

- Truth anchor: `D5/S3/QuantumChannels/ProjectionDiagnostics/StaticDynamicScalarSeparation.pinchingEnd`
- Truth anchor: `D5/S3/QuantumChannels/ProjectionDiagnostics/StaticDynamicScalarSeparation.residualReturnGenerator`
- Truth anchor: `D5/S3/QuantumChannels/ProjectionDiagnostics/StaticDynamicScalarSeparation.static_loss_and_dynamic_return_are_independent`
