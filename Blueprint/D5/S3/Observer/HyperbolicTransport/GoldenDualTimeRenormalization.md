# Golden Dual-Time Renormalization

## Abstract

Golden reciprocal time scaling preserves the dual product and is reversed by reflection.

**Theorem 1.1 (Reciprocal scaling preserves the product and reflection reverses time).**

$$let a = \varphi^{2}; let R = \operatorname{diag2}\left(a^{-1}, a\right); let J = \operatorname{matrix2}\left(0, 1, 1, 0\right); \forall delta \in \operatorname{Real}\left(\right),\; \forall L \in \operatorname{Real}\left(\right),\; \left(\left(\operatorname{mulVec}\left(R, \operatorname{pair}\left(delta, L\right)\right) = \operatorname{pair}\left(a^{-1} \cdot delta, a \cdot L\right) \land a^{-1} \cdot delta \cdot a \cdot L = delta \cdot L\right) \land J \cdot R \cdot J = R^{-1}\right) \land \left(R \cdot R^{-1} = 1 \land R^{-1} \cdot R = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HyperbolicTransport/GoldenDualTimeRenormalization.golden_dual_time_renormalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set a=phi^2. The update contracts the transverse scale delta by a inverse and expands the observation length L by a, so their product is fixed.

The coordinate exchange J conjugates the diagonal update R to the displayed reverse matrix. Lean also checks both matrix products with that reverse are the identity, making the inverse claim explicit.

The theorem records only this self-contained two-coordinate algebra. It does not assert that every observer duality is golden or derive the separate primitive-unimodular classification boundary.

## References

- Truth anchor: `D5/S3/Observer/HyperbolicTransport/GoldenDualTimeRenormalization.golden_dual_time_renormalization`
