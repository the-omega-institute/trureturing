# Conjugate Bridge

## Abstract

A coordinate is the gap between a value and its conjugate, normalised by the square root of thirteen.

The greedy step has the same integer action on coordinates under both embeddings; only the multiplier differs. Since a coordinate equals the normalised gap between the two embeddings, a coordinate sequence is bounded exactly when the conjugate orbit is, and the conjugate multiplier has modulus above one.

**Theorem 1.1 (The conjugate bridge).**

$$\left(\forall p \in R, q \in R,\; p + q \cdot \mathit{betaThirteen} - \left(p + q \cdot \mathit{betaThirteenConjugate}\right) = q \cdot \operatorname{sqrt}\left(13\right)\right) \land 1 < \left|\mathit{betaThirteenConjugate}\right|$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisotFrontier/ConjugateBridge.conjugate_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the mechanism behind the frontier claim, not the claim. That the coordinates of the orbit of one actually grow is measured, not proved: their ratio approaches the conjugate modulus to one part in a million by the fiftieth step.

## References

- Truth anchor: `D5/S0/Tower/NonPisotFrontier/ConjugateBridge.conjugate_bridge`
- Dependency: [D5/S0/Tower/NonPisotFrontier/ExpansionEngine](ExpansionEngine.md)
