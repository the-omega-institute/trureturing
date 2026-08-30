# Golden Lorentz Update

## Abstract

A Fibonacci update negates the golden Lorentz form, while two updates preserve it.

**Theorem 1.1 (One update exchanges sectors and two preserve the form).**

$$let Q_{\phi}(x, y) = x^{2} - x \cdot y - y^{2}; let F = \operatorname{matrix2}\left(1, 1, 1, 0\right); \left(\left(\left(\forall v \in \operatorname{Vector}\left(\operatorname{Real}\left(\right), 2\right),\; \left(Q_{\phi}\right)\left(\operatorname{mulVec}\left(F, v\right)\right) = -\left(Q_{\phi}\right)\left(v\right)\right) \land \left(\forall v \in \operatorname{Vector}\left(\operatorname{Real}\left(\right), 2\right),\; \left(Q_{\phi}\right)\left(\operatorname{mulVec}\left(F^{2}, v\right)\right) = \left(Q_{\phi}\right)\left(v\right)\right)\right) \land \left(\forall v \in \operatorname{Vector}\left(\operatorname{Real}\left(\right), 2\right),\; 0 < \left(Q_{\phi}\right)\left(v\right) \Rightarrow \left(Q_{\phi}\right)\left(\operatorname{mulVec}\left(F, v\right)\right) < 0\right)\right) \land \left(\forall v \in \operatorname{Vector}\left(\operatorname{Real}\left(\right), 2\right),\; \left(Q_{\phi}\right)\left(v\right) < 0 \Rightarrow 0 < \left(Q_{\phi}\right)\left(\operatorname{mulVec}\left(F, v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenLorentzUpdate.golden_lorentz_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic form is constructed on the real two-dimensional carrier as Q_phi(x,y)=x^2-xy-y^2. The update is the repository's canonical real Fibonacci matrix with rows (1,1) and (1,0).

Direct expansion gives the one-step negation identity. Applying that identity twice cancels the two signs and proves exact preservation under the squared update.

The last two public clauses spell out the sector consequence: positive values become negative and negative values become positive after one update.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenLorentzUpdate.golden_lorentz_update`
- Dependency: [D5/S1/Scale/FibonacciEigen](../../../S1/Scale/FibonacciEigen.md)
