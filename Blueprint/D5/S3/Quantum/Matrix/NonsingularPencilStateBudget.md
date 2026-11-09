# Strict budgets and the zero-mass boundary

## Abstract

Nonsingular Hermitian pencils control every positive complex-linear reading on the same matrix algebra.

**Definition 1.1 (The two-parameter pencil).**

$$\forall n \in \operatorname{Type}\left(\right)*,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall E \in \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right),\; \forall K \in \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right),\; \forall G \in \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right),\; \forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \operatorname{pencil}\left(E, K, G, p, q\right) = E + \operatorname{smul}\left(p^{2} + q^{2}, \operatorname{one}\left(\operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)\right)\right) - \operatorname{smul}\left(2 \cdot p, K\right) - \operatorname{smul}\left(2 \cdot q, G\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/NonsingularPencilStateBudget.pencil` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite square complex matrices E,K,G and real parameters p,q, P(E,K,G,p,q)=E+(p²+q²)I−2pK−2qG. All factors and every reading belong to the same matrix algebra.

**Theorem 1.2 (Every positive functional, with its original mass).**

$$\forall n \in \operatorname{Type}\left(\right)*,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall E \in \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right),\; \forall K \in \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right),\; \forall G \in \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right),\; \operatorname{PosDef}\left(E\right) \Rightarrow \left(\operatorname{IsHermitian}\left(K\right) \Rightarrow \left(\operatorname{IsHermitian}\left(G\right) \Rightarrow \left(\left(\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \operatorname{det}\left(\operatorname{pencil}\left(E, K, G, p, q\right)\right) \ne 0\right) \Rightarrow \left(\forall phi \in \operatorname{PositiveLinearMap}\left(\operatorname{Complex}\left(\right), \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right), \operatorname{Complex}\left(\right)\right),\; \left(\operatorname{im}\left(phi\left(E\right)\right) = 0 \land \left(\operatorname{im}\left(phi\left(K\right)\right) = 0 \land \operatorname{im}\left(phi\left(G\right)\right) = 0\right)\right) \land \left(\left(0 < \operatorname{re}\left(phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)\right)\right)\right) \Rightarrow \operatorname{re}\left(phi\left(G\right)\right)^{2} + \operatorname{re}\left(phi\left(K\right)\right)^{2} < \operatorname{re}\left(phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)\right)\right)\right) \cdot \operatorname{re}\left(phi\left(E\right)\right)\right) \land \left(\operatorname{re}\left(phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)\right)\right)\right) = 0 \Rightarrow \left(phi = 0 \land \operatorname{re}\left(phi\left(G\right)\right)^{2} + \operatorname{re}\left(phi\left(K\right)\right)^{2} = \operatorname{re}\left(phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)\right)\right)\right) \cdot \operatorname{re}\left(phi\left(E\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/NonsingularPencilStateBudget.strict_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume E is positive definite, K and G are Hermitian, and the determinant of P(E,K,G,p,q) is nonzero for every real p,q. Every positive complex-linear functional phi has real readings on E,K,G. If m=Re phi(I)>0, then Re phi(G)²+Re phi(K)²<m Re phi(E). If m=0, phi is the zero functional and the corresponding non-strict budget is equality. No normalization, density-matrix representation, or restriction of the functional family is imposed.

The positive-definite locus of a continuous Hermitian family is open. When its determinant never vanishes it agrees with the positive-semidefinite locus, which is closed. The real parameter plane is connected and P(E,K,G,0,0)=E, so every pencil value is positive definite. A positive definite matrix dominates a positive scalar multiple of the unit. Apply the original positive functional at p=Re phi(K)/m and q=Re phi(G)/m. The operator norm of a positive functional is its unit value, which also proves the zero-mass assertion.

The compact-sphere openness argument is adapted from TauCetiProject/TauCeti, commit 8c1eaed7cd02e6fee2db1f66783fb8f03025d76d, TauCeti/Analysis/Matrix/PosDef.lean. The spectral, connectedness, and positive-functional ingredients are classical. This theorem supplies a conditional bridge: a concrete table still has to establish the nonvanishing determinant on the entire real plane and positivity of E. It does not establish a total response, a complete PB family, or physical source contracts.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/NonsingularPencilStateBudget.pencil`
- Truth anchor: `D5/S3/Quantum/Matrix/NonsingularPencilStateBudget.strict_budget`
