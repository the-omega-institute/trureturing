# A commuting residual with a strict budget for every state

## Abstract

A four-dimensional matrix table has a nonzero commuting residual under every positive-state budget.

**Definition 1.1 (The two-parameter pencil).**

$$\forall n \in \operatorname{Type}\left(\right)*,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall E \in \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right),\; \forall K \in \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right),\; \forall G \in \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right),\; \forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \operatorname{pencil}\left(E, K, G, p, q\right) = E + \operatorname{smul}\left(p^{2} + q^{2}, \operatorname{one}\left(\operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)\right)\right) - \operatorname{smul}\left(2 \cdot p, K\right) - \operatorname{smul}\left(2 \cdot q, G\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.pencil` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite square complex matrices E,K,G and real parameters p,q, P(E,K,G,p,q)=E+(p²+q²)I−2pK−2qG. All factors and every reading belong to the same matrix algebra.

**Theorem 1.2 (Every positive functional, with its original mass).**

$$\forall n \in \operatorname{Type}\left(\right)*,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall E \in \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right),\; \forall K \in \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right),\; \forall G \in \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right),\; \operatorname{PosDef}\left(E\right) \Rightarrow \left(\operatorname{IsHermitian}\left(K\right) \Rightarrow \left(\operatorname{IsHermitian}\left(G\right) \Rightarrow \left(\left(\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \operatorname{det}\left(\operatorname{pencil}\left(E, K, G, p, q\right)\right) \ne 0\right) \Rightarrow \left(\forall phi \in \operatorname{PositiveLinearMap}\left(\operatorname{Complex}\left(\right), \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right), \operatorname{Complex}\left(\right)\right),\; \left(\operatorname{im}\left(phi\left(E\right)\right) = 0 \land \left(\operatorname{im}\left(phi\left(K\right)\right) = 0 \land \operatorname{im}\left(phi\left(G\right)\right) = 0\right)\right) \land \left(\left(0 < \operatorname{re}\left(phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)\right)\right)\right) \Rightarrow \operatorname{re}\left(phi\left(G\right)\right)^{2} + \operatorname{re}\left(phi\left(K\right)\right)^{2} < \operatorname{re}\left(phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)\right)\right)\right) \cdot \operatorname{re}\left(phi\left(E\right)\right)\right) \land \left(\operatorname{re}\left(phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)\right)\right)\right) = 0 \Rightarrow \left(phi = 0 \land \operatorname{re}\left(phi\left(G\right)\right)^{2} + \operatorname{re}\left(phi\left(K\right)\right)^{2} = \operatorname{re}\left(phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)\right)\right)\right) \cdot \operatorname{re}\left(phi\left(E\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.strict_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume E is positive definite, K and G are Hermitian, and the determinant of P(E,K,G,p,q) is nonzero for every real p,q. Every positive complex-linear functional phi has real readings on E,K,G. If m=Re phi(I)>0, then Re phi(G)²+Re phi(K)²<m Re phi(E). If m=0, phi is the zero functional and the corresponding non-strict budget is equality. No normalization, density-matrix representation, or restriction of the functional family is imposed.

The positive-definite locus of a continuous Hermitian family is open. When its determinant never vanishes it agrees with the positive-semidefinite locus, which is closed. The real parameter plane is connected and P(E,K,G,0,0)=E, so every pencil value is positive definite. A positive definite matrix dominates a positive scalar multiple of the unit. Apply the original positive functional at p=Re phi(K)/m and q=Re phi(G)/m. The operator norm of a positive functional is its unit value, which also proves the zero-mass assertion.

The compact-sphere openness argument is adapted from TauCetiProject/TauCeti, commit 8c1eaed7cd02e6fee2db1f66783fb8f03025d76d, TauCeti/Analysis/Matrix/PosDef.lean. The spectral, connectedness, and positive-functional ingredients are classical. This theorem supplies a conditional bridge. The fixed table establishes the nonvanishing determinant on the entire real plane and positivity of E. It does not establish a total response, a complete PB family, or physical source contracts.

**Theorem 1.3 (The same table for every positive functional).**

$$\operatorname{IsHermitian}\left(\operatorname{h}\left(\right)\right) \land \left(\operatorname{IsHermitian}\left(\operatorname{x}\left(\right)\right) \land \left(\operatorname{IsHermitian}\left(\operatorname{r}\left(\right)\right) \land \left(\operatorname{h}\left(\right)^{2} = \operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right) \land \left(\operatorname{c}\left(\right) = \operatorname{smul}\left(\frac{1}{2}, \operatorname{x}\left(\right) + \operatorname{h}\left(\right) \cdot \operatorname{x}\left(\right) \cdot \operatorname{h}\left(\right)\right) \land \left(\operatorname{k}\left(\right) = \operatorname{J}\left(\operatorname{h}\left(\right), \operatorname{x}\left(\right)\right) \land \left(\operatorname{t}\left(\right) = \operatorname{smul}\left(\frac{\operatorname{Icomplex}\left(\right)}{2}, \operatorname{h}\left(\right) \cdot \operatorname{x}\left(\right) - \operatorname{x}\left(\right) \cdot \operatorname{h}\left(\right)\right) \land \left(\operatorname{h}\left(\right) \cdot \operatorname{r}\left(\right) = \operatorname{r}\left(\right) \cdot \operatorname{h}\left(\right) \land \left(\operatorname{c}\left(\right) \cdot \operatorname{r}\left(\right) = \operatorname{r}\left(\right) \cdot \operatorname{c}\left(\right) \land \left(\operatorname{r}\left(\right)^{2} = \operatorname{smul}\left(\frac{1}{256}, \operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right)\right) \land \left(\operatorname{J}\left(\operatorname{z}\left(\right), \operatorname{r}\left(\right)\right)^{2} = \operatorname{smul}\left(\frac{1}{256}, \operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right)\right) \land \left(\forall phi \in \operatorname{PositiveLinearMap}\left(\operatorname{Complex}\left(\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right), \operatorname{Complex}\left(\right)\right),\; \operatorname{im}\left(phi\left(\operatorname{x}\left(\right)^{2}\right)\right) = 0 \land \left(\operatorname{im}\left(phi\left(\operatorname{k}\left(\right)\right)\right) = 0 \land \left(\operatorname{im}\left(phi\left(\operatorname{g}\left(\right)\right)\right) = 0 \land \left(\left(0 < \operatorname{re}\left(phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right)\right)\right) \Rightarrow \operatorname{re}\left(phi\left(\operatorname{g}\left(\right)\right)\right)^{2} + \operatorname{re}\left(phi\left(\operatorname{k}\left(\right)\right)\right)^{2} < \operatorname{re}\left(phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right)\right)\right) \cdot \operatorname{re}\left(phi\left(\operatorname{x}\left(\right)^{2}\right)\right)\right) \land \left(\operatorname{re}\left(phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right)\right)\right) = 0 \Rightarrow \left(phi = 0 \land \operatorname{re}\left(phi\left(\operatorname{g}\left(\right)\right)\right)^{2} + \operatorname{re}\left(phi\left(\operatorname{k}\left(\right)\right)\right)^{2} = \operatorname{re}\left(phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right)\right)\right) \cdot \operatorname{re}\left(phi\left(\operatorname{x}\left(\right)^{2}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Work in M4(Complex). Set eta=(1−i)/sqrt(2), h=diag(1,1,−1,−1), c=diag(1,−1,−1,1), r=c/16. The rows of x are (1,0,1,eta), (0,−1,eta,1), (1,conj(eta),−1,0), (conj(eta),1,0,1). Set z=(x−hxh)/2, k=hc, t=ihz, g=t+r, and J(a,b)=(ab+ba)/2. The central self-adjoint involution is the unit matrix. The displayed h(),x(),r(),c(),z(),k(),t(),g() denote precisely these constants. Every positive complex-linear functional on this same algebra has real readings on x²,k,g. For mass m=Re phi(I)>0 its original readings satisfy the homogeneous strict budget. In particular every normalized state satisfies Re phi(g)²+Re phi(k)²<Re phi(x²). At mass zero the functional is zero and the non-strict budget is equality. Direct multiplication also gives r²=J(z,r)²=I/256, so neither residual vanishes. For P(p,q)=x²+(p²+q²)I−2pk−2qg and f(w)=w⁴+2w²+3, direct expansion gives det P=|f(p−iq)|²+4q²−(q²/32)((p²+q²+3)²+4p²+2)+q⁴/4096. Put s=p²+q². When s≤6 the parenthesized coefficient is at most 107; the q=0 branch uses f(p)>0. When s≥6, the reverse triangle inequality gives |f(p−iq)|≥s²/2, while (s+3)²+4p²+2≤3s². These estimates give det P>0 for every real p,q. The identity det x=3 gives positive definiteness of x², and the connected-family bridge turns this nonvanishing determinant into positive definiteness of every P(p,q).

**Definition 1.4 (The zero-residual implication).**

$$\forall H \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right),\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right),\; \forall R \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right),\; \operatorname{IsHermitian}\left(H\right) \Rightarrow \left(\operatorname{IsHermitian}\left(X\right) \Rightarrow \left(\operatorname{IsHermitian}\left(R\right) \Rightarrow \left(H^{2} = \operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right) \Rightarrow \left(H \cdot R = R \cdot H \Rightarrow \left(\operatorname{Even}\left(H, X\right) \cdot R = R \cdot \operatorname{Even}\left(H, X\right) \Rightarrow \left(\left(\forall phi \in \operatorname{PositiveLinearMap}\left(\operatorname{Complex}\left(\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right), \operatorname{Complex}\left(\right)\right),\; phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right)\right) = 1 \Rightarrow \operatorname{re}\left(phi\left(\operatorname{Response}\left(H, X, R\right)\right)\right)^{2} + \operatorname{re}\left(phi\left(\operatorname{J}\left(H, X\right)\right)\right)^{2} < \operatorname{re}\left(phi\left(X^{2}\right)\right)\right) \Rightarrow R = 0\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The assertion quantifies over all Hermitian H,X,R in the same four-dimensional algebra, with H²=I. Even(H,X)=(X+HXH)/2, J(H,X)=(HX+XH)/2 and Response(H,X,R)=(i/2)(HX−XH)+R. It asks whether commuting R with both H and Even(H,X), together with the strict budget for every normalized positive complex-linear state, forces R=0.

**Theorem 1.5 (The implication fails).**

$$\neg \operatorname{claim}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed table satisfies every premise and its residual square is I/256. It therefore refutes the zero-residual implication. The determinant calculation keeps every noncommutative cross term, and positivity is transported over the entire real parameter plane. This is a fixed-table subsystem refutation. It asserts neither a total original response D nor a complete PB countermodel. The seven external contracts remain outside the conclusion: Hilbert preparations; Born masses and complete menus; correlated tensor sources; CP/Kraus maps and recursive references; whole instruments and environment outputs; histories, returns and counting; dynamics, clocks, energy and common positive hbar. The construction and its synthesis are repository-derived; no historical-priority claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.pencil`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.result`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.strict_budget`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.witness`
