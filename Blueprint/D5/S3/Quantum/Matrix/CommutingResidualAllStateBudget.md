# A commuting residual with a strict budget for every state

## Abstract

A four-dimensional matrix table has a nonzero commuting residual under every positive-state budget.

**Theorem 1.1 (The same table for every positive functional).**

$$\operatorname{IsHermitian}\left(\operatorname{h}\left(\right)\right) \land \left(\operatorname{IsHermitian}\left(\operatorname{x}\left(\right)\right) \land \left(\operatorname{IsHermitian}\left(\operatorname{r}\left(\right)\right) \land \left(\operatorname{h}\left(\right)^{2} = \operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right) \land \left(\operatorname{c}\left(\right) = \operatorname{smul}\left(\frac{1}{2}, \operatorname{x}\left(\right) + \operatorname{h}\left(\right) \cdot \operatorname{x}\left(\right) \cdot \operatorname{h}\left(\right)\right) \land \left(\operatorname{k}\left(\right) = \operatorname{J}\left(\operatorname{h}\left(\right), \operatorname{x}\left(\right)\right) \land \left(\operatorname{t}\left(\right) = \operatorname{smul}\left(\frac{\operatorname{Icomplex}\left(\right)}{2}, \operatorname{h}\left(\right) \cdot \operatorname{x}\left(\right) - \operatorname{x}\left(\right) \cdot \operatorname{h}\left(\right)\right) \land \left(\operatorname{h}\left(\right) \cdot \operatorname{r}\left(\right) = \operatorname{r}\left(\right) \cdot \operatorname{h}\left(\right) \land \left(\operatorname{c}\left(\right) \cdot \operatorname{r}\left(\right) = \operatorname{r}\left(\right) \cdot \operatorname{c}\left(\right) \land \left(\operatorname{r}\left(\right)^{2} = \operatorname{smul}\left(\frac{1}{256}, \operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right)\right) \land \left(\operatorname{J}\left(\operatorname{z}\left(\right), \operatorname{r}\left(\right)\right)^{2} = \operatorname{smul}\left(\frac{1}{256}, \operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right)\right) \land \left(\forall phi \in \operatorname{PositiveLinearMap}\left(\operatorname{Complex}\left(\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right), \operatorname{Complex}\left(\right)\right),\; \operatorname{im}\left(phi\left(\operatorname{x}\left(\right)^{2}\right)\right) = 0 \land \left(\operatorname{im}\left(phi\left(\operatorname{k}\left(\right)\right)\right) = 0 \land \left(\operatorname{im}\left(phi\left(\operatorname{g}\left(\right)\right)\right) = 0 \land \left(\left(0 < \operatorname{re}\left(phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right)\right)\right) \Rightarrow \operatorname{re}\left(phi\left(\operatorname{g}\left(\right)\right)\right)^{2} + \operatorname{re}\left(phi\left(\operatorname{k}\left(\right)\right)\right)^{2} < \operatorname{re}\left(phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right)\right)\right) \cdot \operatorname{re}\left(phi\left(\operatorname{x}\left(\right)^{2}\right)\right)\right) \land \left(\operatorname{re}\left(phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right)\right)\right) = 0 \Rightarrow \left(phi = 0 \land \operatorname{re}\left(phi\left(\operatorname{g}\left(\right)\right)\right)^{2} + \operatorname{re}\left(phi\left(\operatorname{k}\left(\right)\right)\right)^{2} = \operatorname{re}\left(phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right)\right)\right) \cdot \operatorname{re}\left(phi\left(\operatorname{x}\left(\right)^{2}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Work in M4(Complex). Set eta=(1−i)/sqrt(2), h=diag(1,1,−1,−1), c=diag(1,−1,−1,1), r=c/16. The rows of x are (1,0,1,eta), (0,−1,eta,1), (1,conj(eta),−1,0), (conj(eta),1,0,1). Set z=(x−hxh)/2, k=hc, t=ihz, g=t+r, and J(a,b)=(ab+ba)/2. The central self-adjoint involution is the unit matrix. The displayed h(),x(),r(),c(),z(),k(),t(),g() denote precisely these constants. Every positive complex-linear functional on this same algebra has real readings on x²,k,g. For mass m=Re phi(I)>0 its original readings satisfy the homogeneous strict budget. In particular every normalized state satisfies Re phi(g)²+Re phi(k)²<Re phi(x²). At mass zero the functional is zero and the non-strict budget is equality. Direct multiplication also gives r²=J(z,r)²=I/256, so neither residual vanishes.

**Definition 1.2 (The zero-residual implication).**

$$\forall H \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right),\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right),\; \forall R \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right),\; \operatorname{IsHermitian}\left(H\right) \Rightarrow \left(\operatorname{IsHermitian}\left(X\right) \Rightarrow \left(\operatorname{IsHermitian}\left(R\right) \Rightarrow \left(H^{2} = \operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right) \Rightarrow \left(H \cdot R = R \cdot H \Rightarrow \left(\operatorname{Even}\left(H, X\right) \cdot R = R \cdot \operatorname{Even}\left(H, X\right) \Rightarrow \left(\left(\forall phi \in \operatorname{PositiveLinearMap}\left(\operatorname{Complex}\left(\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right), \operatorname{Complex}\left(\right)\right),\; phi\left(\operatorname{one}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \operatorname{Complex}\left(\right)\right)\right)\right) = 1 \Rightarrow \operatorname{re}\left(phi\left(\operatorname{Response}\left(H, X, R\right)\right)\right)^{2} + \operatorname{re}\left(phi\left(\operatorname{J}\left(H, X\right)\right)\right)^{2} < \operatorname{re}\left(phi\left(X^{2}\right)\right)\right) \Rightarrow R = 0\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The assertion quantifies over all Hermitian H,X,R in the same four-dimensional algebra, with H²=I. Even(H,X)=(X+HXH)/2, J(H,X)=(HX+XH)/2 and Response(H,X,R)=(i/2)(HX−XH)+R. It asks whether commuting R with both H and Even(H,X), together with the strict budget for every normalized positive complex-linear state, forces R=0.

**Theorem 1.3 (The implication fails).**

$$\neg \operatorname{claim}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed table satisfies every premise and its residual square is I/256. It therefore refutes the zero-residual implication. The determinant calculation keeps every noncommutative cross term, and positivity is transported over the entire real parameter plane. This is a fixed-table subsystem refutation. It asserts neither a total original response D nor a complete PB countermodel. The seven external contracts remain outside the conclusion: Hilbert preparations; Born masses and complete menus; correlated tensor sources; CP/Kraus maps and recursive references; whole instruments and environment outputs; histories, returns and counting; dynamics, clocks, energy and common positive hbar. The construction and its synthesis are repository-derived; no historical-priority claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.result`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.witness`
- Dependency: [D5/S3/Quantum/Matrix/NonsingularPencilStateBudget](NonsingularPencilStateBudget.md)
