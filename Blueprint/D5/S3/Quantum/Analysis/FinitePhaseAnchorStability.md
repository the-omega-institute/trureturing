# Finite Phase Anchor Stability

## Abstract

The literal finite common-phase probes bound the genuine real Hilbert operator error, with positive contraction and simultaneous finite-menu preservation.

Let V be a finite real Hilbert space of dimension 2d, with d>=1, equipped with an orthogonal complex structure J and an exact quadratic effect readout. The finite phase comparisons below control a compatible repaired effect. The exact quadratic representation is an assumption; approximate comparison of these probes does not replace it by an approximate representation.

V is any complete real inner product space, with its given norm. An orthonormal basis b indexed by Fin(d) disjoint-union Fin(d) fixes its real dimension to 2d. Write e(i)=b(inl(i)) and f(i)=b(inr(i)); J is a continuous real linear operator, J(Jx)=-x, J*= -J, and J(e(i))=f(i). These assumptions also give J(f(i))=-e(i). The star is the genuine real Hilbert adjoint. Completeness and continuity add no restriction in the source finite dimension.

**Definition 1.1 (Real effect readout).**

$$\forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{NormedAddCommGroup}\left(V\right)][\operatorname{InnerProductSpace}\left(\operatorname{Real}\left(\right), V\right)]\forall A \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), V, V\right),\; \forall x \in V,\; \operatorname{weight}\left(A, x\right) = \langle x,A\left(x\right)\rangle_{\mathbb{R}}$$

*Formalization.* `D5/S3/Quantum/Analysis/FinitePhaseAnchorStability.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every continuous real linear operator A and every x in V, weight(A,x) is the source real quadratic readout g(x,Ax).

**Definition 1.2 (True adjoint conjugation).**

$$\forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{NormedAddCommGroup}\left(V\right)][\operatorname{InnerProductSpace}\left(\operatorname{Real}\left(\right), V\right)][\operatorname{CompleteSpace}\left(V\right)]\forall J \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), V, V\right),\; \forall A \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), V, V\right),\; \operatorname{phaseConjugate}\left(J, A\right) = J^{*}\circ A\circ J$$

*Formalization.* `D5/S3/Quantum/Analysis/FinitePhaseAnchorStability.phaseConjugate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The conjugation is J* composed with A composed with J. Since J*=-J, replacing J* by J would reverse the required sign.

**Definition 1.3 (Common-complex effect repair).**

$$\forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{NormedAddCommGroup}\left(V\right)][\operatorname{InnerProductSpace}\left(\operatorname{Real}\left(\right), V\right)][\operatorname{CompleteSpace}\left(V\right)]\forall J \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), V, V\right),\; \forall A \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), V, V\right),\; \operatorname{repair}\left(J, A\right) = \frac{1}{2} \cdot \left(A + \operatorname{phaseConjugate}\left(J, A\right)\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/FinitePhaseAnchorStability.repair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real-linear map E(A)=repair(J,A) is the average (A+J*AJ)/2. Complex linearity is a conclusion of the theorem.

**Definition 1.4 (Literal ordered unit probes).**

$$\forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{NormedAddCommGroup}\left(V\right)][\operatorname{InnerProductSpace}\left(\operatorname{Real}\left(\right), V\right)]\forall d \in \operatorname{Nat}\left(\right),\; \forall b \in \operatorname{OrthonormalBasis}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \operatorname{Real}\left(\right), V\right),\; \forall J \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), V, V\right),\; \forall A \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), V, V\right),\; \forall epsilon \in \operatorname{Real}\left(\right),\; \operatorname{AnchorErrors}\left(b, J, A, epsilon\right) \Leftrightarrow \left(\left(\forall i \in \operatorname{Fin}\left(d\right),\; \lvert\operatorname{weight}\left(A, b\left(\operatorname{inl}\left(i\right)\right)\right) - \operatorname{weight}\left(A, J\left(b\left(\operatorname{inl}\left(i\right)\right)\right)\right)\rvert \le epsilon\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(d\right),\; \forall k \in \operatorname{Fin}\left(d\right),\; i < k \Rightarrow \lvert\operatorname{weight}\left(A, \frac{1}{\operatorname{sqrt}\left(2\right)} \cdot \left(b\left(\operatorname{inl}\left(i\right)\right) + b\left(\operatorname{inl}\left(k\right)\right)\right)\right) - \operatorname{weight}\left(A, J\left(\frac{1}{\operatorname{sqrt}\left(2\right)} \cdot \left(b\left(\operatorname{inl}\left(i\right)\right) + b\left(\operatorname{inl}\left(k\right)\right)\right)\right)\right)\rvert \le epsilon\right) \land \left(\forall i \in \operatorname{Fin}\left(d\right),\; \forall k \in \operatorname{Fin}\left(d\right),\; i \le k \Rightarrow \lvert\operatorname{weight}\left(A, \frac{1}{\operatorname{sqrt}\left(2\right)} \cdot \left(b\left(\operatorname{inl}\left(i\right)\right) + b\left(\operatorname{inr}\left(k\right)\right)\right)\right) - \operatorname{weight}\left(A, J\left(\frac{1}{\operatorname{sqrt}\left(2\right)} \cdot \left(b\left(\operatorname{inl}\left(i\right)\right) + b\left(\operatorname{inr}\left(k\right)\right)\right)\right)\right)\rvert \le epsilon\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/FinitePhaseAnchorStability.AnchorErrors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The families are the axis probes e(i), the real bridges (e(i)+e(k))/sqrt(2) for i<k, and the mixed bridges (e(i)+f(k))/sqrt(2) for i<=k. They are all unit vectors by orthonormality. In particular, the diagonal mixed probes are present. The real bridge family and off-diagonal mixed family are empty for d=1. No upper small-error assumption is imposed. The axis family is nonempty because d>=1 and implies epsilon>=0.

**Theorem 1.5 (Finite anchors control the Euclidean operator error and preserve menus).**

$$\forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{NormedAddCommGroup}\left(V\right)][\operatorname{InnerProductSpace}\left(\operatorname{Real}\left(\right), V\right)][\operatorname{CompleteSpace}\left(V\right)]\forall d \in \operatorname{Nat}\left(\right),\; 1 \le d \Rightarrow \left(\forall b \in \operatorname{OrthonormalBasis}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \operatorname{Real}\left(\right), V\right),\; \forall J \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), V, V\right),\; \left(\left(\forall x \in V,\; J\left(J\left(x\right)\right) = -x\right) \land \left(J^{*} = -J \land \left(\forall i \in \operatorname{Fin}\left(d\right),\; J\left(b\left(\operatorname{inl}\left(i\right)\right)\right) = b\left(\operatorname{inr}\left(i\right)\right)\right)\right)\right) \Rightarrow \left(\left(\forall A \in \operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), V, V\right),\; \left(\operatorname{IsPositive}\left(A\right) \land \operatorname{IsPositive}\left(1 - A\right)\right) \Rightarrow \left(\forall epsilon \in \operatorname{Real}\left(\right),\; \operatorname{AnchorErrors}\left(b, J, A, epsilon\right) \Rightarrow \left(\operatorname{IsPositive}\left(\operatorname{repair}\left(J, A\right)\right) \land \left(\operatorname{IsPositive}\left(1 - \operatorname{repair}\left(J, A\right)\right) \land \left(\left\lVert \operatorname{repair}\left(J, A\right) \right\rVert \le 1 \land \left(\left(\forall x \in V,\; \operatorname{repair}\left(J, A\right)\left(J\left(x\right)\right) = J\left(\operatorname{repair}\left(J, A\right)\left(x\right)\right)\right) \land \left(\left\lVert A - \operatorname{repair}\left(J, A\right) \right\rVert \le \operatorname{min}\left(\frac{1}{2}, \left(2 \cdot d - 1\right) \cdot epsilon\right) \land \left(\left(\forall x \in V,\; \langle J\left(x\right),\operatorname{repair}\left(J, A\right)\left(x\right)\rangle_{\mathbb{R}} = 0\right) \land \left(\forall x \in V,\; \lvert\operatorname{weight}\left(A, x\right) - \operatorname{weight}\left(\operatorname{repair}\left(J, A\right), x\right)\rvert \le \operatorname{min}\left(\frac{1}{2}, \left(2 \cdot d - 1\right) \cdot epsilon\right) \cdot \left\lVert x \right\rVert^{2}\right)\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\forall iota \in \operatorname{Type}\left(w\right),\; [\operatorname{Fintype}\left(iota\right)]\forall menu \in iota\to\operatorname{ContinuousLinearMap}\left(\operatorname{Real}\left(\right), V, V\right),\; \sum_{i}menu\left(i\right) = 1 \Rightarrow \sum_{i}\operatorname{repair}\left(J, menu\left(i\right)\right) = 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/FinitePhaseAnchorStability.finite_phase_anchor_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full telescope is: V in any universe, NormedAddCommGroup V, InnerProductSpace Real V, CompleteSpace V; a natural d with 1<=d; b an OrthonormalBasis (Fin d disjoint-union Fin d) Real V; and J a ContinuousLinearMap Real V V satisfying the three displayed J conditions. The conclusion conjoins the universal individual-effect statement and the universal finite-menu identity. In the individual statement, A is any continuous real linear operator, both A and I-A are positive in mathlib's self-adjoint positive-operator sense, epsilon is any real number, and AnchorErrors is exactly the preceding formula. In the menu identity, iota is any Type with a Fintype instance; no nonemptiness or positivity is needed for that linear identity.

Every norm of an operator is the continuous real Hilbert operator norm induced by g. A and A-E need only be real-linear. There is no matrix norm instance in the proof. The orthonormal basis expansion, the existing symmetric quadratic row inequality, and mathlib's Rayleigh-quotient norm characterization connect the finite coefficients to this genuine Euclidean norm.

Set D=A-J*AJ. Its e/e block is S, its e/f and f/e blocks are the same symmetric T, and its f/f block is -S. Axis probes bound the diagonal of S by epsilon. Real bridges bound off-diagonal S by 2 epsilon. Mixed bridges bound off-diagonal T by 2 epsilon and diagonal T by epsilon because the two S diagonal terms cancel. Self-adjoint symmetry supplies the omitted index orders. Each row has two diagonal-sized contributions and 2d-2 remaining contributions, hence absolute sum at most (4d-2)epsilon. Applying the reused quadratic row estimate and Rayleigh theorem gives norm(D)<=(4d-2)epsilon. The identity A-E=D/2 gives the dimension-dependent bound.

Positivity of A and its conjugate, with both complements positive, bounds every quadratic value of D between minus norm(x)^2 and norm(x)^2. The same Rayleigh theorem gives norm(D)<=1, yielding the independent cap 1/2. This argument includes epsilon=0 and d=1 without division by epsilon or by an off-diagonal count.

Positive averaging uses mathlib's IsPositive.adjoint_conj, add and nonnegative scalar multiplication. J*J=I makes the map unital. The repaired operator commutes with J and is therefore complex-linear for the inherited action (r+is)x=rx+sJx. Its real self-adjointness together with commutation makes it self-adjoint for the source complex inner product g(x,y)+i g(Jx,y), positive, and a contraction. The displayed vanishing imaginary expectation identifies weight(E,x) with the source complex expectation. The Cauchy-Schwarz readout estimate uses the same operator norm.

For any finite family with sum A(i)=I, linearity and unitality give sum E(A(i))=I. Applying the individual universal statement to each positive real effect gives all individual bounds simultaneously, with no menu-cardinality factor. The norm of E is at most one because E and I-E are positive; the theorem records those exact effect inequalities.

This is a source-specific formal synthesis using existing norm and positivity results. It makes no claim of literature novelty, optimal constants, supplied experimental control, or modification of an actual successor. The exact real effect representation, common reference, and preparation/measurement supply remain inherited assumptions.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/FinitePhaseAnchorStability.AnchorErrors`
- Truth anchor: `D5/S3/Quantum/Analysis/FinitePhaseAnchorStability.finite_phase_anchor_repair`
- Truth anchor: `D5/S3/Quantum/Analysis/FinitePhaseAnchorStability.phaseConjugate`
- Truth anchor: `D5/S3/Quantum/Analysis/FinitePhaseAnchorStability.repair`
- Truth anchor: `D5/S3/Quantum/Analysis/FinitePhaseAnchorStability.weight`
