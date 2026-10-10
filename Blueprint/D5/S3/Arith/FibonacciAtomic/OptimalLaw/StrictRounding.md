# Strict Dyadic Rounding of Optimal Laws

## Abstract

Every atom above the minimum of an attaining real law has a least dyadic depth and strict rounding.

RealVector(m) denotes the real functions on Fin m. The parameter m is natural; p is a real vector on Fin m and k is an index of its least mass. Optimizer(m,p,k) means m>=2, every coordinate is positive, their sum is one, p(k)<=p(i) for every i, and L(p)/p(k)=alpha(m). The optimization domain includes every such real law. F(x,d) is floor(2^d x), L is its dyadic residual cost, and b(x,D)=F(x,D)-2F(x,D-1).

Write delta=2^(-D), R(p,d)=2^d-sum_i F(p(i),d), and L(p)=sum_d R(p,d)/2^d.

**Theorem 1.1 (Coarser prefixes survive a donor debit).**

$$\forall x \in \mathbb{R}, \forall D \in \mathbb{N}, (1 \le D \land \operatorname{b}\left(x,D\right) = 1) \to \forall d \in \mathbb{N}, (d < D) \to \operatorname{F}\left(x - \frac{1}{2^{D}},d\right) = \operatorname{F}\left(x,d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.donor_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the depth-D digit is one, subtracting one depth-D cylinder leaves every earlier floor prefix unchanged. Division of the depth-(D-1) floor by an integer power of two transports this equality to every coarser depth.

ExchangeHyp(m,D,p,q,j,S,t,u) means: m>=2 and D>=1; p and q are nonnegative vectors of total mass one; q(j)=0; t>0 and u>0; for i in S both t<=p(i) and u<=q(i); for i outside S other than j, t+delta*u<=p(i); the donor satisfies t+delta*(1+u)<=p(j); L(p)=alpha(m)*t and L(q)<alpha(m)*u. Here alpha is the infimum of L divided by the smallest coordinate over all positive normalized real laws.

## An optimal law has no profitable donor leaf

$$
\forall m \in \mathbb{N}, \forall D \in \mathbb{N}, \forall p \in \operatorname{RealVector}\left(m\right), \forall q \in \operatorname{RealVector}\left(m\right), \forall j \in \operatorname{Fin}\left(m\right), \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right), \forall t \in \mathbb{R}, \forall u \in \mathbb{R}, \operatorname{ExchangeHyp}\left(m,D,p,q,j,S,t,u\right) \to \operatorname{b}\left(\operatorname{p}\left(j\right),D\right) \neq 1
$$

Form P(i)=p(i)+delta*q(i)-delta times the indicator of i=j. Coarser residuals do not increase. At depth D+n the residual is at most R(p,D+n)+R(q,n). Splitting the convergent series into its head and shifted tail gives L(P)<=L(p)+delta*L(q). Simultaneously every coordinate of P is at least t+delta*u. The defining lower bound for alpha(m) then contradicts the strict improvement of the same modified law. The classical dyadic cost expression is recalled by Lumbroso; the common-law comparison is the stated additional relation.

**Definition 1.2 (The least terminating strict round).**

$$\forall x \in \mathbb{R}, \forall t \in \mathbb{R}, \operatorname{DyadicStrictRound}\left(x,t\right) \iff \exists D \in \mathbb{N}, 1 \le D \land \operatorname{OnGrid}\left(x,D\right) \land (\forall d < D, \neg \operatorname{OnGrid}\left(x,d\right)) \land x = \frac{\operatorname{F}\left(t,D\right) + 1}{2^{D}}$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.DyadicStrictRound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

OnGrid(x,D) means that 2^D x is an integer. The displayed depth is positive, is the least depth with this property, and rounds t strictly upward by one integer unit at that depth.

**Definition 1.3 (Every larger coordinate has this form).**

$$\forall m \in \mathbb{N}, \forall p \in \operatorname{RealVector}\left(m\right), \forall k \in \operatorname{Fin}\left(m\right), \operatorname{StrictlyRoundedLaw}\left(m,p,k\right) \iff \forall i \in \operatorname{Fin}\left(m\right), \operatorname{p}\left(k\right) < \operatorname{p}\left(i\right) \to \operatorname{DyadicStrictRound}\left(\operatorname{p}\left(i\right),\operatorname{p}\left(k\right)\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.StrictlyRoundedLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The requirement applies to every coordinate strictly above the least mass.

**Definition 1.4 (Strict upper dyadic round).**

$$\forall t \in \mathbb{R}, \forall D \in \mathbb{N}, \operatorname{round}\left(t,D\right) = \frac{\operatorname{F}\left(t,D\right) + 1}{2^{D}}$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.round` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One is added even when the scaled argument is already integral.

**Definition 1.5 (Dyadic grid membership).**

$$\forall x \in \mathbb{R}, \forall D \in \mathbb{N}, \operatorname{OnGrid}\left(x,D\right) \iff \exists z \in \mathbb{Z}, 2^{D} x = z$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.OnGrid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This predicate allows any real x and natural depth, including depth zero.

**Theorem 1.6 (Grid membership at finer depths).**

$$\forall x \in \mathbb{R}, \forall D \in \mathbb{N}, \forall E \in \mathbb{N}, (D \le E \land \operatorname{OnGrid}\left(x,D\right)) \to \operatorname{OnGrid}\left(x,E\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.grid_up` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the integer numerator by 2^(E-D) preserves grid membership.

LeastGrid(x,D) means D>=1, OnGrid(x,D), and not OnGrid(x,d) for every natural d<D.

**Theorem 1.7 (The final terminating digit is one).**

$$\forall x \in \mathbb{R}, \forall D \in \mathbb{N}, \operatorname{LeastGrid}\left(x,D\right) \to \operatorname{b}\left(x,D\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.least_grid_bit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The floor carry is zero or one. A zero carry at the least terminating depth would place x on the preceding grid.

**Theorem 1.8 (Strict rounding for every attaining real law).**

$$\forall m \in \mathbb{N}, \forall p \in \operatorname{RealVector}\left(m\right), \forall k \in \operatorname{Fin}\left(m\right), \operatorname{Optimizer}\left(m,p,k\right) \to \operatorname{StrictlyRoundedLaw}\left(m,p,k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jeremie Lumbroso (2013). *Optimal Discrete Uniform Generation from Coin Flips, and Applications*. URL: <https://arxiv.org/abs/1304.1916v1>.

*Commentary.*

A nonterminating larger coordinate has arbitrarily deep one digits. A smaller-label optimal receiver, extended by zero to the other labels, can exploit such a digit through a profitable leaf exchange. This contradicts optimality, so every larger coordinate terminates.

Choose a putative failure of strict rounding with greatest least terminating depth. The integer residual and the common floor prefixes on the receiver set leave enough fractional margin for another profitable exchange. This rules out the failure. All comparisons concern one actual law and its modified receiver law.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.DyadicStrictRound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.OnGrid`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.StrictlyRoundedLaw`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.donor_prefix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.grid_up`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.least_grid_bit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.round`
- Dependency: [D5/S1/Digit/RadixFloorDigit](../../../../S1/Digit/RadixFloorDigit.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope](../OptimalLawStrictSlope.md)
