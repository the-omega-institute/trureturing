# A nearby trace in the original Hilbert metric

## Abstract

An associative finite complex C-star algebra close to an original Hilbert product has a nearby faithful trace on the same vector space.

**Theorem 1.1 (One trace and its positive Hermitian form).**

$$\forall A \in \operatorname{FiniteDimensionalNontrivialComplexCStarAlgebra}\left(\right),\; \forall B \in \operatorname{PositiveHermitianCore}\left(A\right),\; \forall mu \in \operatorname{ComplexBilinearProduct}\left(A\right),\; \forall M \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall d \in \operatorname{Real}\left(\right),\; \operatorname{OriginalHilbertProductBounds}\left(A, B, mu, M, q, d\right) \Rightarrow \left(\exists t \in \operatorname{ComplexLinearFunctional}\left(A\right),\; \exists Bt \in \operatorname{PositiveHermitianCore}\left(A\right),\; \operatorname{t}\left(1\right) = 1 \land \left(\left(\forall x \in A,\; \forall y \in A,\; \operatorname{t}\left(x \cdot y\right) = \operatorname{t}\left(y \cdot x\right)\right) \land \left(\left(\forall x \in A,\; \operatorname{t}\left(\operatorname{star}\left(x\right)\right) = \operatorname{star}\left(\operatorname{t}\left(x\right)\right)\right) \land \left(\left(\forall x \in A,\; \left\lVert \operatorname{t}\left(x\right) - \operatorname{B}\left(1, x\right) \right\rVert \le 8 \cdot M \cdot q \cdot \operatorname{p}\left(x\right)\right) \land \left(\left(\forall x \in A,\; \forall y \in A,\; \operatorname{Bt}\left(x, y\right) = \operatorname{t}\left(\operatorname{star}\left(x\right) \cdot y\right)\right) \land \left(\operatorname{Bt}\left(1, 1\right) = 1 \land \left(\left(\forall x \in A,\; \forall y \in A,\; \left\lVert \operatorname{Bt}\left(x, y\right) - \operatorname{B}\left(x, y\right) \right\rVert \le 17 \cdot M \cdot M \cdot q \cdot \operatorname{p}\left(x\right) \cdot \operatorname{p}\left(y\right)\right) \land \left(\forall a \in A,\; \forall x \in A,\; \forall y \in A,\; \operatorname{Bt}\left(a \cdot x, y\right) = \operatorname{Bt}\left(x, \operatorname{star}\left(a\right) \cdot y\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/OriginalHilbertTrace.nearby_faithful_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A is a nontrivial finite-dimensional unital complex C-star algebra with its supplied associative product, involution and C-star norm. B is an arbitrary positive definite Hermitian inner product on the same complex vector space. Write p(x)=sqrt(Re B(x,x)) for its original Hilbert norm. The C-star norm is used for the compact topology of the actual unitary group; p is used for every perturbation estimate. Neither norm is identified with the other.

The original unit e is the element 1 of the supplied algebra, and B(1,1)=1. Its involution is isometric for p, hence an isometric antilinear involution for the original metric. The original product mu is complex bilinear, has right unit 1, and satisfies B(mu(x,y),z)=B(y,mu(star(x),z)) for all x,y,z. Thus the theorem also applies when mu has the two-sided unit and star compatibility of the original setup. Assume M>=1, 0<=q<1 and 0<=d<=1/8. For all x,y assume p(mu(x,y))<=M p(x)p(y) and p(xy-mu(x,y))<=q p(x)p(y). For every actual unitary u of the supplied associative algebra assume p(u)<=1+2d.

There are one complex-linear functional t and one positive definite Hermitian form Bt on that same full vector space. They satisfy t(1)=1, t(xy)=t(yx), t(star(x))=conj(t(x)), and Bt(x,y)=t(star(x)y) for every x,y. In particular t is positive and faithful: t(star(x)x) is a nonnegative real number and is strictly positive for x nonzero. Bt(1,1)=1 and Bt(ax,y)=Bt(x,star(a)y) for every a,x,y. All of these conclusions use the same t and Bt.

With tau(x)=B(1,x), the original dual estimate is abs(t(x)-tau(x))<=8 M q p(x) for every x. The same trace form satisfies abs(Bt(x,y)-B(x,y))<=17 M^2 q p(x)p(y) for all x,y. The pointwise dual inequality is precisely the operator norm bound on the original Hilbert dual; no C-star dual norm is substituted.

The unit and adjoint identity give tau(mu(x,y))=B(star(x),y). Polarization of the original isometric antilinear involution makes this symmetric in x,y. Consequently abs(tau(xy-yx))<=2q p(x)p(y) and Re tau(star(x)x)>=(1-q)p(x)^2. In particular tau is a faithful positive unital functional on the supplied associative algebra.

Define t(x) by integrating tau(star(u)xu) over normalized Haar measure on the actual compact unitary group. Left translation makes t invariant under unitary conjugation. For a unitary u, apply this invariance to ux to obtain t(ux)=t(xu). Every element is a complex linear combination of four actual unitaries by Mathlib's CStarAlgebra.exists_sum_four_unitary, so complex linearity gives the full trace identity. Pointwise positivity and positivity of Haar measure near the identity prove faithfulness.

Associativity gives (xu)star(u)=x. Applying the commutator estimate to star(u) and xu bounds the integrand difference by 2q(M+q)(1+2d)^2 p(x), which is at most 8Mq p(x). Combining this with the bilinear product error gives q+8Mq(M+q)<=17M^2q for the form difference. This is a conditional trace and form construction. It does not construct the associative product, a unit-fixing metric transport, or a transported product on the original Hilbert metric, and asserts no physical realization.

## References

- Truth anchor: `D5/S3/Quantum/Approximate/OriginalHilbertTrace.nearby_faithful_trace`
