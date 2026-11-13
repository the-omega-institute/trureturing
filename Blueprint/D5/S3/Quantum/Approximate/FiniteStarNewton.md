# Finite-diagonal exact star correction

## Abstract

A finite contractive diagonal corrects a small all-input multiplicative defect to an exact unital complex star-algebra homomorphism.

B and A are unital complex C-star algebras; the norm of the source identity is one. They come with their complete norms, associative multiplication and isometric involutions. J is any finite index type. FiniteDiagonal B J has legs a(j), b(j), product sum a(j)b(j)=1, and algebraic tensor centrality sum (x a(j)) tensor b(j)=sum a(j) tensor (b(j)x) for every x in B. Its norm budget is sum norm(a(j)) norm(b(j))<=1. No completion of the tensor product is used.

For a bounded complex-linear map u, defect(u,x,y)=u(xy)-u(x)u(y). DefectBound u r means norm(defect(u,x,y))<=r norm(x) norm(y) for every x,y. PreservesStar u means u(star(x))=star(u(x)) for every x, exactly. These are global conditions, with no restriction to entries, unitaries or self-adjoint inputs.

**Theorem 1.1 (An exact homomorphism with dimension-free distance).**

$$\forall B \in \operatorname{Type}\left(\right),\; \forall A \in \operatorname{Type}\left(\right),\; \forall J \in \operatorname{Type}\left(\right),\; [\operatorname{CStarAlgebra}\left(B\right)] [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{Fintype}\left(J\right)] [\operatorname{NormOneClass}\left(B\right)] \operatorname{FiniteDiagonal}\left(B, J\right) \to \left(\forall f \in \operatorname{ComplexCLM}\left(B, A\right),\; \forall d \in \operatorname{Real}\left(\right),\; \left(0 \le d \land \left(d \le \frac{1}{32} \land \left(\operatorname{PreservesStar}\left(f\right) \land \left(\operatorname{DefectBound}\left(f, d\right) \land \left\lVert f\left(1\right) - 1 \right\rVert \le \frac{1}{4}\right)\right)\right)\right) \Rightarrow \left(\exists rho \in \operatorname{ComplexStarAlgHom}\left(B, A\right),\; \forall x \in B,\; \left\lVert rho\left(x\right) - f\left(x\right) \right\rVert \le \frac{8 \cdot d}{3} \cdot \left\lVert x \right\rVert\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/FiniteStarNewton.exists_star_hom_close` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The raw correction is w'(x)=sum u(a(j)) defect(u,b(j),x). Its star reflection is star(w'(star(x))); their half sum w is complex-linear and exactly star preserving. The Newton step is u+w. Associativity gives the exact cocycle identity, and tensor centrality identifies its linearized defect. If the defect radius is r, the residual is at most norm(u(1)-1) r+2 r^2. The correction norm is at most norm(u) r.

The C-star identity applied to star(x)x gives norm(f)^2<=norm(f)+d and hence norm(f)<=3/2. In the neighborhood norm(u)<=2 and norm(u(1)-1)<1/2, the unit defect implies norm(u(1)-1)<=2r. The new multiplicative defect is therefore at most 8r^2. This estimate uses the actual associative target multiplication.

The prescribed orbit starts at f. Its numerical radii satisfy r(0)=d and r(k+1)=8r(k)^2. Simultaneous induction proves exact linearity and star preservation, defect at most r(k), r(k)<=d/4^k, and norm(u(k)-f)<=(8d/3)(1-4^(-k)). The resulting norm and unit neighborhoods close together. Its increments are at most 2d/4^k, so the orbit converges in operator norm.

Continuous evaluation, multiplication and star pass to the limit. Vanishing defect gives exact multiplication. The limit's value at one is an idempotent within distance one third of one, which forces it to be one. No polar correction or later normalization changes the distance estimate. Only the defect contracts; uniqueness and contraction of the map-valued Newton operator are not conclusions.

Finite averaging and correction are motivated by arXiv:2405.02434v2. The constants 1/32, 1/4 and 8/3 are the sufficient constants in the displayed construction. This statement is conditional on an actual finite contractive diagonal and makes no literature originality or full-corner realization claim.

## References

- Truth anchor: `D5/S3/Quantum/Approximate/FiniteStarNewton.exists_star_hom_close`
