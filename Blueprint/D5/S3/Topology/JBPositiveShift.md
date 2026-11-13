# Positive square shifts in the original JB norm

## Abstract

Positive shifts of squares in a complete real JB algebra have inverses in the original singly generated algebra, with inverse norm at most the reciprocal shift and bijective quadratic representations on the whole ambient space.

Let X be a real normed vector space, S its specified real bilinear product, and u its specified unit. Data(X,S,u) means precisely symmetry, the unit law, the Jordan identity, norm(S(x,y))<=norm(x)norm(y), norm(S(x,x))=norm(x)^2, and norm(S(x,x))<=norm(S(x,x)+S(y,y)). Write C(a) for the norm-closed real span of the natural powers of a, with zeroth power u. Every norm and closure is the original one. Write U(a,v)=2 S(a,S(a,v))-S(S(a,a),v), and U(a) for this map on all of X.

**Theorem 1.1 (The ambient fundamental identity).**

$$\forall X \in RealNormedSpaces,\; \forall S \in RealBilinearMaps\left(X\right),\; \forall u \in X,\; Data\left(X, S, u\right) \Rightarrow \left(\forall a \in X,\; \forall b \in X,\; \forall v \in X,\; U\left(U\left(a, b\right), v\right) = U\left(a, U\left(b, U\left(a, v\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/JBPositiveShift.fundamental_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polarized Jordan commutator identity is applied to products of a, b and v and inside multiplication contexts. Its real linear consequences give U(U(a,b),v)=U(a,U(b,U(a,v))). This algebraic identity uses no completeness, dimension, positivity or special representation hypothesis. Evaluating it at the unit gives the square transport identity S(U(c,a),U(c,a))=U(c,U(a,S(c,c))); it does not assert that U(c) preserves squares.

**Theorem 1.2 (Generated inverse with the original norm bound).**

$$\forall X \in RealNormedSpaces,\; \forall S \in RealBilinearMaps\left(X\right),\; \forall u \in X,\; Data\left(X, S, u\right) \Rightarrow \left(Complete\left(X\right) \Rightarrow \left(\forall z \in X,\; \forall t \in Reals,\; 0 < t \Rightarrow \left(\exists b \in X,\; mem\left(b, C\left(S\left(z, z\right)\right)\right) \land \left(S\left(S\left(z, z\right) + scale\left(t, u\right), b\right) = u \land norm\left(b\right) \le inverse\left(t\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/JBPositiveShift.positive_shift_generated_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume X complete. For x in C(z), associativity gives S(S(z,x),S(z,x))=S(S(S(z,z),x),x). Apply square monotonicity to sqrt(t)x and S(z,x), and then product norm domination. Cancel norm(x), treating x=0 separately, to obtain t norm(x)<=norm(S(S(z,z)+t u,x)). Powers of S(z,z) belong to C(z), so this also holds on C(S(z,z)).

On the complete closed subspace C(S(z,z)), let B be left multiplication by S(z,z). For a unit w=B+sI, the lower bound gives norm(w inverse)<=1/s. A Neumann series makes B+sI invertible when s>norm(B). Fix t>0 and choose a natural n with t+n t>norm(B). At each of the finitely many downward steps from t+(k+1)t to t+k t, norm(t w inverse)<1; multiplying w by the corresponding Neumann unit gives the next inverse. Natural-number induction reaches B+tI. Its inverse applied to u supplies b in C(S(z,z)). The lower bound and norm(u)<=1 give norm(b)<=1/t, also when X is the zero space.

**Theorem 1.3 (An actual inverse on the whole ambient carrier).**

$$\forall X \in RealNormedSpaces,\; \forall S \in RealBilinearMaps\left(X\right),\; \forall u \in X,\; Data\left(X, S, u\right) \Rightarrow \left(Complete\left(X\right) \Rightarrow \left(\forall z \in X,\; \forall t \in Reals,\; 0 < t \Rightarrow Bijective\left(U\left(S\left(z, z\right) + scale\left(t, u\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/JBPositiveShift.positive_shift_quadratic_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put a=S(z,z)+t u and take the generated inverse b just constructed. Both a and b lie in the associative algebra C(z), so U(a,S(b,b))=u. The ambient fundamental identity then gives U(a) U(S(b,b)) U(a)=I on every vector in X. This identity gives both injectivity and surjectivity of U(a), without a Peirce decomposition or a change of carrier.

These are classical Jordan and Banach algebra consequences; no literature novelty is claimed. The generated inverse theorem proves the square-to-positive-shift direction and its reciprocal norm bound. It does not prove the converse characterization of squares by positive shifts, positivity of every quadratic representation, square-cone closedness, the positive interior/bijectivity criterion, a boundary kernel vector, the uniform bound in terms of an unshifted inverse, or the response support and closure statements of the original application. In particular, no quotient response, continuity of the response, special C* representation, or physical preparation follows.

## References

- Truth anchor: `D5/S3/Topology/JBPositiveShift.fundamental_identity`
- Truth anchor: `D5/S3/Topology/JBPositiveShift.positive_shift_generated_inverse`
- Truth anchor: `D5/S3/Topology/JBPositiveShift.positive_shift_quadratic_bijective`
- Dependency: [D5/S3/Topology/JBAlgebra](JBAlgebra.md)
