# Orthogonal Projections onto Complementary Subspaces

## Abstract

Complementary orthogonal projections satisfy the six canonical operator identities.

**Theorem 1.1 (Closed-subspace projections obey the complement identities).**

$$\forall k, E: \operatorname{Type},\ [\operatorname{RCLike}(k)],\ [\operatorname{NormedAddCommGroup}(E)],\ [\operatorname{InnerProductSpace}_{k}(E)],\ [\operatorname{CompleteSpace}(E)],\ M: \operatorname{ClosedSubmodule}_{k}(E),\ P_{M^{\perp}} = I - P_{M} \land P_{M} \circ P_{M} = P_{M} \land P_{M^{\perp}} \circ P_{M^{\perp}} = P_{M^{\perp}} \land P_{M} \circ P_{M^{\perp}} = 0 \land P_{M^{\perp}} \circ P_{M} = 0 \land P_{M} + P_{M^{\perp}} = I.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OrthogonalProjectionComplement.orthogonal_complement_projection_identities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M be a closed subspace of a complete real or complex inner-product space, and let P with subscript M denote its orthogonal projection. The projection onto the orthogonal complement is the identity minus P with subscript M.

Both projections are idempotent. Their compositions vanish in both orders, and their sum is the identity operator. These are all six equalities in the named statement, retained as one conjunction.

Loogle and the pinned Mathlib tree supplied the exact complementary, idempotence, orthogonality, and sum declarations used by the Lean proof. The LeanSearch endpoint attempted for corroboration returned HTTP 404.

Rank-one polynomial compression and the ordinary trace.

For the algebra and analysis step of Lemma 54.2 of zero-dimensional center square-orbit reconstruction, take H=EuclideanSpace(Complex,Fin(n)), n>=2, and arbitrary continuous complex-linear operators T,p on this same H. Require p to be an actual orthogonal projection, expressed by IsStarProjection p, and require the complex dimension of its actual range to equal one. All operator norms here are induced by the Euclidean L2 norm on H. Put lambda=Tr(Tp), with the ordinary unnormalized trace. LinearMap.trace_eq_matrix_trace identifies this with the matrix trace in the standard orthonormal basis; there is no factor 1/n.

The projection hypotheses supply the compression identities rather than assuming them. isStarProjection_iff_eq_starProjection_range identifies p with the orthogonal projection onto its range. Since that range has dimension one, exists_norm_eq and eq_span_singleton_of_mem_of_finrank_eq_one give a unit vector v spanning it. Submodule.starProjection_unit_singleton gives p=rankOne(v,v). InnerProductSpace.comp_rankOne and trace_rankOne then give lambda=<v,Tv>. Consequently pTp=lambda p, norm(p)=1 by norm_rankOne, and abs(lambda)<=norm(T) by Cauchy-Schwarz and the operator norm bound. In particular (T-lambda I)p=(I-p)Tp. The vector is selected separately at each point; no continuity or global frame is required.

Suppose norm(T)<=M0 with M0>0, and put S=lambda I. Scalar multiplication commutes with T, S^n=lambda^n I, and norm(S)<=M0. The existing Commute.geom_sum₂_mul factorization, multiplied on the right by p, is (T^n-lambda^n I)p=A((I-p)Tp), where A=sum(i=0,...,n-1) T^i S^(n-1-i). For each summand, submultiplicativity and norm_pow_le give norm(T^i S^(n-1-i))<=M0^i M0^(n-1-i)=M0^(n-1). The triangle inequality therefore gives norm(A)<=n M0^(n-1), and hence norm((T^n-lambda^n I)p)<=n M0^(n-1) norm((I-p)Tp). The right compression by p is part of this conclusion.

Under the actual identity T^n=czI, with c>0 and abs(z)=1, the left side is norm((cz-lambda^n)p)=abs(cz-lambda^n), because norm(p)=1. Thus abs(cz-lambda^n)<=n M0^(n-1) norm((I-p)Tp). The same proof of this inequality does not need positivity of c or the unit-modulus condition; they retain their stated roles in the circle problem. This is an estimate on the actual compressed operator and the actual scalar error, and supplies no bound on the full operator T^n-lambda^n I.

For any topological parameter space X, let T,p:X->End(H) be continuous in the same operator norm topology, with the projection and range-dimension conditions at every point. Multiplication is continuous, and the linear functional Tr on the finite-dimensional space End(H) is continuous by LinearMap.continuous_of_finiteDimensional. Hence lambda(x)=Tr(T(x)p(x)) is continuous. A common bound norm(T(x))<=M0 and the identities T(x)^n=cz(x)I give the preceding bounds pointwise. This includes the circle with z its inclusion into Complex and uses no selection of a continuous generating vector.

These applications use the pinned Mathlib projection, rank-one, trace, geometric-sum and norm interfaces directly. They introduce no new mathematical declaration. They supply only the algebra and analysis bridge needed before the approximate-root obstruction. Lemma 54.1, the nonexistence conclusion of Lemma 54.2, and the finite-transport conclusion of Theorem 54.3 require their separate winding and geometric arguments; none follows from this estimate alone.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/OrthogonalProjectionComplement.orthogonal_complement_projection_identities`
