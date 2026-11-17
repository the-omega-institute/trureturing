# Rank-One Centralizers in Real Metric Lie Algebras

## Abstract

A positive invariant metric and a centralizer line force dimension one or three.

**Theorem 1.1 (The dimension dichotomy).**

$$\forall K: \operatorname{Type},\ [\operatorname{LieRing}\left(K\right)],\ [\operatorname{LieAlgebra}\left(\mathbb{R}, K\right)],\ [\operatorname{FiniteDimensional}\left(\mathbb{R}, K\right)],\ B: \operatorname{InnerProductSpaceCore}\left(\mathbb{R}, K\right),\ a: K,\ (\forall x,y,z:K,\ B([x,y],z)=-B(y,[x,z])) \land a\neq0 \land (\forall z:K,\ [a,z]=0 \Rightarrow \exists c:\mathbb{R},\ z=c\cdot a) \Rightarrow \operatorname{finrank}_{\mathbb{R}}(K)=1 \lor \operatorname{finrank}_{\mathbb{R}}(K)=3$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/RankOneInvariantMetric.finrank_eq_one_or_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be an arbitrary finite-dimensional real Lie algebra. The value B is an InnerProductSpace.Core: its real inner product is positive definite, symmetric and bilinear, with the underlying additive group and real module those of the given Lie algebra. Assume B([x,y],z)=-B(y,[x,z]) for every x,y,z. Let a be nonzero and assume every z commuting with a is a real multiple of a. Since [a,a]=0, this is exactly the assertion that the centralizer of a is its real span. Then the real dimension of K is one or three.

When ad(a) vanishes, the centralizer condition already makes K the span of a. Otherwise normalize a and apply the frozen skew_paired_basis_induction to ad(a) direct-summed with itself on WithLp 2 (K times K). This doubled space has even dimension regardless of the dimension of K. A minimum positive paired frequency and a nonzero original-coordinate component provide a unit vector u. Set v=ad(a)u/mu. Invariance and Jacobi give an orthonormal triple a,u,v with [a,u]=mu v, [a,v]=-mu u and [u,v]=mu a.

The span S of this actual triple is a Lie subalgebra, and its orthogonal complement M in the same K is S-stable. Complexify S and M. The normalized elements h=(2i/mu)a, e=(u+iv)/mu, f=(-u+iv)/mu form an sl2 triple. Mathlib IsSl2Triple.exists_hasPrimitiveVectorWith constructs a primitive vector in every nonzero finite-dimensional complex module. Its existing exists_nat, pow_toEnd_f_ne_zero_of_eq_nat and lie_h_pow_toEnd_f give a nonzero vector of h-weight zero or one. The proof directly applies these results, without reproving the ladder.

Weight zero has real and imaginary parts in the centralizer of a and in S-perp, so both vanish. Weight one has a nonzero real or imaginary part x with ad(a) squared applied to x equal to -(mu/2) squared times x, contradicting minimality of mu. Thus M is zero and S is all of K. The orthonormal triple then gives dimension three. This complement obstruction is the substantive step beyond the reused spectral and sl2 suppliers.

This algebraic theorem supplies the dimension lemma used by the one-point reciprocity argument. To apply it to a compact effective matrix group requires a positive invariant metric on its actual Lie algebra and the derivation of the centralizer line from the entire quotient relation. The original-group exponential bridge, exclusion of the one-dimensional alternative in that application, equality with the orthogonal Lie algebra, identity-component and SO/O classification, and the reverse quotient-relation implication are separate obligations. The dimension lemma alone asserts none of those group conclusions.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/RankOneInvariantMetric.finrank_eq_one_or_three`
- Dependency: [D5/S3/QuadraticForms/PositiveDefiniteWilliamson](../../QuadraticForms/PositiveDefiniteWilliamson.md)
