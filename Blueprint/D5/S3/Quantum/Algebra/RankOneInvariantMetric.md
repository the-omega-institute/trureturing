# Rank-One Centralizers in Real Metric Lie Algebras

## Abstract

A positive invariant metric and a centralizer line force dimension one or three.

**Theorem 1.1 (An orthonormal frame at the minimum positive frequency).**

$$\forall L: \operatorname{Type},\ [\operatorname{NormedAddCommGroup}\left(L\right)],\ [\operatorname{InnerProductSpace}\left(\mathbb{R}, L\right)],\ [\operatorname{FiniteDimensional}\left(\mathbb{R}, L\right)],\ br: \operatorname{LinearMap}\left(\mathbb{R}, L, \operatorname{LinearMap}\left(\mathbb{R}, L, L\right)\right),\ a: L,\ ((\forall z: L,\ br(z,z)=0) \land (\forall x,y,z: L,\ br(x,br(y,z))=br(br(x,y),z)+br(y,br(x,z))) \land \operatorname{norm}\left(a\right)=1 \land (\forall x,y,z: L,\ \operatorname{inner}\left(br(x,y), z\right)=-\operatorname{inner}\left(y, br(x,z)\right)) \land (\forall z: L,\ br(a,z)=0 \Rightarrow \exists c: \mathbb{R},\ z=c\cdot a) \land br(a)\neq 0) \Rightarrow \exists m: \mathbb{R},\ \exists u,v: L,\ 0<m \land \operatorname{norm}\left(u\right)=1 \land \operatorname{norm}\left(v\right)=1 \land \operatorname{inner}\left(a, u\right)=0 \land \operatorname{inner}\left(a, v\right)=0 \land \operatorname{inner}\left(u, v\right)=0 \land br(a,u)=m\cdot v \land br(a,v)=-m\cdot u \land br(u,v)=m\cdot a \land (\forall q: \mathbb{R},\ \forall x: L,\ 0<q \land x\neq 0 \land br(a,br(a,x))=-q^{2}\cdot x \Rightarrow m\leq q)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/RankOneInvariantMetric.min_frame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L be a finite-dimensional real inner product space and br a bilinear operation on L. Assume br(z,z)=0 and the derivation identity br(x,br(y,z))=br(br(x,y),z)+br(y,br(x,z)) for every x,y,z. Fix a unit vector a. Assume the inner product is invariant, in the precise form inner(br(x,y),z)=-inner(y,br(x,z)), that every z with br(a,z)=0 is a real multiple of a, and that the linear map br(a) is nonzero.

There are a positive real number m and unit vectors u,v such that a,u,v are pairwise orthogonal, br(a,u)=m v, br(a,v)=-m u, and br(u,v)=m a. Moreover, m is the least positive rotation frequency: for every positive real q and every nonzero x with br(a,br(a,x))=-(q squared)x, one has m at most q. The finite spectral decomposition supplies a minimum positive frequency and a unit eigenvector; invariance, the derivation identity and the centralizer condition determine the third bracket.

**Theorem 1.2 (The dimension dichotomy).**

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
- Truth anchor: `D5/S3/Quantum/Algebra/RankOneInvariantMetric.min_frame`
- Dependency: [D5/S3/QuadraticForms/PositiveDefiniteWilliamson](../../QuadraticForms/PositiveDefiniteWilliamson.md)
