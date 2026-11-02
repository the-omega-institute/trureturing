# Born interval fixed-overlap maximum

## Abstract

The exact Born interval defect maximum at prescribed overlap is attained for every allowed overlap.

**Theorem 1.1 (Exact maximum over all actual line pairs).**

$$\forall n \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall c \in \mathbb{R},\; \forall R \in \operatorname{Sub}\left(\mathbb{C}^{n}\right),\; \forall T \in \operatorname{Sub}\left(\mathbb{C}^{n}\right),\; \forall r \in \mathbb{R},\; ((2 \le n) \land ((\operatorname{PosDef}\left(rho\right)) \land ((\operatorname{Tr}\left(rho\right) = 1) \land ((0 \le c) \land ((T \le \operatorname{orthogonal}\left(R\right)) \land ((\operatorname{dim}\left(T\right) = 2) \land ((0 \le r) \land (r < 1)))))))) \Rightarrow (\operatorname{IsGreatest}\left(\operatorname{Defects}\left(rho, c, R, T, r\right), \frac{r(\operatorname{lam}\left(rho, T, 0\right)-\operatorname{lam}\left(rho, T, 1\right))}{c+\operatorname{mu}\left(rho, R\right)+(\operatorname{lam}\left(rho, T, 0\right)+\operatorname{lam}\left(rho, T, 1\right))}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/BornJaccardFixedOverlap.fixed_overlap_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n be at least two, rho a positive-definite Hermitian complex matrix of trace one, c a nonnegative real number, R any complex subspace, and T a two-dimensional subspace of the orthogonal complement of R. Neither R nor T must be invariant under rho. All weights and distances are those of BornJaccardTracialClassification, with this same rho. The operator K is the actual composition of inclusion of T, rho, and orthogonal projection onto T. Its sorted eigenvalues are M=lam(0) and m=lam(1). The theorem derives positivity, m at most M, the identity mu(T)=M+m, and positivity of c+mu(R)+M+m.

For every real r with 0 at most r and r strictly below one, there are unit vectors u,v in T with absolute inner product r. Their ambient lines are the images of their spans under the actual inclusion T into H. Both have dimension one, their intersection is zero, and their sum is T. The original meet-over-join distance defect at R+L, R+T, R+N equals r(M-m)/(c+mu(R)+M+m).

Choose an orthonormal eigenbasis e,f of the actual compression in decreasing eigenvalue order. Set a=sqrt((1+r)/2), b=sqrt((1-r)/2), u=ae+bf and v=ae-bf. Both a and b are strictly positive on the full allowed overlap domain. The two vectors have norm one and inner product exactly r. Their sum and difference recover e and f, while comparison of the e and f coordinates proves their spans disjoint. The two line weights are both (M+m+r(M-m))/2.

Write Defects(rho,c,R,T,r) for the set of real d for which there are ordered complex lines L,N in T, both of dimension one, and unit vectors u in L and v in N with absolute inner product r, such that d is the original interval distance defect at R+map(L), R+T, R+map(N). IsGreatest says both that the displayed value belongs to this set and that every member is at most that value. Thus the statement includes every ordered line pair and simultaneous attainment.

For an arbitrary unit pair with eigenbasis coordinates (a,b) and (z,w), the residual-square identity bounds normSq(a)+normSq(z)-1 by the norm of conj(a)z+conj(b)w. The latter is exactly the prescribed overlap. Spectral expansion makes the numerator of the actual defect equal (M-m)(normSq(a)+normSq(z)-1). Multiplication by M-m and division by the derived positive denominator give the universal upper bound.

For every U contained in T, the actual orthogonal projection onto R+U is the sum of the projections onto R and U. Cyclicity of the trace identifies mu(T) with the real trace of the compression; the inner-product compression identity identifies its quadratic forms with those of rho. The actual interval meet and join therefore give defect (mu(L)+mu(N)-mu(T))/(c+mu(R)+mu(T)). This proves the fixed-overlap maximum in Theorem 2.1 of Born-weighted Jaccard projection geometry. The cases r=0, M=m, and c+mu(R)=0 remain included. This is a repository derivation, with no originality claim.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/BornJaccardFixedOverlap.fixed_overlap_maximum`
- Dependency: [D5/S3/Quantum/Algebra/BornJaccardTracialClassification](BornJaccardTracialClassification.md)
