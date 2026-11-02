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

Coincident-line boundary (Proposition 3.2). Keep the same n, rho, c, R and T throughout. Write S=R+T and E(L)=R+L, with orthogonal sums. For y in T the actual compression is Ky=P(T)(rho y), and a(L) is the real quadratic form of K on any unit generator of L. In the notation of the theorem, M=lam(0), m=lam(1). Put

$$
\begin{aligned}b = c+\operatorname{mu}\left(\rho, R\right)\\s = M+m\\0<m\leq M,\quad0<b+s\end{aligned}
$$

Choose one orthonormal eigenbasis e,f of K with eigenvalues M,m, once for the entire family, also when M=m. For any unit x in T, compression_inner and compression_quadratic identify a(L) with M times the squared modulus of its e coordinate plus m times that of its f coordinate. Those squared moduli sum to one, so m<=a(L)<=M and s-a(L)>=m>0.

For every line L in T, distance_properties gives the zero diagonal and symmetry. Since E(L) is contained in S, the actual meet and join in its distance to S are E(L) and S. The projection and weight identities projection_orthogonal_sup, weight_orthogonal_sup and weight_unit_line give

$$
\begin{aligned}\operatorname{d}\left(\operatorname{E}\left(L\right), S\right) = \frac{s-\operatorname{a}\left(L\right)}{(b+s)}\\\Delta_{c}(\operatorname{E}\left(L\right),S,\operatorname{E}\left(L\right))=-2\operatorname{d}\left(\operatorname{E}\left(L\right), S\right)=-\frac{2(s-\operatorname{a}\left(L\right))}{(b+s)}<0\end{aligned}
$$

Thus this statement covers every coincident pair, not just an eigenline. The disjoint-line hypotheses of interval_inf and interval_defect hold only for distinct lines and are not used at coincidence.

Use the actual simultaneous source family (2.7), with e and f fixed:

$$
\begin{aligned}\alpha = \sqrt{\frac{1+r}{2}}\\\beta = \sqrt{\frac{1-r}{2}}\\\operatorname{u}\left(r\right) = \alpha e+\beta f\\\operatorname{v}\left(r\right) = \alpha e-\beta f\\\operatorname{L}\left(r\right) = \mathbb{C}\operatorname{u}\left(r\right)\\\operatorname{N}\left(r\right) = \mathbb{C}\operatorname{v}\left(r\right)\end{aligned}
$$

For every 0<=r<1 both coefficients are positive, the vectors are unit and their inner product is r. Their lines L(r) and N(r) are distinct, have zero intersection, and span T. These are the explicit vectors in pair_construction used by fixed_overlap_attainment; the choice of eigenbasis does not depend on r. Merely choosing an unrelated maximizer for each r would not identify this limiting line. For either w(r)=u(r) or w(r)=v(r), orthonormality gives

$$
\begin{aligned}\alpha\to1,\quad\beta\to0\\(\Vert \operatorname{w}\left(r\right)-e\Vert)^{2}=(\alpha-1)^{2}+(\beta)^{2}=2(1-\alpha)\to0\end{aligned}
$$

The limits are taken through 0<=r<1 as r tends to one. The continuity of Real.sqrt, scalar multiplication and addition gives these vector limits in the ambient H, using the actual inclusion of T into H.

To identify the topology on lines, let Q(x,y) be the ambient rank-one operator z maps to inner(y,z)x. P(L) denotes the ambient orthogonal projector onto L. For a unit w, starProjection_unit_singleton and InnerProductSpace.rankOne_apply identify P(C w) with Q(w,w). Additivity and conjugate additivity in the two rankOne arguments, the triangle inequality and InnerProductSpace.norm_rankOne give

$$
\begin{aligned}\operatorname{P}\left(\mathbb{C}w\right)-\operatorname{P}\left(\mathbb{C}e\right) = \operatorname{Q}\left(w-e, w\right)+\operatorname{Q}\left(e, w-e\right)\\\Vert \operatorname{P}\left(\mathbb{C}w\right)-\operatorname{P}\left(\mathbb{C}e\right)\Vert\leq2\Vert w-e\Vert\to0\end{aligned}
$$

Consequently both actual line projectors converge in operator norm to P(C e). This proves convergence in the topology of ambient orthogonal projectors, with the same M-eigenline for both families. Also P(E(L(r)))=P(R)+P(L(r)) and likewise for N(r), so both interval elements converge to E(C e) in this topology. The continuity inputs are pinned Mathlib results: Mathlib/Analysis/Real/Sqrt.lean, Mathlib/Topology/Algebra/Module/Basic.lean and Mathlib/Topology/Algebra/Group/Basic.lean; the projector and rankOne identities are in Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean and Mathlib/Analysis/InnerProductSpace/LinearMap.lean. These references use mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679.

For r<1 the explicit weights are a(L(r))=a(N(r))=(s+r(M-m))/2. unit_pair_geometry and interval_defect therefore compute the distinct-pair defect; fixed_overlap_maximum identifies it as the maximum at that overlap. At r=1 both actual lines are C e and a(C e)=M. The preceding coincident calculation gives

$$
\begin{aligned}\Delta_{c}(\operatorname{E}\left(\operatorname{L}\left(r\right)\right),S,\operatorname{E}\left(\operatorname{N}\left(r\right)\right))=\frac{r(M-m)}{(b+s)}\to\frac{M-m}{(b+s)}\\\Delta_{c}(\operatorname{E}\left(\mathbb{C}e\right),S,\operatorname{E}\left(\mathbb{C}e\right)) = -\frac{2m}{(b+s)}\\\frac{M-m}{(b+s)}-(-\frac{2m}{(b+s)})=\frac{s}{(b+s)}>0\end{aligned}
$$

For every r<1 the meet of E(L(r)) and E(N(r)) is R and their join is S. At r=1 the meet and join are both E(C e). Thus the distance between the distinct endpoints is s/(b+s), while its actual coincident value is zero. The two distances to S converge to m/(b+s). The positive discrepancy s/(b+s) is exactly the meet-over-join change; substituting r=1 into the distinct-line formula is invalid.

All denominators above remain positive when c=0, R=0 or b=0, because m>0 and s=M+m. For n=2 the assumptions force R=0 and T=H, and the same argument applies. When M=m the chosen basis is still fixed, all distinct-pair defects are zero, and the coincident endpoint is -2m/(b+2m)<0, with positive discrepancy 2m/(b+2m). No invariance of T or R under rho is used: compression_inner, compression_symmetric and native_matrix_faithfulness justify the compression and its positive eigenvalues, while weight_nonneg gives b>=0. This is an application of the existing results to the coherent source family, with no originality claim. Singular densities and infinite-dimensional spaces remain outside these assumptions.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/BornJaccardFixedOverlap.fixed_overlap_maximum`
- Dependency: [D5/S3/Quantum/Algebra/BornJaccardTracialClassification](BornJaccardTracialClassification.md)
