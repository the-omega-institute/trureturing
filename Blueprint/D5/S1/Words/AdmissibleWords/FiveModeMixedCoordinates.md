# Mixed coordinates of the five-mode simplex

## Abstract

The three site occupancies and the log cross-ratio of the base corners form a global chart of the positive five-mode laws, and the base loop is the Fisher gradient of the cross-ratio.

A five-mode law is a probability vector p = (p_O, p_L, p_T, p_R, p_J) on the admissible words 000, 100, 010, 001, 101. Its visible point is (X, Y, Z) = (p_L + p_J, p_R + p_J, p_T), the occupancies of the first, last and middle sites. The hidden coordinate is chi = log(p_O p_J / (p_L p_R)), and the base loop is d = (1, -1, 0, -1, 1). The Fisher inner product at p is the sum over modes of u_s v_s / p_s.

Arbitrary responses on the closed five-mode simplex.

The affine coordinates also describe every nonnegative real law of total one, including zero cells. Use Fin 5 order (0,2,3,5,25) = (O,L,T,R,J), and fix one arbitrary real response f on these same five modes. Source occupancy coordinates are (x,y,z); the low-to-high site bits are (x,z,y). Thus X=p2+p25, Y=p5+p25, Z=p3. Put r=1-Z, kappa=p25, Delta=p0*p25-p2*p5, and Jf=f25-f2-f5+f0. Here r denotes the whole base mass. It differs from the auxiliary 1-X-Y-Z used in the positive-chart root calculation below.

Normalization gives p=(r-X-Y+kappa,X-kappa,Z,Y-kappa,kappa), with 0<=X,Y<=r and r>=0. This is the unrestricted affine probability formula already defined in FiniteRectangleTransport.probability; FiveModeMixedCoordinates.visible is exactly (X,Y,Z). The two-by-two matrix with rows (p0,p5) and (p2,p25) has determinant Delta, and expanding it gives Delta=r*kappa-X*Y. Finite-sum linearity therefore gives E_p f=f0+(f2-f0)*X+(f5-f0)*Y+(f3-f0)*Z+Jf*kappa. These calculations use normalization alone and retain the closed simplex, whereas the logarithmic chart theorem below has its stated positive domain.

The unweighted visible function space.

On the same source carrier, x=(0,1,0,0,1), y=(0,0,0,1,1), and z=(0,0,1,0,0). These are the endpoint, endpoint and middle indicators of the five independent sets empty, {1}, {2}, {3}, {1,3} of the three-vertex path. In this function-space discussion subscripts 0,1,2,3,13 denote these source labels, rather than numeric mode labels. ReadoutInstrument.sourceWindow maps their Fin 5 indices to LiteralWindowEnd.Window.zero, low, middle, high, ends. LiteralWindowEnd.bits writes these windows from low to high as (x,z,y); the Window enumeration itself lists ends before high, so the source index table, rather than enumeration position, specifies the correspondence. The pointwise product xy is the joint-state indicator (0,0,0,0,1). Reindexing a finite expectation by this bijection preserves every arbitrary real response and every mass.

Let A be all real functions on these five states, with the ordinary pairing dot(u,v)=sum_s u_s*v_s, and let B=span{1,x,y,z}. This pairing does not depend on the law p. Evaluating a linear combination a0*1+a1*x+a2*y+a3*z at empty, {1}, {3}, {2} recovers respectively a0, a0+a1, a0+a2, a0+a3. Thus the four generators are linearly independent and dim(B)=4. Orthogonality of u to them is exactly u0+u1+u2+u3+u13=0, u1+u13=0, u3+u13=0, u2=0. Solving these equations gives u=u13*d, and conversely every multiple of d=(1,-1,0,-1,1) satisfies them. Hence B-perp=span{d}. This orthogonal complement uses the ordinary finite dot product; the Fisher pairing of the positive chart is a separate construction.

For every f in A, the linear functional J(f)=dot(d,f) is f13-f1-f3+f0. Each generator of B has J=0. Conversely, when J(f)=0, the values at all five states give f=f0*1+(f1-f0)*x+(f3-f0)*y+(f2-f0)*z. Therefore ker(J)=B, or equivalently f belongs to B exactly when its four-corner difference vanishes. Pinned finite linear algebra supplies Fintype.linearIndependent_iff, finrank_span_eq_card, Submodule.mem_span_range_iff_exists_fun and Submodule.mem_orthogonalBilin_span; dotProductBilin is precisely the unweighted pairing used here.

For arbitrary real X,Y,Z,kappa,t, the existing affine probability formula gives p_(kappa+t)=p_kappa+t*d. Bilinearity of the same dot product then gives E_(p_(kappa+t)) f=E_(p_kappa) f+t*J(f) for every real function f. This raw signed identity has no positivity hypothesis. It is an identity between expectations of probability laws whenever both parameters belong to the closed interval [max(0,X+Y+Z-1),min(X,Y)], with Z>=0. The probability fiber is nonempty exactly for X,Y,Z>=0, X+Z<=1 and Y+Z<=1. Every normalized nonnegative law has these coordinates and this reconstruction, so zero cells, endpoints and singleton fibers are included. A nonzero J(f) distinguishes two different feasible parameters when both exist; it does not ensure a nonzero feasible shift on a singleton fiber. The conclusions concern the complete static real function space and the actual common five-state law; they assert no acquisition procedure, arbitrary native instrument or dynamic sufficiency.

Conditional-base completion, using numeric mode labels.

For r>0 select the conditional-base product completion p* in Fin 5 order as ((r-X)*(r-Y)/r,X*(r-Y)/r,Z,Y*(r-X)/r,X*Y/r). Each entry is nonnegative, their sum is one, and visible(p*)=visible(p). Its conditional endpoint marginals given z=0 are X/r and Y/r, and the four conditional cells are their Bernoulli products. Conditional independence here concerns this positive-mass conditioning event. For the actual law it holds exactly when Delta=0, equivalently kappa=X*Y/r and p=p*. The selection of p* adds no independence hypothesis to p.

Write fhat=E_(p*) f for r>0. Substituting the selected joint mass into the same affine response formula gives E_p f-fhat=Jf*(kappa-X*Y/r)=Jf*Delta/r. Consequently E_p f=fhat if and only if Jf*Delta=0, equivalently Jf=0 or Delta=0. The first alternative permits any feasible Delta; the second permits any real response f. This equality compares the one actual law and the one selected completion for that same law's simultaneous projections. It supplies no whole-fiber constancy claim.

The pinned scalar inequality four_mul_le_sq_add applied to each pair of opposite base cells gives 4*p0*p25<=(p0+p25)^2<=r^2 and 4*p2*p5<=(p2+p5)^2<=r^2. Nonnegativity then yields absolute(Delta)<=r^2/4. Using abs_mul and abs_div in the residual identity gives absolute(E_p f-fhat)<=absolute(Jf)*r/4. For every 0<=Z<=1 the two laws (r/2,0,Z,0,r/2) and (0,r/2,Z,r/2,0) have total one and the same X=Y=r/2. Their determinants are respectively r^2/4 and -r^2/4. For every fixed f and r>0 both therefore attain the error bound, including its zero value when Jf=0. These are probability-table realizations.

At r=0, nonnegativity and normalization force p3=1 and all four base cells to vanish. Thus X=Y=kappa=Delta=0 and E_p f=f3; define fhat=f3 there without conditional division. The apex convention is continuous: for any fixed f put C=sum_s absolute(f_s-f3). Every nonnegative normalized law q with q3=Z satisfies absolute(E_q f-f3)<=r*C, by finite-sum triangle inequality and q_s<=r off the apex. Apply this to p and p*, and use the squeeze theorem as Z tends to one. This includes endpoint marginals and every zero-cell face. All formulas concern one real law and one response; acquisition, physical resources, and the separate whole-fiber and guarded-continuation questions require their own source contracts. The application reuses affine coordinates, finite-sum algebra, Matrix.det_fin_two, the scalar product inequality and the squeeze theorem, with no additional mathematical declaration.

Fix the correspondence (O,L,T,R,J) = (2,3,5,7,83). For a positive integer n, give each sampled prime the weight 1 plus its exponent in n and normalize by the sum of the five weights. These positive weights define a five-mode law to which the chart applies. This sampling includes a pseudocount at 83 and does not record the complete prime support of n.

For n = 5040 * 2^u * 3^v with u in {0,1,2} and v in {0,1}, put d = 13 + u + v. The five-mode law is (5+u,3+v,2,2,1)/d, its visible point is (4+v,3,2)/d, and its hidden coordinate is log((5+u)/(2*(3+v))). The six integer values are 5040, 10080, 15120, 20160, 30240 and 60480; their respective numerator vectors are (5,3,2,2,1), (6,3,2,2,1), (5,4,2,2,1), (7,3,2,2,1), (6,4,2,2,1) and (7,4,2,2,1). This finite application supplies neither an exhaustive congruence classification nor a Robin inequality for all integers above 5040.

**Theorem 1.1 (Global Fisher-orthogonal chart).**

Lean statement: `D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates.mixed_coordinates_global_chart`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates.mixed_coordinates_global_chart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathias Drton and Seth Sullivant (2007). *Algebraic Statistical Models*. DOI: [10.48550/arXiv.math/0703609](https://doi.org/10.48550/arXiv.math/0703609). URL: <https://arxiv.org/abs/math/0703609v1>.

*Commentary.*

Every positive law has its visible point in the open square pyramid 0 < X, Y, Z with X + Z < 1 and Y + Z < 1. Conversely, for every point of the open pyramid and every real c there is exactly one positive law with that visible point and chi = c. Along every direction u the derivative of chi at p equals the Fisher pairing of d with u, the base loop sums to zero, and it leaves X, Y and Z unchanged.

Fixing the visible point leaves one free parameter, the joint mass kappa = p_J, on the open interval from max(0, X + Y + Z - 1) to min(X, Y). With r = 1 - X - Y - Z, the condition chi = c is (r + kappa) kappa = e^c (X - kappa)(Y - kappa). The difference of the two sides is negative at the lower end and positive at the upper end, so the intermediate value theorem gives a root, and the difference is strictly increasing on the interval, so the root is unique. At c = 0 the root is kappa = XY / (1 - Z).

Because the Fisher pairing with d is the differential of chi, the fiber direction d is Fisher-orthogonal to every direction along which chi is constant. Log probability-ratio coordinates of positive categorical laws are classical in algebraic statistics and information geometry; the statement and proof here are for this five-mode simplex.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates.mixed_coordinates_global_chart`
