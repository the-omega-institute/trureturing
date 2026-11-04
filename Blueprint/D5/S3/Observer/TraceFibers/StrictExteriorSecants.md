# Strict Exterior Secant Estimate

## Abstract

A uniform quantitative inverse on a full positive calibrated matrix fiber.

**Theorem 1.1 (One constant for every pair in the fiber).**

$$\forall \theta: \mathbb{Q}, \forall b: \mathbb{R}, (\theta > 0 \land b > 0 \land (b < \operatorname{min}\left(\frac{1}{\theta}, 1+\theta\right) \lor \operatorname{max}\left(\frac{1}{\theta}, 1+\theta\right) < b)) \Rightarrow \exists L: \mathbb{R}, L \ge 0 \land {\forall P, Q: \operatorname{Mat}\left(2, \mathbb{R}\right), (\operatorname{LegalSource}\left(P\right) \land \operatorname{LegalSource}\left(Q\right) \land \operatorname{tr}\left(MP\right) = b \land \operatorname{tr}\left(MQ\right) = b) \Rightarrow \operatorname{maxEntry}\left(P-Q\right) \le L\cdot \operatorname{abs}\left((P_{1,0}-\theta\cdot P_{1,1})-(Q_{1,0}-\theta\cdot Q_{1,1})\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/TraceFibers/StrictExteriorSecants.strict_exterior_uniform_secant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All matrix indices are zero based. A legal source is a real two by two matrix with every entry strictly positive, rank one, and trace one. The atomic matrix M has rows (0,1),(1,1). Fix a positive rational theta, viewed as a real number, and a positive real b strictly outside the closed interval with endpoints 1/theta and 1+theta. Both sources range over the entire legal domain with trace(MP)=trace(MQ)=b. The loss is the maximum of the absolute values of all four entries of P-Q.

The constant precedes both source quantifiers. There is no restriction to a compact part of the positive fiber, no exclusion of b=1, and no positive lower bound on source entries. Equal pairs and pairs on different components are included. The scalar compared on the same pair is ell(P)=P10-theta*P11.

Every legal source has the exact positive chart (1+x*r)^(-1) times the matrix with rows (1,r),(x,x*r). In particular its second row is x times its first row, with x>0. Use x for P and y for Q. Put h=Q11-P11, k=Q10-P10, and e=k-theta*h. Trace normalization gives P00-Q00=h; the common calibrated trace gives P01-Q01=h+k.

The two row relations imply (y-x)P00=k+y*h and (y-x)P01=h+y*(h+k). The calibrated trace of P also gives (b-x)P00+((b-1)x-1)P01=0. Multiplying this last equation by y-x and substituting both row relations yields h*A+e*K=0, where B=b-1-theta, C=b*theta-1, A=(B+C)x*y+B(x+y)+C, and K=(b-1)x*y-(x+y)+b. This identity requires no division by a source difference or by y-x.

The exterior condition makes B and C both strictly negative or both strictly positive. Consequently m=min(abs(B),abs(C)) is positive. With W=x*y+x+y+1>0, every coefficient of A has the same sign, and abs(A)>=m*W. Also D=b+abs(b-1)+1>0 satisfies abs(K)<=D*W by the triangle inequality. Taking absolute values in the identity and canceling W gives abs(h)<=R*abs(e), where R=D/m is finite and nonnegative.

Since k=e+theta*h, the triangle inequality gives abs(k)<=(1+theta*R)abs(e) and abs(h+k)<=(1+(1+theta)R)abs(e). Thus L=1+(1+theta)R controls the two diagonal differences, the lower left difference k, and the upper right difference h+k simultaneously. The absolute value of e is exactly the scalar separation in the statement. This proves the estimate uniformly even as entries approach zero.

For canonical chronological continuation, GainRay.acquisition_append and acquisition_pure identify the word of S copies of M followed by J with J*M^S. The original GraftAffineClosure.result Fibonacci packet gives trace(J*M^S*P)=F_S+F_(S-1)*b+F_S*ell(P), with theta=F_(S-1)/F_S and S>=2. Since F_S>0, the estimate gives maxEntry(P-Q)<=(L/F_S)*abs(trace(J*M^S*P)-trace(J*M^S*Q)). Thus Theorem 22.1's chronological continuation with S=T+n-1 receives a global Lipschitz pair estimate at exactly its strict exterior parameters.

For Theorem 23.1's first positive nonroot offset r, execute M at each earlier offset and J at r; then S=T+r-1. The known gain at that original clock is nonzero. Removing the same known drift and dividing by that gain converts raw error delta to effective trace error delta/abs(H(T+r)). Two legal candidates consistent with one received scalar therefore have distance at most 2*L*delta/(F_S*abs(H(T+r))). Every earlier root action and read remains paid. This pair estimate supplies the quantitative input; this module does not formalize the compact-closure projection decoder, its minimax guarantees, endpoint behavior, all word necessity, or the full stable-cost classification.

## References

- Truth anchor: `D5/S3/Observer/TraceFibers/StrictExteriorSecants.strict_exterior_uniform_secant`
- Dependency: [D5/S3/Observer/Linear/GainRayWordGeometry](../Linear/GainRayWordGeometry.md)
- Dependency: [D5/S3/Observer/TraceFibers/FixedFiberPairModulus](FixedFiberPairModulus.md)
