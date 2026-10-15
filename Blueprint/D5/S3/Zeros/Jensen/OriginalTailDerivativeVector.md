# The original tail derivative vector

## Abstract

The derivative vector of the original primal theta tail.

**Theorem 1.1 (The complete actual-source derivative vector).**

Lean statement: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVector.original_tail_derivative_vector`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/OriginalTailDerivativeVector.original_tail_derivative_vector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Z=Re xi(1/2) is positive and the original density has real-line integral one. For every a>0 there is C>0 such that all the following hold for every N,n>=1 and t>0 with alpha=t/(2*n)<=a. Put A=pi*(N+1)^2, S=4*A^2, Lambda=S+t, Q=originalTail(N), kappa=originalFlux(N), and H=originalHead(N). The flux is the entire cubic sum sum over m>N of exp(-pi*m^2)*(8*(pi*m^2)^3-30*(pi*m^2)^2+15*pi*m^2). Write I=integral over x>0 of B*Q and H0=integral over x>0 of B*H. The inherited all-N estimate is |t*I/kappa-1|<=C*(N+1)^4/t. It is consumed from original_primal_tail_response and has no large-A restriction.

Kappa is positive. The B, b and x^2*B pairings against raw H,Q and the original full density are integrable. J_n(t)=sourceP(n)(-t)=(2/Z)*(H0+I), and its complex coercion equals the canonical sourceJensenPolynomial evaluation at -t. The complex source polynomial equals normalizedJensen with the actual sourceThetaCoefficient, and their zero statements agree. For every real x, B_n has parameter derivative b_n; for n>=1, b_n(0,x)=-x^2/2. Finite moments prove HasDerivAt for the raw Q and H integrals, with derivatives D_Q=rawD(n,t,Q) and D_H=rawD(n,t,H), and for J_n with derivative fullD=-sourceP(n)'(-t). FullD=(2/Z)*(D_H+D_Q), fullM2=(2/Z)*(M2_H+M2_Q), and fullG=(2/Z)*(G_H+G_Q).

For h=H or Q, G_h=-sum k=0..n of c_(n,k)*t^k*mu_h(2*k+2)/(2*(2*k+1)), where mu_h is the raw half-line moment. The finite sum includes the top coefficient k=n and its zero successor. FullG=-sum k=0..n of (-1)^k*(n)_k/n^k*(k+1)*sourceThetaCoefficient(k+1)*t^k, and it is the derivative of J_(n+1) at ((n+1)/n)*t. It is distinct from J_n'.

Let T0(F)=integral B*F, T1(F)=integral b*F, T2(F)=integral x^2*B*F, all over x>0. Put U=T0(R), V=T1(R), Y=T2(R), Lm=Lambda-2*alpha and Lp=Lambda+2*alpha. Five genuine spatial Green pairings give Lambda*I=kappa+U; Lm*D_Q=-I+V; Lp*M2_Q=2*I+8*t*D_Q+Y; Lm*V=-U+T1(R2); Lp*Y=2*U+8*t*V+T2(R2). The full bracket is f*F'-f'*F+alpha*x*f*F. The B/Q origin is -kappa; the b/Q, x^2B/Q, b/R and x^2B/R origins are zero, even for nonzero R(0),R'(0). Each of the fifteen separate infinity products is paid by the existing polynomial/jet endpoints. V is not the total t derivative of U; no norm or error estimate is differentiated.

At A>=max(64,a), w=exp(a*x^2/2), integral w*|R|<=64*kappa/A and integral x^2*w*|R2|<=1100*kappa/A; both integrands are integrable. The resulting complete vector satisfies |Lambda*I/kappa-1|<=64/A, |Lambda^2*D_Q/kappa+1|<=2600/A, |Lambda^3*M2_Q/(2*kappa)-(S-3*t)|<=16000*Lambda/A, and |Lambda^2*G_Q/kappa+c_n|<=(5200*n+16000)/((2*n+1)*A)<=21200/(3*A), where c_n=((2*n+1)*S+(2*n-3)*t)/((2*n+1)*Lambda).

The quantitative escape is the first omitted mode cancellation in R2, with the external x^2 retained. At s=A and z=A*exp(2*x), the grouped pure jet expression is bounded by 1024*x^2*z^6+1772*z^5. Weighted Gamma moments give 5100*A^2*exp(-A) for that mode. Every later mode is bounded by 600*s^3*exp(-s), and the actual scale gap pays their complete sum. The shifted constants are shiftedBudget(2)-1<=2 and shiftedBudget(3)-1<=9; one is subtracted, never the index. The total is at most 6000*A^2*exp(-A), whereas the full cubic flux is at least (11/2)*A^3*exp(-A). Weighted monomial bounds include p=4,k=6. The existing B energy bound and an integrating-factor tx bound for B' give |b|<=x^2*exp(alpha*x^2/2)/2 uniformly down to t=0.

At A>=max(72000,a), D_Q<=-kappa/(2*Lambda^2), G_Q<=-kappa/(10*Lambda^2), and D_Q*G_Q>=kappa^2/(20*Lambda^4)>0. For d_Q=(2/Z)*D_Q and g_Q=(2/Z)*G_Q, d_Q<=-kappa/(Z*Lambda^2), g_Q<=-kappa/(5*Z*Lambda^2), and d_Q*g_Q>=kappa^2/(5*Z^2*Lambda^4)>0. The statements include n=1 and arbitrarily small positive t. Small cutoffs excluded by these thresholds remain covered by the inherited all-N P estimate.

For every actual node J_n(t)=0, put delta=n/(n+1), xi=delta/t>0 and q=sourceQ(n+1). Then q'(xi)=0, (n+1)*q(xi)=xi^n*fullG, xi^2*q''(xi)=-n*xi^n*fullD, and q(xi)*q''(xi)=-(n/(n+1))*xi^(2*n-2)*fullD*fullG. These are division-free identities, also valid when fullD or fullG is zero. FullD is nonzero if and only if q''(xi) is nonzero. Under that explicit guard, sourceCoupling(n+1,xi)=(xi^2/n)*(fullG/fullD), and its ordinary nonnegative sign is equivalent to fullD*fullG>=0. No node existence or simple-root premise is introduced.

Exactly fullD*fullG=(4/Z^2)*(D_H*G_H+D_H*G_Q+D_Q*G_H+D_Q*G_Q). The head product and both cross terms remain unpaid. So do global node existence, count, multiplicity and cofactor sign, strict Robin above 5040, the three/five-mode source maps, and RH. Current or historical novelty and independent formal admission are not inferred from supplier text. This is one source-specific quantitative tail vector with its necessary bindings.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/OriginalTailDerivativeVector.original_tail_derivative_vector`
- Dependency: [D5/S3/Zeros/Jensen/OriginalPrimalTailProjection](OriginalPrimalTailProjection.md)
- Dependency: [D5/S3/Zeros/Jensen/OriginalPrimalTailResponse](OriginalPrimalTailResponse.md)
- Dependency: [D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals](OriginalTailDerivativeVectorResiduals.md)
- Dependency: [D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources](OriginalTailDerivativeVectorSources.md)
- Dependency: [D5/S3/Zeros/Jensen/SourceJensenIntegralExtension](SourceJensenIntegralExtension.md)
- Dependency: [D5/S3/Zeros/Jensen/SourceJensenPositiveExtension](SourceJensenPositiveExtension.md)
