# The universal second-order prime-min correction

## Abstract

A uniform three-term lower bound for the original integer's complete tail correction.

**Theorem 1.1 (One threshold before every initial-support integer).**

Lean statement: `D5/S3/Arith/Robin/EulerLayer/PrimeMinCorrectionSecondOrderLower.uniform_min_tail_robin_second_order_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/EulerLayer/PrimeMinCorrectionSecondOrderLower.uniform_min_tail_robin_second_order_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put X=log(m), L=log(X), s=sqrt(2), b=log(2), and c2=s*(8+4*b+3*b^2/4). A single X0>1 precedes every pair of natural numbers m,P. For positive m with m.primeFactors=Nat.primesLE(P), theta(P)>1 and X>=X0, the same integer's actual complete tail satisfies sqrt(X)*L*(tail(m)+log(log(X))-log(log(theta(P)))) >=2*s-s*(2+b)/L+c2/L^2-3200/L^3. Composite plateau endpoints P are allowed; local support normalization identifies their theta with theta(largestPrime(m)). No record, optimizer or exponent-order premise enters.

The canonical real root rho is retained opaquely and satisfies rho^2*log(rho)=X*log(X). With x=rho/sqrt(X) and h=1/L, its exact normalized equation gives |x-s|<=h and |x-s+(s*b/2)*h|<=4*h^2. The finite head contains every p<=rho, including a prime endpoint rho; the finite reciprocal-square tail contains exactly rho<p<=P. The existing finite_min_tail_robin_bound connects this finite sum to the original tail of the same m.

The stationary profile is x+(1/x)*(2/(1+z)-4*h/(1+z)^2 +16*h^2/(1+z)^3), z=2*h*log(x). Its three polynomial pieces are x+2/x, -4*(log(x)+1)/x, and 8*((log(x))^2+2*log(x)+2)/x. Stationarity of the first piece at s makes the quadratic root error sufficient for the displayed coefficient c2. Rational remainder bounds, the existing quadratic logarithm inequality and a derivative bound on the last piece control the cubic error. The finite A3 theorem from PrimeSquareTail and the unconditional theta_error_eight supply the arithmetic errors. Their thresholds are chosen before X,m,P.

If theta(P)>=X/2, the Chebyshev bound theta(P)<=log(4)*P places P above c*X for c=1/(2*log(4)), and the finite-root estimate applies. If 1<theta(P)<X/2, the existing log-log tangent gives a clock gap >1/(2*L). Nonnegativity of the original tail then closes the same bound. Neither branch inserts an asymptotic threshold depending on m.

For the signed Robin application let M(P) be the finite sum of -log(1-1/p) over primes p<=P and set Etheta(P)=M(P)-gamma-log(log(theta(P))). Full support identifies M(P) with eulerMass(m). The existing exact tail_robin_data identity gives margin(m)=A(m)-Etheta(P), where A(m)=tail(m)+log(log(X))-log(log(theta(P))). Thus Robin positivity is equivalent to Etheta(P)<A(m). The displayed lower bound gives the sufficient strict comparison Etheta(P)<(2*s-s*(2+b)/L+c2/L^2-3200/L^3)/(sqrt(X)*L). This lower bound establishes neither that signed comparison nor Robin for all m>5040, RH, the actual-record two-sided expansion, or a sharpness family. Those obligations remain open.

## References

- Truth anchor: `D5/S3/Arith/Robin/EulerLayer/PrimeMinCorrectionSecondOrderLower.uniform_min_tail_robin_second_order_lower`
- Dependency: [D5/S3/Arith/Robin/EulerLayer/EulerLayerRootSecondOrder](EulerLayerRootSecondOrder.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/PrimeSquareTail](../PriceRecord/PrimeSquareTail.md)
- Dependency: [D5/S3/Arith/Robin/PrimeMinCorrectionLower](../PrimeMinCorrectionLower.md)
