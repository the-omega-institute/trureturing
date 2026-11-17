# Exact real-power prefix-lcm expansion

## Abstract

The actual real-power divisor transform has an exact logarithmic decomposition on prefix least common multiples.

**Definition 1.1 (Real-power divisor transform).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.sigmaKappa`

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.sigmaKappa` (`✓ std3`).

*Citation.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

The value at a natural n is the finite sum over positive divisors d of n of mu(n/d) times sigma(d)^kappa. The real exponent is unrestricted in this definition. The divisor set is empty at zero. This is Definition 1.2 of Fan, Kobayashi and Molnar, arXiv:2511.02106v1.

**Definition 1.2 (Normalized divisor ratio).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.G`

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.G` (`✓ std3`).

*Citation.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

For natural n the expression is zeta(kappa)*sigmaKappa(kappa,n)/(exp(gamma)*n*log(log(n)))^kappa. The real part of the complex Riemann zeta at a real argument is used. The positive domain used below has kappa>1 and log(n)>1. This is the normalization in equation (1.1) of Fan, Kobayashi and Molnar.

**Definition 1.3 (Finite prime support).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.primeCutoff`

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.primeCutoff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set consists of positive natural primes at most the natural floor of the real cutoff x.

**Definition 1.4 (Prime-clock Mertens correction).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.B`

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B(x) is gamma+log(log(theta(x))) plus the finite sum of log(1-1/p) over the prime cutoff. Thus it equals gamma+log(log(theta(x)))-log(P(x)), where P(x) is the finite product of inverse Euler factors.

**Definition 1.5 (Terminal prime-power layers).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.A`

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A(x) is minus the finite sum of log(1-p^(-a-1)), where a is the natural base-p logarithm of the natural floor of x. These are the omitted terminal terms in the ordinary sigma ratio of the prefix least common multiple.

**Definition 1.6 (Prime-power clock correction).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.J`

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

J(x) is log(log(psi(x)))-log(log(theta(x))). It measures the change from the prime clock to the prime-power clock.

**Definition 1.7 (Missing Euler logarithms).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.T`

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T(kappa,x) is log(zeta(kappa)) plus the finite sum of log(1-p^(-kappa)) over primes not exceeding x. In the convergent domain kappa>1 this is the logarithm of the missing inverse Euler factors.

**Definition 1.8 (Exact local Euler correction).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.C`

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C(kappa,x) is the sum of log((1-r^kappa)/(1-p^(-kappa))), where r=sigma(p^(a-1))/sigma(p^a) at the maximal prime-power exponent a allowed by x. Its strict upper bound 1/p follows from sigma(p^a)=p*sigma(p^(a-1))+1.

**Theorem 1.9 (The local correction is nonnegative).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.C_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.C_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real kappa and every real x, C(kappa,x) is nonnegative. Every prime in the finite support has a positive maximal exponent. Its exact successive divisor-sum ratio is strictly between zero and 1/p, so the logarithm of the corresponding quotient of Euler factors is nonnegative.

**Theorem 1.10 (Positivity on the logarithmic domain).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.G_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.G_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For kappa>1 and psi(x)>1, G(kappa,lcmUpto(floor(x))) is positive. The convolution transform is multiplicative, and at a positive prime-power exponent it is the positive difference sigma(p^a)^kappa-sigma(p^(a-1))^kappa. The real zeta factor and the logarithmic normalizing factor are positive.

**Theorem 1.11 (The exact logarithmic decomposition).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.log_G_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.log_G_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real kappa>1 and every real x with psi(x)>1, log(G(kappa,lcmUpto(floor(x))))=-kappa*B(x)-kappa*A(x)-kappa*J(x)+T(kappa,x)+C(kappa,x). Dirichlet convolution gives the exact prime-power difference. Multiplicativity turns its logarithm into the sum of kappa times the ordinary sigma logarithm and the exact local corrections. The existing ordinary divisor-ratio factorization supplies A and the finite Euler prefix, while log(lcmUpto(floor(x)))=psi(x) supplies the change of clock. This identity is exact; the subsequent correction estimates are unconditional.

**Theorem 1.12 (The unit clock correction).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.J_scaled_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.J_scaled_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write J(x)=log(log(psi(x)))-log(log(theta(x))). As the real variable x tends to infinity, sqrt(x)*log(x)*J(x) tends to one. The assertion is unconditional.

The existing prime number theorem gives theta(x)/x and psi(x)/x tending to one. Continuity of the logarithm and division by log(x) then give log(theta(x))/log(x) and log(psi(x))/log(x) tending to one. Both clocks eventually exceed one.

The existing prime-power layer identity gives (psi(x)-theta(x))/sqrt(x) tending to one. The tangent inequality for log(log(t)), applied in both directions, places J(x) between (psi(x)-theta(x))/(psi(x)*log(psi(x))) and (psi(x)-theta(x))/(theta(x)*log(theta(x))). Multiplication by sqrt(x)*log(x) makes both bounds tend to one.

**Theorem 1.13 (The coefficient two).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.A_scaled_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.A_scaled_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a_p=floor(log(x)/log(p)) for each prime p<=x, and put A(x)=-sum log(1-p^(-a_p-1)). As the real cutoff x tends to infinity, sqrt(x)*log(x)*A(x) tends to two. The maximal exponent a_p is represented exactly by p.log(floorNat(x)); the terminal exponent in A(x) is a_p+1, represented by p.log(floorNat(x))+1.

Write tau_p=p^(-a_p-1) and Q(x)=sum tau_p. Maximality of a_p gives tau_p<1/x. For p>sqrt(x), a_p=1 and tau_p=1/p^2; for p<=sqrt(x), a_p>=2 and tau_p<=1/p^3. Splitting the latter primes at u=x^(1/3), their smaller part has at most u terms and total at most u/x=1/u^2. The existing finite cubic-tail estimate bounds the larger part by 2/u^2.

Thus, with S(x)=sum over sqrt(x)<p<=x of 1/p^2, S(x)<=Q(x)<=S(x)+3*x^(-2/3). The logarithm inequality t<=-log(1-t)<=t+t^2 gives Q(x)<=A(x)<=(1+1/x)*Q(x) for x>=2. The existing uniform prime-square tail gives sqrt(x)*log(x)*S(x) tending to two, while sqrt(x)*log(x)*x^(-2/3) tends to zero. Both bounds therefore have the same limit.

**Theorem 1.14 (The endpoint Euler tail supplies coefficient two).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.endpoint_euler_tail_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.endpoint_euler_tail_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every epsilon>0, eventually for all real x, sqrt(x)*log(x)*T(3/2,x)>2-epsilon. Finite Abel summation at the weight 1/(t*sqrt(t)) uses the unconditional prime number theorem for theta. Truncate at C*x for one fixed sufficiently large C, and compare log(p) with log(C*x). The positive, absolutely convergent Euler logarithm series identifies the actual log-zeta remainder and bounds it below by this finite prime interval. Only the lower direction needed by the endpoint argument is asserted.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.A`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.A_scaled_limit`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.B`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.C`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.C_nonneg`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.G`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.G_pos`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.J`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.J_scaled_limit`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.T`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.endpoint_euler_tail_lower`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.log_G_decomposition`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.primeCutoff`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.sigmaKappa`
- Dependency: [D5/S3/Arith/GoldenResourceObjectiveFactorization](../../GoldenResourceObjectiveFactorization.md)
- Dependency: [D5/S3/Arith/Robin/EulerLayerRootCorrection](../EulerLayerRootCorrection.md)
- Dependency: [D5/S3/Arith/Robin/LogarithmBounds](../LogarithmBounds.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/PrimeOccupationDefect](../PriceRecord/PrimeOccupationDefect.md)
