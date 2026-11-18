# The endpoint on the prefix lcm sequence

## Abstract

Under the Riemann hypothesis every sufficiently late prefix least common multiple violates the endpoint real-power Robin inequality.

**Remark 1.1 (The real-power divisor transform).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.sigmaKappa`

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.sigmaKappa` (`✓ std3`).

*Citation.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

Fan, Kobayashi and Molnar, Definition 1.2 and equation (1.1), use sigmaKappa(kappa,n)=sum_(d divides n) mu(n/d)*sigma(d)^kappa and G(kappa,n)=zeta(kappa)*sigmaKappa(kappa,n)/(exp(gamma)*n*log(log(n)))^kappa. Here zeta at a real argument greater than one is its real part, which is positive. This transform differs from the corresponding transform of sigma(n)/n.

**Theorem 1.2 (Eventual strict reversal under RH).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointRH.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointRH.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the Riemann hypothesis. There is a natural M0 at least three such that every natural m at least M0, with L=lcm(1,...,m), satisfies (exp(gamma)*L*log(log(L)))^(3/2)/zeta(3/2)<sigmaKappa(3/2,L). The cutoff is uniform over all later m. No explicit cutoff is asserted.

For a real cutoff x put D=sqrt(x)*log(x), a_p=floor(log_p(x)), A=-sum_(p<=x) log(1-p^(-a_p-1)), and J=log(log(psi(x)))-log(log(theta(x))). The exact multiplicative identity is log(G)=-kappa*B-kappa*A-kappa*J+T+C, where T=log(zeta(kappa))+sum_(p<=x)log(1-p^(-kappa)) and C>=0. All terms use the same cutoff and the same prefix lcm.

The B in the sharp arithmetic envelope is exactly gamma+log(log(theta(x)))-log(P(x)), with P(x)=product_(p<=x)(1-1/p)^(-1): expand Mertens.E3 and take the logarithm of this finite positive product. Under RH, D*B<-2+firstLiMass+eta eventually for every eta>0. The unconditional corrections satisfy D*A->2 and D*J->1. Finite Abel summation and the positive Euler logarithm series give D*T>2-epsilon eventually at kappa=3/2. Consequently D*log(G)>1/2-(3/2)*firstLiMass-(11/2)*eta after taking the three errors below eta. Since firstLiMass<1/3, a fixed small positive eta gives log(G)>0. Restrict to natural cutoffs and divide by the positive real zeta value.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.sigmaKappa`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerEndpointRH.result`
- Dependency: [D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion](LcmPowerEndpointExpansion.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/RHSharpArithmeticEnvelope](RHSharpArithmeticEnvelope.md)
