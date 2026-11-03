# Exact Endpoint Jets of Metallic Continuants

## Abstract

Arbitrary-order endpoint coefficients of the same supported metallic continuants have exact rational polynomial laws.

**Theorem 1.1 (Four coefficient polynomials at every order).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelEndpointJets.continuant_endpoint_jets`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelEndpointJets.continuant_endpoint_jets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For every n>=1, take the identical L,k,b,D,Q,s, recurrence, initial conditions and support bounds supplied by normal_family. Set nu=1 for even n and 2 for odd n, and rho=2n(n+1) for even n and 4n(n+1) for odd n. At p=(K nu)L write c_K=reverseAt(s(p),Q(p)) and d_K=reverseAt(s(p-1),Q(p-1)). For each h>=0 there are four polynomials P_0,P_1,P_2,P_3 in Q[Z], each of degree at most h. For every K>=1, P_0(K)=[X^h]c_K and P_1(K)=[X^h]d_K. Whenever h<2K rho, P_2(K)=[X^h]Q(p) and P_3(K)=[X^h](X^(n+1)Q(p-1)). Coefficients on the right are mapped from Z to Q. These ranges include K=1 and the exceptional golden n=1 cycle.

The same theorem retains s(p)=s(p-1)+(n+1). Together with s(p)=K rho from normal_family, Q(p) and X^(n+1)Q(p-1) are precisely the reversals of c_K and d_K at the common support degree K rho. Reversal uses the supplied support bound rather than the actual degree, so leading zeros and coefficients outside the support are preserved. The theorem states the high endpoint using these ordinary continuants, with the fixed predecessor shift inside coefficient extraction.

For the low endpoint, put V=R-I for the reversed block R. The identity R(0)=I factors V as X times a matrix. Thus the coefficient at height h of V^a vanishes for a>h. The finite binomial expansion of R^K gives a polynomial sum of coeff(h,V^a) times the falling factorial Z(Z-1)...(Z-a+1)/a!, for 0<=a<=h. The vanishing terms for a>K are handled by the ordinary binomial coefficient, so no eventual-in-K restriction appears.

For the high endpoint, ordinary_blocks supplies constantCoeff(trace U)=1 and det U=X^(2rho). The existing transfer_spectral_remainder supplies one unit branch and one fixed matrix prefactor, with exact coefficient control at depth h<2K rho. The existing unit_power_coefficients supplies the rational polynomial in the exponent; the second coordinate uses the prefactor X^(n+1)E_(1,0). The proof reuses both results and does not assert trace U=1 as a series.

This result supplies endpoint jets for the later complementary-minor assembly. It does not assert the residue-polynomial conclusion of Conjecture C or integer values of those residue polynomials on all integers. Metallic existence and uniqueness remain supplied by normal_family; no alternative continuant family is substituted.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelEndpointJets.continuant_endpoint_jets`
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks](MetallicHankelBlocks.md)
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelEndpointSpectral](MetallicHankelEndpointSpectral.md)
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelBranches](../MotzkinHankel/CiglerMotzkinHankelBranches.md)
