# Primitive non-deficient integers outside B

## Abstract

A power saving for primitive non-deficient radical-component exceptions.

**Theorem 1.1 (A uniform exceptional-set estimate).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyPrimitiveExceptionalSet.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyPrimitiveExceptionalSet.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Acknowledgement.* Jared Duker Lichtman (2018). *The reciprocal sum of primitive nondeficient numbers*. DOI: [10.1016/j.jnt.2018.03.021](https://doi.org/10.1016/j.jnt.2018.03.021). URL: <https://arxiv.org/abs/1801.01925>.

*Commentary.*

There are a positive constant K and a natural threshold X0 such that for every natural X>=X0, the number of positive primitive non-deficient integers n<=X outside radicalComponentSet(2) is at most K*X^(39/40). This estimate concerns the exceptional set associated with Zelinsky's Conjectures 11, 13 and 15, as collected in https://github.com/the-omega-institute/trureturing/issues/31919. It asserts no resolution of those questions.

Write h(n)=sigma(n)/n. For a natural parameter M>=100, first count up to M^40. The initial interval n<=M^39 contributes at most M^39. Integers divisible by some b^2 with b>M contribute at most 2*M^40/(M+1). Outside these sets, write n=b^2*a with a squarefree and b<=M. Then n<=M^2*rad(n), and a prime occurring at least twice has its full next prime power at most M^4. Failure of the component condition therefore forces the largest prime factor above M^18.

Put g=gcd(a,b), r=b^2*g and t=a/g. Then n=r*t, r<=M^3, and t is squarefree and coprime to r. A prime factor of t in [M,M^8] supplies a unitary squarefree divisor d in that interval. If none exists, split t=s*v into primes below M and primes above M^8. The latter part has at most 40 prime factors. If s<M, then u=r*s<=M^4 is a proper divisor, so sigma(u)<=2u-1. Writing z as the sum of 1/p over the primes of v gives z<=40/M^8 and h(v)*(1-z)<=1. Non-deficiency of n then forces 1<=2u*z, contradicting 80u<M^8. Thus s>=M, and a minimal subproduct supplies M<=d<=M^2.

The compression mapping n to n/d follows the rational-gap method of Lichtman's Lemma 2.2, with d chosen unitary as well as squarefree. Primitivity and the large prime give 2<=h(n)<2+M^(-16). For a fixed cofactor m>1, two admissible d,e<=M^8 must therefore satisfy sigma(d)*e=sigma(e)*d, since distinct rational values have separation at least 1/(d*e). Cancel their common squarefree part. The remaining coprime factors each divide their own divisor sum, so any factor greater than one would be a non-deficient proper divisor of n. Both factors are one, giving d=e. Consequently there are at most M^39 compressed values. The three counts total at most 4*M^39. Finally choose M=ceil(X^(1/40))+100<=102*X^(1/40) for X>=1.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyPrimitiveExceptionalSet.result`
- Dependency: [D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures](ZelinskyRadicalComponentConjectures.md)
