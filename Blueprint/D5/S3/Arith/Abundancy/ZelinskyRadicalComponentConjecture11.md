# Zelinsky's Conjecture 11 is false

## Abstract

Almost every primitive non-deficient integer satisfies the component condition.

**Theorem 1.1 (A uniform exceptional-set estimate).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.exceptional_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.exceptional_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Acknowledgement.* Jared Duker Lichtman (2018). *The reciprocal sum of primitive nondeficient numbers*. DOI: [10.1016/j.jnt.2018.03.021](https://doi.org/10.1016/j.jnt.2018.03.021). URL: <https://arxiv.org/abs/1801.01925>.

*Commentary.*

There are a positive constant K and a natural threshold X0 such that for every natural X>=X0, the number of positive primitive non-deficient integers n<=X outside radicalComponentSet(2) is at most K*X^(39/40). This estimate concerns the exceptional set for the radical component condition.

Write h(n)=sigma(n)/n. For a natural parameter M>=100, first count up to M^40. The initial interval n<=M^39 contributes at most M^39. Integers divisible by some b^2 with b>M contribute at most 2*M^40/(M+1). Outside these sets, write n=b^2*a with a squarefree and b<=M. Then n<=M^2*rad(n), and a prime occurring at least twice has its full next prime power at most M^4. Failure of the component condition therefore forces the largest prime factor above M^18.

Put g=gcd(a,b), r=b^2*g and t=a/g. Then n=r*t, r<=M^3, and t is squarefree and coprime to r. A prime factor of t in [M,M^8] supplies a unitary squarefree divisor d in that interval. If none exists, split t=s*v into primes below M and primes above M^8. The latter part has at most 40 prime factors. If s<M, then u=r*s<=M^4 is a proper divisor, so sigma(u)<=2u-1. Writing z as the sum of 1/p over the primes of v gives z<=40/M^8 and h(v)*(1-z)<=1. Non-deficiency of n then forces 1<=2u*z, contradicting 80u<M^8. Thus s>=M, and finite logarithmic packing supplies M<=d<=M^2.

The compression mapping n to n/d follows the rational-gap method of Lichtman's Lemma 2.2, with d chosen unitary as well as squarefree. Primitivity and the large prime give 2<=h(n)<2+M^(-16). For a fixed cofactor m>1, two admissible d,e<=M^8 must therefore satisfy sigma(d)*e=sigma(e)*d, since distinct rational values have separation at least 1/(d*e). Cancel their common squarefree part. The remaining coprime factors each divide their own divisor sum, so any factor greater than one would be a non-deficient proper divisor of n. Both factors are one, giving d=e. Consequently there are at most M^39 compressed values. The three counts total at most 4*M^39. Finally choose M=ceil(X^(1/40))+100<=102*X^(1/40) for X>=1.

**Theorem 1.2 (Relative density one for sufficiently numerous subfamilies).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.relative_density_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.relative_density_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Commentary.*

Let S be any set of primitive non-deficient integers whose positive inclusive count is at least X^(79/80) for every sufficiently large natural X. Then the proportion of its members in B tends to one. Indeed, the missing count is at most K*X^(39/40), so its proportion is at most K*X^(-1/80), which tends to zero. No closure property or independence assumption on S is needed.

**Definition 1.3 (Conjecture 11).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.claim`

*Formalization.* `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.claim` (`✓ std3`).

*Citation.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Commentary.*

In section 3, Conjecture 11 asserts lim (B intersect C)(X)/C(X)=0, where C is the set of primitive non-deficient integers and B consists of the integers n>=2 with p^(v_p(n)+1)<2*rad(n) for every prime divisor p. Counts use inclusive positive bounds.

**Theorem 1.4 (The limit in Conjecture 11 is one, contradicting zero).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.result` (`✓ std3`). ∎

*Resolves.* `Problems/zelinsky-2026-conjectures-11-13-15` (refuted) by `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.result` and `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture13.result` and `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture15.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zelinsky-2026-conjectures-11-13-15","declaration_gid":"D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.result","resolution_kind":"refuted"} -->

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zelinsky-2026-conjectures-11-13-15","declaration_gid":"D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture13.result","resolution_kind":"refuted"} -->

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zelinsky-2026-conjectures-11-13-15","declaration_gid":"D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture15.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Commentary.*

The odd squarefree lower bound with the empty excluded prime set gives C(X)>=X^(79/80) eventually. The relative density comparison therefore gives (B intersect C)(X)/C(X) tending to one. Uniqueness of limits refutes Conjecture 11. The same comparison applies to the odd family and to each family avoiding finitely many primes, giving the separate refutations of Conjectures 13 and 15.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.claim`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.exceptional_bound`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.relative_density_one`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.result`
- Dependency: [D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures](ZelinskyRadicalComponentConjectures.md)
- Dependency: [D5/S3/Arith/Divisors/UnitaryProductBridge](../Divisors/UnitaryProductBridge.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair](../Robin/PriceRecord/ActualHigherLayerBudgetRepair.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions](../../Combinatorics/SpectralGraph/IdealIntersectionObstructions.md)
