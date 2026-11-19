# The density of bounded radical components

## Abstract

Radical component inequalities have natural density 1-log(2).

**Definition 1.1 (A threshold for every prime-power component).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.radicalComponentSet`

*Formalization.* `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.radicalComponentSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Commentary.*

For a real parameter lam, the set consists of natural numbers n at least two for which every prime divisor p satisfies p^(v_p(n)+1) < lam*rad(n). Here rad(n) is the product of the distinct prime factors of n. At lam=2 this is the set B of the source, apart from its immaterial convention at n=1.

**Definition 1.2 (Inclusive positive counting functions).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.count`

*Formalization.* `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.count` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Commentary.*

For a set S of natural numbers, count(S,X) is the number of its elements in the inclusive interval from 1 to X. Both endpoints are natural numbers.

**Definition 1.3 (The counting function of the component set).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.radicalComponentCount`

*Formalization.* `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.radicalComponentCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Commentary.*

The function radicalComponentCount(lam,X) counts the members of radicalComponentSet(lam) up to X, using the same inclusive positive counting convention.

**Theorem 1.4 (The asymptotic density is independent of the positive threshold).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.result` (`✓ std3`). ∎

*Resolves.* `Problems/zelinsky-2026-radical-component-density` (proved) by `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zelinsky-2026-radical-component-density","declaration_gid":"D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Commentary.*

For every positive real lam, the quotient radicalComponentCount(lam,X)/X tends to 1-log(2) as the natural threshold X tends to infinity. Thus the source's set B has positive natural density, and its assertion that B has natural density zero is false.

Write P(n) for the largest prime factor of n and F_c={n>=2 : P(n)^2<c*n}. The complement of F_1 has a unique representation n=p*m with p prime and 1<=m<=p. Its exact counting function is the sum of p over primes p<=sqrt(X), plus the sum of floor(X/p) over primes sqrt(X)<p<=X. The first sum is at most sqrt(X)*pi(sqrt(X))=o(X). Replacing floor(X/p) by X/p in the second sum has error at most pi(X)=o(X).

Mertens' reciprocal-prime estimate writes the sum of 1/p up to x as log(log(x))+M+o(1). Subtracting the value at sqrt(x) gives log(2)+o(1). Consequently F_1 has natural density 1-log(2).

For fixed c>0, put a=min(1,c) and b=max(1,c). If membership in F_c and F_1 differs, then a*n<=P(n)^2<=b*n. Writing n=p*m bounds p by sqrt(b*X) and m by p/a. The number of such pairs is at most pi(Y)*Y/a, where Y=floor(sqrt(b*X)). Since Y^2<=b*X and pi(Y)/Y tends to zero, this bound is o(X). Every F_c therefore has the same density as F_1.

To control repeated prime factors, write n=s^2*u with u squarefree. The number of integers n<=X divisible by some s^2 with s>T is at most 2*X/(T+1). Outside this set the square factor can be chosen with s<=T. Since u divides rad(n), one has n<=T^2*rad(n). If v_p(n)>=2, squarefreeness of u gives v_p(n)=2*v_p(s)+v_p(u) with v_p(u)<=1, hence p^(v_p(n)+1)<=s^4<=T^4.

For n>T^6/lam, repeated prime factors thus satisfy the required strict component inequality. A prime factor of exponent one satisfies it whenever P(n)^2<(lam/T^2)*n. Apart from the finite initial interval and the exceptional large square divisors, F_(lam/T^2) is contained in radicalComponentSet(lam). Conversely radicalComponentSet(lam) is contained in F_lam, because rad(n)<=n and the largest prime factor has positive exponent. The common density of the two critical sets and the error 2/(T+1), which tends to zero as T increases, give the result.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.count`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.radicalComponentCount`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.radicalComponentSet`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.result`
- Dependency: [D5/S1/Deficit/AlmostAdditivity](../../../S1/Deficit/AlmostAdditivity.md)
- Dependency: [D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality](../../Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.md)
- Dependency: [D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity](StrongPseudoperfectEulerDensity.md)
- Dependency: [D5/S3/Arith/Robin/OriginalEndpointPrimeTail](../Robin/OriginalEndpointPrimeTail.md)
