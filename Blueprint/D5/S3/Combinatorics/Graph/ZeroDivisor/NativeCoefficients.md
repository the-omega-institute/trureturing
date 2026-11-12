# Native three-domain coefficients

## Abstract

Coefficient inequalities for the actual zero divisor graph of three finite domains.

**Theorem 1.1 (Exact support and strict interior log concavity).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/NativeCoefficients.coefficients_three_domains`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/NativeCoefficients.coefficients_three_domains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be a finite commutative ring, let L be three finite nontrivial commutative rings without zero divisors, and let e identify R with their dependent product. Their cardinalities are nondecreasing, with the second at least three and the third at least five. Put a=card(L(0))-1, b=card(L(1))-1, c=card(L(2))-1, A=ab+ac+bc and N=max(A,c+ac+bc). For every natural k, let s(k) be the coefficient of the native independence polynomial of the actual zero divisor graph on its full vertex set, cast from the integers to the rationals. Then N is at least fourteen, s(k) is strictly positive for k at most N, s(k) vanishes for k greater than N, and s(k-1)s(k+1) is strictly smaller than s(k) squared whenever 1 is at most k less than N. There is no bound on the coordinate cardinalities or on k.

The seven-term formula is derived from the existing actual-vertex support correspondence. A maximal positive exponent equals N. Monotonicity of binomial coefficients makes the coefficient at every rank at most N at least choose(N,k), including when the singleton family exceeds A. The normalized coefficient s(k)/choose(N,k) is therefore at least one.

At ranks at least three, apply the exact normalized second difference to each subtracted term and the uniform curvature bound to the other three positive terms after removing a term with exponent N. The normalized curvature is at most 1/(k+1). Positivity pays for this error: the square of f(k), multiplied by k+1, is greater than k f(k-1)f(k+1). The adjacent binomial recurrence transfers this to strict log concavity of the actual coefficients.

At the first two ranks, v=A+a+b+c and E=A+3abc give s(0)=1, s(1)=v and s(2)=v(v-1)/2-E. The coefficient-count identity identifies v with the actual vertex count and bounds s(3) by choose(v,3). For integral a at least one, b at least two and c at least four, an expansion in a-1, b-2 and c-4 proves 11E at most v(v-1), hence s(2) at least nine elevenths of choose(v,2). Its square exceeds v choose(v,3), proving the second rank. The finite-ring and graph definitions are those of Rather's arXiv:2606.04789v1, Theorem 4.1 and Problem 1; this coefficient argument is a repository derivation.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/NativeCoefficients.coefficients_three_domains`
- Dependency: [D5/S3/Combinatorics/Graph/ZeroDivisor/NormalizedCurvature](NormalizedCurvature.md)
- Dependency: [D5/S3/Combinatorics/Graph/ZeroDivisor/Support](Support.md)
