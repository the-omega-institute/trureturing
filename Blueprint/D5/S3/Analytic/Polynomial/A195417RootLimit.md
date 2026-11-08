# The absolute coefficient root limit in OEIS A195417

## Abstract

The complete absolute coefficient sum of (1+X-X cubed) to power n has root limit sqrt((97+26 sqrt(13))/27).

The polynomial p has integer coefficients. For each natural n, including zero, a(n) sums the natural absolute values of every coefficient of p to power n at indices zero through 3n. Coefficients outside that interval vanish. The cast to the reals occurs after this complete sum. Powers with exponent 1/(n:R) use real rpow; the limit is along all natural numbers.

**Definition 1.1 (The original integer polynomial).**

$$(p: \operatorname{Polynomial}\left(\mathbb{Z}\right)) = 1 + X - (X)^{3}$$

*Formalization.* `D5/S3/Analytic/Polynomial/A195417RootLimit.p` (`✓ std3`).

*Citation.* Paul D. Hanna and The Online Encyclopedia of Integer Sequences contributors (2011). *OEIS A195417, absolute coefficient sums of powers of 1+x-x^3*. URL: <https://oeis.org/A195417/internal>.

*Commentary.*

No coefficient normalization or substitution changes the sequence.

**Definition 1.2 (The original complete coefficient sum).**

$$\forall n:\mathbb{N}, \operatorname{a}\left(n\right) = \sum_{i \in \operatorname{range}\left(3 \cdot n + 1\right)} \operatorname{natAbs}\left(\operatorname{coeff}\left((p)^{n}, i\right)\right)$$

*Formalization.* `D5/S3/Analytic/Polynomial/A195417RootLimit.a` (`✓ std3`).

*Citation.* Paul D. Hanna and The Online Encyclopedia of Integer Sequences contributors (2011). *OEIS A195417, absolute coefficient sums of powers of 1+x-x^3*. URL: <https://oeis.org/A195417/internal>.

*Commentary.*

The range 3n+1 includes both endpoints zero and 3n. natAbs is the absolute value of an integer as a natural number. At n=0 the polynomial is one and the sum is one. Mapping the integer polynomial to the complex numbers preserves each coefficient and converts its natural absolute value, after a real cast, to its complex norm. The degree bound 3n identifies the padded sum with the entire support sum.

**Theorem 1.3 (The complete real root limit).**

$$\operatorname{Tendsto}\left((fun (n:\mathbb{N}) \mapsto ((\operatorname{a}\left(n\right): \mathbb{R}))^{\frac{1}{(n: \mathbb{R})}}), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(\sqrt{\frac{97 + 26 \cdot \sqrt{13}}{27}}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/A195417RootLimit.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a195417-absolute-coefficient-root-limit` (proved) by `D5/S3/Analytic/Polynomial/A195417RootLimit.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a195417-absolute-coefficient-root-limit","declaration_gid":"D5/S3/Analytic/Polynomial/A195417RootLimit.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna and The Online Encyclopedia of Integer Sequences contributors (2011). *OEIS A195417, absolute coefficient sums of powers of 1+x-x^3*. URL: <https://oeis.org/A195417/internal>.

*Commentary.*

Put s=sqrt(13), C=(97+26s)/27 and M=sqrt(C). For a unit complex number z, let u=Re(z). Then the squared modulus of p(z) is f(u)=5+8u-4u squared-8u cubed. The identity C-f(u)=(6u+1-s) squared times (6u+1+2s)/27 proves f(u) is at most C: u is at least -1 and s is at least 5/2, so both factors on the right are nonnegative. Equality holds when u=(-1+s)/6 and z=u+i sqrt(1-u squared). This u lies between -1 and 1, so z has norm one. The original CountableHankelNegativeWitness.eval_bound applied to the real image of p to power n at this z gives M to power n at most a(n). The generic power_sum_sq_le in A192205RootLimit uses Parseval and Cauchy-Schwarz to bound a(n) squared by the number of support indices times M to power 2n. There are at most 3n+1 indices, giving a(n) at most (3n+1) M to power n. For n at least one, taking real powers 1/n bounds the root between M and (3n+1) to power 1/n times M. The original degree_root_limit in A192205RootLimit makes that extra factor tend to one. The squeeze theorem proves the full natural-index limit. This result answers only the first root-limit question; it makes no assertion about successive ratios or their attractors.

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/A195417RootLimit.a`
- Truth anchor: `D5/S3/Analytic/Polynomial/A195417RootLimit.p`
- Truth anchor: `D5/S3/Analytic/Polynomial/A195417RootLimit.result`
- Dependency: [D5/S3/Analytic/Polynomial/A192205RootLimit](A192205RootLimit.md)
