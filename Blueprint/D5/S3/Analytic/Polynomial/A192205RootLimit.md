# The absolute coefficient root limit in OEIS A192205

## Abstract

The complete absolute coefficient sum of (1-X-X squared+X cubed) to power n has root limit 16 sqrt(3)/9.

The polynomial p has integer coefficients. For each natural n, including zero, a(n) sums the natural absolute values of every coefficient of p to power n at indices zero through 3n. Coefficients outside that interval vanish. The cast to the reals occurs after this complete sum. Powers with exponent 1/(n:R) use real rpow; the limit is along all natural numbers.

**Definition 1.1 (The original integer polynomial).**

$$(p: \operatorname{Polynomial}\left(\mathbb{Z}\right)) = 1 - X - (X)^{2} + (X)^{3}$$

*Formalization.* `D5/S3/Analytic/Polynomial/A192205RootLimit.p` (`✓ std3`).

*Citation.* Paul D. Hanna and OEIS contributors (2011). *OEIS A192205, absolute coefficient sums of powers of 1-x-x^2+x^3*. URL: <https://oeis.org/A192205/internal>.

*Commentary.*

The polynomial factors as (1-X) squared times (1+X). No coefficient normalization or substitution changes the sequence.

**Definition 1.2 (The original complete coefficient sum).**

$$\forall n:\mathbb{N}, \operatorname{a}\left(n\right) = \sum_{i \in \operatorname{range}\left(3 \cdot n + 1\right)} \operatorname{natAbs}\left(\operatorname{coeff}\left((p)^{n}, i\right)\right)$$

*Formalization.* `D5/S3/Analytic/Polynomial/A192205RootLimit.a` (`✓ std3`).

*Citation.* Paul D. Hanna and OEIS contributors (2011). *OEIS A192205, absolute coefficient sums of powers of 1-x-x^2+x^3*. URL: <https://oeis.org/A192205/internal>.

*Commentary.*

The range 3n+1 includes both endpoints zero and 3n. natAbs is the absolute value of an integer as a natural number. At n=0 the polynomial is one and the sum is one. Mapping the integer polynomial to the complex numbers preserves each coefficient and converts its natural absolute value, after a real cast, to its complex norm. The degree bound 3n identifies the padded sum with the entire support sum.

**Theorem 1.3 (The complete real root limit).**

$$\operatorname{Tendsto}\left((fun (n:\mathbb{N}) \mapsto ((\operatorname{a}\left(n\right): \mathbb{R}))^{\frac{1}{(n: \mathbb{R})}}), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(\frac{16 \cdot \sqrt{3}}{9}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/A192205RootLimit.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a192205-absolute-coefficient-root-limit` (proved) by `D5/S3/Analytic/Polynomial/A192205RootLimit.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a192205-absolute-coefficient-root-limit","declaration_gid":"D5/S3/Analytic/Polynomial/A192205RootLimit.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna and OEIS contributors (2011). *OEIS A192205, absolute coefficient sums of powers of 1-x-x^2+x^3*. URL: <https://oeis.org/A192205/internal>.

*Commentary.*

Put M=16 sqrt(3)/9 and write u=Re(z) for a unit complex number z. The squared modulus of p(z) is 8(1-u) squared times (1+u). Subtracting this squared modulus from 256/27 gives 8(3u+1) squared times (5-3u)/27, which is nonnegative since u is at most one. Thus the modulus is at most M. Equality holds at z=-1/3+(2 sqrt(2)/3)i, whose norm is one. The original CountableHankelNegativeWitness.eval_bound applied to the real image of p to power n at this z gives M to power n at most a(n). Parseval identifies the sum of squared complex coefficient norms with the unit-circle average of the squared modulus. The bound M on p yields a square sum at most M to power 2n. Cauchy-Schwarz and at most 3n+1 support indices give a(n) squared at most (3n+1) M to power 2n. In particular a(n) is at most (3n+1) M to power n. For n at least one, taking real powers 1/n bounds the root between M and (3n+1) to power 1/n times M. That extra factor tends to one. The squeeze theorem proves the stated full limit, with no sign assumption on the coefficients. The squared-coefficient binomial observation in the source is not assumed or asserted here.

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/A192205RootLimit.a`
- Truth anchor: `D5/S3/Analytic/Polynomial/A192205RootLimit.p`
- Truth anchor: `D5/S3/Analytic/Polynomial/A192205RootLimit.result`
- Dependency: [D5/S3/Constants/Moments/CountableHankelNegativeWitness](../../Constants/Moments/CountableHankelNegativeWitness.md)
