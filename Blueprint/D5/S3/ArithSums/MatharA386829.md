# Mathar's A386829 recurrence and D-finiteness

## Abstract

The inclusive binomial sum A386829 satisfies Mathar's complete recurrence and a nonzero homogeneous formal differential equation.

All sequence indices are natural numbers. Binomial coefficients are ordinary natural binomial coefficients, cast into the integers in the finite sum. Both k=0 and k=n are included. Coefficient subtraction in the recurrence is integer subtraction. The offset is zero, and n>=2 is the complete domain on which all three sequence indices are defined; the source does not explicitly give a recurrence onset.

**Definition 1.1 (Literal inclusive binomial sum).**

$$\forall n:\mathbb{N}, \operatorname{a}\left(n\right)=\sum_{k=0}^{n} 3^{k} \cdot 2^{n - k} \cdot \operatorname{choose}\left(2 \cdot n + 1, k\right) \cdot \operatorname{choose}\left(2 \cdot n - k, n - k\right)$$

*Formalization.* `D5/S3/ArithSums/MatharA386829.a` (`✓ std3`).

*Citation.* R. J. Mathar; Seiichi Manyama (2026). *OEIS A386829: binomial sum recurrence and D-finiteness*. URL: <https://oeis.org/A386829>.

*Commentary.*

This is the original Manyama definition in OEIS A386829, without assuming equivalence to another formula from the entry.

**Definition 1.2 (Entire formal generating series).**

$$series=\sum_{n=0}^{\infty} \operatorname{a}\left(n\right) \cdot z^{n}$$

*Formalization.* `D5/S3/ArithSums/MatharA386829.series` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Seiichi Manyama (2026). *OEIS A386829: binomial sum recurrence and D-finiteness*. URL: <https://oeis.org/A386829>.

*Commentary.*

series is the power series with coefficient a(n), cast into the rationals, at every natural index. It belongs to Q[[z]]; no analytic convergence is required.

**Theorem 1.3 (Full recurrence and homogeneous differential equation).**

$$(\forall n:\mathbb{N}, 2 \le n \implies 2 \cdot n \cdot \operatorname{a}\left(n\right) + \left(20 - 31 \cdot n\right) \cdot \operatorname{a}\left(n - 1\right) + 90 \cdot \left(1 - 2 \cdot n\right) \cdot \operatorname{a}\left(n - 2\right)=0) \land (\exists r:\mathbb{N}, \exists p:\mathbb{N} \to \mathbb{Q}[z], (\exists j:\mathbb{N}, 0 \le j \le r \land \operatorname{p}\left(j\right) \neq 0)\land \sum_{j=0}^{r} \operatorname{p}\left(j\right) \cdot series^{(j)}=0)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/MatharA386829.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathar-a386829-recurrence-dfinite` (proved) by `D5/S3/ArithSums/MatharA386829.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathar-a386829-recurrence-dfinite","declaration_gid":"D5/S3/ArithSums/MatharA386829.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Seiichi Manyama (2026). *OEIS A386829: binomial sum recurrence and D-finiteness*. URL: <https://oeis.org/A386829>.

*Commentary.*

The first conjunct quantifies over every n>=2. The second provides a natural r and a function p from the naturals to Q[z], with at least one nonzero member among indices 0 through r whose weighted formal derivatives sum to zero. The notation series superscript (j) means its j-fold formal derivative, with the zero-fold derivative equal to series; each polynomial coefficient is embedded in Q[[z]]. A witness has order two: p0=-270, p1=-(42+630z), and p2=2-31z-180z squared. The constant coefficient of p2 is 2, proving that the equation is nonzero.

Expanding the auxiliary sum b(n)=sum over j=0 through n of 5 to the j times 3 to the (n-j) times choose(n+j,j), interchanging finite triangular sums, and applying the hockey-stick identity proves a(n)=b(n). The binomial product identity and the reflection of the inclusive index range account for every endpoint.

A weighted telescoping identity gives 4b(n+1)+18b(n)=7c(n+1), where c(n)=5 to the n times choose(2n,n). The central-binomial identity (n+1)c(n+1)=10(2n+1)c(n) eliminates c and yields the recurrence. Initial values a(0)=1 and a(1)=13 determine the constant term in the first-order inhomogeneous equation. Formal differentiation produces the displayed homogeneous equation.

## References

- Truth anchor: `D5/S3/ArithSums/MatharA386829.a`
- Truth anchor: `D5/S3/ArithSums/MatharA386829.result`
- Truth anchor: `D5/S3/ArithSums/MatharA386829.series`
