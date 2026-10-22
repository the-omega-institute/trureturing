# Hanna's OEIS 386655 congruence

## Abstract

Integrality and a period-six congruence for Hanna's Lambert W exponential coefficients.

**Definition 1.1 (The Lambert W series).**

$$\operatorname{W} = \operatorname{mk}\left((m: \mathbb{N} \mapsto \operatorname{if} (m = 0) \operatorname{then} 0 \operatorname{else} \frac{(-(m: \mathbb{Q}))^{m - 1}}{(m!: \mathbb{Q})})\right)$$

*Formalization.* `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.W` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A386655–A386658, Lambert W exponential generating functions*. URL: <https://oeis.org/A386655>.

*Commentary.*

The coefficient of positive degree m is (-m)^(m-1)/m!, and the constant coefficient is zero.

**Definition 1.2 (The exponential generating coefficient).**

$$\forall q: \mathbb{N}, \forall m: \mathbb{N}, \operatorname{egf}\left(q, m\right) = ((m!: \mathbb{Q})) \cdot (\sum_{n \in \operatorname{range}\left(m + 1\right)} (\frac{\operatorname{coeff}\left(m, ((\operatorname{C}\left(((q: \mathbb{Q}))^{n}\right)) \cdot (X) + \operatorname{W})^{n}\right)}{(n!: \mathbb{Q})}))$$

*Formalization.* `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.egf` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A386655–A386658, Lambert W exponential generating functions*. URL: <https://oeis.org/A386655>.

*Commentary.*

For q=2 the entry NAME reads verbatim: E.g.f.: Sum_{n>=0} (2^n*x + LambertW(x))^n / n!. The series in the n-th summand has order at least n; therefore only n at most m contributes to coefficient m. The casts and divisions are in the rational field.

**Definition 1.3 (OEIS A386655).**

$$\forall m: \mathbb{N}, \operatorname{a}\left(m\right) = \operatorname{egf}\left(2, m\right)$$

*Formalization.* `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.a` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A386655–A386658, Lambert W exponential generating functions*. URL: <https://oeis.org/A386655>.

*Commentary.*

The entry NAME reads verbatim: E.g.f.: Sum_{n>=0} (2^n*x + LambertW(x))^n / n!. Here egf is the rational coefficient function of OeisA386655LambertWEgfModSix.

**Definition 1.4 (The proposed six-term pattern).**

$$\operatorname{claim} = (\forall n: \mathbb{N}, (6 \le n) \implies (\exists z: \mathbb{Z}, ((z: \mathbb{Q}) = \operatorname{a}\left(n\right)) \land (z \bmod 6 = \operatorname{getD}\left([1, 0, 3, 0, 3, 2], (n - 6) \bmod 6, 0\right))))$$

*Formalization.* `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A386655–A386658, Lambert W exponential generating functions*. URL: <https://oeis.org/A386655>.

*Commentary.*

Conjecture: for n >= 6, a(n) (mod 6) equals [1, 0, 3, 0, 3, 2] repeating. This is the COMMENTS sentence of OEIS A386655 (unpaginated). The integer z has rational cast a(n); getD uses the zero-based index (n-6) mod 6 and default zero. Both remainder operations and natural subtraction are Lean integer or natural operations, respectively.

**Definition 1.5 (An integral closed form).**

$$\forall q: \mathbb{N}, \forall n: \mathbb{N}, \operatorname{closedZ}\left(q, n\right) = ((q: \mathbb{Z}))^{(n) \cdot (n)} + \sum_{k \in \operatorname{range}\left(n\right)} ((((\operatorname{choose}\left(n, k\right): \mathbb{Z})) \cdot (((q: \mathbb{Z}))^{(k) \cdot (k + 1)})) \cdot ((((q: \mathbb{Z}))^{k} - (n - k: \mathbb{Z}))^{n - k - 1}))$$

*Formalization.* `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.closedZ` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A386655–A386658, Lambert W exponential generating functions*. URL: <https://oeis.org/A386655>.

*Commentary.*

The FORMULA field of OEIS A386655 (unpaginated) reads verbatim: a(n) = Sum_{k=0..n} binomial(n,k) * 2^(k*(k+1)) * (2^k - (n-k))^(n-k-1). Replace 2 by the natural parameter q. Separate the last summand, whose exponent in the source formula is negative, as q^(n*n). Every remaining exponent is a natural number. Subtractions in exponents and in n-k are natural subtraction, followed by the displayed integer cast.

**Theorem 1.6 (Integrality for every q and n).**

$$\forall q: \mathbb{N}, \forall n: \mathbb{N}, \operatorname{egf}\left(q, n\right) = (\operatorname{closedZ}\left(q, n\right): \mathbb{Q})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.egf_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A386655–A386658, Lambert W exponential generating functions*. URL: <https://oeis.org/A386655>.

*Commentary.*

Lagrange inversion evaluates the coefficients of exp(y W). Binomial expansion and triangular reindexing then give the integral finite sum. This identity also supplies the integer z for each of the four coefficient sequences.

**Theorem 1.7 (Period six after the sixth index).**

$$\forall q: \mathbb{N}, \forall n: \mathbb{N}, (6 \le n) \implies (\operatorname{closedZ}\left(q, n\right) \bmod 6 = \operatorname{closedZ}\left(q, (n - 6) \bmod 6 + 6\right) \bmod 6)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.closedZ_reduce` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A386655–A386658, Lambert W exponential generating functions*. URL: <https://oeis.org/A386655>.

*Commentary.*

In ZMod(6), x cubed equals x. The binomial transform satisfies B(n+9)=B(n+3), and its endpoint corrections depend only on n modulo six. Casting the resulting identity back to integer remainders gives the displayed formula for every q.

**Theorem 1.8 (Hanna's congruence).**

$$\forall n: \mathbb{N}, (6 \le n) \implies (\exists z: \mathbb{Z}, ((z: \mathbb{Q}) = \operatorname{a}\left(n\right)) \land (z \bmod 6 = \operatorname{getD}\left([1, 0, 3, 0, 3, 2], (n - 6) \bmod 6, 0\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a386655-hanna-lambert-w-egf-mod-six` (proved) by `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a386655-hanna-lambert-w-egf-mod-six","declaration_gid":"D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A386655–A386658, Lambert W exponential generating functions*. URL: <https://oeis.org/A386655>.

*Commentary.*

The integral closed form and its six-term periodicity reduce the assertion to the six indices from six through eleven, which give the displayed pattern.

## References

- Truth anchor: `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.W`
- Truth anchor: `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.a`
- Truth anchor: `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.claim`
- Truth anchor: `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.closedZ`
- Truth anchor: `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.closedZ_reduce`
- Truth anchor: `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.egf`
- Truth anchor: `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.egf_closed`
- Truth anchor: `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.result`
- Dependency: [D5/S1/Recurrence/Invariants/TripleIterateShiftModThree](../../../S1/Recurrence/Invariants/TripleIterateShiftModThree.md)
- Dependency: [D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree](../../../S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.md)
- Dependency: [D5/S1/Recurrence/Residue/QuarticEGFModFour](../../../S1/Recurrence/Residue/QuarticEGFModFour.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo](../Nonnesting/NonnestingOneThreeTwoTwo.md)
