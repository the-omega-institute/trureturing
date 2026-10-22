# Hanna's OEIS 386658 congruence

## Abstract

Integrality and a period-six congruence for Hanna's Lambert W exponential coefficients.

**Definition 1.1 (OEIS A386658).**

$$\forall m: \mathbb{N}, \operatorname{a}\left(m\right) = \operatorname{egf}\left(5, m\right)$$

*Formalization.* `D5/S3/Combinatorics/HannaLambertW/OeisA386658LambertWEgfModSix.a` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A386655–A386658, Lambert W exponential generating functions*. URL: <https://oeis.org/A386655>.

*Commentary.*

The entry NAME reads verbatim: E.g.f.: Sum_{n>=0} (5^n*x + LambertW(x))^n / n!. Here egf is the rational coefficient function of OeisA386655LambertWEgfModSix.

**Definition 1.2 (The proposed six-term pattern).**

$$\operatorname{claim} = (\forall n: \mathbb{N}, (6 \le n) \implies (\exists z: \mathbb{Z}, ((z: \mathbb{Q}) = \operatorname{a}\left(n\right)) \land (z \bmod 6 = \operatorname{getD}\left([4, 3, 0, 3, 0, 5], (n - 6) \bmod 6, 0\right))))$$

*Formalization.* `D5/S3/Combinatorics/HannaLambertW/OeisA386658LambertWEgfModSix.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A386655–A386658, Lambert W exponential generating functions*. URL: <https://oeis.org/A386655>.

*Commentary.*

Conjecture: for n >= 6, a(n) (mod 6) equals [4, 3, 0, 3, 0, 5] repeating. This is the COMMENTS sentence of OEIS A386658 (unpaginated). The integer z has rational cast a(n); getD uses the zero-based index (n-6) mod 6 and default zero. Both remainder operations and natural subtraction are Lean integer or natural operations, respectively.

**Theorem 1.3 (Hanna's congruence).**

$$\forall n: \mathbb{N}, (6 \le n) \implies (\exists z: \mathbb{Z}, ((z: \mathbb{Q}) = \operatorname{a}\left(n\right)) \land (z \bmod 6 = \operatorname{getD}\left([4, 3, 0, 3, 0, 5], (n - 6) \bmod 6, 0\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/HannaLambertW/OeisA386658LambertWEgfModSix.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A386655–A386658, Lambert W exponential generating functions*. URL: <https://oeis.org/A386655>.

*Commentary.*

The integral closed form and its six-term periodicity reduce the assertion to the six indices from six through eleven, which give the displayed pattern.

## References

- Truth anchor: `D5/S3/Combinatorics/HannaLambertW/OeisA386658LambertWEgfModSix.a`
- Truth anchor: `D5/S3/Combinatorics/HannaLambertW/OeisA386658LambertWEgfModSix.claim`
- Truth anchor: `D5/S3/Combinatorics/HannaLambertW/OeisA386658LambertWEgfModSix.result`
- Dependency: [D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix](OeisA386655LambertWEgfModSix.md)
