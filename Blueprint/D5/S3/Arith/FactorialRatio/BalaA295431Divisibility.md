# Bala A295431: five fixed quotients and two uniform families

## Abstract

Actual T divisibilities.

**Definition 1.1 (ratio).**

$$\forall n \in \mathbb{N},\; \operatorname{ratio}\left(n\right) = \frac{(\operatorname{factorial}\left(12 \cdot n\right): \mathbb{Q}) \cdot (\operatorname{factorial}\left(n\right): \mathbb{Q})}{(\operatorname{factorial}\left(6 \cdot n\right): \mathbb{Q}) \cdot (\operatorname{factorial}\left(4 \cdot n\right): \mathbb{Q}) \cdot (\operatorname{factorial}\left(3 \cdot n\right): \mathbb{Q})}$$

*Formalization.* `D5/S3/Arith/FactorialRatio/BalaA295431Divisibility.ratio` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Bala's parity conjecture and product extensions of his divisibilities (2026): OEIS A295462, References (#19, 23 August 2026)*. URL: <https://oeis.org/A295431>.

*Commentary.*

T(n) is the actual rational factorial ratio (12n)! n! / ((6n)! (4n)! (3n)!). Every index is natural, including zero. The existing even_dvd producer at OeisA347854BalaHalfIndexIntegral supplies its integrality; that prior result is not new content here.

**Definition 1.2 (rising_denominator).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall R \in \mathbb{N},\; \operatorname{risingdenominator}\left(k, n, R\right) = \prod_{i \in \operatorname{Icc}\left(1, R\right)} (k \cdot n + i)$$

*Formalization.* `D5/S3/Arith/FactorialRatio/BalaA295431Divisibility.rising_denominator` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Bala's parity conjecture and product extensions of his divisibilities (2026): OEIS A295462, References (#19, 23 August 2026)*. URL: <https://oeis.org/A295431>.

*Commentary.*

The natural product of k*n+i over 1 <= i <= R is positive whenever the interval is nonempty and equals one for R=0. Its rational cast is the denominator of the first uniform family.

**Definition 1.3 (signed_denominator).**

$$\forall n \in \mathbb{N},\; \forall R \in \mathbb{N},\; \operatorname{signeddenominator}\left(n, R\right) = \prod_{i \in \operatorname{filter}\left(\operatorname{fun} i \mapsto \operatorname{Coprime}\left(i, 12\right), \operatorname{Icc}\left(1, R\right)\right)} (12 \cdot (n: \mathbb{Z}) - (i: \mathbb{Z}))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/BalaA295431Divisibility.signed_denominator` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Bala's parity conjecture and product extensions of his divisibilities (2026): OEIS A295462, References (#19, 23 August 2026)*. URL: <https://oeis.org/A295431>.

*Commentary.*

This integer product runs over 1 <= i <= R with gcd(i,12)=1. Subtraction takes place in the integers before the rational cast. None of its factors is zero, even when R exceeds 12n. A product over an empty set equals one.

**Definition 1.4 (first_constant).**

$$\forall R \in \mathbb{N},\; \operatorname{firstconstant}\left(R\right) = 36 \cdot \operatorname{factorial}\left(\operatorname{NatSub}\left(R, 1\right)\right) \cdot \operatorname{lcmUpto}\left(12 \cdot R\right)$$

*Formalization.* `D5/S3/Arith/FactorialRatio/BalaA295431Divisibility.first_constant` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Bala's parity conjecture and product extensions of his divisibilities (2026): OEIS A295462, References (#19, 23 August 2026)*. URL: <https://oeis.org/A295431>.

*Commentary.*

C(R)=36*(R-1)!*lcm(1,...,12R), independently of k. NatSub denotes natural subtraction, which occurs only in the factorial index; the theorem assumes R>=1. The constant is sufficient, with no minimality assertion.

**Definition 1.5 (second_constant).**

$$\forall R \in \mathbb{N},\; \operatorname{secondconstant}\left(R\right) = \operatorname{factorial}\left(\operatorname{NatSub}\left(R, 1\right)\right) \cdot \operatorname{lcmUpto}\left(R\right)$$

*Formalization.* `D5/S3/Arith/FactorialRatio/BalaA295431Divisibility.second_constant` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Bala's parity conjecture and product extensions of his divisibilities (2026): OEIS A295462, References (#19, 23 August 2026)*. URL: <https://oeis.org/A295431>.

*Commentary.*

D(R)=(R-1)!*lcm(1,...,R). The least common multiple is mathlib Nat.lcmUpto. This is a sufficient constant for the signed family.

**Definition 1.6 (claim).**

$$\operatorname{claim} = ((\forall n \in \mathbb{N},\; ((((((\exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \frac{385 \cdot \operatorname{ratio}\left(n\right)}{(n: \mathbb{Q}) + 1}) \land (\exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \frac{5 \cdot \operatorname{ratio}\left(n\right)}{2 \cdot (n: \mathbb{Q}) + 1})) \land (\exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \frac{\operatorname{ratio}\left(n\right)}{3 \cdot (n: \mathbb{Q}) + 1})) \land (\exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \frac{770 \cdot \operatorname{ratio}\left(n\right)}{\left((n: \mathbb{Q}) + 1\right) \cdot \left(2 \cdot (n: \mathbb{Q}) + 1\right) \cdot \left(3 \cdot (n: \mathbb{Q}) + 1\right)})) \land (\exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \frac{\operatorname{ratio}\left(n\right)}{12 \cdot (n: \mathbb{Q}) - 1})) \land (\forall R \in \mathbb{N},\; (1 \le R) \implies (\forall k \in \mathbb{N},\; ((1 \le k) \land (k \le 3)) \implies ((\operatorname{risingdenominator}\left(k, n, R\right) \neq 0) \land (\exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \frac{(\operatorname{firstconstant}\left(R\right): \mathbb{Q}) \cdot \operatorname{ratio}\left(n\right)}{(\operatorname{risingdenominator}\left(k, n, R\right): \mathbb{Q})}))))) \land (\forall R \in \mathbb{N},\; (1 \le R) \implies ((\operatorname{signeddenominator}\left(n, R\right) \neq 0) \land (\exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \frac{(\operatorname{secondconstant}\left(R\right): \mathbb{Q}) \cdot \operatorname{ratio}\left(n\right)}{(\operatorname{signeddenominator}\left(n, R\right): \mathbb{Q})})))) \land (\frac{\operatorname{ratio}\left(0\right)}{12 \cdot (0: \mathbb{Q}) - 1} = 0 - 1))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/BalaA295431Divisibility.claim` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Bala's parity conjecture and product extensions of his divisibilities (2026): OEIS A295462, References (#19, 23 August 2026)*. URL: <https://oeis.org/A295431>.

*Commentary.*

Corollary 5 of Ma and Zhang, revision 3, states all five fixed expressions and both families for all natural n. The family quantifiers preserve every R>=1 and each k=1,2,3. Integer realizations concern the actual rational expressions, with nonzero denominator assertions for both products and the signed value -1 at zero.

**Theorem 1.7 (result).**

$$(\forall n \in \mathbb{N},\; ((((((\exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \frac{385 \cdot \operatorname{ratio}\left(n\right)}{(n: \mathbb{Q}) + 1}) \land (\exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \frac{5 \cdot \operatorname{ratio}\left(n\right)}{2 \cdot (n: \mathbb{Q}) + 1})) \land (\exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \frac{\operatorname{ratio}\left(n\right)}{3 \cdot (n: \mathbb{Q}) + 1})) \land (\exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \frac{770 \cdot \operatorname{ratio}\left(n\right)}{\left((n: \mathbb{Q}) + 1\right) \cdot \left(2 \cdot (n: \mathbb{Q}) + 1\right) \cdot \left(3 \cdot (n: \mathbb{Q}) + 1\right)})) \land (\exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \frac{\operatorname{ratio}\left(n\right)}{12 \cdot (n: \mathbb{Q}) - 1})) \land (\forall R \in \mathbb{N},\; (1 \le R) \implies (\forall k \in \mathbb{N},\; ((1 \le k) \land (k \le 3)) \implies ((\operatorname{risingdenominator}\left(k, n, R\right) \neq 0) \land (\exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \frac{(\operatorname{firstconstant}\left(R\right): \mathbb{Q}) \cdot \operatorname{ratio}\left(n\right)}{(\operatorname{risingdenominator}\left(k, n, R\right): \mathbb{Q})}))))) \land (\forall R \in \mathbb{N},\; (1 \le R) \implies ((\operatorname{signeddenominator}\left(n, R\right) \neq 0) \land (\exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \frac{(\operatorname{secondconstant}\left(R\right): \mathbb{Q}) \cdot \operatorname{ratio}\left(n\right)}{(\operatorname{signeddenominator}\left(n, R\right): \mathbb{Q})})))) \land (\frac{\operatorname{ratio}\left(0\right)}{12 \cdot (0: \mathbb{Q}) - 1} = 0 - 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/BalaA295431Divisibility.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Bala's parity conjecture and product extensions of his divisibilities (2026): OEIS A295462, References (#19, 23 August 2026)*. URL: <https://oeis.org/A295431>.

*Commentary.*

All seven outcomes hold. Legendre valuations reuse the original h854 and h854_nonneg floor producer, reduced modulo each prime power. At a level dividing k*n+i with modulus at least 12*i, the left floor cells give defect one for every prime, including 2 and 3. For 12*n-i, the right cells and coprimality give defect one beyond R. Removing a factor of maximal valuation bounds the remaining product by valuations of index differences; their product divides (R-1)!. The lcm valuations supply the logarithmic losses. The required factor 36 is retained without a minimality claim. For the fixed constants, the only large-prime missing first levels are 5,7,11 for n+1 and 5 for 2n+1. At 2 and 3, factorial multiplication identities identify the needed valuations with those of binomial coefficients, and the adjacent-binomial identity supplies the lower bounds. The first two denominators are coprime, and gcd((n+1)*(2n+1),3n+1) divides 2, giving constant 770. The fifth fixed assertion is obtained internally from the signed family at R=1; it is not a separately discovered result. At n=0 its denominator is -1 and T(0)=1. Attribution is to the supplied Corollary 5 and earlier literature; no priority, world novelty, converse, congruence, Gamma, moment-density or other-ratio claim is made.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA295431Divisibility.claim`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA295431Divisibility.first_constant`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA295431Divisibility.ratio`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA295431Divisibility.result`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA295431Divisibility.rising_denominator`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA295431Divisibility.second_constant`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA295431Divisibility.signed_denominator`
- Dependency: [D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral](OeisA347854BalaHalfIndexIntegral.md)
