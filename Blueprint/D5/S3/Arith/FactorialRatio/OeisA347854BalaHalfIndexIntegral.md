# Bala A347854: integrality at every natural index

## Abstract

Bala A347854 integrality.

**Definition 1.1 (ffact).**

$$\forall x \in \mathbb{R},\; \operatorname{ffact}\left(x\right) = \operatorname{Real}.\operatorname{Gamma}\left(1 + x\right)$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.ffact` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

OEIS A347854, COMMENTS (unpaginated): "Fractional factorials are defined using the Gamma function; for example, (n/2)! := Gamma(1 + n/2)." The function ffact uses a real argument.

**Definition 1.2 (a).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \frac{(\operatorname{Nat}.\operatorname{factorial}\left(6 \cdot n\right): \mathbb{R})}{(\operatorname{Nat}.\operatorname{factorial}\left(3 \cdot n\right): \mathbb{R}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(2 \cdot n\right): \mathbb{R})} \cdot \frac{\operatorname{ffact}\left(\frac{(n: \mathbb{R})}{2}\right)}{\operatorname{ffact}\left(\frac{3 \cdot (n: \mathbb{R})}{2}\right)}$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.a` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

OEIS A347854, NAME (unpaginated): "a(n) = (6*n)!/((3*n)!*(2*n)!) * (n/2)!/(3*n/2)!." Natural factorials are cast to the reals; fractional factorials use ffact.

**Definition 1.3 (claim).**

$$\operatorname{claim} = (\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; (z: \mathbb{R}) = \operatorname{a}\left(n\right))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.claim` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

OEIS A347854, COMMENTS (unpaginated): "The sequence is conjectured to be integral." Integrality means that for every natural index, including zero, the value is the cast of an integer.

**Theorem 1.4 (mul_div_reduce).**

$$\forall c \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; (0 < q) \implies (\operatorname{Nat}.\operatorname{div}\left(c \cdot n, q\right) = c \cdot \operatorname{Nat}.\operatorname{div}\left(n, q\right) + \operatorname{Nat}.\operatorname{div}\left(c \cdot \operatorname{Nat}.\operatorname{mod}\left(n, q\right), q\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.mul_div_reduce` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

Natural floor division separates a multiple of the quotient from the contribution of the remainder. Nat.div and Nat.mod denote natural division and remainder.

**Theorem 1.5 (grid_floor).**

$$\forall L \in \mathbb{N},\; \forall c \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall q \in \mathbb{N},\; (0 < q) \implies ((0 < d) \implies ((L = c \cdot d) \implies (\operatorname{Nat}.\operatorname{div}\left(c \cdot r, q\right) = \operatorname{Nat}.\operatorname{div}\left(\operatorname{Nat}.\operatorname{div}\left(L \cdot r, q\right), d\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.grid_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

When L equals c times the positive integer d, division of the L-scaled numerator and then by d gives the c-scaled quotient. Nat.div denotes natural floor division.

**Theorem 1.6 (factorial_prod_dvd_of_floor).**

$$\forall A \in \operatorname{List}\left(\mathbb{N}\right),\; \forall B \in \operatorname{List}\left(\mathbb{N}\right),\; (\forall q \in \mathbb{N},\; (0 < q) \implies (\operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left(\operatorname{fun} (n: \mathbb{N}) \mapsto \operatorname{Nat}.\operatorname{div}\left(n, q\right), B\right)\right) \le \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left(\operatorname{fun} (n: \mathbb{N}) \mapsto \operatorname{Nat}.\operatorname{div}\left(n, q\right), A\right)\right))) \implies (\operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{map}\left(\operatorname{Nat}.\operatorname{factorial}, B\right)\right) \mid \operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{map}\left(\operatorname{Nat}.\operatorname{factorial}, A\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.factorial_prod_dvd_of_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

If every positive-modulus floor sum of B is at most the corresponding sum of A, the product of the factorials in B divides that in A. Nat.div denotes natural floor division. Legendre valuations turn the floor inequalities into divisibility.

**Theorem 1.7 (quotient_cast_integral).**

$$\forall A \in \mathbb{N},\; \forall B \in \mathbb{N},\; (B \mid A) \implies ((B \neq 0) \implies (\exists z \in \mathbb{Z},\; (z: \mathbb{R}) = \frac{(A: \mathbb{R})}{(B: \mathbb{R})}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.quotient_cast_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

A quotient of natural numbers with a nonzero denominator that divides the numerator is the real cast of an integer.

**Definition 1.8 (h856).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; \operatorname{h856}\left(n, q\right) = (\operatorname{Nat}.\operatorname{div}\left(12 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(1 \cdot n, q\right): \mathbb{Z}) - \left((\operatorname{Nat}.\operatorname{div}\left(8 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(2 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(3 \cdot n, q\right): \mathbb{Z})\right)$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.h856` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

The integer-valued floor defect for this factorial ratio. Nat.div denotes natural floor division before the cast to the integers. The associated Landau function occurs in Bober, Table 2.

**Theorem 1.9 (h856_nonneg).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; (0 < q) \implies (0 \le \operatorname{h856}\left(n, q\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.h856_nonneg` (`✓ std3`). ∎

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

This floor defect is nonnegative at every natural numerator and positive modulus. Reduction modulo the modulus and subdivision at the floor breakpoints gives the inequality.

**Definition 1.10 (h857).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; \operatorname{h857}\left(n, q\right) = (\operatorname{Nat}.\operatorname{div}\left(12 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(3 \cdot n, q\right): \mathbb{Z}) - \left((\operatorname{Nat}.\operatorname{div}\left(6 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(4 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(5 \cdot n, q\right): \mathbb{Z})\right)$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.h857` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

The integer-valued floor defect for this factorial ratio. Nat.div denotes natural floor division before the cast to the integers. The associated Landau function occurs in Bober, Table 2.

**Theorem 1.11 (h857_nonneg).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; (0 < q) \implies (0 \le \operatorname{h857}\left(n, q\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.h857_nonneg` (`✓ std3`). ∎

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

This floor defect is nonnegative at every natural numerator and positive modulus. Reduction modulo the modulus and subdivision at the floor breakpoints gives the inequality.

**Definition 1.12 (h858).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; \operatorname{h858}\left(n, q\right) = (\operatorname{Nat}.\operatorname{div}\left(18 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(1 \cdot n, q\right): \mathbb{Z}) - \left((\operatorname{Nat}.\operatorname{div}\left(6 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(4 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(9 \cdot n, q\right): \mathbb{Z})\right)$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.h858` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

The integer-valued floor defect for this factorial ratio. Nat.div denotes natural floor division before the cast to the integers. The associated Landau function occurs in Bober, Table 2.

**Theorem 1.13 (h858_nonneg).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; (0 < q) \implies (0 \le \operatorname{h858}\left(n, q\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.h858_nonneg` (`✓ std3`). ∎

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

This floor defect is nonnegative at every natural numerator and positive modulus. Reduction modulo the modulus and subdivision at the floor breakpoints gives the inequality.

**Definition 1.14 (k856).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; \operatorname{k856}\left(n, q\right) = (\operatorname{Nat}.\operatorname{div}\left(12 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(3 \cdot n, q\right): \mathbb{Z}) - \left((\operatorname{Nat}.\operatorname{div}\left(8 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(6 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(1 \cdot n, q\right): \mathbb{Z})\right)$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.k856` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

The integer-valued floor defect for this factorial ratio. Nat.div denotes natural floor division before the cast to the integers. The associated Landau function occurs in Bober, Table 2.

**Theorem 1.15 (k856_nonneg).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; (0 < q) \implies (0 \le \operatorname{k856}\left(n, q\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.k856_nonneg` (`✓ std3`). ∎

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

This floor defect is nonnegative at every natural numerator and positive modulus. Reduction modulo the modulus and subdivision at the floor breakpoints gives the inequality.

**Definition 1.16 (k857).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; \operatorname{k857}\left(n, q\right) = (\operatorname{Nat}.\operatorname{div}\left(12 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(5 \cdot n, q\right): \mathbb{Z}) - \left((\operatorname{Nat}.\operatorname{div}\left(4 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(10 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(3 \cdot n, q\right): \mathbb{Z})\right)$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.k857` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

The integer-valued floor defect for this factorial ratio. Nat.div denotes natural floor division before the cast to the integers. The associated Landau function occurs in Bober, Table 2.

**Theorem 1.17 (k857_nonneg).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; (0 < q) \implies (0 \le \operatorname{k857}\left(n, q\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.k857_nonneg` (`✓ std3`). ∎

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

This floor defect is nonnegative at every natural numerator and positive modulus. Reduction modulo the modulus and subdivision at the floor breakpoints gives the inequality.

**Definition 1.18 (k858).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; \operatorname{k858}\left(n, q\right) = (\operatorname{Nat}.\operatorname{div}\left(2 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(9 \cdot n, q\right): \mathbb{Z}) - \left((\operatorname{Nat}.\operatorname{div}\left(6 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(4 \cdot n, q\right): \mathbb{Z}) + (\operatorname{Nat}.\operatorname{div}\left(1 \cdot n, q\right): \mathbb{Z})\right)$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.k858` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

The integer-valued floor defect for this factorial ratio. Nat.div denotes natural floor division before the cast to the integers. The associated Landau function occurs in Bober, Table 2.

**Theorem 1.19 (k858_nonneg).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; (0 < q) \implies (0 \le \operatorname{k858}\left(n, q\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.k858_nonneg` (`✓ std3`). ∎

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

This floor defect is nonnegative at every natural numerator and positive modulus. Reduction modulo the modulus and subdivision at the floor breakpoints gives the inequality.

**Theorem 1.20 (gamma_nat).**

$$\forall n \in \mathbb{N},\; \operatorname{Real}.\operatorname{Gamma}\left(1 + (n: \mathbb{R})\right) = (\operatorname{Nat}.\operatorname{factorial}\left(n\right): \mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.gamma_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

The Gamma value at one plus a natural number equals its factorial.

**Theorem 1.21 (gamma_ratio_half).**

$$\forall r \in \mathbb{N},\; \forall s \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{mod}\left(r, 2\right) = 1) \implies ((\operatorname{Nat}.\operatorname{mod}\left(s, 2\right) = 1) \implies ((r \le s) \implies (\frac{\operatorname{Real}.\operatorname{Gamma}\left(1 + \frac{(r: \mathbb{R})}{2}\right)}{\operatorname{Real}.\operatorname{Gamma}\left(1 + \frac{(s: \mathbb{R})}{2}\right)} = (2: \mathbb{R})^{s - r} \cdot \frac{(\operatorname{Nat}.\operatorname{factorial}\left(r\right): \mathbb{R}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(\operatorname{Nat}.\operatorname{div}\left(s, 2\right)\right): \mathbb{R})}{(\operatorname{Nat}.\operatorname{factorial}\left(s\right): \mathbb{R}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(\operatorname{Nat}.\operatorname{div}\left(r, 2\right)\right): \mathbb{R})})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.gamma_ratio_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

For odd natural r ≤ s, the quotient of the two half-integer Gamma values is a factorial ratio times 2 raised to s−r. Nat.div denotes natural floor division in the factorial arguments.

**Theorem 1.22 (gamma_third_ratio).**

$$\forall n \in \mathbb{N},\; \frac{\operatorname{Real}.\operatorname{Gamma}\left(1 + \frac{(n: \mathbb{R})}{3}\right)}{\operatorname{Real}.\operatorname{Gamma}\left(1 + \frac{4 \cdot (n: \mathbb{R})}{3}\right)} = \frac{(3: \mathbb{R})^{n}}{\prod_{k \in \operatorname{Finset}.\operatorname{range}\left(n\right)} ((n: \mathbb{R}) + 3 \cdot \left((k: \mathbb{R}) + 1\right))}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.gamma_third_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

Applying the Gamma recurrence n times expresses the third-index quotient as 3 to the power n divided by a product of n positive linear factors.

**Theorem 1.23 (even_dvd).**

$$\forall m \in \mathbb{N},\; \operatorname{Nat}.\operatorname{factorial}\left(6 \cdot m\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(4 \cdot m\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(3 \cdot m\right) \mid \operatorname{Nat}.\operatorname{factorial}\left(12 \cdot m\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(1 \cdot m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.even_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

The denominator of the even-index factorial expression divides its numerator. This supplies both the half-index sequence and the third-index sequence at multiples of three.

**Theorem 1.24 (result).**

$$\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; (z: \mathbb{R}) = \operatorname{a}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a347854-bala-half-index-integrality` (proved) by `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a347854-bala-half-index-integrality","declaration_gid":"D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

Every natural index has an integer value. Reduction to factorial quotients and comparison of prime valuations give an integer cast.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.a`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.claim`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.even_dvd`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.factorial_prod_dvd_of_floor`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.ffact`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.gamma_nat`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.gamma_ratio_half`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.gamma_third_ratio`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.grid_floor`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.h856`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.h856_nonneg`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.h857`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.h857_nonneg`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.h858`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.h858_nonneg`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.k856`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.k856_nonneg`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.k857`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.k857_nonneg`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.k858`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.k858_nonneg`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.mul_div_reduce`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.quotient_cast_integral`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.result`
