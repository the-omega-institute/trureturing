# Tebni's logarithmic coefficient divisibility criterion

## Abstract

The divisibility criterion and shared prime residues of the logarithmic coefficient array.

PowerSeries.logOf is the formal logarithm at a series with constant coefficient one. All indices are natural numbers starting at zero. In T, Nat.div is natural-number division, followed by the displayed cast to integers. Int.ModEq takes the integer modulus first. The inverse series invOneSubPow includes exponent zero.

**Definition 1.1 (The logarithmic series).**

$$L = \operatorname{PowerSeries}.\operatorname{logOf}\left((1 - X) \cdot (1 - 2 \cdot X)^{-1}\right)$$

*Formalization.* `D5/S3/Arith/Congruence/TebniA355257Divisibility.L` (`✓ std3`).

*Citation.* Peter Luschny and Mélika Tebni (2022). *OEIS A355257, logarithmic coefficient array and congruence conjectures*. URL: <https://oeis.org/A355257>.

*Commentary.*

OEIS A355257, revision 37, NAME (unpaginated): "Array read by ascending antidiagonals. A(n, k) = k! * [x^k] log((1 - x) / (1 - 2*x)) / (1 - x)^n, for 0 <= k <= n." L is the formal logarithm of the numerator times the inverse denominator over Q.

**Definition 1.2 (The source coefficient array).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{A}\left(n, k\right) = (k!: \mathbb{Q}) \cdot \operatorname{PowerSeries}.\operatorname{coeff}\left(k, L \cdot ((1 - X)^{n})^{-1}\right)$$

*Formalization.* `D5/S3/Arith/Congruence/TebniA355257Divisibility.A` (`✓ std3`).

*Citation.* Peter Luschny and Mélika Tebni (2022). *OEIS A355257, logarithmic coefficient array and congruence conjectures*. URL: <https://oeis.org/A355257>.

*Commentary.*

OEIS A355257, revision 37, NAME (unpaginated): "Array read by ascending antidiagonals. A(n, k) = k! * [x^k] log((1 - x) / (1 - 2*x)) / (1 - x)^n, for 0 <= k <= n." The same formal coefficient expression defines A for every natural n and k, including n=0.

**Definition 1.3 (Integer summands).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{T}\left(n, k, j\right) = (\operatorname{Nat}.\operatorname{div}\left(k!, j\right): \mathbb{Z}) \cdot ((2: \mathbb{Z})^{j} - 1) \cdot \operatorname{PowerSeries}.\operatorname{coeff}\left(k - j, \operatorname{val}\left(\operatorname{PowerSeries}.\operatorname{invOneSubPow}\left(\mathbb{Z}, n\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Congruence/TebniA355257Divisibility.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Luschny and Mélika Tebni (2022). *OEIS A355257, logarithmic coefficient array and congruence conjectures*. URL: <https://oeis.org/A355257>.

*Commentary.*

Each summand multiplies the integer factorial quotient by 2^j-1 and by the degree k-j coefficient of the integral inverse power of 1-X. The j=0 term vanishes.

**Definition 1.4 (The representing integer).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{Z}\left(n, k\right) = \sum_{j \in \operatorname{Finset}.\operatorname{range}\left(k + 1\right)} \operatorname{T}\left(n, k, j\right)$$

*Formalization.* `D5/S3/Arith/Congruence/TebniA355257Divisibility.Z` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Luschny and Mélika Tebni (2022). *OEIS A355257, logarithmic coefficient array and congruence conjectures*. URL: <https://oeis.org/A355257>.

*Commentary.*

The finite sum includes j=0 through j=k. It represents the rational coefficient A(n,k) as an integer.

**Theorem 1.5 (Integrality of every coefficient).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{A}\left(n, k\right) = (\operatorname{Z}\left(n, k\right): \mathbb{Q})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TebniA355257Divisibility.A_eq_Z` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Luschny and Mélika Tebni (2022). *OEIS A355257, logarithmic coefficient array and congruence conjectures*. URL: <https://oeis.org/A355257>.

*Commentary.*

The logarithmic degree-j coefficient is (2^j-1)/j. Coefficient convolution with the inverse power series and factorial divisibility give the displayed integer sum, also when n=0 or k=0.

**Theorem 1.6 (Prime residues).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow (\operatorname{Int}.\operatorname{ModEq}\left((p: \mathbb{Z}), \operatorname{Z}\left(n, p\right), -1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TebniA355257Divisibility.prime_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Luschny and Mélika Tebni (2022). *OEIS A355257, logarithmic coefficient array and congruence conjectures*. URL: <https://oeis.org/A355257>.

*Commentary.*

All summands with j<p vanish modulo p. Wilson's theorem and the finite-field power identity make the remaining summand equal to minus one. This residue also determines the prime quotient.

**Theorem 1.7 (The divisor preceding a prime).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow ((\operatorname{Even}\left(n\right)) \Rightarrow (((p: \mathbb{Z}) - 1) \mid \operatorname{Z}\left(n, p\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TebniA355257Divisibility.even_pred_divides` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Luschny and Mélika Tebni (2022). *OEIS A355257, logarithmic coefficient array and congruence conjectures*. URL: <https://oeis.org/A355257>.

*Commentary.*

Modulo p-1 only the j=p-1 summand can remain. For primes at least seven, p-1 divides (p-2)!. At p=3 and p=5 the even factor n supplies the missing divisibility; p=2 has modulus one.

**Definition 1.8 (The source conjecture).**

$$claim = (\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; (1 \le k) \Rightarrow ((k \ne 4) \Rightarrow (\exists z \in \mathbb{Z},\; ((z: \mathbb{Q}) = \operatorname{A}\left(n, k\right)) \land (((k: \mathbb{Z}) \mid z) \Leftrightarrow \left(\neg \operatorname{Nat}.\operatorname{Prime}\left(k\right)\right)))))$$

*Formalization.* `D5/S3/Arith/Congruence/TebniA355257Divisibility.claim` (`✓ std3`).

*Citation.* Peter Luschny and Mélika Tebni (2022). *OEIS A355257, logarithmic coefficient array and congruence conjectures*. URL: <https://oeis.org/A355257>.

*Commentary.*

OEIS A355257, revision 37, COMMENTS (unpaginated): "Conjecture: Let n >= 0, k >= 1 and k != 4. Then k divides A(n, k) if and only if k is not prime." An integer z equal to A(n,k) expresses integer divisibility of the rational coefficient. The natural index n includes zero, and k is positive and different from four.

**Theorem 1.9 (The divisibility criterion holds).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; (1 \le k) \Rightarrow ((k \ne 4) \Rightarrow (\exists z \in \mathbb{Z},\; ((z: \mathbb{Q}) = \operatorname{A}\left(n, k\right)) \land (((k: \mathbb{Z}) \mid z) \Leftrightarrow \left(\neg \operatorname{Nat}.\operatorname{Prime}\left(k\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TebniA355257Divisibility.result` (`✓ std3`). ∎

*Resolves.* `Problems/tebni355257-logcoef` (proved) by `D5/S3/Arith/Congruence/TebniA355257Divisibility.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tebni355257-logcoef","declaration_gid":"D5/S3/Arith/Congruence/TebniA355257Divisibility.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Luschny and Mélika Tebni (2022). *OEIS A355257, logarithmic coefficient array and congruence conjectures*. URL: <https://oeis.org/A355257>.

*Commentary.*

Modulo k all terms below j=k vanish. The remaining value is (k-1)! times 2^k-1. For prime k it is minus one; for composite k other than four the factorial is divisible by k. The index k=1 is included.

## References

- Truth anchor: `D5/S3/Arith/Congruence/TebniA355257Divisibility.A`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA355257Divisibility.A_eq_Z`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA355257Divisibility.L`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA355257Divisibility.T`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA355257Divisibility.Z`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA355257Divisibility.claim`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA355257Divisibility.even_pred_divides`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA355257Divisibility.prime_residue`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA355257Divisibility.result`
- Dependency: [D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue](LaymanOddPowerFactorialResidue.md)
