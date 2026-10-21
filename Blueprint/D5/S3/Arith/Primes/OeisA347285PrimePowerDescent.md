# De Vlieger's descending prime-power exponents

## Abstract

Descending prime-power exponents end at one, so their absolute first differences sum to n minus one.

The primes are indexed from one. The function prime is D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative.prime, whose value at k is Nat.nth Nat.Prime (k - 1). All row indices, exponents and lengths are natural numbers; subtraction between them is truncated natural subtraction. Nat.floor rounds a real number down to a natural number, returning zero for negative inputs. The casts in the recurrence are to the reals; the casts in S and the conjecture are to the integers.

**Definition 1.1 (The exponent recurrence).**

$$\begin{aligned}\forall n \in \mathbb{N},\; \operatorname{e}\left(n, 0\right) = n\\\forall n \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{e}\left(n, j + 1\right) = \operatorname{Nat}.\operatorname{floor}\left(\operatorname{Real}.\operatorname{logb}\left((\operatorname{prime}\left(j + 2\right): \mathbb{R}), ((\operatorname{prime}\left(j + 1\right): \mathbb{R}))^{\operatorname{e}\left(n, j\right)}\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Arith/Primes/OeisA347285PrimePowerDescent.e` (`✓ std3`).

*Citation.* M. De Vlieger; OEIS Foundation Inc. (2021). *OEIS A347285 descending prime-power exponents*. URL: <https://oeis.org/A347285>.

*Commentary.*

OEIS A347285, NAME (unpaginated): "Irregular triangle T(n,k) starting with n followed by e_k = floor(log_p_k(p_(k-1)^e_(k-1))) such that e_k > 0." FORMULA (unpaginated): "T(n,1) = n; T(n,k) = floor(log_p_k(p_(k-1)^T(n,k-1)))." Here e n j is T(n,j+1); e extends the row through its first zero and thereafter. The logarithm is Real.logb and the floor is Nat.floor.

**Definition 1.2 (The number of positive entries).**

$$\forall n \in \mathbb{N},\; \operatorname{len}\left(n\right) = (\operatorname{if} h: (\exists j \in \mathbb{N},\; \operatorname{e}\left(n, j\right) = 0) \operatorname{then} \operatorname{Nat}.\operatorname{find}\left(h\right) \operatorname{else} 0)$$

*Formalization.* `D5/S3/Arith/Primes/OeisA347285PrimePowerDescent.len` (`✓ std3`).

*Citation.* M. De Vlieger; OEIS Foundation Inc. (2021). *OEIS A347285 descending prime-power exponents*. URL: <https://oeis.org/A347285>.

*Commentary.*

OEIS A347285, COMMENTS (unpaginated): "T(0,1) = 0 by convention; 0 is not allowed for n > 0." Together with "such that e_k > 0" in the NAME, this selects the positive entries. The length is the first zero index; the displayed fallback is zero when no such index exists. The proof establishes that a zero index exists for every n. At n=0, len is zero; the separately listed source row {0} is outside the positive-row conjecture.

**Definition 1.3 (The absolute first differences).**

$$\forall n \in \mathbb{N},\; \operatorname{S}\left(n\right) = \sum_{i \in \operatorname{Finset}.\operatorname{range}\left(\operatorname{len}\left(n\right) - 1\right)} \operatorname{Int}.\operatorname{natAbs}\left(((\operatorname{e}\left(n, i + 1\right): \mathbb{Z}) - (\operatorname{e}\left(n, i\right): \mathbb{Z}))\right)$$

*Formalization.* `D5/S3/Arith/Primes/OeisA347285PrimePowerDescent.S` (`✓ std3`).

*Citation.* M. De Vlieger; OEIS Foundation Inc. (2021). *OEIS A347285 descending prime-power exponents*. URL: <https://oeis.org/A347285>.

*Commentary.*

OEIS A347285, COMMENTS (unpaginated): "Conjecture: let S be the sum of the absolute values of the first differences of terms in row n. For all n > 0, n - S = 1." The index i ranges from zero through len n minus two. Int.natAbs makes each integer difference a natural summand; the range is empty for a row of length at most one.

**Definition 1.4 (De Vlieger's conjecture).**

$$claim = (\forall n \in \mathbb{N},\; (0 < n) \Rightarrow ((n: \mathbb{Z}) - (\operatorname{S}\left(n\right): \mathbb{Z}) = 1))$$

*Formalization.* `D5/S3/Arith/Primes/OeisA347285PrimePowerDescent.claim` (`✓ std3`).

*Citation.* M. De Vlieger; OEIS Foundation Inc. (2021). *OEIS A347285 descending prime-power exponents*. URL: <https://oeis.org/A347285>.

*Commentary.*

OEIS A347285, COMMENTS (unpaginated): "Conjecture: let S be the sum of the absolute values of the first differences of terms in row n. For all n > 0, n - S = 1." The variable n ranges over all positive natural numbers. The final subtraction and equality are in the integers.

**Theorem 1.5 (The conjecture holds).**

$$\forall n \in \mathbb{N},\; (0 < n) \Rightarrow ((n: \mathbb{Z}) - (\operatorname{S}\left(n\right): \mathbb{Z}) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/OeisA347285PrimePowerDescent.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a347285-de-vlieger-prime-power-descent` (proved) by `D5/S3/Arith/Primes/OeisA347285PrimePowerDescent.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a347285-de-vlieger-prime-power-descent","declaration_gid":"D5/S3/Arith/Primes/OeisA347285PrimePowerDescent.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. De Vlieger; OEIS Foundation Inc. (2021). *OEIS A347285 descending prime-power exponents*. URL: <https://oeis.org/A347285>.

*Commentary.*

An exponent greater than zero strictly decreases at the next prime, because that prime is larger. There is no infinite strictly descending sequence of natural numbers, so the row reaches zero. Bertrand's postulate bounds the next prime by twice the current prime, hence by its square. A positive exponent immediately before zero must therefore equal one. Monotonicity turns each absolute difference into the preceding exponent minus the next, and the sum telescopes from n to one.

## References

- Truth anchor: `D5/S3/Arith/Primes/OeisA347285PrimePowerDescent.S`
- Truth anchor: `D5/S3/Arith/Primes/OeisA347285PrimePowerDescent.claim`
- Truth anchor: `D5/S3/Arith/Primes/OeisA347285PrimePowerDescent.e`
- Truth anchor: `D5/S3/Arith/Primes/OeisA347285PrimePowerDescent.len`
- Truth anchor: `D5/S3/Arith/Primes/OeisA347285PrimePowerDescent.result`
- Dependency: [D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative](../../../S1/Recurrence/Parity/PrimePowerShiftLogDerivative.md)
- Dependency: [D5/S3/Arith/Primes/PrimeGap](PrimeGap.md)
