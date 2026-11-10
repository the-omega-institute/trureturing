# Prime Multiplicity in Bouras Continued Fractions

## Abstract

Every occurring prime other than five has exactly two indices in Bouras A363347.

Indices are natural numbers, including zero; occurrence counts use only indices n at least three. Continued fractions are rational, and Rat.den is their positive reduced denominator. Natural subtraction is truncated at zero. Set.ncard counts a finite set, and is zero on an infinite set. The proof exhibits the occurrence set as a pair, rather than assuming its finiteness.

**Definition 1.1 (The right-folded inner fraction).**

$$\forall n \in \mathbb{N},\; \forall x \in \mathbb{Q},\; \operatorname{BourasA356360}.\operatorname{nested}\left(n, x\right) = \operatorname{List}.\operatorname{foldr}\left((\operatorname{fun} (k: \mathbb{N}) (t: \mathbb{Q}) \mapsto (k: \mathbb{Q}) - \frac{(k: \mathbb{Q}) + 1}{t}), x, \operatorname{List}.\operatorname{range}'\left(2, n - 2\right)\right)$$

*Formalization.* `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.nested` (`✓ std3`).

*Citation.* M. Bouras (2023). *OEIS A363347 and A363102, prime multiplicities of continued-fraction denominators*. URL: <https://oeis.org/A363347>.

*Commentary.*

OEIS A363347, NAME (unpaginated): "Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(-4)))))." For a rational terminal value x, the inner expression is the right fold over k = 2 through n-1. List.range' starts at two and has length n-2. The casts into the rationals are explicit.

**Definition 1.2 (The reciprocal continued fraction).**

$$\forall n \in \mathbb{N},\; \forall x \in \mathbb{Q},\; \operatorname{BourasA356360}.\operatorname{K}\left(n, x\right) = \frac{1}{\operatorname{BourasA356360}.\operatorname{nested}\left(n, x\right)}$$

*Formalization.* `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.K` (`✓ std3`).

*Citation.* M. Bouras (2023). *OEIS A363347 and A363102, prime multiplicities of continued-fraction denominators*. URL: <https://oeis.org/A363347>.

*Commentary.*

K takes the reciprocal of the inner fraction. Rational division has Lean's total semantics; the denominator identity in the proof applies to negative integer terminal values.

**Definition 1.3 (The polynomial for terminal value minus two).**

$$\forall n \in \mathbb{N},\; \operatorname{BourasPolynomials}.\operatorname{U}\left(n\right) = n^{2} - 2$$

*Formalization.* `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.U` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Bouras (2023). *OEIS A363347 and A363102, prime multiplicities of continued-fraction denominators*. URL: <https://oeis.org/A363347>.

*Commentary.*

The natural polynomial n squared minus two describes the absolute linear denominator for terminal value minus two, at indices at least three.

**Theorem 1.4 (Casting the polynomial into a residue ring).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; 3 \le n \Rightarrow (\operatorname{BourasPolynomials}.\operatorname{U}\left(n\right): \operatorname{ZMod}\left(m\right)) = (n: \operatorname{ZMod}\left(m\right))^{2} - 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.cast_U` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Bouras (2023). *OEIS A363347 and A363102, prime multiplicities of continued-fraction denominators*. URL: <https://oeis.org/A363347>.

*Commentary.*

For n at least three the natural subtraction agrees with subtraction in ZMod m, for every natural modulus m, including zero.

**Theorem 1.5 (The two roots in the index interval).**

$$\forall p \in \mathbb{N},\; \forall s \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall q \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(3 \le r \Rightarrow \left(3 \le q \Rightarrow \left(r + s < p \Rightarrow \left(q + s < p \Rightarrow \left(r + q + 2 \cdot s = p \Rightarrow \{n: \mathbb{N} \mid 3 \le n \land \left(n + s < p \land ((n + s: \mathbb{N}): \operatorname{ZMod}\left(p\right))^{2} = ((r + s: \mathbb{N}): \operatorname{ZMod}\left(p\right))^{2}\right)\} = \{r, q\}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.root_fiber_eq_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Bouras (2023). *OEIS A363347 and A363102, prime multiplicities of continued-fraction denominators*. URL: <https://oeis.org/A363347>.

*Commentary.*

Two indices whose shifted sum is the prime modulus are the complete fiber of their common square. The interval assumptions make equality in ZMod p imply equality of the natural representatives.

**Theorem 1.6 (Constructing two admissible square roots).**

$$\forall p \in \mathbb{N},\; \forall s \in \mathbb{N},\; \forall c \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(\left(\left(s = 0 \land \left(c = 2 \land 7 \le p\right)\right) \lor \left(s = 1 \land \left(c = 5 \land 11 \le p\right)\right)\right) \Rightarrow \left(\forall z \in \operatorname{ZMod}\left(p\right),\; z^{2} = (c: \operatorname{ZMod}\left(p\right)) \Rightarrow \left(\exists r \in \mathbb{N},\; \exists q \in \mathbb{N},\; 3 \le r \land \left(3 \le q \land \left(r + s < p \land \left(q + s < p \land \left(r \ne q \land \left(r + q + 2 \cdot s = p \land ((r + s: \mathbb{N}): \operatorname{ZMod}\left(p\right))^{2} = (c: \operatorname{ZMod}\left(p\right))\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.square_residue_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Bouras (2023). *OEIS A363347 and A363102, prime multiplicities of continued-fraction denominators*. URL: <https://oeis.org/A363347>.

*Commentary.*

For either of the displayed shift and residue choices, a square root and its negative give two distinct indices at least three. Their shifted sum is p; the small excluded indices cannot square to the stated residue.

**Theorem 1.7 (Necessary conditions for a prime denominator at minus two).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; 3 \le n \Rightarrow \left(\operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(\operatorname{Rat}.\operatorname{den}\left(\operatorname{BourasA356360}.\operatorname{K}\left(n, -2\right)\right) = p \Rightarrow \left(7 \le p \land \left(p \mid \operatorname{BourasPolynomials}.\operatorname{U}\left(n\right) \land \left(n < p \lor n^{2} = 2 \cdot p^{2} + 2\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.U_prime_constraints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Bouras (2023). *OEIS A363347 and A363102, prime multiplicities of continued-fraction denominators*. URL: <https://oeis.org/A363347>.

*Commentary.*

A prime denominator is at least seven and divides U n. Its index is below the prime unless n squared equals twice p squared plus two. The factorial divisibility bound eliminates larger quotients n divided by p.

**Theorem 1.8 (A root below the prime gives that denominator).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; 3 \le n \Rightarrow \left(\operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(n < p \Rightarrow \left(p \mid \operatorname{BourasPolynomials}.\operatorname{U}\left(n\right) \Rightarrow \operatorname{Rat}.\operatorname{den}\left(\operatorname{BourasA356360}.\operatorname{K}\left(n, -2\right)\right) = p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.U_prime_of_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Bouras (2023). *OEIS A363347 and A363102, prime multiplicities of continued-fraction denominators*. URL: <https://oeis.org/A363347>.

*Commentary.*

If p divides U n and exceeds the index, the cofactor cancels against n!/2 and p remains in the reduced denominator.

**Definition 1.9 (OEIS A363347).**

$$\forall n \in \mathbb{N},\; \operatorname{BourasA363347}.\operatorname{a}\left(n\right) = \operatorname{Rat}.\operatorname{den}\left(\operatorname{BourasA356360}.\operatorname{K}\left(n, -4\right)\right)$$

*Formalization.* `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.a` (`✓ std3`).

*Citation.* M. Bouras (2023). *OEIS A363347 and A363102, prime multiplicities of continued-fraction denominators*. URL: <https://oeis.org/A363347>.

*Commentary.*

OEIS A363347, NAME (unpaginated): "Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(-4)))))." The terminal value is -4 and the sequence uses the rational denominator, with offset n = 3.

**Definition 1.10 (Bouras's Conjecture 3).**

$$\operatorname{BourasA363347}.\operatorname{claim} = (\forall p \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(p \ne 5 \Rightarrow \left(\left(\exists n \in \mathbb{N},\; 3 \le n \land \operatorname{BourasA363347}.\operatorname{a}\left(n\right) = p\right) \Rightarrow \operatorname{Set}.\operatorname{ncard}\left(\{n: \mathbb{N} \mid 3 \le n \land \operatorname{BourasA363347}.\operatorname{a}\left(n\right) = p\}\right) = 2\right)\right))$$

*Formalization.* `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.claim` (`✓ std3`).

*Citation.* M. Bouras (2023). *OEIS A363347 and A363102, prime multiplicities of continued-fraction denominators*. URL: <https://oeis.org/A363347>.

*Commentary.*

OEIS A363347, COMMENTS, Conjecture 3 (unpaginated): "Conjecture 3: Except for 5, the primes all appear exactly twice." Here p ranges over prime values that occur, excluding five. The counted set consists of every natural index n at least three with a n = p.

**Theorem 1.11 (Exactly two occurrences).**

$$\forall p \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(p \ne 5 \Rightarrow \left(\left(\exists n \in \mathbb{N},\; 3 \le n \land \operatorname{BourasA363347}.\operatorname{a}\left(n\right) = p\right) \Rightarrow \operatorname{Set}.\operatorname{ncard}\left(\{n: \mathbb{N} \mid 3 \le n \land \operatorname{BourasA363347}.\operatorname{a}\left(n\right) = p\}\right) = 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.result` (`✓ std3`). ∎

*Resolves.* `Problems/bouras` (proved) by `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bouras","declaration_gid":"D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. Bouras (2023). *OEIS A363347 and A363102, prime multiplicities of continued-fraction denominators*. URL: <https://oeis.org/A363347>.

*Commentary.*

For each occurring prime p other than five, the indices are the two roots of (n+1) squared equal to five in ZMod p. They lie below p and sum to p-2. Cancellation against n!/2 excludes every other index, so the occurrence set has cardinality two.

## References

- Truth anchor: `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.K`
- Truth anchor: `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.U`
- Truth anchor: `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.U_prime_constraints`
- Truth anchor: `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.U_prime_of_root`
- Truth anchor: `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.a`
- Truth anchor: `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.cast_U`
- Truth anchor: `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.claim`
- Truth anchor: `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.nested`
- Truth anchor: `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.result`
- Truth anchor: `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.root_fiber_eq_pair`
- Truth anchor: `D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.square_residue_pair`
