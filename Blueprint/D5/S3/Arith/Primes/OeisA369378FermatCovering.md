# Ordowski A369378: the Fermat-number covering proof

## Abstract

Ordowski's A369378 conjecture is proved by a Fermat-number covering.

The variables n and k are natural numbers. The source sentence is quoted verbatim in the claim description: "Conjecture: if n > 0, then 2^(2^n+1)-1 + 2^k is not prime for every k < 2^n." The Lean encoding uses 0 < n, the natural bound k < 2^n including k = 0, natural subtraction, and Nat.Prime. The proof selects F_j = 2^(2^j)+1 from the odd part of k; modulo F_j, the large power is 2 and 2^k is -1.

**Definition 1.1 (Ordowski's conjecture).**

$$\operatorname{claim}\left(\right) = (\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; (0 < n) \Rightarrow ((k < 2^{n}) \Rightarrow (\neg (\operatorname{Nat}.\operatorname{Prime}\left(2^{2^{n} + 1} - 1 + 2^{k}\right)))))$$

*Formalization.* `D5/S3/Arith/Primes/OeisA369378FermatCovering.claim` (`✓ std3`).

*Citation.* T. Ordowski (2024). *OEIS A369378: Fermat-number covering conjecture*. URL: <https://oeis.org/A369378>.

*Commentary.*

OEIS A369378, COMMENTS (unpaginated): "Conjecture: if n > 0, then 2^(2^n+1)-1 + 2^k is not prime for every k < 2^n." The formula below preserves the natural-number expression and its quantifiers exactly.

**Theorem 1.2 (The Fermat-number covering settlement).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; (0 < n) \Rightarrow ((k < 2^{n}) \Rightarrow (\neg (\operatorname{Nat}.\operatorname{Prime}\left(2^{2^{n} + 1} - 1 + 2^{k}\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/OeisA369378FermatCovering.result` (`✓ std3`). ∎

*Resolves.* `Problems/ordowski` (proved) by `D5/S3/Arith/Primes/OeisA369378FermatCovering.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ordowski","declaration_gid":"D5/S3/Arith/Primes/OeisA369378FermatCovering.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* T. Ordowski (2024). *OEIS A369378: Fermat-number covering conjecture*. URL: <https://oeis.org/A369378>.

*Commentary.*

For k = 0, the number is a power of two with a proper divisor. For positive k, write k as 2^j times an odd number; k < 2^n gives j < n. The Fermat number 2^(2^j)+1 divides the target by the congruences 2^(2^n) = 1 and 2^k = -1 in its residue ring, and it is a proper divisor. The finite fidelity examples at n = 1 and n = 2 certify the boundary primes 11 and 47.

## References

- Truth anchor: `D5/S3/Arith/Primes/OeisA369378FermatCovering.claim`
- Truth anchor: `D5/S3/Arith/Primes/OeisA369378FermatCovering.result`
