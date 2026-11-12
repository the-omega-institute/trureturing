# Sun A346934: the composite-modulus sentence

## Abstract

For every positive n with composite 2*n+1, that modulus divides the signed-difference permanent.

**Definition 1.1 (a).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{Matrix.permanent}\left((fun (i : \operatorname{Fin}\left(2 \cdot n\right)) \mapsto fun (j : \operatorname{Fin}\left(2 \cdot n\right)) \mapsto ((\operatorname{val}\left(i\right) : \mathbb{Z}) + 1) - ((\operatorname{val}\left(j\right) : \mathbb{Z}) + 1))\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SunA346934CompositeModulus.a` (`✓ std3`).

*Citation.* Zhi-Wei Sun (2021). *OEIS A346934: signed-difference permanents*. URL: <https://oeis.org/A346934>.

*Commentary.*

OEIS A346934 revision 29, NAME (unpaginated): "Permanent of the 2n X 2n matrix with the (i,j)-entry i-j (i,j=1..2n)." The type Fin (2*n) represents these indices through val i + 1. Each entry and the permanent are integers. Matrix.permanent sums products of M (sigma i) i; inversion of permutations gives the source's row-first sum.

**Definition 1.2 (claim).**

$$claim \Leftrightarrow \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\neg (\operatorname{Nat.Prime}\left(2 \cdot n + 1\right)) \Rightarrow ((2 \cdot n + 1 : \mathbb{N}) : \mathbb{Z}) \mid \operatorname{a}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SunA346934CompositeModulus.claim` (`✓ std3`).

*Citation.* Zhi-Wei Sun (2021). *OEIS A346934: signed-difference permanents*. URL: <https://oeis.org/A346934>.

*Commentary.*

OEIS A346934 revision 29, COMMENT, Conjecture 1 (unpaginated): "Conjecture 1: (-1)^n*a(n) > 0 for all n > 0. Also, a(n) == 0 (mod 2n+1) if 2n+1 is composite." The formula expresses the sentence beginning Also. Natural n starts at 1, as specified by the sequence offset 1,2. Since 2*n+1 is at least 3, its nonprimality is exactly compositeness; divisibility in the integers expresses the zero congruence. The sign sentence and Conjecture 2 are outside this proposition.

**Theorem 1.3 (result).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\neg (\operatorname{Nat.Prime}\left(2 \cdot n + 1\right)) \Rightarrow ((2 \cdot n + 1 : \mathbb{N}) : \mathbb{Z}) \mid \operatorname{a}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/SunA346934CompositeModulus.result` (`✓ std3`). ∎

*Resolves.* `Problems/sun346934` (proved) by `D5/S3/Combinatorics/Permanental/SunA346934CompositeModulus.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sun346934","declaration_gid":"D5/S3/Combinatorics/Permanental/SunA346934CompositeModulus.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2021). *OEIS A346934: signed-difference permanents*. URL: <https://oeis.org/A346934>.

*Commentary.*

Expanding the additive integer matrix permanent and grouping permutations by their subset images gives factorial-split multiplicities. At order q-1, every multiplicity is divisible by the odd composite modulus q. Distinct factors in the larger factorial prove this divisibility, with the three central products 720, 576 and 720 treating q = 9. Taking q = 2*n+1 proves the stated divisibility for the signed-difference matrix.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/SunA346934CompositeModulus.a`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SunA346934CompositeModulus.claim`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SunA346934CompositeModulus.result`
