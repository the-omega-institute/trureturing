# Value Four in OEIS A374911

## Abstract

The original power-residue recursion has value four exactly at three and nine.

**Definition 1.1 (The recursive sequence).**

$$\forall n: \mathbb{N}, \operatorname{seq}\left(n\right) = \operatorname{ite}\left(n = 0, 1, \operatorname{seq}\left(2^{n} \bmod n\right) + \operatorname{seq}\left(3^{n} \bmod n\right)\right)$$

*Formalization.* `D5/S3/Arith/Congruence/PowerResidueRecursionFour.seq` (`✓ std3`).

*Citation.* OEIS Foundation Inc. (2024). *OEIS A374911*. URL: <https://oeis.org/A374911>.

*Commentary.*

The zero case is selected before either recursive call. At a positive index both remainders are strictly smaller than that index, so well-founded recursion defines the sequence on every natural number. In the displayed formula, ite selects the second argument when the first argument holds and the third otherwise.

**Theorem 1.2 (Value one).**

$$\forall n: \mathbb{N}, \operatorname{seq}\left(n\right) = 1 \Leftrightarrow (n = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PowerResidueRecursionFour.seq_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2024). *OEIS A374911*. URL: <https://oeis.org/A374911>.

*Commentary.*

Strong induction proves every term positive. At a nonzero index the sum of two positive recursive terms is at least two.

**Theorem 1.3 (Value two).**

$$\forall n: \mathbb{N}, \operatorname{seq}\left(n\right) = 2 \Leftrightarrow (n = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PowerResidueRecursionFour.seq_eq_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2024). *OEIS A374911*. URL: <https://oeis.org/A374911>.

*Commentary.*

Both recursive terms must equal one, making the index divide both two to the index and three to the index. These powers are coprime, so the index is one.

**Theorem 1.4 (Value three).**

$$\forall n: \mathbb{N}, \operatorname{seq}\left(n\right) = 3 \Leftrightarrow (\exists k: \mathbb{N}, 0 < k \land n = 2^{k})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PowerResidueRecursionFour.seq_eq_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2024). *OEIS A374911*. URL: <https://oeis.org/A374911>.

*Acknowledgement.* OEIS Foundation Inc. (2026). *OEIS A036236*. URL: <https://oeis.org/A036236>.

*Commentary.*

A least-prime-divisor and multiplicative-order argument excludes two to the index having remainder one at every index greater than one. Thus the left recursive term must be one, forcing a power of two. Euler's theorem supplies the converse for every positive exponent. The modular exclusion is also proved in the A036236 comments.

**Theorem 1.5 (Value four).**

$$\forall n: \mathbb{N}, \operatorname{seq}\left(n\right) = 4 \Leftrightarrow (n = 3 \lor n = 9)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PowerResidueRecursionFour.a374911_eq_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2024). *OEIS A374911*. URL: <https://oeis.org/A374911>.

*Acknowledgement.* OEIS Foundation Inc. (2026). *OEIS A036236*. URL: <https://oeis.org/A036236>.

*Commentary.*

Values one and two for the left recursive term are impossible. The right term is therefore one, forcing the index to be a power of three. Addition lifting of the exponent gives remainder three to the k minus one for the left argument. For even k, two-adic lifting gives j = 2 + v₂(k) when that remainder is two to the j; this implies two to the j is at most 4k, contradicting exponential growth for k at least three. Odd k at least three is excluded modulo four. The remaining exponents one and two give precisely three and nine. This proves the question explicitly posed by A374911; the proof is derived here from the preceding arithmetic ingredients.

## References

- Truth anchor: `D5/S3/Arith/Congruence/PowerResidueRecursionFour.a374911_eq_four`
- Truth anchor: `D5/S3/Arith/Congruence/PowerResidueRecursionFour.seq`
- Truth anchor: `D5/S3/Arith/Congruence/PowerResidueRecursionFour.seq_eq_one`
- Truth anchor: `D5/S3/Arith/Congruence/PowerResidueRecursionFour.seq_eq_three`
- Truth anchor: `D5/S3/Arith/Congruence/PowerResidueRecursionFour.seq_eq_two`
