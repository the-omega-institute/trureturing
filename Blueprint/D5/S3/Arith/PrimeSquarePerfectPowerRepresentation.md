# Prime Square Perfect-Power Representation

## Abstract

Every prime can be added to a square to obtain a perfect power with exponent at least two.

**Theorem 1.1 (Every prime has a square-to-perfect-power representation).**

$$\forall p \in \mathbb{N}, \operatorname{Prime}\left(p\right) \implies \exists x, y, n \in \mathbb{N}, 2 \leq n \land x^{2} + p = y^{n}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeSquarePerfectPowerRepresentation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a115039-prime-square-perfect-power-representation` (proved) by `D5/S3/Arith/PrimeSquarePerfectPowerRepresentation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a115039-prime-square-perfect-power-representation","declaration_gid":"D5/S3/Arith/PrimeSquarePerfectPowerRepresentation.result","resolution_kind":"proved"} -->

*Citation.* Cino Hilliard; Robert Israel (2006). *OEIS A115039 and A115038, prime square perfect-power representation*. URL: <https://oeis.org/A115039>.

*Commentary.*

For the prime two, five squared plus two is three cubed. Every odd prime has the form two times t plus one, and t squared plus that prime equals (t+1) squared. Both constructions use positive bases and an exponent at least two.

## References

- Truth anchor: `D5/S3/Arith/PrimeSquarePerfectPowerRepresentation.result`
