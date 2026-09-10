# Cube Gaps at Five

## Abstract

Cubes five apart differ by two modulo three, and no square does.

Indices and values are natural numbers. Subtraction of naturals truncates, so the difference is defined in expanded form and the subtracted form is recovered from an identity that shows the subtraction is exact here.

**Definition 1.1 (The difference in expanded form).**

$$\forall n \in \mathbb{N}, \operatorname{gap}\left(n\right) = 5 \cdot {3 \cdot {n}^{2} + 15 \cdot n + 25}$$

*Formalization.* `D5/S3/Factorization/CubeGapFiveNoSquare.gap` (`✓ std3`).

*Citation.* OEIS Foundation Inc. (2026). *OEIS A038867*. URL: <https://oeis.org/A038867>.

*Commentary.*

Five times a quadratic. Every term but the constant carries a factor of three, and the constant leaves two.

**Lemma 1.2 (The subtracted form).**

$$\forall n \in \mathbb{N}, \operatorname{gap}\left(n\right) = {{n + 5}}^{3} - {n}^{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/CubeGapFiveNoSquare.gap_eq_cube_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The larger cube exceeds the smaller by exactly this amount, so the truncating subtraction agrees with the expansion. This is what lets the conclusion be stated in the source's own notation.

**Theorem 1.3 (The residue is always two).**

$$\forall n \in \mathbb{N}, \operatorname{gap}\left(n\right) \bmod 3 = 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/CubeGapFiveNoSquare.gap_mod_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Immediate from the expansion: three divides every term except the constant, and five times twenty-five leaves two.

**Theorem 1.4 (No square leaves two).**

$$\forall m \in \mathbb{N}, {m}^{2} \bmod 3 \neq 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/CubeGapFiveNoSquare.sq_mod_three_ne_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Split the base by its own residue and expand. The cross terms carry a factor of three, so only the squared residue survives, and the three possible values leave zero, one and one.

**Theorem 1.5 (The conjecture).**

$$\forall n, m \in \mathbb{N}, {m}^{2} \neq \operatorname{gap}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/CubeGapFiveNoSquare.cube_gap_five_ne_sq` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a038867-cube-gap-five-no-square` (proved) by `D5/S3/Factorization/CubeGapFiveNoSquare.cube_gap_five_ne_sq`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a038867-cube-gap-five-no-square","declaration_gid":"D5/S3/Factorization/CubeGapFiveNoSquare.cube_gap_five_ne_sq","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2026). *OEIS A038867*. URL: <https://oeis.org/A038867>.

*Commentary.*

The two residue sets do not meet, so no index gives a square. No size estimate or descent is needed.

**Theorem 1.6 (The conjecture in the source's form).**

$$\forall n, m \in \mathbb{N}, {m}^{2} \neq {{n + 5}}^{3} - {n}^{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/CubeGapFiveNoSquare.cube_gap_five_ne_sq_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2026). *OEIS A038867*. URL: <https://oeis.org/A038867>.

*Commentary.*

The same statement with the difference written as a subtraction, which is how the source prints it.

Nothing here applies to cube differences at other gaps. The argument uses that the constant term leaves two modulo three, which is particular to this gap.

## References

- Truth anchor: `D5/S3/Factorization/CubeGapFiveNoSquare.cube_gap_five_ne_sq`
- Truth anchor: `D5/S3/Factorization/CubeGapFiveNoSquare.cube_gap_five_ne_sq_sub`
- Truth anchor: `D5/S3/Factorization/CubeGapFiveNoSquare.gap`
- Truth anchor: `D5/S3/Factorization/CubeGapFiveNoSquare.gap_eq_cube_sub`
- Truth anchor: `D5/S3/Factorization/CubeGapFiveNoSquare.gap_mod_three`
- Truth anchor: `D5/S3/Factorization/CubeGapFiveNoSquare.sq_mod_three_ne_two`
