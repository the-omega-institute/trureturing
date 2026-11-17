# Positive square-and-triangular multipliers

## Abstract

Every natural index has a least positive multiplier satisfying the two independent square and triangular alternatives of A400520.

**Definition 1.1 (Natural squares).**

$$\forall x \in \mathbb{N},\; (\operatorname{Sq}\left(x\right)) \Leftrightarrow (\exists s \in \mathbb{N},\; x = (s)^{2})$$

*Formalization.* `D5/S3/Arith/Congruence/SquareTriangularMultipliers.Sq` (`✓ std3`).

*Citation.* Alex Ratushnyak; OEIS Foundation and contributors (2026). *OEIS A400520: least square-and-triangular multipliers*. URL: <https://oeis.org/A400520>.

*Commentary.*

The root is a natural number. In particular, zero is a square.

**Definition 1.2 (Natural triangular numbers).**

$$\forall x \in \mathbb{N},\; (\operatorname{Tri}\left(x\right)) \Leftrightarrow (\exists t \in \mathbb{N},\; 2 \cdot x = t \cdot \left(t + 1\right))$$

*Formalization.* `D5/S3/Arith/Congruence/SquareTriangularMultipliers.Tri` (`✓ std3`).

*Citation.* Alex Ratushnyak; OEIS Foundation and contributors (2026). *OEIS A400520: least square-and-triangular multipliers*. URL: <https://oeis.org/A400520>.

*Commentary.*

The triangular index is natural and may be zero. The equation avoids truncated division.

**Definition 1.3 (The original independent alternatives).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; (\operatorname{P}\left(n, k\right)) \Leftrightarrow (((\operatorname{Sq}\left(n \cdot k\right)) \lor (\operatorname{Sq}\left(n \cdot k + 1\right))) \land ((\operatorname{Tri}\left(n \cdot k\right)) \lor (\operatorname{Tri}\left(n \cdot k + 1\right))))$$

*Formalization.* `D5/S3/Arith/Congruence/SquareTriangularMultipliers.P` (`✓ std3`).

*Citation.* Alex Ratushnyak; OEIS Foundation and contributors (2026). *OEIS A400520: least square-and-triangular multipliers*. URL: <https://oeis.org/A400520>.

*Commentary.*

A square and a triangular number can be supplied by different members of the pair. Positivity of the multiplier is imposed separately.

**Definition 1.4 (The least positive multiplier or minus one).**

$$\forall n \in \mathbb{N},\; ((\exists k \in \mathbb{N},\; (1 \le k) \land (\operatorname{P}\left(n, k\right))) \Rightarrow (\exists k \in \mathbb{N},\; (1 \le k) \land ((\operatorname{P}\left(n, k\right)) \land ((\operatorname{a}\left(n\right) = (k: \mathbb{Z})) \land (\forall j \in \mathbb{N},\; (1 \le j) \Rightarrow ((\operatorname{P}\left(n, j\right)) \Rightarrow (k \le j))))))) \land ((\neg (\exists k \in \mathbb{N},\; (1 \le k) \land (\operatorname{P}\left(n, k\right)))) \Rightarrow (\operatorname{a}\left(n\right) = -1))$$

*Formalization.* `D5/S3/Arith/Congruence/SquareTriangularMultipliers.a` (`✓ std3`).

*Citation.* Alex Ratushnyak; OEIS Foundation and contributors (2026). *OEIS A400520: least square-and-triangular multipliers*. URL: <https://oeis.org/A400520>.

*Commentary.*

This characterizes the integer-valued definition: select the least natural k satisfying both 1<=k and P(n,k), if one exists, and use -1 otherwise. The minimum is taken for the original predicate P, rather than only for simultaneous square triangular multiples. The positive-multiplier convention is supported by the listed initial values and source program; the NAME itself says only multiplier.

**Theorem 1.5 (Positivity and exact least-witness semantics at every index).**

$$(\forall n \in \mathbb{N},\; (0 < \operatorname{a}\left(n\right)) \land (\exists k \in \mathbb{N},\; (1 \le k) \land ((\operatorname{P}\left(n, k\right)) \land ((\operatorname{a}\left(n\right) = (k: \mathbb{Z})) \land (\forall j \in \mathbb{N},\; (1 \le j) \Rightarrow ((\operatorname{P}\left(n, j\right)) \Rightarrow (k \le j))))))) \land ((\operatorname{a}\left(0\right) = 1) \land (\operatorname{a}\left(1\right) = 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/SquareTriangularMultipliers.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a400520-positive-square-triangular-multipliers` (proved) by `D5/S3/Arith/Congruence/SquareTriangularMultipliers.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a400520-positive-square-triangular-multipliers","declaration_gid":"D5/S3/Arith/Congruence/SquareTriangularMultipliers.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Alex Ratushnyak; OEIS Foundation and contributors (2026). *OEIS A400520: least square-and-triangular multipliers*. URL: <https://oeis.org/A400520>.

*Commentary.*

There are no hypotheses on n and no finite cutoff. For n>0, use Mathlib's Pell.xn and Pell.yn at parameter a=3, so the discriminant a^2-1 is 8. Their natural coordinates x(j), y(j) start at (1,0), satisfy x(j)^2=8y(j)^2+1, and obey x(j+1)=3x(j)+8y(j) and y(j+1)=x(j)+3y(j). Mathlib's Pell.yn_ge_n makes y(j)>0 at every positive j.

Reduce the same pair recurrence modulo n. Its inverse is (u,v) -> (3u-8v,-u+3v), so it is injective on the finite set ZMod(n) x ZMod(n). Function.Injective.mem_periodicPts supplies a positive return time j to (1,0). Induction identifies this finite orbit with the reductions of the actual Pell coordinates, hence n divides y(j). This argument applies to every positive modulus, including one and composite moduli.

Induction on the x recurrence gives x(j) odd. Write x(j)=2t+1 and y(j)=nq. The Pell identity gives 2y(j)^2=t(t+1). Since y(j)>0, q>0, and k=nq^2 is positive. Then nk=y(j)^2 is both square and triangular, which implies each of the original alternatives. At n=0, k=1 works with square root and triangular index zero. The least-witness principle applied to P gives the displayed positive integer a(n), its witness and its minimality. At n=0 and n=1, k=1 itself satisfies P, so positivity and minimality force both initial values to equal one.

The source is the OEIS conjecture cited above. The Pell identities, growth bound and finite injective dynamics are reused established results. The conclusion settles the stated multiplier assertion; it supplies no formula for the least multiplier.

## References

- Truth anchor: `D5/S3/Arith/Congruence/SquareTriangularMultipliers.P`
- Truth anchor: `D5/S3/Arith/Congruence/SquareTriangularMultipliers.Sq`
- Truth anchor: `D5/S3/Arith/Congruence/SquareTriangularMultipliers.Tri`
- Truth anchor: `D5/S3/Arith/Congruence/SquareTriangularMultipliers.a`
- Truth anchor: `D5/S3/Arith/Congruence/SquareTriangularMultipliers.result`
