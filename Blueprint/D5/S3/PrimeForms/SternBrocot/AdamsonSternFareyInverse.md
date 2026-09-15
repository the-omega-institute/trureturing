# Adamson's Stern-Farey Inverse Relation

## Abstract

Stern's diatomic values invert the next Farey-tree numerator modulo its denominator.

All indices n, m, j and r are natural numbers; a and b are pairs of natural numerator and denominator coordinates, with subscripts 1 and 2 denoting their projections. The function stern is Stern's diatomic sequence, mediant adds both coordinates, and fareyRow(m,j) is position j in the full mediant row m, whose valid positions are 0 through 2^m. The total definition below also specifies values outside these positions. The pair fareyEntry(r) has numerator fareyNum(r) and denominator fareyDen(r). Entries 0 and 1 are 0/1 and 1/1; subsequent entries list each level's new mediants in increasing order in [0,1]. At r = 2^m + j with 1 <= j <= 2^m, the selected position is fareyRow(m+1,2(j-1)+1). The operator log_2 is the natural floor logarithm, with log_2(0)=0; / is natural-number division, subtraction is truncated at zero, and mod is the natural remainder. Only Adamson's inverse sentence is settled here; Yurramendi's frequency conjecture, Torres's conjectures and other Farey-tree properties are not claimed.

**Definition 1.1 (Stern's diatomic sequence).**

$$\forall n \in \mathbb{N},\; \operatorname{stern}\left(n\right) = \begin{cases}0 & n = 0\\1 & n = 1\\\operatorname{stern}\left((n / 2)\right) & (1 < n) \land (n \bmod 2 = 0)\\\operatorname{stern}\left((n / 2)\right) + \operatorname{stern}\left((n / 2) + 1\right) & (1 < n) \land (n \bmod 2 \ne 0)\end{cases}$$

*Formalization.* `D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.stern` (`✓ std3`).

*Citation.* N. J. A. Sloane; Gary W. Adamson (2023). *OEIS A002487, Stern's diatomic series, with the Adamson Farey-tree inverse conjecture*. URL: <https://oeis.org/A002487>.

*Commentary.*

The initial values are 0 and 1. At a larger even index the value is copied from half the index; at an odd index the two neighboring values at half the index are added.

**Definition 1.2 (The mediant of two coordinate pairs).**

$$\forall a \in \mathbb{N} \times \mathbb{N}, b \in \mathbb{N} \times \mathbb{N},\; \operatorname{mediant}\left(a, b\right) = (a_{1} + b_{1}, a_{2} + b_{2})$$

*Formalization.* `D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.mediant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mediant adds the numerators and adds the denominators.

**Definition 1.3 (Full mediant rows).**

$$\begin{aligned}\forall j \in \mathbb{N},\; \operatorname{fareyRow}\left(0, j\right) = \begin{cases}(0, 1) & j = 0\\(1, 1) & j \ne 0\end{cases}\\\forall m \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{fareyRow}\left(m + 1, j\right) = \begin{cases}\operatorname{fareyRow}\left(m, (j / 2)\right) & j \bmod 2 = 0\\\operatorname{mediant}\left(\operatorname{fareyRow}\left(m, (j / 2)\right), \operatorname{fareyRow}\left(m, (j / 2) + 1\right)\right) & j \bmod 2 \ne 0\end{cases}\end{aligned}$$

*Formalization.* `D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.fareyRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial row has endpoints (0,1) and (1,1). Refinement copies the old entries into even positions and inserts the mediant of adjacent entries into each intervening odd position.

**Definition 1.4 (The level-by-level entry selector).**

$$\forall r \in \mathbb{N},\; \operatorname{fareyEntry}\left(r\right) = \begin{cases}(0, 1) & r = 0\\(1, 1) & r = 1\\\operatorname{fareyRow}\left(\left(\operatorname{log}_{2}\right)\left(r - 1\right) + 1, 2 \cdot ((r - 1) - 2^{\left(\operatorname{log}_{2}\right)\left(r - 1\right)}) + 1\right) & 1 < r\end{cases}$$

*Formalization.* `D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.fareyEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

After the two endpoints, each block consists of the new mediants from one refinement. The floor logarithm locates the block, and the odd row position locates its mediant.

**Definition 1.5 (Farey-tree numerators).**

$$\forall r \in \mathbb{N},\; \operatorname{fareyNum}\left(r\right) = (\operatorname{fareyEntry}\left(r\right))_{1}$$

*Formalization.* `D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.fareyNum` (`✓ std3`).

*Citation.* N. J. A. Sloane; Gary W. Adamson (2023). *OEIS A002487, Stern's diatomic series, with the Adamson Farey-tree inverse conjecture*. URL: <https://oeis.org/A002487>.

*Commentary.*

The first coordinate gives the A007305 numerator at the same index.

**Definition 1.6 (Farey-tree denominators).**

$$\forall r \in \mathbb{N},\; \operatorname{fareyDen}\left(r\right) = (\operatorname{fareyEntry}\left(r\right))_{2}$$

*Formalization.* `D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.fareyDen` (`✓ std3`).

*Citation.* N. J. A. Sloane; Gary W. Adamson (2023). *OEIS A002487, Stern's diatomic series, with the Adamson Farey-tree inverse conjecture*. URL: <https://oeis.org/A002487>.

*Commentary.*

The second coordinate gives the A007306 denominator at the same index.

**Theorem 1.7 (Adamson's modular inverse relation).**

$$\forall n \in \mathbb{N},\; (0 < n) \Rightarrow (\operatorname{stern}\left(n\right) \cdot \operatorname{fareyNum}\left(n + 1\right) \bmod \operatorname{fareyDen}\left(n + 1\right) = 1 \bmod \operatorname{fareyDen}\left(n + 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a002487-adamson-stern-farey-inverse` (proved) by `D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a002487-adamson-stern-farey-inverse","declaration_gid":"D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.result","resolution_kind":"proved"} -->

*Citation.* N. J. A. Sloane; Gary W. Adamson (2023). *OEIS A002487, Stern's diatomic series, with the Adamson Farey-tree inverse conjecture*. URL: <https://oeis.org/A002487>.

*Commentary.*

The coordinates of each mediant row are Stern values. The adjacent-column determinant identity then writes the product of stern(n) and fareyNum(n+1) as a multiple of fareyDen(n+1) plus one. Taking remainders proves the relation for every positive n; for example, stern(12)=2 and entry 13 is (4,7).

## References

- Truth anchor: `D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.fareyDen`
- Truth anchor: `D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.fareyEntry`
- Truth anchor: `D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.fareyNum`
- Truth anchor: `D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.fareyRow`
- Truth anchor: `D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.mediant`
- Truth anchor: `D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.result`
- Truth anchor: `D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.stern`
