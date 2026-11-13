# Odd powers cannot be self-conjugate CMP sizes

## Abstract

Dietz–Flowers–Lockard Question 5.14 has a universal negative answer.

**Definition 1.1 (m-ary partition).**

$$\forall m \in \mathbb{N},\; (\forall mu \in \operatorname{YoungDiagram},\; (\operatorname{IsMAry}\left(m, mu\right) = \left(\forall i \in \mathbb{N},\; ((0 < \operatorname{rowLen}\left(mu, i\right)) \Rightarrow (\exists j \in \mathbb{N},\; (\operatorname{rowLen}\left(mu, i\right) = (m)^{j})))\right)))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.IsMAry` (`✓ std3`).

*Citation.* Geoffrey D. Dietz, Timothy B. Flowers, and Shannon R. Lockard (2026). *A study of m-ary partitions whose conjugates are q-ary*. DOI: [10.13069/jacodesmath.v13i3.393](https://doi.org/10.13069/jacodesmath.v13i3.393). URL: <https://jacodesmath.com/index.php/jacodesmath/article/download/393/304>.

*Commentary.*

Definition 1.1(2), printed page 386: “If all of the parts of λ are powers of m, then we say λ is m-ary.” Here the positive row lengths of the YoungDiagram μ are the parts and the exponents are natural numbers.

**Definition 1.2 (Part multiplicity).**

$$\forall m \in \mathbb{N},\; (\forall mu \in \operatorname{YoungDiagram},\; (\forall j \in \mathbb{N},\; (\operatorname{multiplicity}\left(m, mu, j\right) = \operatorname{count}\left(\operatorname{rowLens}\left(mu\right), (m)^{j}\right))))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.multiplicity` (`✓ std3`).

*Citation.* Geoffrey D. Dietz, Timothy B. Flowers, and Shannon R. Lockard (2026). *A study of m-ary partitions whose conjugates are q-ary*. DOI: [10.13069/jacodesmath.v13i3.393](https://doi.org/10.13069/jacodesmath.v13i3.393). URL: <https://jacodesmath.com/index.php/jacodesmath/article/download/393/304>.

*Commentary.*

Definition 1.1(2), printed page 386: “Let a_i denote the number of times that the part m^i appears in λ.” The list count is taken over the row lengths.

**Definition 1.3 (Conjugate m-ary partition).**

$$\forall m \in \mathbb{N},\; (\forall mu \in \operatorname{YoungDiagram},\; (\operatorname{IsCMP}\left(m, mu\right) = \left((\operatorname{IsMAry}\left(m, mu\right)) \land (\operatorname{IsMAry}\left(m, \operatorname{transpose}\left(mu\right)\right))\right)))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.IsCMP` (`✓ std3`).

*Citation.* Geoffrey D. Dietz, Timothy B. Flowers, and Shannon R. Lockard (2026). *A study of m-ary partitions whose conjugates are q-ary*. DOI: [10.13069/jacodesmath.v13i3.393](https://doi.org/10.13069/jacodesmath.v13i3.393). URL: <https://jacodesmath.com/index.php/jacodesmath/article/download/393/304>.

*Commentary.*

Definition 1.1(3), printed page 386: “If λ and λ' are both m-ary, then λ is a conjugate m-ary partition (or CMP).” The conjugate is YoungDiagram.transpose.

**Definition 1.4 (Question 5.14).**

$$\operatorname{claim} = \left(\forall m \in \mathbb{N},\; ((2 \le m) \Rightarrow ((\operatorname{Odd}\left(m\right)) \Rightarrow (\forall s \in \mathbb{N},\; (\forall mu \in \operatorname{YoungDiagram},\; ((\operatorname{card}\left(mu\right) = (m)^{2 \cdot s + 1}) \Rightarrow ((\operatorname{IsCMP}\left(m, mu\right)) \Rightarrow (\operatorname{transpose}\left(mu\right) \ne mu)))))))\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Geoffrey D. Dietz, Timothy B. Flowers, and Shannon R. Lockard (2026). *A study of m-ary partitions whose conjugates are q-ary*. DOI: [10.13069/jacodesmath.v13i3.393](https://doi.org/10.13069/jacodesmath.v13i3.393). URL: <https://jacodesmath.com/index.php/jacodesmath/article/download/393/304>.

*Commentary.*

Question 5.14, printed page 404 (publisher PDF page 20 of 23; arXiv HTML label V.20): “When m is odd, are there any self-conjugate CMPs of odd powers of m?” The displayed proposition is its negative answer, with m ≥ 2, Odd m, exponent 2s+1, literal YoungDiagram equality for self-conjugacy, and the two m-ary conditions.

**Theorem 1.5 (Negative answer).**

$$\forall m \in \mathbb{N},\; ((2 \le m) \Rightarrow ((\operatorname{Odd}\left(m\right)) \Rightarrow (\forall s \in \mathbb{N},\; (\forall mu \in \operatorname{YoungDiagram},\; ((\operatorname{card}\left(mu\right) = (m)^{2 \cdot s + 1}) \Rightarrow ((\operatorname{IsCMP}\left(m, mu\right)) \Rightarrow (\operatorname{transpose}\left(mu\right) \ne mu)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.result` (`✓ std3`). ∎

*Resolves.* `Problems/dfl514-selfconj` (proved) by `D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dfl514-selfconj","declaration_gid":"D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Geoffrey D. Dietz, Timothy B. Flowers, and Shannon R. Lockard (2026). *A study of m-ary partitions whose conjugates are q-ary*. DOI: [10.13069/jacodesmath.v13i3.393](https://doi.org/10.13069/jacodesmath.v13i3.393). URL: <https://jacodesmath.com/index.php/jacodesmath/article/download/393/304>.

*Commentary.*

The finite row fibers are differences of adjacent column-height ranges. The m-ary hypotheses make every positive row and column height congruent to 1 modulo m−1; self-conjugacy identifies the largest row and column. Summing the fibers gives (m−1)^2 dividing N−(2L−1), then oddness gives 2(m−1) dividing N−1. For N=m^(2s+1), the same divisor also divides N−m, forcing it to divide m−1, which contradicts m ≥ 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.IsCMP`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.IsMAry`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.claim`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.multiplicity`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP.result`
- Dependency: [D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts](../../../S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.md)
