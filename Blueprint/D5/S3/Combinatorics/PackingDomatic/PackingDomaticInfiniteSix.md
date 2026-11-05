# Six Broadcast-Dominating Classes on the Infinite Path

## Abstract

The six-class packing-domatic palette of the two-way infinite path is exactly five.

**Definition 1.1 (A common infinite realization).**

$$\forall t \in Nat,\; Q\left(t\right) \Leftrightarrow \left(\exists f \in Int \to Nat,\; \exists c \in Int \to Fin\left(6\right),\; \left(\forall x \in Int,\; 1 \le f\left(x\right) \land f\left(x\right) \le t\right) \land \left(\left(\forall u \in Int,\; \forall v \in Int,\; u \ne v \Rightarrow \left(f\left(u\right) = f\left(v\right) \Rightarrow f\left(u\right) < \lvert u - v\rvert \right)\right) \land \left(\forall x \in Int,\; \forall i \in Fin\left(6\right),\; \exists a \in Int,\; c\left(a\right) = i \land \lvert x - a\rvert  \le f\left(a\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PackingDomatic/PackingDomaticInfiniteSix.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Boštjan Brešar, Jasmina Ferme, Wenjie Hu (2026). *Partitioning an S-packing coloring into broadcast dominating sets*. DOI: [10.48550/arXiv.2610.03477](https://doi.org/10.48550/arXiv.2610.03477). URL: <https://arxiv.org/abs/2610.03477v1>.

*Commentary.*

The vertices of the two-way infinite path are all integers, with distance |u-v|. Nat denotes the natural numbers, Int the integers, and Fin(6) the six labels 0 through 5. Q(t) asks for a positive packing colouring f bounded by t and one class map c on the same vertex set. Each of the six classes broadcast-dominates every integer: its witness a covers x to radius f(a). Natural colour values are coerced to integers in the distance comparisons. Neither map has a periodicity, measurability, computability or colour-determined-class requirement.

**Theorem 1.2 (The least palette is five).**

$$Q\left(5\right) \land \left(\forall t \in Nat,\; Q\left(t\right) \Rightarrow 5 \le t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PackingDomatic/PackingDomaticInfiniteSix.result` (`✓ std3`). ∎

*Resolves.* `Problems/bresar-ferme-hu-infinite-path-six-reader-question` (proved) by `D5/S3/Combinatorics/PackingDomatic/PackingDomaticInfiniteSix.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bresar-ferme-hu-infinite-path-six-reader-question","declaration_gid":"D5/S3/Combinatorics/PackingDomatic/PackingDomaticInfiniteSix.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Boštjan Brešar, Jasmina Ferme, Wenjie Hu (2026). *Partitioning an S-packing coloring into broadcast dominating sets*. DOI: [10.48550/arXiv.2610.03477](https://doi.org/10.48550/arXiv.2610.03477). URL: <https://arxiv.org/abs/2610.03477v1>.

*Commentary.*

Theorem 3.6 of Brešar, Ferme and Hu supplies the five-colour upper construction: the repeating colour pattern [5,1,2,4,1,3], starting with colour 5 at vertex 0. Its class 0 consists of residues 1 and 4 modulo 6. Classes 1 through 5 have, respectively, residues {0,8,15,23}, {2,9,17,24}, {3,11,18,26}, {5,12,20,27}, and {6,14,21,29} modulo 30. This construction is the source's prior upper bound. For each of the 30 residues and six classes, a checked finite certificate finds a covering vertex at an offset from -5 through 5. Reduction modulo 30, together with reduction modulo 6, transfers that certificate to every integer, including negative vertices. Packing separation is proved for arbitrary pairs of integers. For the lower bound, take any hypothetical Q(4) realization. Let J be the integer interval [0,999] and I the interval [4,995]. Every x in I needs six distinct covering vertices in J, since one class map assigns different labels to its six witnesses. There are therefore at least 6 times 992 = 5952 vertex-broadcast incidences. A vertex of colour j covers at most 2j+1 vertices. For j equal to 2, 3 and 4, sending a vertex a of colour j to the integer quotient a/(j+1) is injective, by strict packing separation. The resulting colour-count bounds are 334, 250 and 200. Writing the total capacity as 3 times 1000 + 2 times N(2) + 4 times N(3) + 6 times N(4) bounds it by 5868, contradicting 5952. This obstruction applies to arbitrary infinite realizations. Increasing a palette bound preserves both maps, so exclusion at 4 excludes every natural palette below 5. Together with attainment, this answers the reader question immediately after Theorem 3.6 in Section 3.2: the exact value of the six-class packing-domatic chromatic number of the two-way infinite path is 5. This is a different question from the finite-path Problem 2.

## References

- Truth anchor: `D5/S3/Combinatorics/PackingDomatic/PackingDomaticInfiniteSix.Q`
- Truth anchor: `D5/S3/Combinatorics/PackingDomatic/PackingDomaticInfiniteSix.result`
