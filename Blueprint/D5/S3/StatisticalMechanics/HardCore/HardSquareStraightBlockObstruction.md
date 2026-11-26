# A Yang–Baxter obstruction for straight hard-square blocks

## Abstract

The straight horizontal clause of Ortega and Peña-Ancavil's Question 5.2.

**Definition 1.1 (Legal block heights).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.Word`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.Word` (`✓ std3`).

*Citation.* Gabriel Ortega; Eliecer Peña-Ancavil (2026). *A local Yang–Baxter obstruction for the hard-square model*. DOI: [10.48550/arXiv.2611.06780](https://doi.org/10.48550/arXiv.2611.06780). URL: <https://arxiv.org/abs/2611.06780v1>.

*Commentary.*

Word k consists of binary words on Fin k with no two consecutive occupied sites. The finite enumeration counts each legal word once.

**Definition 1.2 (Face weights).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.Weight`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.Weight` (`✓ std3`).

*Citation.* Gabriel Ortega; Eliecer Peña-Ancavil (2026). *A local Yang–Baxter obstruction for the hard-square model*. DOI: [10.48550/arXiv.2611.06780](https://doi.org/10.48550/arXiv.2611.06780). URL: <https://arxiv.org/abs/2611.06780v1>.

*Commentary.*

Weight k assigns a complex number to each ordered face [a,b;c,d], with top row (a,b) and bottom row (c,d).

**Definition 1.3 (Ordered horizontal compatibility).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.H`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.H` (`✓ std3`).

*Citation.* Gabriel Ortega; Eliecer Peña-Ancavil (2026). *A local Yang–Baxter obstruction for the hard-square model*. DOI: [10.48550/arXiv.2611.06780](https://doi.org/10.48550/arXiv.2611.06780). URL: <https://arxiv.org/abs/2611.06780v1>.

*Commentary.*

The last bit of the left height and the first bit of the right height cannot both be occupied.

**Definition 1.4 (Vertical compatibility).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.V`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.V` (`✓ std3`).

*Citation.* Gabriel Ortega; Eliecer Peña-Ancavil (2026). *A local Yang–Baxter obstruction for the hard-square model*. DOI: [10.48550/arXiv.2611.06780](https://doi.org/10.48550/arXiv.2611.06780). URL: <https://arxiv.org/abs/2611.06780v1>.

*Commentary.*

No coordinate is occupied in both heights.

**Definition 1.5 (Common face support).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.FaceSupport`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.FaceSupport` (`✓ std3`).

*Citation.* Gabriel Ortega; Eliecer Peña-Ancavil (2026). *A local Yang–Baxter obstruction for the hard-square model*. DOI: [10.48550/arXiv.2611.06780](https://doi.org/10.48550/arXiv.2611.06780). URL: <https://arxiv.org/abs/2611.06780v1>.

*Commentary.*

The two ordered seams are H(a,b) and H(c,d). The two vertical pairs are V(a,c) and V(b,d).

**Definition 1.6 (Zero extension).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.Supported`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.Supported` (`✓ std3`).

*Citation.* Gabriel Ortega; Eliecer Peña-Ancavil (2026). *A local Yang–Baxter obstruction for the hard-square model*. DOI: [10.48550/arXiv.2611.06780](https://doi.org/10.48550/arXiv.2611.06780). URL: <https://arxiv.org/abs/2611.06780v1>.

*Commentary.*

The weight vanishes when any of the four compatibility conditions fails. Values on legal faces can vanish.

**Definition 1.7 (Occupation).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.occ`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.occ` (`✓ std3`).

*Citation.* Gabriel Ortega; Eliecer Peña-Ancavil (2026). *A local Yang–Baxter obstruction for the hard-square model*. DOI: [10.48550/arXiv.2611.06780](https://doi.org/10.48550/arXiv.2611.06780). URL: <https://arxiv.org/abs/2611.06780v1>.

*Commentary.*

Sum the binary entries of the height as natural numbers.

**Definition 1.8 (Blocked hard-square weight).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.blocked`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.blocked` (`✓ std3`).

*Citation.* Gabriel Ortega; Eliecer Peña-Ancavil (2026). *A local Yang–Baxter obstruction for the hard-square model*. DOI: [10.48550/arXiv.2611.06780](https://doi.org/10.48550/arXiv.2611.06780). URL: <https://arxiv.org/abs/2611.06780v1>.

*Commentary.*

On a legal face the value is A^occ(a) B^occ(b) C^occ(c) D^occ(d). The four parameters are complex units. The value on every other face is zero.

**Definition 1.9 (Equation (2.2)).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.EqAt`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.EqAt` (`✓ std3`).

*Citation.* Gabriel Ortega; Eliecer Peña-Ancavil (2026). *A local Yang–Baxter obstruction for the hard-square model*. DOI: [10.48550/arXiv.2611.06780](https://doi.org/10.48550/arXiv.2611.06780). URL: <https://arxiv.org/abs/2611.06780v1>.

*Commentary.*

At (a,b,c,d,e,f), sum P[f,g;a,b] Q[e,d;f,g] R[d,c;g,b] over all legal g. The right side is the nonzero scalar ρ times the sum of R[e,g;f,a] Q[g,c;a,b] P[e,d;g,c] over the same heights.

**Definition 1.10 (Analytic family through a target).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.HasFamily`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.HasFamily` (`✓ std3`).

*Citation.* Gabriel Ortega; Eliecer Peña-Ancavil (2026). *A local Yang–Baxter obstruction for the hard-square model*. DOI: [10.48550/arXiv.2611.06780](https://doi.org/10.48550/arXiv.2611.06780). URL: <https://arxiv.org/abs/2611.06780v1>.

*Commentary.*

All parameter pairs in Ω use the common face support. Each matrix entry is holomorphic in each variable on Ω. For every p,q,r in Ω one nonzero scalar works for all boundaries, with (P,Q,R) = (W(p,q),W(p,r),W(q,r)). The weight equals the target at some ordered pair in Ω × Ω, including the possibility of equal parameters.

**Theorem 1.11 (Nonexistence through the blocked weight).**

$$\forall k : \mathbb{N}, 3 \leq k \implies \forall A,B,C,D : \mathbb{C}^{\times}, \forall U \subseteq \mathbb{C}, \operatorname{IsOpen}\left(U\right) \land \operatorname{IsConnected}\left(U\right) \implies \neg \operatorname{HasFamily}\left(k, U, \operatorname{blocked}\left(A, B, C, D\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.result` (`✓ std3`). ∎

*Resolves.* `Problems/ortega-pena-ancavil-2026-question-5-2-straight` (proved) by `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ortega-pena-ancavil-2026-question-5-2-straight","declaration_gid":"D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Ortega; Eliecer Peña-Ancavil (2026). *A local Yang–Baxter obstruction for the hard-square model*. DOI: [10.48550/arXiv.2611.06780](https://doi.org/10.48550/arXiv.2611.06780). URL: <https://arxiv.org/abs/2611.06780v1>.

*Commentary.*

Let 0 be the empty height, L the even-position height and M the odd-position height, with one-based numbering. At the ordered boundary (0,M,L,L,0,L), simultaneous support of the left P and Q factors requires V(g,M) and V(L,g). The two parity classes cover every site, so only g = 0 can contribute. The right P factor has vertical column (L,L), which shares the occupied second site and forces every right summand to vanish.

The retained faces are [L,0;0,M], [0,L;L,0], and [L,L;0,M]. The last face is legal because L starts empty and L and M are disjoint. Fix the special pair (p,r) and vary q. The middle factor is a nonzero blocked weight, so the first and third factors form a product of holomorphic slices that vanishes throughout Ω. The identity theorem makes one slice zero throughout Ω, contradicting its special value at r or p.

The theorem concerns straight horizontal blocks and the common support. Arbitrary shapes, mixed support for row weights and intertwiners, and hidden heights are open here.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.EqAt`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.FaceSupport`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.H`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.HasFamily`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.Supported`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.V`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.Weight`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.Word`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.blocked`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.occ`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.result`
