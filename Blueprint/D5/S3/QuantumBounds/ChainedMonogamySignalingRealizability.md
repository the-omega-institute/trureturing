# The realizability conjecture for chained monogamy relations

## Abstract

Kłobus, Oszmaniec, Augusiak and Grudka (arXiv:1408.1223, Section 5) conjecture that every vector of the correlators x_A^i, y_A^i, x_B^i, y_B^i satisfying their inequalities (ElPrat) is realized by a signaling box whose chained Bell expression plus twice the correlator of B_0 and E equals 2M + Delta. This holds for every number of settings M at least 2 and every Delta in [0, 2]: an explicit box realizes the coordinates, has all one- and three-party expectation values zero and a common value of the correlator of B_0 and E, and attains R_M = 2M + Delta exactly.

**Definition 1.1 (Outcome signs).**

$$(\operatorname{sgn}\left(true\right) = 1) \land (\operatorname{sgn}\left(false\right) = -1)$$

*Formalization.* `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.sgn` (`✓ std3`).

*Citation.* Waldemar Kłobus; Michał Oszmaniec; Remigiusz Augusiak; Andrzej Grudka (2016). *Communication strength of correlations violating monogamy relations*. DOI: [10.1007/s10701-015-9983-5](https://doi.org/10.1007/s10701-015-9983-5). URL: <https://arxiv.org/abs/1408.1223v2>.

*Commentary.*

Outcomes are elements of Bool, and sgn maps true to 1 and false to -1.

**Definition 1.2 (Boxes).**

$$\forall M : \mathbb{N}, \forall p : \mathbb{N} \to \mathbb{N} \to Bool \to Bool \to Bool \to \mathbb{R}, (\operatorname{IsBox}\left(M, p\right)) \Leftrightarrow (\forall i : \mathbb{N}, \forall j : \mathbb{N}, (i < M) \Rightarrow ((j < M) \Rightarrow ((\forall a : Bool, \forall b : Bool, \forall e : Bool, 0 \le \operatorname{p}\left(i, j, a, b, e\right)) \land (\sum_{a} \sum_{b} \sum_{e} \operatorname{p}\left(i, j, a, b, e\right) = 1))))$$

*Formalization.* `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.IsBox` (`✓ std3`).

*Citation.* Waldemar Kłobus; Michał Oszmaniec; Remigiusz Augusiak; Andrzej Grudka (2016). *Communication strength of correlations violating monogamy relations*. DOI: [10.1007/s10701-015-9983-5](https://doi.org/10.1007/s10701-015-9983-5). URL: <https://arxiv.org/abs/1408.1223v2>.

*Commentary.*

A box assigns to each pair of settings (A_i, B_j) a function p(i, j) of the three outcomes a, b, e; Eve has a single setting. IsBox(M, p) says that for all i, j < M this function is a probability distribution. No relation between different setting pairs is imposed, so signaling is allowed.

**Definition 1.3 (The class of boxes with vanishing odd moments).**

$$\forall M : \mathbb{N}, \forall p : \mathbb{N} \to \mathbb{N} \to Bool \to Bool \to Bool \to \mathbb{R}, (\operatorname{OddMomentsVanish}\left(M, p\right)) \Leftrightarrow (\forall i : \mathbb{N}, \forall j : \mathbb{N}, (i < M) \Rightarrow ((j < M) \Rightarrow ((\sum_{a} \sum_{b} \sum_{e} \operatorname{sgn}\left(a\right) \cdot \operatorname{p}\left(i, j, a, b, e\right) = 0) \land ((\sum_{a} \sum_{b} \sum_{e} \operatorname{sgn}\left(b\right) \cdot \operatorname{p}\left(i, j, a, b, e\right) = 0) \land ((\sum_{a} \sum_{b} \sum_{e} \operatorname{sgn}\left(e\right) \cdot \operatorname{p}\left(i, j, a, b, e\right) = 0) \land (\sum_{a} \sum_{b} \sum_{e} \operatorname{sgn}\left(a\right) \cdot \operatorname{sgn}\left(b\right) \cdot \operatorname{sgn}\left(e\right) \cdot \operatorname{p}\left(i, j, a, b, e\right) = 0))))))$$

*Formalization.* `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.OddMomentsVanish` (`✓ std3`).

*Citation.* Waldemar Kłobus; Michał Oszmaniec; Remigiusz Augusiak; Andrzej Grudka (2016). *Communication strength of correlations violating monogamy relations*. DOI: [10.1007/s10701-015-9983-5](https://doi.org/10.1007/s10701-015-9983-5). URL: <https://arxiv.org/abs/1408.1223v2>.

*Commentary.*

The paper restricts attention to the convex set of boxes whose one-party expectation values and three-party expectation values all vanish, so that only the bipartite correlators are nonzero.

**Definition 1.4 (The correlator of A and B).**

$$\forall p : \mathbb{N} \to \mathbb{N} \to Bool \to Bool \to Bool \to \mathbb{R}, \forall i : \mathbb{N}, \forall j : \mathbb{N}, \operatorname{corrAB}\left(p, i, j\right) = \sum_{a} \sum_{b} \sum_{e} \operatorname{sgn}\left(a\right) \cdot \operatorname{sgn}\left(b\right) \cdot \operatorname{p}\left(i, j, a, b, e\right)$$

*Formalization.* `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.corrAB` (`✓ std3`).

*Citation.* Waldemar Kłobus; Michał Oszmaniec; Remigiusz Augusiak; Andrzej Grudka (2016). *Communication strength of correlations violating monogamy relations*. DOI: [10.1007/s10701-015-9983-5](https://doi.org/10.1007/s10701-015-9983-5). URL: <https://arxiv.org/abs/1408.1223v2>.

*Commentary.*

The correlator of A_i and B_j at the setting pair (i, j).

**Definition 1.5 (The correlator of A and E).**

$$\forall p : \mathbb{N} \to \mathbb{N} \to Bool \to Bool \to Bool \to \mathbb{R}, \forall i : \mathbb{N}, \forall j : \mathbb{N}, \operatorname{corrAE}\left(p, i, j\right) = \sum_{a} \sum_{b} \sum_{e} \operatorname{sgn}\left(a\right) \cdot \operatorname{sgn}\left(e\right) \cdot \operatorname{p}\left(i, j, a, b, e\right)$$

*Formalization.* `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.corrAE` (`✓ std3`).

*Citation.* Waldemar Kłobus; Michał Oszmaniec; Remigiusz Augusiak; Andrzej Grudka (2016). *Communication strength of correlations violating monogamy relations*. DOI: [10.1007/s10701-015-9983-5](https://doi.org/10.1007/s10701-015-9983-5). URL: <https://arxiv.org/abs/1408.1223v2>.

*Commentary.*

The correlator of A_i and E conditioned on the setting B_j of the third party.

**Definition 1.6 (The correlator of B and E).**

$$\forall p : \mathbb{N} \to \mathbb{N} \to Bool \to Bool \to Bool \to \mathbb{R}, \forall i : \mathbb{N}, \forall j : \mathbb{N}, \operatorname{corrBE}\left(p, i, j\right) = \sum_{a} \sum_{b} \sum_{e} \operatorname{sgn}\left(b\right) \cdot \operatorname{sgn}\left(e\right) \cdot \operatorname{p}\left(i, j, a, b, e\right)$$

*Formalization.* `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.corrBE` (`✓ std3`).

*Citation.* Waldemar Kłobus; Michał Oszmaniec; Remigiusz Augusiak; Andrzej Grudka (2016). *Communication strength of correlations violating monogamy relations*. DOI: [10.1007/s10701-015-9983-5](https://doi.org/10.1007/s10701-015-9983-5). URL: <https://arxiv.org/abs/1408.1223v2>.

*Commentary.*

The correlator of B_j and E conditioned on the setting A_i of the third party.

**Definition 1.7 (The chained Bell expression plus Eve's correlator).**

$$\forall M : \mathbb{N}, \forall p : \mathbb{N} \to \mathbb{N} \to Bool \to Bool \to Bool \to \mathbb{R}, \operatorname{chainR}\left(M, p\right) = \sum_{k<M} \operatorname{corrAB}\left(p, k, k\right) + \sum_{k<M - 1} \operatorname{corrAB}\left(p, k + 1, k\right) - \operatorname{corrAB}\left(p, 0, M - 1\right) + 2 \cdot \operatorname{corrBE}\left(p, 0, 0\right)$$

*Formalization.* `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.chainR` (`✓ std3`).

*Citation.* Waldemar Kłobus; Michał Oszmaniec; Remigiusz Augusiak; Andrzej Grudka (2016). *Communication strength of correlations violating monogamy relations*. DOI: [10.1007/s10701-015-9983-5](https://doi.org/10.1007/s10701-015-9983-5). URL: <https://arxiv.org/abs/1408.1223v2>.

*Commentary.*

The chained Bell expression is the sum over k < M of the correlators of A_k B_k and of A_(k+1) B_k, with the convention A_M = -A_0, so its last term is minus the correlator of A_0 B_(M-1). R_M adds twice the correlator of B_0 and E, read at the setting A_0; for the boxes of the conjecture it does not depend on the setting of A.

**Definition 1.8 (The inequalities (ElPrat)).**

$$\forall M : \mathbb{N}, \forall \Delta : \mathbb{R}, \forall xA : \mathbb{N} \to \mathbb{R}, \forall yA : \mathbb{N} \to \mathbb{R}, \forall xB : \mathbb{N} \to \mathbb{R}, \forall yB : \mathbb{N} \to \mathbb{R}, (\operatorname{ElPrat}\left(M, \Delta, xA, yA, xB, yB\right)) \Leftrightarrow (\forall a : \mathbb{N} \to \operatorname{Fin}\left(2\right), \forall b : \mathbb{N} \to \operatorname{Fin}\left(2\right), \forall c : \operatorname{Fin}\left(2\right), \Delta \le \sum_{i \in \operatorname{Icc}\left(1, M - 1\right)} (-1)^{\operatorname{a}\left(i\right)} \cdot (\operatorname{xA}\left(i\right) - \operatorname{yB}\left(i\right)) + \sum_{i \in \operatorname{Icc}\left(1, M - 2\right)} (-1)^{\operatorname{b}\left(i\right)} \cdot (\operatorname{xB}\left(i + 1\right) - \operatorname{yA}\left(i\right)) + (-1)^{c} \cdot (\operatorname{yA}\left(M - 1\right) + \operatorname{yB}\left(0\right)) + \operatorname{xB}\left(1\right) + \operatorname{xB}\left(0\right))$$

*Formalization.* `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.ElPrat` (`✓ std3`).

*Citation.* Waldemar Kłobus; Michał Oszmaniec; Remigiusz Augusiak; Andrzej Grudka (2016). *Communication strength of correlations violating monogamy relations*. DOI: [10.1007/s10701-015-9983-5](https://doi.org/10.1007/s10701-015-9983-5). URL: <https://arxiv.org/abs/1408.1223v2>.

*Commentary.*

One inequality for each choice of the signs a_i, b_i and c in {0, 1}, with a_i for i from 1 to M - 1 and b_i for i from 1 to M - 2.

**Definition 1.9 (The range of the coordinates).**

$$\forall M : \mathbb{N}, \forall xA : \mathbb{N} \to \mathbb{R}, \forall yA : \mathbb{N} \to \mathbb{R}, \forall xB : \mathbb{N} \to \mathbb{R}, \forall yB : \mathbb{N} \to \mathbb{R}, (\operatorname{CoordinateBounds}\left(M, xA, yA, xB, yB\right)) \Leftrightarrow ((\forall i : \mathbb{N}, (i \in \operatorname{Icc}\left(1, M - 1\right)) \Rightarrow ((\left|\operatorname{xA}\left(i\right)\right| \le 1) \land ((\left|\operatorname{yA}\left(i\right)\right| \le 1) \land ((\left|\operatorname{xB}\left(i\right)\right| \le 1) \land (\left|\operatorname{yB}\left(i\right)\right| \le 1))))) \land ((\left|\operatorname{xB}\left(0\right)\right| \le 1) \land (\left|\operatorname{yB}\left(0\right)\right| \le 1)))$$

*Formalization.* `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.CoordinateBounds` (`✓ std3`).

*Citation.* Waldemar Kłobus; Michał Oszmaniec; Remigiusz Augusiak; Andrzej Grudka (2016). *Communication strength of correlations violating monogamy relations*. DOI: [10.1007/s10701-015-9983-5](https://doi.org/10.1007/s10701-015-9983-5). URL: <https://arxiv.org/abs/1408.1223v2>.

*Commentary.*

The coordinates are correlators, so each lies in [-1, 1]; the bound is required on the indices where the coordinate is defined.

**Definition 1.10 (Realizing the coordinates).**

$$\forall M : \mathbb{N}, \forall p : \mathbb{N} \to \mathbb{N} \to Bool \to Bool \to Bool \to \mathbb{R}, \forall xA : \mathbb{N} \to \mathbb{R}, \forall yA : \mathbb{N} \to \mathbb{R}, \forall xB : \mathbb{N} \to \mathbb{R}, \forall yB : \mathbb{N} \to \mathbb{R}, (\operatorname{Realizes}\left(M, p, xA, yA, xB, yB\right)) \Leftrightarrow ((\forall i : \mathbb{N}, (i \in \operatorname{Icc}\left(1, M - 1\right)) \Rightarrow ((\operatorname{corrBE}\left(p, i, i\right) = \operatorname{xA}\left(i\right)) \land ((\operatorname{corrAE}\left(p, i, i - 1\right) = \operatorname{xB}\left(i\right)) \land (\operatorname{corrAE}\left(p, i, i\right) = \operatorname{yB}\left(i\right))))) \land ((\forall i : \mathbb{N}, (i \in \operatorname{Icc}\left(1, M - 2\right)) \Rightarrow (\operatorname{corrBE}\left(p, i + 1, i\right) = \operatorname{yA}\left(i\right))) \land ((\operatorname{corrBE}\left(p, 0, M - 1\right) = \operatorname{yA}\left(M - 1\right)) \land ((\operatorname{corrAE}\left(p, 0, 0\right) = \operatorname{xB}\left(0\right)) \land (\operatorname{corrAE}\left(p, 0, M - 1\right) = \operatorname{yB}\left(0\right))))))$$

*Formalization.* `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.Realizes` (`✓ std3`).

*Citation.* Waldemar Kłobus; Michał Oszmaniec; Remigiusz Augusiak; Andrzej Grudka (2016). *Communication strength of correlations violating monogamy relations*. DOI: [10.1007/s10701-015-9983-5](https://doi.org/10.1007/s10701-015-9983-5). URL: <https://arxiv.org/abs/1408.1223v2>.

*Commentary.*

The coordinates are x_A^i = <B_i E>_(A_i), y_A^i = <B_i E>_(A_(i+1)), x_B^i = <A_i E>_(B_(i-1)) and y_B^i = <A_i E>_(B_i) for i from 1 to M - 1, together with x_B^0 = <A_0 E>_(B_0) and y_B^0 = <A_0 E>_(B_(M-1)). The setting A_M = -A_0 in y_A^(M-1) is the setting A_0 with relabelled outcomes, which does not change a correlator of B and E, so y_A^(M-1) is read at the setting pair (A_0, B_(M-1)).

**Definition 1.11 (The conjecture).**

$$(claim) \Leftrightarrow (\forall M : \mathbb{N}, (2 \le M) \Rightarrow (\forall \Delta : \mathbb{R}, (0 \le \Delta) \Rightarrow ((\Delta \le 2) \Rightarrow (\forall xA : \mathbb{N} \to \mathbb{R}, \forall yA : \mathbb{N} \to \mathbb{R}, \forall xB : \mathbb{N} \to \mathbb{R}, \forall yB : \mathbb{N} \to \mathbb{R}, (\operatorname{CoordinateBounds}\left(M, xA, yA, xB, yB\right)) \Rightarrow ((\operatorname{ElPrat}\left(M, \Delta, xA, yA, xB, yB\right)) \Rightarrow (\exists p : \mathbb{N} \to \mathbb{N} \to Bool \to Bool \to Bool \to \mathbb{R}, (\operatorname{IsBox}\left(M, p\right)) \land ((\operatorname{OddMomentsVanish}\left(M, p\right)) \land ((\forall i : \mathbb{N}, (i < M) \Rightarrow (\operatorname{corrBE}\left(p, i, 0\right) = \operatorname{corrBE}\left(p, 0, 0\right))) \land ((\operatorname{chainR}\left(M, p\right) = 2 \cdot M + \Delta) \land (\operatorname{Realizes}\left(M, p, xA, yA, xB, yB\right)))))))))))$$

*Formalization.* `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.claim` (`✓ std3`).

*Citation.* Waldemar Kłobus; Michał Oszmaniec; Remigiusz Augusiak; Andrzej Grudka (2016). *Communication strength of correlations violating monogamy relations*. DOI: [10.1007/s10701-015-9983-5](https://doi.org/10.1007/s10701-015-9983-5). URL: <https://arxiv.org/abs/1408.1223v2>.

*Commentary.*

The paper conjectures that all values of the coordinates satisfying (ElPrat) can be realized with some signaling distribution for which R_M = 2M + Delta, within the class of boxes with vanishing one- and three-party expectation values and a common correlator of B_0 and E. The displayed statement reads it for every M at least 2 and every Delta in [0, 2]; the conjecture is the case M at least 3, and for M = 2 the inequalities (ElPrat) are the paper's printed list with the signs of x_A^1 and y_A^1 corrected in two of its four lines.

**Theorem 1.12 (The conjecture holds).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.result` (`✓ std3`). ∎

*Resolves.* `Problems/klobus-2016-chained-monogamy-realizability` (proved) by `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"klobus-2016-chained-monogamy-realizability","declaration_gid":"D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Waldemar Kłobus; Michał Oszmaniec; Remigiusz Augusiak; Andrzej Grudka (2016). *Communication strength of correlations violating monogamy relations*. DOI: [10.1007/s10701-015-9983-5](https://doi.org/10.1007/s10701-015-9983-5). URL: <https://arxiv.org/abs/1408.1223v2>.

*Commentary.*

For |v|, |w| at most 1 and -1 + |v + w| <= u <= 1 - |v - w|, the function (1 + ab u + ae v + be w)/8 of the signs a, b, e is a probability distribution whose correlators of A and B, A and E, and B and E are u, v and w, and whose one- and three-party expectation values vanish. Let T be the sum of |x_A^i - y_B^i| over 1 <= i <= M - 1, of |x_B^(i+1) - y_A^i| over 1 <= i <= M - 2, and |y_A^(M-1) + y_B^0|. Choosing every sign in (ElPrat) against its term gives x_B^0 + x_B^1 - T >= Delta, so t = (2 + Delta + T)/(2 + x_B^0 + x_B^1) lies in (0, 1]. Take (u, v, w) = (t x_B^0, x_B^0, t) at (A_0, B_0) and (t x_B^1, x_B^1, t) at (A_1, B_0); (0, 0, t) at the other pairs (A_i, B_0); at (A_i, B_i) and (A_(i+1), B_i) with i >= 1 the prescribed v and w with u = 1 - |v - w|; at (A_0, B_(M-1)) the prescribed v = y_B^0 and w = y_A^(M-1) with u = -1 + |v + w|; and (0, 0, 0) elsewhere. The box realizes the coordinates, the correlator of B_0 and E equals t at every setting of A, and R_M = (2M - 2 - T) + t (x_B^0 + x_B^1 + 2) = 2M + Delta.

## References

- Truth anchor: `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.CoordinateBounds`
- Truth anchor: `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.ElPrat`
- Truth anchor: `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.IsBox`
- Truth anchor: `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.OddMomentsVanish`
- Truth anchor: `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.Realizes`
- Truth anchor: `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.chainR`
- Truth anchor: `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.claim`
- Truth anchor: `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.corrAB`
- Truth anchor: `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.corrAE`
- Truth anchor: `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.corrBE`
- Truth anchor: `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.result`
- Truth anchor: `D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability.sgn`
