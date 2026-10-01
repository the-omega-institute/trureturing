# Tight penalty coefficients for the QUBO reformulations of max k-cut

## Abstract

For max k-cut with real edge weights, every optimal solution of the one-hot QUBO reformulation is an optimal k-cut as soon as each penalty c_v exceeds max(d+_v / k, -d-_v / 2), and every optimal solution of the reduced R-QUBO reformulation is one as soon as c_v exceeds d+_v - d-_v, where d+_v and d-_v are the sums of the positive and of the negative weights at v. These are Conjectures 1 and 2 of A. Harkness et al. (arXiv:2511.01108), who proved the bounds with -(3/2) d-_v and -2 d-_v.

**Definition 1.1 (Positive weighted degree).**

$$\operatorname{dplus}\left(w, v\right) = \sum_{u \neq v, 0 < w\left(u, v\right)} w\left(u, v\right)$$

*Formalization.* `D5/S3/Quantum/Information/MaxKCutQuboPenalty.dplus` (`✓ std3`).

*Citation.* Adrian Harkness; Hamidreza Validi; Ramin Fakhimi; Illya V. Hicks; Samuel Stein; Tamás Terlaky; Luis F. Zuluaga (2025). *Characterizing QUBO Reformulations of the Max-k-Cut Problem for Quantum Computing*. DOI: [10.48550/arXiv.2511.01108](https://doi.org/10.48550/arXiv.2511.01108). URL: <https://arxiv.org/abs/2511.01108v3>.

*Commentary.*

The sum of the positive weights w(u, v) over the vertices u other than v.

**Definition 1.2 (Negative weighted degree).**

$$\operatorname{dminus}\left(w, v\right) = \sum_{u \neq v, w\left(u, v\right) < 0} w\left(u, v\right)$$

*Formalization.* `D5/S3/Quantum/Information/MaxKCutQuboPenalty.dminus` (`✓ std3`).

*Citation.* Adrian Harkness; Hamidreza Validi; Ramin Fakhimi; Illya V. Hicks; Samuel Stein; Tamás Terlaky; Luis F. Zuluaga (2025). *Characterizing QUBO Reformulations of the Max-k-Cut Problem for Quantum Computing*. DOI: [10.48550/arXiv.2511.01108](https://doi.org/10.48550/arXiv.2511.01108). URL: <https://arxiv.org/abs/2511.01108v3>.

*Commentary.*

The sum of the negative weights w(u, v) over the vertices u other than v.

**Definition 1.3 (The BQO objective).**

$$\operatorname{cutValue}\left(w, x\right) = \sum_{u < v} w\left(u, v\right) \cdot (1 - \sum_{j} \operatorname{bit}\left(x\left(u, j\right)\right) \cdot \operatorname{bit}\left(x\left(v, j\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/MaxKCutQuboPenalty.cutValue` (`✓ std3`).

*Citation.* Adrian Harkness; Hamidreza Validi; Ramin Fakhimi; Illya V. Hicks; Samuel Stein; Tamás Terlaky; Luis F. Zuluaga (2025). *Characterizing QUBO Reformulations of the Max-k-Cut Problem for Quantum Computing*. DOI: [10.48550/arXiv.2511.01108](https://doi.org/10.48550/arXiv.2511.01108). URL: <https://arxiv.org/abs/2511.01108v3>.

*Commentary.*

The BQO objective of max k-cut, evaluated on every Boolean matrix; each entry is read by the frozen bit as 1 or 0. On one-hot matrices it is the weight of the edges u < v whose endpoints lie in different parts.

**Definition 1.4 (The QUBO objective).**

$$\operatorname{quboObjective}\left(w, c, x\right) = \operatorname{cutValue}\left(w, x\right) - \sum_{v} c\left(v\right) \cdot (\sum_{j} \operatorname{bit}\left(x\left(v, j\right)\right) - 1)^{2}$$

*Formalization.* `D5/S3/Quantum/Information/MaxKCutQuboPenalty.quboObjective` (`✓ std3`).

*Citation.* Adrian Harkness; Hamidreza Validi; Ramin Fakhimi; Illya V. Hicks; Samuel Stein; Tamás Terlaky; Luis F. Zuluaga (2025). *Characterizing QUBO Reformulations of the Max-k-Cut Problem for Quantum Computing*. DOI: [10.48550/arXiv.2511.01108](https://doi.org/10.48550/arXiv.2511.01108). URL: <https://arxiv.org/abs/2511.01108v3>.

*Commentary.*

The BQO objective minus the penalty c_v (sum_j x_vj - 1)^2 at every vertex.

**Definition 1.5 (BQO feasibility).**

$$\operatorname{OneHot}\left(x\right) \Leftrightarrow (\forall v \in \operatorname{Fin}\left(n\right),\; \sum_{j} \operatorname{bit}\left(x\left(v, j\right)\right) = 1)$$

*Formalization.* `D5/S3/Quantum/Information/MaxKCutQuboPenalty.OneHot` (`✓ std3`).

*Citation.* Adrian Harkness; Hamidreza Validi; Ramin Fakhimi; Illya V. Hicks; Samuel Stein; Tamás Terlaky; Luis F. Zuluaga (2025). *Characterizing QUBO Reformulations of the Max-k-Cut Problem for Quantum Computing*. DOI: [10.48550/arXiv.2511.01108](https://doi.org/10.48550/arXiv.2511.01108). URL: <https://arxiv.org/abs/2511.01108v3>.

*Commentary.*

Every vertex lies in exactly one part.

**Definition 1.6 (The R-BQO objective).**

$$\operatorname{reducedCutValue}\left(w, x\right) = \sum_{u < v} w\left(u, v\right) \cdot (1 - \sum_{j} \operatorname{bit}\left(x\left(u, j\right)\right) \cdot \operatorname{bit}\left(x\left(v, j\right)\right) - (1 - \sum_{j} \operatorname{bit}\left(x\left(u, j\right)\right)) \cdot (1 - \sum_{j} \operatorname{bit}\left(x\left(v, j\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Information/MaxKCutQuboPenalty.reducedCutValue` (`✓ std3`).

*Citation.* Adrian Harkness; Hamidreza Validi; Ramin Fakhimi; Illya V. Hicks; Samuel Stein; Tamás Terlaky; Luis F. Zuluaga (2025). *Characterizing QUBO Reformulations of the Max-k-Cut Problem for Quantum Computing*. DOI: [10.48550/arXiv.2511.01108](https://doi.org/10.48550/arXiv.2511.01108). URL: <https://arxiv.org/abs/2511.01108v3>.

*Commentary.*

The reduced formulation keeps k - 1 columns; a vertex with no column set lies in the last part, so an edge is cut unless its endpoints share a column or both have none.

**Definition 1.7 (The R-QUBO objective).**

$$\operatorname{reducedQuboObjective}\left(w, c, x\right) = \operatorname{reducedCutValue}\left(w, x\right) - \sum_{v} c\left(v\right) \cdot \sum_{i < j} \operatorname{bit}\left(x\left(v, i\right)\right) \cdot \operatorname{bit}\left(x\left(v, j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/MaxKCutQuboPenalty.reducedQuboObjective` (`✓ std3`).

*Citation.* Adrian Harkness; Hamidreza Validi; Ramin Fakhimi; Illya V. Hicks; Samuel Stein; Tamás Terlaky; Luis F. Zuluaga (2025). *Characterizing QUBO Reformulations of the Max-k-Cut Problem for Quantum Computing*. DOI: [10.48550/arXiv.2511.01108](https://doi.org/10.48550/arXiv.2511.01108). URL: <https://arxiv.org/abs/2511.01108v3>.

*Commentary.*

The R-BQO objective minus the penalty c_v sum_{i<j} x_vi x_vj at every vertex.

**Definition 1.8 (R-BQO feasibility).**

$$\operatorname{AtMostOneHot}\left(x\right) \Leftrightarrow (\forall v \in \operatorname{Fin}\left(n\right),\; \sum_{j} \operatorname{bit}\left(x\left(v, j\right)\right) \le 1)$$

*Formalization.* `D5/S3/Quantum/Information/MaxKCutQuboPenalty.AtMostOneHot` (`✓ std3`).

*Citation.* Adrian Harkness; Hamidreza Validi; Ramin Fakhimi; Illya V. Hicks; Samuel Stein; Tamás Terlaky; Luis F. Zuluaga (2025). *Characterizing QUBO Reformulations of the Max-k-Cut Problem for Quantum Computing*. DOI: [10.48550/arXiv.2511.01108](https://doi.org/10.48550/arXiv.2511.01108). URL: <https://arxiv.org/abs/2511.01108v3>.

*Commentary.*

Every vertex has at most one of the k - 1 columns set.

**Definition 1.9 (Conjecture 1).**

$$quboPenaltyConjecture \Leftrightarrow (\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{R}\right),\; \forall c \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; (3 \le k) \Rightarrow \left((\forall u \in \operatorname{Fin}\left(n\right),\; \forall v \in \operatorname{Fin}\left(n\right),\; w\left(u, v\right) = w\left(v, u\right)) \Rightarrow \left((\forall v \in \operatorname{Fin}\left(n\right),\; \operatorname{max}\left(\frac{\operatorname{dplus}\left(w, v\right)}{k}, \frac{-\operatorname{dminus}\left(w, v\right)}{2}\right) < c\left(v\right)) \Rightarrow \left(\forall xh \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(k\right) \to \operatorname{Bool}\right),\; (\forall x \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(k\right) \to \operatorname{Bool}\right),\; \operatorname{quboObjective}\left(w, c, x\right) \le \operatorname{quboObjective}\left(w, c, xh\right)) \Rightarrow \left((\operatorname{OneHot}\left(xh\right)) \land (\forall x \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(k\right) \to \operatorname{Bool}\right),\; (\operatorname{OneHot}\left(x\right)) \Rightarrow \operatorname{cutValue}\left(w, x\right) \le \operatorname{cutValue}\left(w, xh\right))\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/MaxKCutQuboPenalty.quboPenaltyConjecture` (`✓ std3`).

*Citation.* Adrian Harkness; Hamidreza Validi; Ramin Fakhimi; Illya V. Hicks; Samuel Stein; Tamás Terlaky; Luis F. Zuluaga (2025). *Characterizing QUBO Reformulations of the Max-k-Cut Problem for Quantum Computing*. DOI: [10.48550/arXiv.2511.01108](https://doi.org/10.48550/arXiv.2511.01108). URL: <https://arxiv.org/abs/2511.01108v3>.

*Commentary.*

For k at least 3 (the scope of the paper) and symmetric real weights, if c_v > max(d+_v / k, -d-_v / 2) for every vertex, then every maximiser of the QUBO objective over all Boolean matrices is one-hot and maximises the BQO objective among one-hot matrices.

**Definition 1.10 (Conjecture 2).**

$$reducedQuboPenaltyConjecture \Leftrightarrow (\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{R}\right),\; \forall c \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; (2 \le m) \Rightarrow \left((\forall u \in \operatorname{Fin}\left(n\right),\; \forall v \in \operatorname{Fin}\left(n\right),\; w\left(u, v\right) = w\left(v, u\right)) \Rightarrow \left((\forall v \in \operatorname{Fin}\left(n\right),\; \operatorname{dplus}\left(w, v\right) - \operatorname{dminus}\left(w, v\right) < c\left(v\right)) \Rightarrow \left(\forall xh \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(m\right) \to \operatorname{Bool}\right),\; (\forall x \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(m\right) \to \operatorname{Bool}\right),\; \operatorname{reducedQuboObjective}\left(w, c, x\right) \le \operatorname{reducedQuboObjective}\left(w, c, xh\right)) \Rightarrow \left((\operatorname{AtMostOneHot}\left(xh\right)) \land (\forall x \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(m\right) \to \operatorname{Bool}\right),\; (\operatorname{AtMostOneHot}\left(x\right)) \Rightarrow \operatorname{reducedCutValue}\left(w, x\right) \le \operatorname{reducedCutValue}\left(w, xh\right))\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/MaxKCutQuboPenalty.reducedQuboPenaltyConjecture` (`✓ std3`).

*Citation.* Adrian Harkness; Hamidreza Validi; Ramin Fakhimi; Illya V. Hicks; Samuel Stein; Tamás Terlaky; Luis F. Zuluaga (2025). *Characterizing QUBO Reformulations of the Max-k-Cut Problem for Quantum Computing*. DOI: [10.48550/arXiv.2511.01108](https://doi.org/10.48550/arXiv.2511.01108). URL: <https://arxiv.org/abs/2511.01108v3>.

*Commentary.*

For m = k - 1 at least 2 columns and symmetric real weights, if c_v > d+_v - d-_v for every vertex, then every maximiser of the R-QUBO objective has at most one column set at each vertex and maximises the R-BQO objective among such matrices.

**Definition 1.11 (Both conjectures).**

$$claim \Leftrightarrow ((\operatorname{quboPenaltyConjecture}) \land (\operatorname{reducedQuboPenaltyConjecture}))$$

*Formalization.* `D5/S3/Quantum/Information/MaxKCutQuboPenalty.claim` (`✓ std3`).

*Citation.* Adrian Harkness; Hamidreza Validi; Ramin Fakhimi; Illya V. Hicks; Samuel Stein; Tamás Terlaky; Luis F. Zuluaga (2025). *Characterizing QUBO Reformulations of the Max-k-Cut Problem for Quantum Computing*. DOI: [10.48550/arXiv.2511.01108](https://doi.org/10.48550/arXiv.2511.01108). URL: <https://arxiv.org/abs/2511.01108v3>.

*Commentary.*

The conjunction of Conjectures 1 and 2.

**Theorem 1.12 (Proof of both conjectures).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/MaxKCutQuboPenalty.result` (`✓ std3`). ∎

*Resolves.* `Problems/harkness-2025-maxkcut-qubo-penalty` (proved) by `D5/S3/Quantum/Information/MaxKCutQuboPenalty.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"harkness-2025-maxkcut-qubo-penalty","declaration_gid":"D5/S3/Quantum/Information/MaxKCutQuboPenalty.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Adrian Harkness; Hamidreza Validi; Ramin Fakhimi; Illya V. Hicks; Samuel Stein; Tamás Terlaky; Luis F. Zuluaga (2025). *Characterizing QUBO Reformulations of the Max-k-Cut Problem for Quantum Computing*. DOI: [10.48550/arXiv.2511.01108](https://doi.org/10.48550/arXiv.2511.01108). URL: <https://arxiv.org/abs/2511.01108v3>.

*Commentary.*

Let t_v be the number of parts of v in an optimal x, and suppose some vertex has t_v at least 2. For each colour j delete j from every vertex with two or more colours, and add up the changes of the objective over all k colours. The penalty of such a vertex drops by c_v t_v (2 t_v - 3) in total, and the term of an edge touching such a vertex increases by w_uv times the number of its shared colours, since each deletion removes one shared colour. That number is at most half the sum of t (2t - 3) over the endpoints with two or more colours, so the edges with negative weight cost at most -d-_v / 2 times t_v (2 t_v - 3) at each such vertex, and the edges with positive weight only help. The total is therefore at least the sum of (c_v + d-_v / 2) t_v (2 t_v - 3), which is positive, so one of the deletions improves x, a contradiction. If some vertex had no colour, giving it colour i gains c_v minus the weight of its neighbours of colour i, which is at least k c_v - d+_v > 0 when summed over i. So x is one-hot and, since the penalty vanishes on one-hot matrices, an optimal k-cut. For the reduced objective the same deletion changes each edge term by at most s_u (s_u - 1) + s_v (s_v - 1) in absolute value and each penalty by c_v s_v (s_v - 1), where s_v is the number of columns set, so the total gain is at least the sum of (c_v - d+_v + d-_v) s_v (s_v - 1) > 0.

## References

- Truth anchor: `D5/S3/Quantum/Information/MaxKCutQuboPenalty.AtMostOneHot`
- Truth anchor: `D5/S3/Quantum/Information/MaxKCutQuboPenalty.OneHot`
- Truth anchor: `D5/S3/Quantum/Information/MaxKCutQuboPenalty.claim`
- Truth anchor: `D5/S3/Quantum/Information/MaxKCutQuboPenalty.cutValue`
- Truth anchor: `D5/S3/Quantum/Information/MaxKCutQuboPenalty.dminus`
- Truth anchor: `D5/S3/Quantum/Information/MaxKCutQuboPenalty.dplus`
- Truth anchor: `D5/S3/Quantum/Information/MaxKCutQuboPenalty.quboObjective`
- Truth anchor: `D5/S3/Quantum/Information/MaxKCutQuboPenalty.quboPenaltyConjecture`
- Truth anchor: `D5/S3/Quantum/Information/MaxKCutQuboPenalty.reducedCutValue`
- Truth anchor: `D5/S3/Quantum/Information/MaxKCutQuboPenalty.reducedQuboObjective`
- Truth anchor: `D5/S3/Quantum/Information/MaxKCutQuboPenalty.reducedQuboPenaltyConjecture`
- Truth anchor: `D5/S3/Quantum/Information/MaxKCutQuboPenalty.result`
- Dependency: [D5/S3/Quantum/Entanglement/PhaseHistoryBound](../Entanglement/PhaseHistoryBound.md)
