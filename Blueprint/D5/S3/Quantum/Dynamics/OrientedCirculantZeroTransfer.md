# Song and Lin's parity conjecture for zero transfer is false

## Abstract

On the connected oriented circulant graph G(Z_30, {5, 6, 9, 20}) the continuous-time quantum walk never moves amplitude between the vertex 0 and the even vertex 2, so the parity restriction conjectured for orders n = 2 (mod 4) fails at n = 30.

**Definition 1.1 (The Hermitian adjacency matrix).**

$$\forall a \in \operatorname{ZMod}\left(n\right),\; \forall b \in \operatorname{ZMod}\left(n\right),\; (\operatorname{hermAdj}\left(n, C\right))_{a, b} = \operatorname{ite}\left(b - a \in C, i, \operatorname{ite}\left(a - b \in C, -i, 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.hermAdj` (`✓ std3`).

*Citation.* Xingkun Song, Huiqiu Lin (2026). *Zero transfer on mixed graphs*. DOI: [10.48550/arXiv.2608.10643](https://doi.org/10.48550/arXiv.2608.10643). URL: <https://arxiv.org/abs/2608.10643v1>.

*Commentary.*

For a connection set C in Z_n the circulant graph has an arc from a to b when b - a lies in C. The Hermitian adjacency matrix has entry i on arcs, -i on reversed arcs and 0 elsewhere; for an oriented connection set no pair carries both.

**Definition 1.2 (The transition matrix).**

$$\forall t \in \mathbb{R},\; \operatorname{transition}\left(n, C, t\right) = \operatorname{NormedSpace.exp}\left(-\left(i \cdot t\right) \cdot \operatorname{hermAdj}\left(n, C\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.transition` (`✓ std3`).

*Citation.* Xingkun Song, Huiqiu Lin (2026). *Zero transfer on mixed graphs*. DOI: [10.48550/arXiv.2608.10643](https://doi.org/10.48550/arXiv.2608.10643). URL: <https://arxiv.org/abs/2608.10643v1>.

*Commentary.*

The continuous-time quantum walk at real time t is the matrix exponential U(t) = exp(-i t H).

**Definition 1.3 (Zero transfer).**

$$\operatorname{ZeroTransfer}\left(n, C, u, v\right) \Leftrightarrow (\forall t \in \mathbb{R},\; (0 \le t) \Rightarrow ((\operatorname{transition}\left(n, C, t\right))_{u, v} = 0))$$

*Formalization.* `D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.ZeroTransfer` (`✓ std3`).

*Citation.* Xingkun Song, Huiqiu Lin (2026). *Zero transfer on mixed graphs*. DOI: [10.48550/arXiv.2608.10643](https://doi.org/10.48550/arXiv.2608.10643). URL: <https://arxiv.org/abs/2608.10643v1>.

*Commentary.*

The graph has zero transfer from u to v when the (u, v) entry of U(t) vanishes at every time t >= 0.

**Definition 1.4 (Oriented connection sets).**

$$\operatorname{Oriented}\left(C\right) \Leftrightarrow ((\neg 0 \in C) \land (\forall x \in C,\; \neg -x \in C))$$

*Formalization.* `D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.Oriented` (`✓ std3`).

*Citation.* Xingkun Song, Huiqiu Lin (2026). *Zero transfer on mixed graphs*. DOI: [10.48550/arXiv.2608.10643](https://doi.org/10.48550/arXiv.2608.10643). URL: <https://arxiv.org/abs/2608.10643v1>.

*Commentary.*

The connection set avoids 0 and contains no element together with its negative.

**Definition 1.5 (Connectedness).**

$$(\forall a \in \operatorname{ZMod}\left(n\right),\; \forall b \in \operatorname{ZMod}\left(n\right),\; \operatorname{arc}\left(C, a, b\right) \Leftrightarrow (b - a \in C)) \land (\operatorname{Connected}\left(C\right) \Leftrightarrow (\operatorname{SimpleGraph.Connected}\left(\operatorname{SimpleGraph.fromRel}\left(\operatorname{arc}\left(C\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.Connected` (`✓ std3`).

*Citation.* Xingkun Song, Huiqiu Lin (2026). *Zero transfer on mixed graphs*. DOI: [10.48550/arXiv.2608.10643](https://doi.org/10.48550/arXiv.2608.10643). URL: <https://arxiv.org/abs/2608.10643v1>.

*Commentary.*

The underlying undirected graph, which joins distinct a and b when b - a or a - b lies in C, is connected.

**Definition 1.6 (The conjecture).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; (\operatorname{NatMod}\left(n, 4\right) = 2) \Rightarrow (\forall C \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{Oriented}\left(C\right)) \Rightarrow ((\operatorname{Connected}\left(C\right)) \Rightarrow (\forall v \in \operatorname{ZMod}\left(n\right),\; ((\operatorname{ZeroTransfer}\left(n, C, v, 0\right)) \land (\operatorname{ZeroTransfer}\left(n, C, 0, v\right))) \Rightarrow (\operatorname{Odd}\left(\operatorname{ZMod.val}\left(v\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.claim` (`✓ std3`).

*Citation.* Xingkun Song, Huiqiu Lin (2026). *Zero transfer on mixed graphs*. DOI: [10.48550/arXiv.2608.10643](https://doi.org/10.48550/arXiv.2608.10643). URL: <https://arxiv.org/abs/2608.10643v1>.

*Commentary.*

For every order n = 2 (mod 4), every oriented connection set with connected graph and every vertex v, zero transfer between v and 0 in both directions forces the representative of v in 0, ..., n - 1 to be odd. Reading zero transfer between v and 0 in both directions only strengthens the hypothesis.

**Theorem 1.7 (The counterexample n = 30, C = {5, 6, 9, 20}, v = 2).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.result` (`✓ std3`). ∎

*Resolves.* `Problems/song-lin-2026-oriented-circulant-zero-transfer-parity-refutation` (refuted) by `D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"song-lin-2026-oriented-circulant-zero-transfer-parity-refutation","declaration_gid":"D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Xingkun Song, Huiqiu Lin (2026). *Zero transfer on mixed graphs*. DOI: [10.48550/arXiv.2608.10643](https://doi.org/10.48550/arXiv.2608.10643). URL: <https://arxiv.org/abs/2608.10643v1>.

*Commentary.*

The set C is oriented, and 6 - 5 = 1 connects every vertex a to a + 1 through a + 6, so the graph is connected. H is i times the integer skew-symmetric matrix S with entry 1 on arcs and -1 on reversed arcs, so every power of H is a power of i times the corresponding power of S. Seven exact row products give the rows r_k of S^k at vertex 0 for k <= 7; they satisfy r_k(2) = 0 for k <= 6 and r_7 = -32 r_5 - 320 r_3 - 960 r_1. Multiplying by S propagates this relation to r_(k+7) for every k, so strong induction gives (S^k)(0, 2) = 0 for all k, and skew-symmetry gives (S^k)(2, 0) = (-1)^k (S^k)(0, 2) = 0. Each term of the exponential series of -i t H therefore has vanishing (0, 2) and (2, 0) entries, so U(t) has them too at every time, and zero transfer holds between 0 and the even vertex 2.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.Connected`
- Truth anchor: `D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.Oriented`
- Truth anchor: `D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.ZeroTransfer`
- Truth anchor: `D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.hermAdj`
- Truth anchor: `D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.result`
- Truth anchor: `D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.transition`
