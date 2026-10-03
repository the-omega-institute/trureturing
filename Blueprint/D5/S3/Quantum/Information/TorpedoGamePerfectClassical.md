# A perfect classical strategy for the Torpedo Game

## Abstract

For every d >= 5, the dimension-d Torpedo Game has a perfect classical strategy: the classical value, the greatest winning probability of a one-dit prepare-and-measure strategy with shared randomness, equals 1. This is the conjecture theta^C_(d>=5) = 1 of P.-E. Emeriau, M. Howard and S. Mansfield (arXiv:2007.15643, PRX Quantum 3, 020307 (2022)), who found perfect strategies for 5 <= d <= 23.

**Definition 1.1 (The answer to avoid).**

$$\forall x \in \mathbb{Z}/d,\; \forall z \in \mathbb{Z}/d,\; (\operatorname{label}\left(\operatorname{none}\left(\right), x, z\right) = x) \land (\forall q \in \mathbb{Z}/d,\; \operatorname{label}\left(\operatorname{some}\left(q\right), x, z\right) = q \cdot x - z)$$

*Formalization.* `D5/S3/Quantum/Information/TorpedoGamePerfectClassical.label` (`✓ std3`).

*Citation.* Pierre-Emmanuel Emeriau; Mark Howard; Shane Mansfield (2022). *Quantum Advantage in Information Retrieval*. DOI: [10.1103/PRXQuantum.3.020307](https://doi.org/10.1103/PRXQuantum.3.020307). URL: <https://arxiv.org/abs/2007.15643v2>.

*Commentary.*

Alice receives x and z in Z/d and Bob a question q in {infinity, 0, ..., d - 1}, written none for infinity and some(q) for q in Z/d. Bob wins when his answer is not label(q, x, z): the winning relations of eq. (2) are w_infinity(x, z) = {a | a != x} and w_q(x, z) = {a | a != q x - z}.

**Definition 1.2 (Winning probability).**

$$\operatorname{winProb}\left(mu, e, f\right) = \frac{1}{d^{2} \cdot (d + 1)} \cdot (\sum_{x \in \mathbb{Z}/d} \sum_{z \in \mathbb{Z}/d} \sum_{q \in \operatorname{Option}\left(\mathbb{Z}/d\right)} \sum_{l \in \operatorname{Fin}\left(n\right)} mu\left(l\right) \cdot (\sum_{j \in \mathbb{Z}/d} e\left(l, x, z, j\right) \cdot (\sum_{c \in \mathbb{Z}/d, c \ne \operatorname{label}\left(q, x, z\right)} f\left(l, j, q, c\right))))$$

*Formalization.* `D5/S3/Quantum/Information/TorpedoGamePerfectClassical.winProb` (`✓ std3`).

*Citation.* Pierre-Emmanuel Emeriau; Mark Howard; Shane Mansfield (2022). *Quantum Advantage in Information Retrieval*. DOI: [10.1103/PRXQuantum.3.020307](https://doi.org/10.1103/PRXQuantum.3.020307). URL: <https://arxiv.org/abs/2007.15643v2>.

*Commentary.*

The winning probability with uniform referee inputs, as in eq. (cval): shared randomness l in Fin(n) drawn from mu, Alice sends j with probability e(l, x, z, j), Bob answers c to question q on message j with probability f(l, j, q, c), and the probability of a winning answer is averaged over the d^2 (d + 1) triples (x, z, q).

**Definition 1.3 (Classical winning probabilities).**

$$\operatorname{classicalValues}\left(d\right) = \{v \mid \exists n : \mathbb{N}, \exists mu : \operatorname{Fin}\left(n\right) \to \mathbb{R}, \exists e : \operatorname{Fin}\left(n\right) \to \mathbb{Z}/d \to \mathbb{Z}/d \to \mathbb{Z}/d \to \mathbb{R}, \exists f : \operatorname{Fin}\left(n\right) \to \mathbb{Z}/d \to \operatorname{Option}\left(\mathbb{Z}/d\right) \to \mathbb{Z}/d \to \mathbb{R}, (mu \in \operatorname{stdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right)) \land \left((\forall l \in \operatorname{Fin}\left(n\right),\; \forall x \in \mathbb{Z}/d,\; \forall z \in \mathbb{Z}/d,\; e\left(l, x, z\right) \in \operatorname{stdSimplex}\left(\mathbb{R}, \mathbb{Z}/d\right)) \land \left((\forall l \in \operatorname{Fin}\left(n\right),\; \forall j \in \mathbb{Z}/d,\; \forall q \in \operatorname{Option}\left(\mathbb{Z}/d\right),\; f\left(l, j, q\right) \in \operatorname{stdSimplex}\left(\mathbb{R}, \mathbb{Z}/d\right)) \land (\operatorname{winProb}\left(mu, e, f\right) = v)\right)\right)\}$$

*Formalization.* `D5/S3/Quantum/Information/TorpedoGamePerfectClassical.classicalValues` (`✓ std3`).

*Citation.* Pierre-Emmanuel Emeriau; Mark Howard; Shane Mansfield (2022). *Quantum Advantage in Information Retrieval*. DOI: [10.1103/PRXQuantum.3.020307](https://doi.org/10.1103/PRXQuantum.3.020307). URL: <https://arxiv.org/abs/2007.15643v2>.

*Commentary.*

The winning probabilities of all classical strategies: finite shared randomness with a probability vector mu, and encodings and decodings that are probability vectors for every value of the randomness and every input or question. Here stdSimplex(R, X) is Mathlib's standard simplex, the functions X -> R with nonnegative values summing to 1.

**Definition 1.4 (The conjecture).**

$$claim \Leftrightarrow (\forall d \in \mathbb{N},\; (\operatorname{NeZero}\left(d\right)) \Rightarrow \left((5 \le d) \Rightarrow \operatorname{IsGreatest}\left(\operatorname{classicalValues}\left(d\right), 1\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/TorpedoGamePerfectClassical.claim` (`✓ std3`).

*Citation.* Pierre-Emmanuel Emeriau; Mark Howard; Shane Mansfield (2022). *Quantum Advantage in Information Retrieval*. DOI: [10.1103/PRXQuantum.3.020307](https://doi.org/10.1103/PRXQuantum.3.020307). URL: <https://arxiv.org/abs/2007.15643v2>.

*Commentary.*

Eq. (11) of the paper, theta^C_(d>=5) = 1: for every d >= 5 the classical value, the greatest classical winning probability, is 1. The hypothesis NeZero(d), that d is nonzero, makes Z/d finite and holds for every d >= 5.

**Theorem 1.5 (Proof of the conjecture).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/TorpedoGamePerfectClassical.result` (`✓ std3`). ∎

*Resolves.* `Problems/emeriau-2020-torpedo-perfect-classical` (proved) by `D5/S3/Quantum/Information/TorpedoGamePerfectClassical.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"emeriau-2020-torpedo-perfect-classical","declaration_gid":"D5/S3/Quantum/Information/TorpedoGamePerfectClassical.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pierre-Emmanuel Emeriau; Mark Howard; Shane Mansfield (2022). *Quantum Advantage in Information Retrieval*. DOI: [10.1103/PRXQuantum.3.020307](https://doi.org/10.1103/PRXQuantum.3.020307). URL: <https://arxiv.org/abs/2007.15643v2>.

*Commentary.*

Every classical winning probability is at most 1, since each term is a probability. For the lower bound it suffices to give a deterministic strategy that wins on every input and question. For d = 5 the colouring of the paper's Fig. 9 with a tabulated decoding is checked on all 150 cases. For d >= 6, rows 2i and 2i + 1 carry two classes, {(2i, 0), (2i, 1)} together with row 2i + 1 outside columns 0 and 2, and the rest of row 2i together with (2i + 1, 0) and (2i + 1, 2); for odd d the last three rows r, r + 1, r + 2 carry three classes, row r outside -1, -2, -3 with row r + 1 at 0, 1, 3, the rest of row r + 1 with row r + 2 at 0, 2, 3, and row r at -1, -2, -3 with the rest of row r + 2. For each class and question, Bob answers an explicit value that no point of the class has as its label: the labels q x - z of a row part missing columns F miss exactly q x - F, and the chosen value in that gap avoids the labels of the other row part once d >= 6 separates the small constants involved. The strategy with one-point shared randomness and 0/1 encoding and decoding then wins with probability 1.

## References

- Truth anchor: `D5/S3/Quantum/Information/TorpedoGamePerfectClassical.claim`
- Truth anchor: `D5/S3/Quantum/Information/TorpedoGamePerfectClassical.classicalValues`
- Truth anchor: `D5/S3/Quantum/Information/TorpedoGamePerfectClassical.label`
- Truth anchor: `D5/S3/Quantum/Information/TorpedoGamePerfectClassical.result`
- Truth anchor: `D5/S3/Quantum/Information/TorpedoGamePerfectClassical.winProb`
