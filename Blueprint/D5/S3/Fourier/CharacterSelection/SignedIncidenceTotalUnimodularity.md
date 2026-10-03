# Integer Signed Incidence Boundaries are Totally Unimodular

## Abstract

Integer signed endpoint boundaries are totally unimodular for arbitrary parallel directed edges and loops.

**Definition 1.1 (The integer signed endpoint incidence matrix).**

$$\operatorname{signedIncidence}\left(tail, head, v, e\right) = \mathbf{1}_{{v = \operatorname{head}\left(e\right)}} - \mathbf{1}_{{v = \operatorname{tail}\left(e\right)}} \in \mathbb{Z}.$$

*Formalization.* `D5/S3/Fourier/CharacterSelection/SignedIncidenceTotalUnimodularity.signedIncidence` (`✓ std3`).

*Citation.* Jan Vondrák; Richard Pang (scribe) (2017). *MATH233B: Polyhedral techniques in combinatorial optimization, Lecture 3*. URL: <https://theory.stanford.edu/~jvondrak/MATH233B-2017/lec3.pdf>.

*Commentary.*

For arbitrary vertex and edge types, each column records one positive head endpoint and one negative tail endpoint. A loop therefore gives a zero column, while parallel edge labels remain separate columns.

**Theorem 1.2 (Every finite minor has determinant minus one, zero, or one).**

$$\forall V: \operatorname{Type}, \forall E: \operatorname{Type}, [\operatorname{DecidableEq}\left(V\right)], \forall tail, head: E \to V, \forall k: \mathbb{N}, \forall f: \operatorname{Fin}\left(k\right) \to V, \forall g: \operatorname{Fin}\left(k\right) \to E, \operatorname{Injective}\left(f\right) \Rightarrow \operatorname{Injective}\left(g\right) \Rightarrow \operatorname{det}\left(\operatorname{submatrix}\left(\operatorname{signedIncidence}\left(tail, head\right), f, g\right)\right) \in \{-1, 0, 1\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/SignedIncidenceTotalUnimodularity.signed_incidence_is_totally_unimodular` (`✓ std3`). ∎

*Citation.* Jan Vondrák; Richard Pang (scribe) (2017). *MATH233B: Polyhedral techniques in combinatorial optimization, Lecture 3*. URL: <https://theory.stanford.edu/~jvondrak/MATH233B-2017/lec3.pdf>.

*Commentary.*

For every natural minor order k, every injective row selection f from Fin k to V, and every injective column selection g from Fin k to E, the determinant of the selected signed incidence minor belongs to {-1, 0, 1}. No finiteness, simplicity, loop-free, connectedness, or orientation restriction is imposed.

The proof inducts on the minor order. A loop or a selected column with a missing endpoint is handled by Laplace expansion and the induction hypothesis. If every selected column has two distinct selected endpoints, the sum of the selected rows is zero, so the determinant vanishes. The zero-order minor has determinant one.

This is literature-attested from Vondrak's MATH233B Lecture 3, Lemma 10, and is formalized here with the stronger arbitrary endpoint presentation. It does not claim flow integrality or a matrix-tree theorem.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/SignedIncidenceTotalUnimodularity.signedIncidence`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/SignedIncidenceTotalUnimodularity.signed_incidence_is_totally_unimodular`
