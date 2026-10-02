# Suvagiya Conjecture 28 is false

## Abstract

A signed square-cycle on 32 vertices has radius below the proposed universal optimum.

**Definition 1.1 (All independent edge signings).**

$$\forall n \in \mathrm{Nat},\; \operatorname{Signing}\left(n\right) = ((\operatorname{Fin}\left(n\right)) \to (\mathrm{Bool})) \times ((\operatorname{Fin}\left(n\right)) \to (\mathrm{Bool}))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.Signing` (`✓ std3`).

*Citation.* Vaibhav Suvagiya (2026). *Parity families and signed spectra: kernel averaging, near-Ramanujan bounds, and exact circulant models*. DOI: [10.48550/arXiv.2607.17343](https://doi.org/10.48550/arXiv.2607.17343). URL: <https://arxiv.org/html/2607.17343v2>.

*Commentary.*

The two Boolean functions assign independent signs to the forward edges of lengths one and two. True represents +1 and false represents -1. For n at least five these index each undirected edge exactly once; the carrier includes both Hamilton-cycle sign products.

**Definition 1.2 (The two edge weights).**

$$\forall b \in \mathrm{Bool},\; \operatorname{edgeSign}\left(b\right) = \operatorname{if}\left(b, 1, -1\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.edgeSign` (`✓ std3`).

*Citation.* Vaibhav Suvagiya (2026). *Parity families and signed spectra: kernel averaging, near-Ramanujan bounds, and exact circulant models*. DOI: [10.48550/arXiv.2607.17343](https://doi.org/10.48550/arXiv.2607.17343). URL: <https://arxiv.org/html/2607.17343v2>.

*Commentary.*

Each Boolean selects exactly one of the two rational weights.

**Definition 1.3 (Forward adjacency).**

$$\forall n \in \mathrm{Nat},\; \forall sigma \in \operatorname{Signing}\left(n\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{forward}\left(sigma, i, j\right) = \operatorname{if}\left(\operatorname{val}\left(j\right) = \operatorname{mod}\left(\operatorname{val}\left(i\right) + 1, n\right), \operatorname{edgeSign}\left(\operatorname{fst}\left(sigma\right)(i)\right), \operatorname{if}\left(\operatorname{val}\left(j\right) = \operatorname{mod}\left(\operatorname{val}\left(i\right) + 2, n\right), \operatorname{edgeSign}\left(\operatorname{snd}\left(sigma\right)(i)\right), 0\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.forward` (`✓ std3`).

*Citation.* Vaibhav Suvagiya (2026). *Parity families and signed spectra: kernel averaging, near-Ramanujan bounds, and exact circulant models*. DOI: [10.48550/arXiv.2607.17343](https://doi.org/10.48550/arXiv.2607.17343). URL: <https://arxiv.org/html/2607.17343v2>.

*Commentary.*

Indices are residues modulo n, represented by Fin n. The first test assigns the step-one sign and the second assigns the step-two sign; every remaining forward entry is zero.

**Definition 1.4 (Undirected rational adjacency).**

$$\forall n \in \mathrm{Nat},\; \forall sigma \in \operatorname{Signing}\left(n\right),\; \operatorname{adjacencyRat}\left(sigma\right) = \operatorname{forward}\left(sigma\right) + \operatorname{transpose}\left(\operatorname{forward}\left(sigma\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.adjacencyRat` (`✓ std3`).

*Citation.* Vaibhav Suvagiya (2026). *Parity families and signed spectra: kernel averaging, near-Ramanujan bounds, and exact circulant models*. DOI: [10.48550/arXiv.2607.17343](https://doi.org/10.48550/arXiv.2607.17343). URL: <https://arxiv.org/html/2607.17343v2>.

*Commentary.*

Adding the transpose places each signed edge in both symmetric positions. At n = 8m with m at least four, the diagonal is zero and there are exactly 2n undirected edges, with four incident edges at each vertex.

**Definition 1.5 (Real signed adjacency).**

$$\forall n \in \mathrm{Nat},\; \forall sigma \in \operatorname{Signing}\left(n\right),\; \operatorname{adjacency}\left(sigma\right) = \operatorname{map}\left(\operatorname{adjacencyRat}\left(sigma\right), \operatorname{castHom}\left(\mathrm{Real}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.adjacency` (`✓ std3`).

*Citation.* Vaibhav Suvagiya (2026). *Parity families and signed spectra: kernel averaging, near-Ramanujan bounds, and exact circulant models*. DOI: [10.48550/arXiv.2607.17343](https://doi.org/10.48550/arXiv.2607.17343). URL: <https://arxiv.org/html/2607.17343v2>.

*Commentary.*

The rational entries are cast into the real field. The real matrix is the actual symmetric signed adjacency, with unchanged edge weights.

**Definition 1.6 (The proposed optimal-radius quartic).**

$$\forall x \in \mathrm{Real},\; \operatorname{quartic}\left(x\right) = x^{4} - 2\cdot x^{3} - 6\cdot x^{2} + 12\cdot x - 4$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.quartic` (`✓ std3`).

*Citation.* Vaibhav Suvagiya (2026). *Parity families and signed spectra: kernel averaging, near-Ramanujan bounds, and exact circulant models*. DOI: [10.48550/arXiv.2607.17343](https://doi.org/10.48550/arXiv.2607.17343). URL: <https://arxiv.org/html/2607.17343v2>.

*Commentary.*

This is the quartic in Conjecture 28.

**Definition 1.7 (Real quartic roots).**

$$\forall x \in \mathrm{Real},\; (x \in quarticRoots) \Leftrightarrow (\operatorname{quartic}\left(x\right) = 0)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.quarticRoots` (`✓ std3`).

*Citation.* Vaibhav Suvagiya (2026). *Parity families and signed spectra: kernel averaging, near-Ramanujan bounds, and exact circulant models*. DOI: [10.48550/arXiv.2607.17343](https://doi.org/10.48550/arXiv.2607.17343). URL: <https://arxiv.org/html/2607.17343v2>.

*Commentary.*

A greatest element of this set is a real root and bounds every real root above.

**Definition 1.8 (Attained maximum absolute spectra).**

$$\forall n \in \mathrm{Nat},\; \forall s \in \mathrm{Real},\; (s \in \operatorname{radiusValues}\left(n\right)) \Leftrightarrow (\exists sigma \in \operatorname{Signing}\left(n\right),\; \operatorname{IsGreatest}\left(\operatorname{image}\left(abs, \operatorname{spectrum}\left(\mathrm{Real}, \operatorname{adjacency}\left(sigma\right)\right)\right), s\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.radiusValues` (`✓ std3`).

*Citation.* Vaibhav Suvagiya (2026). *Parity families and signed spectra: kernel averaging, near-Ramanujan bounds, and exact circulant models*. DOI: [10.48550/arXiv.2607.17343](https://doi.org/10.48550/arXiv.2607.17343). URL: <https://arxiv.org/html/2607.17343v2>.

*Commentary.*

The radius set ranges over the entire finite signing carrier. IsGreatest requires membership in the absolute spectrum as well as an upper bound for every member. Thus these are attained maxima, with no default value for an empty set.

**Definition 1.9 (The complete Conjecture 28).**

$$(claim) \Leftrightarrow (\forall m \in \mathrm{Int},\; (4 \le m) \Rightarrow (\exists r \in \mathrm{Real},\; (\operatorname{IsGreatest}\left(quarticRoots, r\right)) \land (\operatorname{IsLeast}\left(\operatorname{radiusValues}\left(8\cdot \operatorname{toNat}\left(m\right)\right), r\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.claim` (`✓ std3`).

*Citation.* Vaibhav Suvagiya (2026). *Parity families and signed spectra: kernel averaging, near-Ramanujan bounds, and exact circulant models*. DOI: [10.48550/arXiv.2607.17343](https://doi.org/10.48550/arXiv.2607.17343). URL: <https://arxiv.org/html/2607.17343v2>.

*Commentary.*

The source asserts the equality for every integer m at least four. IsLeast requires the radius to be attained by some signing and to bound every signing's radius below. Greatest roots are unique, so the per-m existential denotes the same r-star at every m. No periodic or gauge restriction is imposed.

**Theorem 1.10 (A strict counterexample to Conjecture 28).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/suvagiya-conjecture28-refutation` (refuted) by `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"suvagiya-conjecture28-refutation","declaration_gid":"D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

At m = 4, the step-one weights are +1 except a_31 = -1. Repeat (1,1,-1,1,-1,-1,1,-1) for the step-two weights, then set b_30 = -1 and b_31 = +1. The squared adjacency is annihilated by R(y) = y^8-32y^7+416y^6-2816y^5+10568y^4-21632y^3 +22168y^2-9408y+1262. Exact finite Horner identities establish R(A^2) = 0. Every coefficient of R((279/100)^2+z) is positive. Spectral mapping therefore gives absolute eigenvalues at most 279/100; the finite real spectrum attains its maximum. The quartic takes values -6766519/100000000 at 279/100 and 5 at 3. Continuity supplies a root strictly between them. A greatest root therefore exceeds the attained radius of the displayed signing, contradicting the proposed minimum. Theorem 26's upper bound is unaffected; the exact optima and any repaired restrictions remain undetermined.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.Signing`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.adjacency`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.adjacencyRat`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.edgeSign`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.forward`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.quartic`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.quarticRoots`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.radiusValues`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.result`
