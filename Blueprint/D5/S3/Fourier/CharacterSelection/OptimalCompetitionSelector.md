# Optimal Competition Selector

## Abstract

A positive projection margin produces the normalized selector that removes every competitor.

**Definition 1.1 (Finite complex character-profile space).**

Lean statement: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.CharacterProfileSpace`

*Formalization.* `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.CharacterProfileSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient carrier is EuclideanSpace C (Fin d), the finite complex coordinate space named in the source chain.

**Definition 1.2 (Underlying real profile pairing).**

Lean statement: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.profileDot`

*Formalization.* `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.profileDot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Because the competitor span is real, the source dot product is represented by the underlying real inner product on the complex coordinate space.

**Definition 1.3 (Real span of competitor profiles).**

Lean statement: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.competitorProfileSpace`

*Formalization.* `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.competitorProfileSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

W is the real submodule spanned by the finite family Phi(z_j).

**Definition 1.4 (Target-to-competitor margin).**

Lean statement: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.selectorMargin`

*Formalization.* `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.selectorMargin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Delta is the metric distance from the target profile to the real competitor span.

**Theorem 1.5 (The normalized complementary projection is optimal).**

$$\begin{gathered}\forall d, m: \mathbb{N},\\{}Phi: \mathbb{C} \to \operatorname{EuclideanSpace}(\mathbb{C}, \operatorname{Fin}(d)), z_{0}: \mathbb{C}, z: \operatorname{Fin}(m) \to \mathbb{C},\\{}\operatorname{let}(W := \operatorname{competitorProfileSpace}(Phi, z), Delta := \operatorname{selectorMargin}(Phi, z_{0}, z))\;\\{}0 < Delta \Rightarrow \exists c_{*}: \operatorname{EuclideanSpace}(\mathbb{C}, \operatorname{Fin}(d)), \operatorname{norm}(c_{*}) = 1 \land \left(c_{*} \in W^{\perp} \land \left({\forall j: \operatorname{Fin}(m), \operatorname{profileDot}(c_{*}, Phi(z(j))) = 0} \land \left(\operatorname{abs}(\operatorname{profileDot}(c_{*}, Phi(z_{0}))) = Delta \land c_{*} = \operatorname{norm}(\operatorname{starProjection}(W^{\perp}, Phi(z_{0})))^{-1} \cdot \operatorname{starProjection}(W^{\perp}, Phi(z_{0}))\right)\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.optimal_competition_selector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the sole substantive premise Delta > 0, the displayed witness has unit norm and belongs to the orthogonal complement of W.

The same public result states all three displayed source conclusions: every competing profile is annihilated, the absolute target response is Delta, and the witness equals the normalized complementary projection.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.CharacterProfileSpace`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.competitorProfileSpace`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.optimal_competition_selector`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.profileDot`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.selectorMargin`
- Dependency: [D5/S3/Observer/CanonicalStrongestSeparatingObserver](../../Observer/CanonicalStrongestSeparatingObserver.md)
