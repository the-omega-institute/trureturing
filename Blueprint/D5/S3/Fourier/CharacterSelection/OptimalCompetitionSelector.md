# Optimal Competition Selector

## Abstract

A positive projection margin produces the normalized selector that removes every competitor.

**Definition 1.1 (Finite complex character-profile space).**

Lean statement: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.CharacterProfileSpace`

*Formalization.* `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.CharacterProfileSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient carrier is EuclideanSpace C (Fin d), the finite complex coordinate space named in the source chain.

**Definition 1.2 (Finite real-rational feature family).**

Lean statement: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.FiniteRealRationalFeatureFamily`

*Formalization.* `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.FiniteRealRationalFeatureFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier consists of d real rational functions. Its public fields require conjugation equivariance, evenness, reality on the real axis, every pole outside the critical strip, and sufficient decay in the real direction.

**Definition 1.3 (Evaluation of the feature family).**

Lean statement: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.featureProfile`

*Formalization.* `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.featureProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Phi(z) evaluates every real-rational feature at the same complex point and collects the values in EuclideanSpace C (Fin d).

**Definition 1.4 (Underlying real profile pairing).**

Lean statement: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.profileDot`

*Formalization.* `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.profileDot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Because the competitor span is real, the source dot product is represented by the underlying real inner product on the complex coordinate space.

**Definition 1.5 (Real span of competitor profiles).**

Lean statement: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.competitorProfileSpace`

*Formalization.* `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.competitorProfileSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

W is the real submodule spanned by the finite family Phi(z_j).

**Definition 1.6 (Target-to-competitor margin).**

Lean statement: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.selectorMargin`

*Formalization.* `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.selectorMargin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Delta is the metric distance from the target profile to the real competitor span.

**Definition 1.7 (Competitor interpolation constraints).**

Lean statement: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.IsLagrangeInterpolant`

*Formalization.* `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.IsLagrangeInterpolant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Lagrange candidate here means only a unit coefficient vector whose pairing with every competing feature profile vanishes.

**Definition 1.8 (The interpolation constraints do not select arbitrarily).**

Lean statement: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.NotArbitraryLagrangeInterpolation`

*Formalization.* `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.NotArbitraryLagrangeInterpolation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

It is not the case that every unit solution of the bare zero-value interpolation constraints equals the displayed selector.

**Definition 1.9 (Orthogonal projection formulation).**

Lean statement: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.IsOrthogonalProjectionProblem`

*Formalization.* `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.IsOrthogonalProjectionProblem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The geometric margin is exactly the norm of the target feature profile's projection onto the orthogonal complement of the competitor span.

**Theorem 1.10 (The normalized complementary projection is optimal).**

$$\begin{gathered}\forall d, m: \mathbb{N},\\{}Phi: \operatorname{FiniteRealRationalFeatureFamily}(d), z_{0}: \mathbb{C}, z: \operatorname{Fin}(m) \to \mathbb{C},\\{}\operatorname{let}(W := \operatorname{competitorProfileSpace}(Phi, z), Delta := \operatorname{selectorMargin}(Phi, z_{0}, z))\;\\{}0 < Delta \Rightarrow \exists c_{*}: \operatorname{EuclideanSpace}(\mathbb{C}, \operatorname{Fin}(d)), \operatorname{norm}(c_{*}) = 1 \land \left(c_{*} \in W^{\perp} \land \left({\forall j: \operatorname{Fin}(m), \operatorname{profileDot}(c_{*}, \operatorname{featureProfile}(Phi, z(j))) = 0} \land \left(\operatorname{abs}(\operatorname{profileDot}(c_{*}, \operatorname{featureProfile}(Phi, z_{0}))) = Delta \land \left(c_{*} = \operatorname{norm}(\operatorname{starProjection}(W^{\perp}, \operatorname{featureProfile}(Phi, z_{0})))^{-1} \cdot \operatorname{starProjection}(W^{\perp}, \operatorname{featureProfile}(Phi, z_{0})) \land \left(\operatorname{NotArbitraryLagrangeInterpolation}(Phi, z, c_{*}) \land \operatorname{IsOrthogonalProjectionProblem}(Phi, z_{0}, z)\right)\right)\right)\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.optimal_competition_selector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite real-rational feature family satisfying all five source conditions, the premise Delta > 0 yields a unit witness in W perp.

The public result states every source conclusion: competitors are annihilated, the target response is Delta, the witness has the displayed normalized-projection formula, the interpolation is not arbitrary, and the problem is explicitly an orthogonal projection.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.CharacterProfileSpace`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.FiniteRealRationalFeatureFamily`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.IsLagrangeInterpolant`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.IsOrthogonalProjectionProblem`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.NotArbitraryLagrangeInterpolation`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.competitorProfileSpace`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.featureProfile`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.optimal_competition_selector`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.profileDot`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector.selectorMargin`
- Dependency: [D5/S3/Observer/CanonicalStrongestSeparatingObserver](../../Observer/CanonicalStrongestSeparatingObserver.md)
