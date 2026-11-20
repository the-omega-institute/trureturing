# A transposition bound from two readouts

## Abstract

Sharp mass fixed by a transposition for paired labels and two-element subsets.

**Theorem 1.1 (The mass fixed by a transposition is at most one sixth).**

$$\forall S w f g, \operatorname{InvariantSeedWeights}\left(S, w\right) \land \operatorname{EquivariantLabelAndPair}\left(S, f, g\right) \Rightarrow \operatorname{FixedMass}\left(w, \operatorname{Swap}\left(0, 1\right)\right) \le \frac{1}{6}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/TranspositionFixedMass.seeded_transposition_mass_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite seed set carries an action of the group of permutations of four labels. The weights are nonnegative, total one, and invariant. Each seed is read as a label and as a two-element subset of labels, with both readouts equivariant. FixedMass sums the weights of seeds fixed by the transposition of labels zero and one.

For every label and two-element subset exactly one of the six transpositions fixes both. Conjugacy and invariance give each transposition the same mass among the readout pairs. Every fixed seed contributes to that transposition's fixed readout mass.

**Theorem 1.2 (The uniform label-and-pair law attains the bound).**

$$\exists w, \operatorname{PositiveExactlyOnLabelAndPair}\left(w\right) \land \operatorname{Invariant}\left(w\right) \land \operatorname{UniformLabelMarginal}\left(w, \frac{1}{4}\right) \land \operatorname{UniformPairMarginal}\left(w, \frac{1}{6}\right) \land \operatorname{TotalMass}\left(w\right) = 1 \land \operatorname{FixedMass}\left(w, \operatorname{Swap}\left(0, 1\right)\right) = \frac{1}{6}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/TranspositionFixedMass.uniform_label_pair_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The invariant law assigns positive mass to every label and two-element subset pair and zero elsewhere. The label marginal has mass one quarter per label and the subset marginal has mass one sixth per two-element subset. The total mass is one. The fixed mass is one sixth.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/TranspositionFixedMass.seeded_transposition_mass_le`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/TranspositionFixedMass.uniform_label_pair_attains`
