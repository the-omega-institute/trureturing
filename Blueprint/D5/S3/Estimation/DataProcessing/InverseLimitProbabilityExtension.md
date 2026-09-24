# Probability Extension on Compatible Threads

## Abstract

A compatible family of finite joint probability laws has one unique Borel extension on the corresponding finite tuple of inverse-limit threads.

**Theorem 1.1 (Compatible joint laws extend uniquely).**

$$\begin{aligned}(\forall l \in \mathbb{N}, \operatorname{push}\left(\operatorname{nodewise}\left(q_{l}, n\right), Q_{l+1}\right) = Q_{l}) \Rightarrow\\\operatorname{ExistsUnique}\left(mu, \operatorname{Prob}\left(X\right)\right): \forall l \in \mathbb{N}, \operatorname{push}\left(pi_{l}, mu\right) = Q_{l}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/InverseLimitProbabilityExtension.exists_unique_probability_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each alphabet is finite, nonempty, and discrete, with its Borel measurable structure. Adjacent carrier maps are surjective. At each level there is a probability law on tuples of the same fixed finite length.

The only compatibility condition on these laws is exact pushforward by the coordinatewise bonding map. No restricted feasible-law map is assumed surjective.

A prescribed symbol extends downward by the bonding maps and upward by chosen right inverses. These threads lift every finite joint law. The sets of completed probabilities with a prescribed level law are nonempty, closed, and decreasing. Compactness of the probability space gives their common member.

Two extensions have identical level laws, so the full event total-variation identity makes their distance zero. Equality on every measurable event establishes uniqueness.

Uniqueness concerns the extension of an already compatible family. It does not imply uniqueness of a nearest feasible law, and the theorem does not select compatible finite minimizers.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/InverseLimitProbabilityExtension.exists_unique_probability_extension`
- Dependency: [D5/S3/Estimation/DataProcessing/InverseLimitEventTotalVariation](InverseLimitEventTotalVariation.md)
