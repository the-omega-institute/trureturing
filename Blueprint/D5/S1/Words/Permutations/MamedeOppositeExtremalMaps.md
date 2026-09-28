# Opposite Extremal Maps

## Abstract

Symmetric excursions and opposite extremal maps force oscillation.

**Theorem 1.1 (No two exterior factors around a symmetric excursion).**

$$\operatorname {ReducedConsecutiveSymmetricExcursion}\left(n, m, M, p, q\right) \land \operatorname {InteriorSupport}\left(m, M, p, q\right) \implies p = \operatorname {EmptyWord}\left(\right) \lor q = \operatorname {EmptyWord}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeOppositeExtremalMaps.symmetric_excursion_outer_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let 1<=m<M<=n and let the middle word descend from M to m, then ascend from m+1 to M. If p and q contain only generators strictly between m and M, and the combined word is reduced and consecutive, then p or q is empty. The middle product swaps positions m and M+1 and fixes the interior. When both factors are nonempty, consecutiveness forces generator M-1 at both boundaries; the two copies commute through the middle product and cancel, contradicting reducedness. This is an unbounded source theorem. It does not derive the displayed factorization from opposite endpoint maps or prove their oscillation consequence.

**Theorem 1.2 (Oscillation from both extremal position maps).**

$$\operatorname {SingletonWord}\left(n, sigma, a\right) \land \operatorname {AttainedGeneratorExtrema}\left(m, M, a\right) \land \operatorname {GeneratorInterval}\left(n, m, M, a\right) \land \operatorname {OppositeExtremalMaps}\left(n, m, M, sigma\right) \implies \operatorname {Oscillation}\left(a\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeOppositeExtremalMaps.opposite_extremal_maps_oscillation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a be a singletonWord for sigma, so a is reduced and consecutive and its product is sigma. Suppose m and M both occur in a, 1<=m<=M<=n, and every letter k satisfies m<=k<=M. If sigma sends position M+1 to m and position m to M+1 simultaneously, then oscillation(a). For m=M the word begins at its attained minimum. For m<M, exterior fixedness and the guarded strand walk force a full descent in a and another full descent in its reverse, hence a full ascent in a. Comparing the run prefixes aligns them at m or M; the two occurrences of m are not assumed equal. The resulting descent-then-ascent or ascent-then-descent excursion has strictly interior outer factors. The symmetric-excursion obstruction, with generator reflection for the second orientation, makes one factor empty. An actual extremal first or last letter then supplies the endpoint-oscillation theorem. No oscillation, source shape, exterior fixedness, or word endpoint is an input. This is the implication for the explicit attained-generator interval, not a global fiber count.

## References

- Truth anchor: `D5/S1/Words/Permutations/MamedeOppositeExtremalMaps.opposite_extremal_maps_oscillation`
- Truth anchor: `D5/S1/Words/Permutations/MamedeOppositeExtremalMaps.symmetric_excursion_outer_empty`
- Dependency: [D5/S1/Words/Permutations/MamedeEndpointUniqueness](MamedeEndpointUniqueness.md)
