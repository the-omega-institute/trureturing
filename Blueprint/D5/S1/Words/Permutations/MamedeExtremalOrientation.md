# Extremal Orientation

## Abstract

Extremal generators determine an endpoint orientation.

**Theorem 1.1 (Support and full extremal run).**

$$\operatorname {Reduced}\left(n, w\right) \land \operatorname {Consecutive}\left(w\right) \land w \neq \operatorname {nil}\left(\right) \implies \exists m M , \operatorname {AttainedSupport}\left(n, w, m, M\right) \land \operatorname {ExteriorFixed}\left(n, w, m, M\right) \land ( \operatorname {DescendingOrientation}\left(n, w, m, M\right) \lor \operatorname {AscendingOrientation}\left(n, w, m, M\right) )$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeExtremalOrientation.extremal_orientation` (`✓ std3`). ∎

*Citation.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

For every nonempty reduced consecutive adjacent-swap word w, there are attained generator extrema 1<=m<=M<=n, and every letter lies in [m,M]. The product fixes all one-based positions outside [m,M+1]. In the descending orientation it maps m to M+1 and w=p++descending(M,m)++q, with every prefix letter below M and every suffix letter above m. In the ascending orientation it maps M+1 to m and w=p++ascending(m,M)++q, with every prefix letter above m and every suffix letter below M. Either or both orientations can hold. This is the generator-extrema form of Mamede, Santos and Soares, Lemma 3.1, together with the exterior support property. Word reversal represents permutation inversion. No nonoscillation assumption or strict internal endpoints are asserted; the result applies to oscillating words and single-generator words as well.

## References

- Truth anchor: `D5/S1/Words/Permutations/MamedeExtremalOrientation.extremal_orientation`
- Dependency: [D5/S1/Words/Permutations/MamedeCrossing](MamedeCrossing.md)
