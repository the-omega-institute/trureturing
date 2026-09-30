# The distinguished-entry obstruction

## Abstract

Every transversal of the literal H-family square contains at least two of its three distinguished entries.

**Theorem 1.1 (The distinguished-entry obstruction).**

$$\forall k \in \mathrm{Nat},\; 9 \le k \Rightarrow \left(\forall S \in \operatorname{Set}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{order}\left(k\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{order}\left(k\right)\right), \operatorname{Fin}\left(\operatorname{order}\left(k\right)\right)\right)\right)\right),\; \operatorname{IsTransversal}\left(k, S\right) \Rightarrow 2 \le \operatorname{ncard}\left(\operatorname{inter}\left(\operatorname{D}\left(k\right), S\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinHTransversals.transversal_obstruction` (`✓ std3`). ∎

*Citation.* Afsane Ghafari, Ian M. Wanless (2026). *Latin Squares whose transversals intersect in unusual ways*. DOI: [10.48550/arXiv.2607.17547](https://doi.org/10.48550/arXiv.2607.17547). URL: <https://arxiv.org/abs/2607.17547v1>.

*Commentary.*

The square adds its priority increment to the row and column representatives modulo four k. The three literal profiles use affine cap columns and four bulk progressions, with the cap choice depending on the parity of k. Choosing the unique entry in each row of an arbitrary transversal gives column and symbol permutations. Their sums force the total priority increment to be congruent to two k modulo four k. The row lower bounds sum to minus two k plus three. If at most one distinguished entry is selected, the upper bound is two k minus three, which contradicts that congruence.

## References

- Truth anchor: `D5/S3/Combinatorics/LatinHTransversals.transversal_obstruction`
- Dependency: [D5/S3/Combinatorics/LatinEulerianDefs](LatinEulerianDefs.md)
