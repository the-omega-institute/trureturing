# Weak similarity of minimum-order ultrametric spaces

## Abstract

Minimum-order finite ultrametric spaces with equally many points are weakly similar, and weak similarity preserves the number of central distances.

**Definition 1.1 (Weak similarity).**

Lean statement: `D5/S3/Combinatorics/Geometry/Ultrametric/MCDWeakSimilarity.WeaklySimilar`

*Formalization.* `D5/S3/Combinatorics/Geometry/Ultrametric/MCDWeakSimilarity.WeaklySimilar` (`✓ std3`).

*Citation.* Oleksiy Dovgoshey and Olga Rovenska (2026). *On the center of distances of finite ultrametric spaces*. DOI: [10.48550/arXiv.2603.25850](https://doi.org/10.48550/arXiv.2603.25850). URL: <https://arxiv.org/abs/2603.25850v1>.

*Commentary.*

A weak similarity of metric spaces X and Y is a bijection Φ : X → Y together with a function f, strictly increasing on the set of distances of Y, such that d(x, y) = f(ρ(Φ x, Φ y)) for all x and y (Dovgoshey and Rovenska, Definition 4.1).

**Theorem 1.2 (Weak similarity and the center).**

Lean statement: `D5/S3/Combinatorics/Geometry/Ultrametric/MCDWeakSimilarity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Ultrametric/MCDWeakSimilarity.result` (`✓ std3`). ∎

*Citation.* Oleksiy Dovgoshey and Olga Rovenska (2026). *On the center of distances of finite ultrametric spaces*. DOI: [10.48550/arXiv.2603.25850](https://doi.org/10.48550/arXiv.2603.25850). URL: <https://arxiv.org/abs/2603.25850v1>.

*Commentary.*

Two finite ultrametric spaces X and Y with |X| = 2^(|C(X)| - 1), |Y| = 2^(|C(Y)| - 1) and |X| = |Y| are weakly similar. Every weak similarity of metric spaces preserves the number of central distances, finite or infinite. Hence, for finite ultrametric spaces with |X| = |Y| = 2^h and |C(X)| = h + 1, |C(Y)| = h + 1 exactly when X and Y are weakly similar. This is Conjecture 4.2 of O. Dovgoshey and O. Rovenska. The paper arXiv:2609.11384 of Dovgoshey, Jaiswal, Kainth, Kaur and Rovenska proves their companion Conjecture 4.3 and classifies the representing trees of minimum-order spaces (Theorem 4.1) but does not state Conjecture 4.2; the proof here is direct.

On a minimum-order space every distance is central, and the two open balls below the diameter around points at the diameter are minimum-order halves with the lower center. Let g be the order isomorphism from C(Y) to C(X); it sends the diameter of Y to that of X and restricts to the lower centers, so by induction the halves of X and Y admit bijections carrying ρ to d through g, and these glue across the diameter. Conversely a weak similarity Φ, f maps C(Y) onto C(X) through f, which is injective on the distances of Y.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/Ultrametric/MCDWeakSimilarity.WeaklySimilar`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Ultrametric/MCDWeakSimilarity.result`
- Dependency: [D5/S3/Combinatorics/Geometry/Ultrametric/MCDIsometry](MCDIsometry.md)
