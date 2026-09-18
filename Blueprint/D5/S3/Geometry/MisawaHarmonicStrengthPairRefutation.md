# A Harmonic-Strength Pair Obstruction on the Unit Circle

## Abstract

The pair {2,4} refutes the proposed universal value five for two-element harmonic strength.

**Definition 1.1 (Complex moments).**

$$\forall X \in \operatorname{Finset}\left(\mathbb{C}\right),\; \forall k \in \mathbb{N},\; \operatorname{momentSum}\left(X, k\right) = \sum_{x \in X} x^{k}$$

*Formalization.* `D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.momentSum` (`✓ std3`).

*Citation.* Ryutaro Misawa, Yusaku Nishimura (2025). *Spherical Designs on S¹ of Finite Harmonic Strength*. DOI: [10.48550/arXiv.2505.06893](https://doi.org/10.48550/arXiv.2505.06893). URL: <https://arxiv.org/abs/2505.06893v2>.

*Commentary.*

For a finite set X of complex numbers, momentSum(X,k) is the sum of the k-th powers of its elements. This is P_k(X) on printed pages 2--3.

**Definition 1.2 (Harmonic strength).**

$$\forall X \in \operatorname{Finset}\left(\mathbb{C}\right),\; \operatorname{harmonicStrength}\left(X\right) = \{k \in \mathbb{N} \mid \operatorname{momentSum}\left(X, k\right) = 0\}$$

*Formalization.* `D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.harmonicStrength` (`✓ std3`).

*Citation.* Ryutaro Misawa, Yusaku Nishimura (2025). *Spherical Designs on S¹ of Finite Harmonic Strength*. DOI: [10.48550/arXiv.2505.06893](https://doi.org/10.48550/arXiv.2505.06893). URL: <https://arxiv.org/abs/2505.06893v2>.

*Commentary.*

The harmonic strength is the set of natural indices at which the complex moment vanishes. This is the paper's working form of Hst(X).

**Definition 1.3 (Finite subsets of the unit circle).**

$$\forall X \in \operatorname{Finset}\left(\mathbb{C}\right),\; (\operatorname{OnUnitCircle}\left(X\right)) \Leftrightarrow (\forall x \in X,\; \left\lVert x \right\rVert = 1)$$

*Formalization.* `D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.OnUnitCircle` (`✓ std3`).

*Citation.* Ryutaro Misawa, Yusaku Nishimura (2025). *Spherical Designs on S¹ of Finite Harmonic Strength*. DOI: [10.48550/arXiv.2505.06893](https://doi.org/10.48550/arXiv.2505.06893). URL: <https://arxiv.org/abs/2505.06893v2>.

*Commentary.*

OnUnitCircle(X) means that every member of the finite complex set X has norm one, matching the identification S¹ = {z ∈ ℂ | |z| = 1}.

**Definition 1.4 (Minimum size at a prescribed strength).**

$$\forall T \in \operatorname{Set}\left(\mathbb{N}\right),\; \operatorname{minimumSize}\left(T\right) = \operatorname{sInf}\left(\{n \in \mathbb{N} \mid \exists X \in \operatorname{Finset}\left(\mathbb{C}\right),\; (\operatorname{OnUnitCircle}\left(X\right)) \land ((\operatorname{harmonicStrength}\left(X\right) = T) \land ((\operatorname{card}\left(X\right) = n)))\}\right)$$

*Formalization.* `D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.minimumSize` (`✓ std3`).

*Citation.* Ryutaro Misawa, Yusaku Nishimura (2025). *Spherical Designs on S¹ of Finite Harmonic Strength*. DOI: [10.48550/arXiv.2505.06893](https://doi.org/10.48550/arXiv.2505.06893). URL: <https://arxiv.org/abs/2505.06893v2>.

*Commentary.*

minimumSize(T) is the infimum in the natural numbers of the attainable cardinalities of finite unit-circle sets with harmonic strength exactly T. The convention for an empty family is Nat.sInf_empty = 0.

**Definition 1.5 (Misawa--Nishimura Conjecture 3.3).**

$$(claim) \Leftrightarrow (\forall p \in \mathbb{N},\; \forall q \in \mathbb{N},\; (1 < p) \Rightarrow ((1 < q) \Rightarrow ((p \ne q) \Rightarrow (\operatorname{minimumSize}\left(\left\{p, q\right\}\right) = 5))))$$

*Formalization.* `D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.claim` (`✓ std3`).

*Citation.* Ryutaro Misawa, Yusaku Nishimura (2025). *Spherical Designs on S¹ of Finite Harmonic Strength*. DOI: [10.48550/arXiv.2505.06893](https://doi.org/10.48550/arXiv.2505.06893). URL: <https://arxiv.org/abs/2505.06893v2>.

*Commentary.*

Conjecture 3.3 on printed page 6 reads verbatim: “Let p ≠ q be integers with p, q > 1. Then N({p, q}, 2) = 5.” On the same page, “For a nonempty finite set T ⊂ ℕ, define N(T, 2) := min{|X| | X ⊂ S¹, Hst(X) = T}.” The formal statement uses natural p and q with the printed lower bounds.

**Theorem 1.6 (The pair {2,4} refutes the conjecture).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/misawa-nishimura-harmonic-strength-pair-refutation` (refuted) by `D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"misawa-nishimura-harmonic-strength-pair-refutation","declaration_gid":"D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Assume a five-point unit-circle set has vanishing second and fourth moments. After squaring its five points, conjugation and the unit relations turn the first two vanishing power sums into a polynomial identity forcing the third power sum to vanish. Thus the original sixth moment also vanishes, so its harmonic strength cannot equal {2,4}. No value for minimumSize({2,4}) is asserted.

## References

- Truth anchor: `D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.OnUnitCircle`
- Truth anchor: `D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.claim`
- Truth anchor: `D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.harmonicStrength`
- Truth anchor: `D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.minimumSize`
- Truth anchor: `D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.momentSum`
- Truth anchor: `D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.result`
