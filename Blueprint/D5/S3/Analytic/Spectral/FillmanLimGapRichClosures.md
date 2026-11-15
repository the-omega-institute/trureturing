# FillmanLimGapRichClosures

## Abstract

Gap-rich alphabets fail closure under union, sum, and ordered product.

**Definition 1.1 (Question 2: the three universal assertions).**

$$claim = ((\forall k: Nat, (0 < k) \Rightarrow (\forall Xone: Set\left(EuclideanSpace\left(Real, Fin\left(k\right)\right)\right), \forall Xtwo: Set\left(EuclideanSpace\left(Real, Fin\left(k\right)\right)\right), (GapRich\left(Xone\right)) \Rightarrow ((GapRich\left(Xtwo\right)) \Rightarrow (GapRich\left(Xone \cup Xtwo\right))))) \lor ((\forall k: Nat, (0 < k) \Rightarrow (\forall Xone: Set\left(EuclideanSpace\left(Real, Fin\left(k\right)\right)\right), \forall Xtwo: Set\left(EuclideanSpace\left(Real, Fin\left(k\right)\right)\right), (GapRich\left(Xone\right)) \Rightarrow ((GapRich\left(Xtwo\right)) \Rightarrow (GapRich\left((Xone)+(Xtwo)\right))))) \lor (\forall k: Nat, \forall ell: Nat, (0 < k) \Rightarrow ((0 < ell) \Rightarrow (\forall Xone: Set\left(EuclideanSpace\left(Real, Fin\left(k\right)\right)\right), \forall Xthree: Set\left(EuclideanSpace\left(Real, Fin\left(ell\right)\right)\right), (GapRich\left(Xone\right)) \Rightarrow ((GapRich\left(Xthree\right)) \Rightarrow (GapRich\left(cartesianProduct\left(Xone, Xthree\right)\right))))))))$$

*Formalization.* `D5/S3/Analytic/Spectral/FillmanLimGapRichClosures.claim` (`✓ std3`).

*Citation.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Page 20, Section 6, Question 2: “If X₁, X₂ ⊆ ℝᵏ and X₃ ⊆ ℝˡ are gap-rich, are any of the following sets X₁ ∪ X₂, X₁ + X₂, and X₁ × X₃ gap-rich?” Positive dimensions are natural numbers greater than zero. The union and sum clauses quantify over two subsets of the same Euclidean space. The Cartesian clause uses ordered coordinate concatenation. The three assertions are alternatives, represented by their disjunction.

**Theorem 1.2 (All three closure assertions fail).**

$$\neg ((\forall k: Nat, (0 < k) \Rightarrow (\forall Xone: Set\left(EuclideanSpace\left(Real, Fin\left(k\right)\right)\right), \forall Xtwo: Set\left(EuclideanSpace\left(Real, Fin\left(k\right)\right)\right), (GapRich\left(Xone\right)) \Rightarrow ((GapRich\left(Xtwo\right)) \Rightarrow (GapRich\left(Xone \cup Xtwo\right))))) \lor ((\forall k: Nat, (0 < k) \Rightarrow (\forall Xone: Set\left(EuclideanSpace\left(Real, Fin\left(k\right)\right)\right), \forall Xtwo: Set\left(EuclideanSpace\left(Real, Fin\left(k\right)\right)\right), (GapRich\left(Xone\right)) \Rightarrow ((GapRich\left(Xtwo\right)) \Rightarrow (GapRich\left((Xone)+(Xtwo)\right))))) \lor (\forall k: Nat, \forall ell: Nat, (0 < k) \Rightarrow ((0 < ell) \Rightarrow (\forall Xone: Set\left(EuclideanSpace\left(Real, Fin\left(k\right)\right)\right), \forall Xthree: Set\left(EuclideanSpace\left(Real, Fin\left(ell\right)\right)\right), (GapRich\left(Xone\right)) \Rightarrow ((GapRich\left(Xthree\right)) \Rightarrow (GapRich\left(cartesianProduct\left(Xone, Xthree\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Spectral/FillmanLimGapRichClosures.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-fl2609q2` (refuted) by `D5/S3/Analytic/Spectral/FillmanLimGapRichClosures.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-fl2609q2","declaration_gid":"D5/S3/Analytic/Spectral/FillmanLimGapRichClosures.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

The input alphabets have empty exceptional set. Small variations inside a vertical component yield a hyperbolic relative transfer and then a hyperbolic positive word. Locally isolated output components force transfers minus J, minus the identity, or alternating H and minus its adjugate. Their obstruction energies form a nondiscrete set. The witnesses use dimensions three for sums and five for the two union or product factors.

## References

- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichClosures.claim`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimGapRichClosures.result`
- Dependency: [D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy](../ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.md)
- Dependency: [D5/S3/Analytic/Spectral/FillmanLimGapRichWords](FillmanLimGapRichWords.md)
- Dependency: [D5/S3/Analytic/Spectral/FillmanLimPositiveSemigroup](FillmanLimPositiveSemigroup.md)
