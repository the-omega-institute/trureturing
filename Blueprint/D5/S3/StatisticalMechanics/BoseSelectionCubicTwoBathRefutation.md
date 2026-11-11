# Five Bose-selected modes for two cubic baths

## Abstract

Two cubic product-coupled baths admit an open set with five Bose-selected modes.

**Definition 1.1 (pfaffianVector).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.pfaffianVector`

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.pfaffianVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For any real five by five matrix, the explicit vector of signed four by four principal Pfaffians. The sign convention is the alternating principal-minor convention used in the cubic selection criterion.

**Theorem 1.2 (spectral_three).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.spectral_three`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.spectral_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For every real x, the original signed spectral power at exponent three equals x cubed, including x zero. The equality also holds at zero.

**Theorem 1.3 (asym_skew).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.asym_skew`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.asym_skew` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For every finite dimension and real energy and weight vectors, the cubic asymmetry entry with reversed indices is the negative of the original entry. The weight vectors retain the normalization of asym.

**Theorem 1.4 (pfaffian_kernel).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.pfaffian_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.pfaffian_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For every real skew-symmetric five by five matrix, multiplication by its original signed principal-Pfaffian vector gives zero. The identity supplies the kernel in both the arbitrary-weight and fixed-coordinate-bath constructions.

**Definition 1.5 (The two-bath rate asymmetry).**

$$\forall (d: \mathbb{R}), (\forall (m: \mathbb{N}), (\forall (\varepsilon: (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})), (\forall (F: (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})), (\forall (G: (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})), (\operatorname{D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation.asym}\left(d, \varepsilon, F, G\right) = \lambda (i: \operatorname{Fin}\left(m\right)) \mapsto (\lambda (j: \operatorname{Fin}\left(m\right)) \mapsto ((\operatorname{D5.S3.Analytic.SeriesInequalities.StampachWaclawekExpansionRefutation.spow}\left(d, (\varepsilon\left(j\right)) - (\varepsilon\left(i\right))\right)) \cdot (((\operatorname{D5.S3.Geometry.FiniteCoordinateTruncation.normalize}\left(F, i\right)) \cdot (\operatorname{D5.S3.Geometry.FiniteCoordinateTruncation.normalize}\left(F, j\right))) - ((\operatorname{D5.S3.Geometry.FiniteCoordinateTruncation.normalize}\left(G, i\right)) \cdot (\operatorname{D5.S3.Geometry.FiniteCoordinateTruncation.normalize}\left(G, j\right)))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.asym` (`✓ std3`).

*Citation.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For a real exponent d, an energy vector ε and two real coupling vectors F and G, asym is the matrix whose (i,j)-entry is the odd power law spow applied to εⱼ − εᵢ, multiplied by the difference of the two normalized product couplings. The declaration D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.spow means |x|ᵈ sgn(x), and the declaration D5/S3/Geometry/FiniteCoordinateTruncation.normalize divides a finite vector by the sum of its coordinates. This is the source's two-bath matrix after the positive factor 2π/ℏ is suppressed, as in main.tex lines 1066–1083.

**Definition 1.6 (The Bose-selection condition).**

$$\forall (m: \mathbb{N}), (\forall (a: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{R}\right)), (\forall (s: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right)), (\forall (w: (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})), ((\operatorname{D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation.IsSelected}\left(a, s, w\right)) \Leftrightarrow (\forall (i: \operatorname{Fin}\left(m\right)), (((i \in s) \Rightarrow (((0: \mathbb{R}) < w\left(i\right)) \land (\operatorname{Matrix.mulVec}\left(a, w, i\right) = (0: \mathbb{R})))) \land ((\neg (i \in s)) \Rightarrow ((w\left(i\right) = (0: \mathbb{R})) \land (\operatorname{Matrix.mulVec}\left(a, w, i\right) < (0: \mathbb{R}))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.IsSelected` (`✓ std3`).

*Citation.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

IsSelected a s w says that every index in s has a strictly positive occupation and zero matrix output, while every index outside s has zero occupation and strictly negative matrix output. Here a.mulVec w is the matrix-vector product. The vector w is the source's η. This is the source's MS-problem condition μ = Aη with the selected and unselected sign conditions, main.tex lines 373–381.

**Definition 1.7 (Parameters with at least four selected modes).**

$$\forall (d: \mathbb{R}), (\forall (m: \mathbb{N}), (\operatorname{D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation.violating}\left(d, m\right) = \{(p: \operatorname{Prod}\left((\operatorname{Fin}\left(m\right)) \to (\mathbb{R}), \operatorname{Prod}\left((\operatorname{Fin}\left(m\right)) \to (\mathbb{R}), (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})\right)\right)) | ((\forall (i: \operatorname{Fin}\left(m\right)), ((0: \mathbb{R}) < \operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(p\right)\right)\left(i\right))) \land ((\forall (i: \operatorname{Fin}\left(m\right)), ((0: \mathbb{R}) < \operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(p\right)\right)\left(i\right))) \land (\exists (s: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right)), (\exists (w: (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})), ((\operatorname{D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation.IsSelected}\left(\operatorname{D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation.asym}\left(d, \operatorname{Prod.fst}\left(p\right), \operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(p\right)\right), \operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(p\right)\right)\right), s, w\right)) \land ((4: \mathbb{N}) \le \operatorname{Finset.card}\left(s\right)))))))\}))$$

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.violating` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For d and m, violating d m is the set of triples of m-component real vectors whose two coupling vectors are positive coordinatewise and for which some finite selected set s and occupation vector w satisfy IsSelected for the matrix asym d ε F G and have cardinality at least four. The three components are the energies and the two coupling vectors.

**Definition 1.8 (The generic two-bath bound).**

$$\operatorname{D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation.claim}\left(\right) = (\forall (d: \mathbb{R}), (((0: \mathbb{R}) < d) \Rightarrow (\forall (m: \mathbb{N}), (\operatorname{interior}\left(\operatorname{D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation.violating}\left(d, m\right)\right) = \emptyset))))$$

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.claim` (`✓ std3`).

*Citation.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

The preregistered generic reading of the source's non-ohmic expectation asks that, for every d > 0 and every natural m, the parameter set supporting at least four selected modes have empty interior. It is the two-bath instance of the proposed bound M_S ≤ 2M_B − 1, corresponding to the source's checked family J(ε) proportional to |ε|ᵈ sgn(ε), main.tex lines 1173–1179.

**Theorem 1.9 (An open five-mode counterexample).**

$$\neg (\forall (d: \mathbb{R}), (((0: \mathbb{R}) < d) \Rightarrow (\forall (m: \mathbb{N}), (\operatorname{interior}\left(\operatorname{D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation.violating}\left(d, m\right)\right) = \emptyset))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/schnell-ketzmerick-eckardt-2018-bose-selection-cubic-refutation` (refuted) by `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"schnell-ketzmerick-eckardt-2018-bose-selection-cubic-refutation","declaration_gid":"D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

At d = 3 and m = 5, the referenced odd power law reduces to the cubic map, so asym is skew-symmetric: swapping i and j changes the sign of εⱼ − εᵢ while the product difference is unchanged. For every skew-symmetric 5 by 5 matrix a, the signed Pfaffians of its 4 by 4 principal minors form an explicit vector, and direct expansion gives zero after multiplying a by that vector.

On the positive coupling domain, continuous_normalize supplies continuity of each normalized vector because its coordinate sum is positive. The entries of asym and then every coordinate of the Pfaffian vector are therefore continuous. The finite intersection of the positive Pfaffian-coordinate conditions with the positive coupling domain is an open neighborhood.

The explicit base point ε = (1,2,3,4,5), F = (5,4,4,4,4), and G = (6,6,3,3,3) belongs to that neighborhood: the five Pfaffian coordinates are positive by exact finite calculation. Every point p in the neighborhood has positive coupling coordinates, and the Pfaffian vector is positive and lies in the kernel of asym 3 p.1 p.2.1 p.2.2. Taking s to be the universal five-element finset and w to be that vector satisfies IsSelected; its cardinality is five, so the neighborhood is contained in violating 3 5.

The neighborhood is nonempty because it contains the base point, and its inclusion in violating 3 5 makes the interior of violating 3 5 nonempty. If claim held, its instance at d = 3 and m = 5 would identify that interior with the empty set, contradicting the exhibited point. Hence the generic two-bath bound is false.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.IsSelected`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.asym`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.asym_skew`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.pfaffianVector`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.pfaffian_kernel`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.result`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.spectral_three`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.violating`
- Dependency: [D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation](../Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.md)
- Dependency: [D5/S3/Geometry/FiniteCoordinateTruncation](../Geometry/FiniteCoordinateTruncation.md)
