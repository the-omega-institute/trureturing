# LabeledComplementClassification

## Abstract

Finite binary Riordan complements: LabeledComplementClassification

**Theorem 1.1 (riordan adj lower).**

$$\forall (n: \operatorname{Nat}), \forall (g: (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), \forall (f: (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), \forall (i: \operatorname{Fin}\left(n\right)), \forall (j: \operatorname{Fin}\left(n\right)), (j.\operatorname{val} < i.\operatorname{val}) \Rightarrow ((((\operatorname{riordanGraph}\left(n\right)\left(g\right)\left(f\right))).\operatorname{Adj}\left(i\right)\left(j\right)) \Leftrightarrow (\operatorname{PowerSeries}.\operatorname{coeff}\left((i.\operatorname{val} - 1)\right)\left((g \cdot f^{j.\operatorname{val}})\right) = 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.riordan_adj_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

For a strictly lower-triangular entry, adjacency is exactly the specified coefficient being one.

**Theorem 1.2 (graph eq iff columns).**

$$\forall (N: \operatorname{Nat}), \forall (g: (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), \forall (f: (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), \forall (g': (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), \forall (f': (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), (\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(f\right) = 0) \Rightarrow ((\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(f'\right) = 0) \Rightarrow ((\operatorname{riordanGraph}\left((N + 2)\right)\left(g\right)\left(f\right) = \operatorname{riordanGraph}\left((N + 2)\right)\left(g'\right)\left(f'\right)) \Leftrightarrow (\forall (j: \operatorname{Nat}), (j < N + 1) \Rightarrow (\operatorname{truncateMap}\left(N\right)\left((g \cdot f^{j})\right) = \operatorname{truncateMap}\left(N\right)\left((g' \cdot f'^{j})\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.graph_eq_iff_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

Fixed-label graphs agree exactly when their finite quotient columns agree.

**Definition 1.3 (Oriented).**

$$\forall (N: \operatorname{Nat}), \operatorname{Oriented}\left(N\right) = \{G: \operatorname{SimpleGraph}\left((\operatorname{Fin}\left((N + 2)\right))\right) \mid (\operatorname{IsLabeledRiordan}\left(G\right)) \land ((\operatorname{IsLabeledRiordan}\left(G^{\operatorname{c}}\right)) \land (G.\operatorname{Adj}\left(\langle1\rangle\right)\left(0\right)))\}$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.Oriented` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

Select the complement-compatible graphs containing the edge between vertices zero and one.

**Definition 1.4 (UnitParameters).**

$$\forall (N: \operatorname{Nat}), \operatorname{UnitParameters}\left(N\right) = \{p: (\operatorname{AdjoinRoot}\left(((\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial}\left((\operatorname{ZMod}\left(2\right))\right))^{(N + 1)})\right)) \times (\operatorname{AdjoinRoot}\left(((\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial}\left((\operatorname{ZMod}\left(2\right))\right))^{(N + 1)})\right)) \mid (\operatorname{PowerSeries}.\operatorname{constantCoeff}\left((\operatorname{canonicalSeries}\left(N\right)\left(p.1\right))\right) = 1) \land ((\operatorname{PowerSeries}.\operatorname{constantCoeff}\left((\operatorname{canonicalSeries}\left(N\right)\left(p.2\right))\right) = 0) \land (\operatorname{IsLabeledRiordan}\left((\operatorname{riordanGraph}\left((N + 2)\right)\left((\operatorname{canonicalSeries}\left(N\right)\left(p.1\right))\right)\left((\operatorname{canonicalSeries}\left(N\right)\left(p.2\right))\right))^{\operatorname{c}}\right)))\}$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.UnitParameters` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

The first quotient parameter has constant coefficient one, the second has constant coefficient zero, and their graph has a Riordan complement.

**Definition 1.5 (unitParametersToGraph).**

$$\forall (N: \operatorname{Nat}), \forall (p: \operatorname{UnitParameters}\left(N\right)), ((\operatorname{unitParametersToGraph}\left(N\right)\left(p\right))).\operatorname{val} = \operatorname{riordanGraph}\left((N + 2)\right)\left((\operatorname{canonicalSeries}\left(N\right)\left(p.\operatorname{val}.1\right))\right)\left((\operatorname{canonicalSeries}\left(N\right)\left(p.\operatorname{val}.2\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.unitParametersToGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

The representative series of a parameter pair determine its oriented graph. Proof arguments of the subtype constructor are omitted.

**Theorem 1.6 (unitParametersToGraph injective).**

$$\forall (N: \operatorname{Nat}), \operatorname{Function}.\operatorname{Injective}\left((\operatorname{unitParametersToGraph}\left(N\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.unitParametersToGraph_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

An oriented graph determines its finite unit-side parameters uniquely.

**Theorem 1.7 (canonical constant truncateMap).**

$$\forall (N: \operatorname{Nat}), \forall (f: (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), \operatorname{PowerSeries}.\operatorname{constantCoeff}\left((\operatorname{canonicalSeries}\left(N\right)\left((\operatorname{truncateMap}\left(N\right)\left(f\right))\right))\right) = \operatorname{PowerSeries}.\operatorname{constantCoeff}\left(f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.canonical_constant_truncateMap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

Truncating a representative preserves the constant coefficient.

**Theorem 1.8 (canonicalSeries zero).**

$$\forall (N: \operatorname{Nat}), \operatorname{canonicalSeries}\left(N\right)\left(0\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.canonicalSeries_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

The representative series of zero is zero.

**Theorem 1.9 (canonicalGraph eq).**

$$\forall (N: \operatorname{Nat}), \forall (g: (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), \forall (f: (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), (\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(f\right) = 0) \Rightarrow (\operatorname{riordanGraph}\left((N + 2)\right)\left((\operatorname{canonicalSeries}\left(N\right)\left((\operatorname{truncateMap}\left(N\right)\left(g\right))\right))\right)\left((\operatorname{canonicalSeries}\left(N\right)\left((\operatorname{truncateMap}\left(N\right)\left(f\right))\right))\right) = \operatorname{riordanGraph}\left((N + 2)\right)\left(g\right)\left(f\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.canonicalGraph_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

Replacing both parameters by their representative series preserves the fixed-label graph.

**Theorem 1.10 (unitParametersToGraph surjective).**

$$\forall (N: \operatorname{Nat}), \operatorname{Function}.\operatorname{Surjective}\left((\operatorname{unitParametersToGraph}\left(N\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.unitParametersToGraph_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

Every oriented complement-compatible graph has a finite unit-side parameter pair.

**Theorem 1.11 (graph complement criterion).**

$$\forall (N: \operatorname{Nat}), \forall (g: \operatorname{Units}\left((\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))\right)), \forall (f: (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), (\operatorname{PowerSeries}.\operatorname{constantCoeff}\left((g : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)))\right) = 1) \Rightarrow ((\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(f\right) = 0) \Rightarrow ((\operatorname{IsLabeledRiordan}\left((\operatorname{riordanGraph}\left((N + 2)\right)\left((g : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)))\right)\left(f\right))^{\operatorname{c}}\right)) \Leftrightarrow (\exists (delta: (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), (\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(delta\right) = 0) \land ((\operatorname{truncateMap}\left(N\right)\left(f\right) = \operatorname{truncateMap}\left(N\right)\left(\operatorname{PowerSeries}.\operatorname{X}\right) + (\operatorname{truncateMap}\left(N\right)\left((\operatorname{allOnes} + (g : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))))\right) \cdot \operatorname{truncateMap}\left(N\right)\left((\operatorname{Units}.\operatorname{val}\left(g^{-1}\right) : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)))\right)) \cdot \operatorname{truncateMap}\left(N\right)\left(delta\right)) \land (\operatorname{truncateMap}\left(N\right)\left(((\operatorname{allOnes} + (g : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)))) \cdot delta^{2})\right) = 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.graph_complement_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

A unit-side graph has a Riordan complement exactly when the finite quotient admits a displacement with zero constant coefficient satisfying the displayed linear and square-annihilator equations.

**Theorem 1.12 (graph complement factor criterion).**

$$\forall (N: \operatorname{Nat}), \forall (k: \operatorname{Nat}), (1 \le k) \Rightarrow ((k < N + 1) \Rightarrow (\forall (g: \operatorname{Units}\left((\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))\right)), \forall (v: \operatorname{Units}\left((\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))\right)), \forall (f: (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), (\operatorname{PowerSeries}.\operatorname{constantCoeff}\left((g : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)))\right) = 1) \Rightarrow ((\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(f\right) = 0) \Rightarrow ((\operatorname{allOnes} + (g : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))) = \operatorname{PowerSeries}.\operatorname{X}^{k} \cdot (v : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)))) \Rightarrow ((\operatorname{IsLabeledRiordan}\left((\operatorname{riordanGraph}\left((N + 2)\right)\left((g : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)))\right)\left(f\right))^{\operatorname{c}}\right)) \Leftrightarrow ((\operatorname{PowerSeries}.\operatorname{X} : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)))^{(k + \operatorname{Nat}.\operatorname{div}\left((N + 1 - k + 1), 2\right))} \mid (f + \operatorname{PowerSeries}.\operatorname{X})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.graph_complement_factor_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

When the complementary first parameter has first nonzero degree k, the second parameter differs from X only in the displayed coefficient tail. Nat.div denotes floor division on natural numbers.

**Theorem 1.13 (first degree factor).**

$$\forall (r: (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), \forall (k: \operatorname{Nat}), (\forall (i: \operatorname{Nat}), (i < k) \Rightarrow (\operatorname{PowerSeries}.\operatorname{coeff}\left(i\right)\left(r\right) = 0)) \Rightarrow ((\operatorname{PowerSeries}.\operatorname{coeff}\left(k\right)\left(r\right) = 1) \Rightarrow (\exists (v: \operatorname{Units}\left((\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))\right)), r = \operatorname{PowerSeries}.\operatorname{X}^{k} \cdot (v : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.first_degree_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

A binary series with first nonzero coefficient at degree k factors as X to the power k times a unit.

**Definition 1.14 (seriesOfVector).**

$$\forall (N: \operatorname{Nat}), \forall (v: \operatorname{Fin}\left((N + 1)\right) \to (\operatorname{ZMod}\left(2\right))), \operatorname{seriesOfVector}\left(N\right)\left(v\right) = \operatorname{canonicalSeries}\left(N\right)\left((((\operatorname{coefficientEquiv}\left(N\right))).\operatorname{symm}\left(v\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.seriesOfVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

Use the inverse coefficient equivalence and the polynomial representative to lift a finite binary vector to a power series.

**Theorem 1.15 (seriesOfVector coeff).**

$$\forall (N: \operatorname{Nat}), \forall (v: \operatorname{Fin}\left((N + 1)\right) \to (\operatorname{ZMod}\left(2\right))), \forall (i: \operatorname{Fin}\left((N + 1)\right)), \operatorname{PowerSeries}.\operatorname{coeff}\left(i.\operatorname{val}\right)\left((\operatorname{seriesOfVector}\left(N\right)\left(v\right))\right) = v\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.seriesOfVector_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

The lifted series recovers every specified finite coefficient.

## References

- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.Oriented`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.UnitParameters`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.canonicalGraph_eq`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.canonicalSeries_zero`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.canonical_constant_truncateMap`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.first_degree_factor`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.graph_complement_criterion`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.graph_complement_factor_criterion`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.graph_eq_iff_columns`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.riordan_adj_lower`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.seriesOfVector`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.seriesOfVector_coeff`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.unitParametersToGraph`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.unitParametersToGraph_injective`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementClassification.unitParametersToGraph_surjective`
- Dependency: [D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra](LabeledComplementAlgebra.md)
