# Paley-Wiener L-Gauge

## Abstract

Equality of tempered distributions on tests supported in an open window defines the Paley-Wiener gauge equivalence relation.

**Definition 1.1 (Paley-Wiener gauge on tempered distributions).**

$$\forall L: \operatorname{Real}\left(\right), W1, W2: \operatorname{TemperedDistribution}\left(\operatorname{Real}\left(\right), \operatorname{Complex}\left(\right)\right),\\{}\operatorname{PaleyWienerGauge}\left(L, W1, W2\right) \Leftrightarrow \forall phi: \operatorname{SchwartzMap}\left(\operatorname{Real}\left(\right), \operatorname{Complex}\left(\right)\right), \operatorname{tsupport}\left(phi\right) \subseteq \operatorname{Ioo}\left(-\left(2 \cdot L\right), 2 \cdot L\right) \Rightarrow W1\left(phi\right) = W2\left(phi\right).$$

*Formalization.* `D5/S3/Weil/TestFunctions/PaleyWienerGauge.paleyWienerGauge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The restriction of a tempered distribution is represented by all of its values on Schwartz tests whose topological support lies in the open interval (-2L, 2L). The gauge is the Setoid kernel of this restriction map, so reflexivity, symmetry, and transitivity are inherited from equality.

The Lean module also proves that the relation is genuinely coarser than equality: the zero distribution and the Dirac distribution at the excluded endpoint 2L have the same window restriction but are distinct.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/PaleyWienerGauge.paleyWienerGauge`
