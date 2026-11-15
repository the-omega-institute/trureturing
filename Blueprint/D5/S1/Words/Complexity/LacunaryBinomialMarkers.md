# Lacunary Binomial Markers

## Abstract

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.1 (profile eq iff).**

$$\forall \{\operatorname{A} : \operatorname{Type}\} [\operatorname{Fintype} \operatorname{A}] [\operatorname{DecidableEq} \operatorname{A}] \{\operatorname{n} \operatorname{k} : \mathbb{N}\} \{\operatorname{u} \operatorname{v} : \operatorname{Fin} \operatorname{n} \to \operatorname{A}\}, \operatorname{binomialProfile} \operatorname{k} \operatorname{u} = \operatorname{binomialProfile} \operatorname{k} \operatorname{v} \iff \forall (\operatorname{pattern} : \operatorname{List} \operatorname{A}), \operatorname{pattern}.\operatorname{length} \leq \operatorname{k} \to \operatorname{scatteredCount} \operatorname{pattern} (\operatorname{List}.\operatorname{ofFn} \operatorname{u}) = \operatorname{scatteredCount} \operatorname{pattern} (\operatorname{List}.\operatorname{ofFn} \operatorname{v})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.profile_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.2 (profile eq mono).**

$$\forall \{\operatorname{A} : \operatorname{Type}\} [\operatorname{Fintype} \operatorname{A}] [\operatorname{DecidableEq} \operatorname{A}] \{\operatorname{n} \operatorname{j} \operatorname{k} : \mathbb{N}\}, \operatorname{j} \leq \operatorname{k} \to \forall \{\operatorname{u} \operatorname{v} : \operatorname{Fin} \operatorname{n} \to \operatorname{A}\}, \operatorname{binomialProfile} \operatorname{k} \operatorname{u} = \operatorname{binomialProfile} \operatorname{k} \operatorname{v} \to \operatorname{binomialProfile} \operatorname{j} \operatorname{u} = \operatorname{binomialProfile} \operatorname{j} \operatorname{v}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.profile_eq_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.3 (complexity eq factor iff).**

$$\forall \{\operatorname{A} : \operatorname{Type}\} [\operatorname{Fintype} \operatorname{A}] [\operatorname{DecidableEq} \operatorname{A}] (\operatorname{word} : \mathbb{N} \to \operatorname{A}) (\operatorname{k} \operatorname{n} : \mathbb{N}), \operatorname{binomialComplexity} \operatorname{word} \operatorname{k} \operatorname{n} = (\operatorname{wordFactorSet} \operatorname{word} \operatorname{n}).\operatorname{card} \iff \operatorname{Set}.\operatorname{InjOn} (\operatorname{binomialProfile} \operatorname{k}) (\operatorname{CoeTC}.\operatorname{coe} (\operatorname{wordFactorSet} \operatorname{word} \operatorname{n}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.complexity_eq_factor_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.4 (complexity lt of split).**

$$\forall \{\operatorname{A} : \operatorname{Type}\} [\operatorname{Fintype} \operatorname{A}] [\operatorname{DecidableEq} \operatorname{A}] (\operatorname{word} : \mathbb{N} \to \operatorname{A}) \{\operatorname{j} \operatorname{k} \operatorname{n} : \mathbb{N}\}, \operatorname{j} \leq \operatorname{k} \to \forall \{\operatorname{u} \operatorname{v} : \operatorname{Fin} \operatorname{n} \to \operatorname{A}\}, \operatorname{u} \in \operatorname{wordFactorSet} \operatorname{word} \operatorname{n} \to \operatorname{v} \in \operatorname{wordFactorSet} \operatorname{word} \operatorname{n} \to \operatorname{binomialProfile} \operatorname{j} \operatorname{u} = \operatorname{binomialProfile} \operatorname{j} \operatorname{v} \to \operatorname{binomialProfile} \operatorname{k} \operatorname{u} \neq \operatorname{binomialProfile} \operatorname{k} \operatorname{v} \to \operatorname{binomialComplexity} \operatorname{word} \operatorname{j} \operatorname{n} < \operatorname{binomialComplexity} \operatorname{word} \operatorname{k} \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.complexity_lt_of_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.5 (profile eq map).**

$$\forall \{\operatorname{A} : \operatorname{Type}\} \{\operatorname{B} : \operatorname{Type}\} [\operatorname{Fintype} \operatorname{A}] [\operatorname{DecidableEq} \operatorname{A}] [\operatorname{Fintype} \operatorname{B}] [\operatorname{DecidableEq} \operatorname{B}] (\operatorname{g} : \operatorname{A} \to \operatorname{B}) \{\operatorname{n} \operatorname{k} : \mathbb{N}\} \{\operatorname{u} \operatorname{v} : \operatorname{Fin} \operatorname{n} \to \operatorname{A}\}, \operatorname{binomialProfile} \operatorname{k} \operatorname{u} = \operatorname{binomialProfile} \operatorname{k} \operatorname{v} \to \operatorname{binomialProfile} \operatorname{k} (\operatorname{g} \circ \operatorname{u}) = \operatorname{binomialProfile} \operatorname{k} (\operatorname{g} \circ \operatorname{v})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.profile_eq_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.6 (complexity map le).**

$$\forall \{\operatorname{A} : \operatorname{Type}\} \{\operatorname{B} : \operatorname{Type}\} [\operatorname{Fintype} \operatorname{A}] [\operatorname{DecidableEq} \operatorname{A}] [\operatorname{Fintype} \operatorname{B}] [\operatorname{DecidableEq} \operatorname{B}] (\operatorname{g} : \operatorname{A} \to \operatorname{B}) (\operatorname{word} : \mathbb{N} \to \operatorname{A}) (\operatorname{k} \operatorname{n} : \mathbb{N}), \operatorname{binomialComplexity} (\operatorname{g} \circ \operatorname{word}) \operatorname{k} \operatorname{n} \leq \operatorname{binomialComplexity} \operatorname{word} \operatorname{k} \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.complexity_map_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.7 (split of complexity lt).**

$$\forall \{\operatorname{A} : \operatorname{Type}\} [\operatorname{Fintype} \operatorname{A}] [\operatorname{DecidableEq} \operatorname{A}] (\operatorname{word} : \mathbb{N} \to \operatorname{A}) \{\operatorname{j} \operatorname{k} \operatorname{n} : \mathbb{N}\}, \operatorname{j} \leq \operatorname{k} \to \operatorname{binomialComplexity} \operatorname{word} \operatorname{j} \operatorname{n} < \operatorname{binomialComplexity} \operatorname{word} \operatorname{k} \operatorname{n} \to \exists \operatorname{u} \in \operatorname{wordFactorSet} \operatorname{word} \operatorname{n}, \exists \operatorname{v} \in \operatorname{wordFactorSet} \operatorname{word} \operatorname{n}, \operatorname{binomialProfile} \operatorname{j} \operatorname{u} = \operatorname{binomialProfile} \operatorname{j} \operatorname{v} \land \operatorname{binomialProfile} \operatorname{k} \operatorname{u} \neq \operatorname{binomialProfile} \operatorname{k} \operatorname{v}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.split_of_complexity_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.8 (product profile injective).**

$$\forall \{\operatorname{A} : \operatorname{Type}\} \{\operatorname{B} : \operatorname{Type}\} [\operatorname{Fintype} \operatorname{A}] [\operatorname{DecidableEq} \operatorname{A}] [\operatorname{Fintype} \operatorname{B}] [\operatorname{DecidableEq} \operatorname{B}] (\operatorname{x} : \mathbb{N} \to \operatorname{A}) (\operatorname{y} : \mathbb{N} \to \operatorname{B}) (\operatorname{k} \operatorname{n} : \mathbb{N}), \operatorname{Set}.\operatorname{InjOn} (\operatorname{binomialProfile} \operatorname{k}) (\operatorname{CoeTC}.\operatorname{coe} (\operatorname{wordFactorSet} \operatorname{x} \operatorname{n})) \to \operatorname{Set}.\operatorname{InjOn} (\operatorname{binomialProfile} \operatorname{k}) (\operatorname{CoeTC}.\operatorname{coe} (\operatorname{wordFactorSet} \operatorname{y} \operatorname{n})) \to \operatorname{Set}.\operatorname{InjOn} (\operatorname{binomialProfile} \operatorname{k}) (\operatorname{CoeTC}.\operatorname{coe} (\operatorname{wordFactorSet} (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{x} \operatorname{i}, \operatorname{y} \operatorname{i})) \operatorname{n}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.product_profile_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.9 (strict lifts through constant tag).**

$$\forall \{\operatorname{A} : \operatorname{Type}\} \{\operatorname{B} : \operatorname{Type}\} [\operatorname{Fintype} \operatorname{A}] [\operatorname{DecidableEq} \operatorname{A}] [\operatorname{Fintype} \operatorname{B}] [\operatorname{DecidableEq} \operatorname{B}] (\operatorname{x} : \mathbb{N} \to \operatorname{A}) (\operatorname{y} : \mathbb{N} \to \operatorname{B}) (\operatorname{tag} : \operatorname{B}) \{\operatorname{j} \operatorname{k} \operatorname{n} : \mathbb{N}\}, \operatorname{j} \leq \operatorname{k} \to (\forall \operatorname{u} \in \operatorname{wordFactorSet} \operatorname{x} \operatorname{n}, (\operatorname{fun} \operatorname{r} \mapsto (\operatorname{u} \operatorname{r}, \operatorname{tag})) \in \operatorname{wordFactorSet} (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{x} \operatorname{i}, \operatorname{y} \operatorname{i})) \operatorname{n}) \to \operatorname{binomialComplexity} \operatorname{x} \operatorname{j} \operatorname{n} < \operatorname{binomialComplexity} \operatorname{x} \operatorname{k} \operatorname{n} \to \operatorname{binomialComplexity} (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{x} \operatorname{i}, \operatorname{y} \operatorname{i})) \operatorname{j} \operatorname{n} < \operatorname{binomialComplexity} (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{x} \operatorname{i}, \operatorname{y} \operatorname{i})) \operatorname{k} \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.strict_lifts_through_constant_tag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.10 (constant tag factors of recurrence).**

$$\forall \{\operatorname{A} : \operatorname{Type}\} [\operatorname{Fintype} \operatorname{A}] [\operatorname{DecidableEq} \operatorname{A}] (\operatorname{x} : \mathbb{N} \to \operatorname{A}) (\operatorname{y} : \mathbb{N} \to \operatorname{Bool}), (\forall (\operatorname{n} : \mathbb{N}), \forall \operatorname{u} \in \operatorname{wordFactorSet} \operatorname{x} \operatorname{n}, \exists \operatorname{R}, \forall (\operatorname{s} : \mathbb{N}), \exists \operatorname{t}, \operatorname{s} \leq \operatorname{t} \land \operatorname{t} + \operatorname{n} \leq \operatorname{s} + \operatorname{R} \land \operatorname{u} = \operatorname{wordFactor} \operatorname{x} \operatorname{n} \operatorname{t}) \to (\forall (\operatorname{R} : \mathbb{N}), \exists \operatorname{s}, \forall (\operatorname{q} : \mathbb{N}), \operatorname{s} \leq \operatorname{q} \to \operatorname{q} < \operatorname{s} + \operatorname{R} \to \operatorname{y} \operatorname{q} = \operatorname{false}) \to \forall (\operatorname{n} : \mathbb{N}), \forall \operatorname{u} \in \operatorname{wordFactorSet} \operatorname{x} \operatorname{n}, (\operatorname{fun} \operatorname{r} \mapsto (\operatorname{u} \operatorname{r}, \operatorname{false})) \in \operatorname{wordFactorSet} (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{x} \operatorname{i}, \operatorname{y} \operatorname{i})) \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.constant_tag_factors_of_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.11 (complexity map eq of leftInverse).**

$$\forall \{\operatorname{A} : \operatorname{Type}\} \{\operatorname{B} : \operatorname{Type}\} [\operatorname{Fintype} \operatorname{A}] [\operatorname{DecidableEq} \operatorname{A}] [\operatorname{Fintype} \operatorname{B}] [\operatorname{DecidableEq} \operatorname{B}] (\operatorname{g} : \operatorname{A} \to \operatorname{B}) (\operatorname{r} : \operatorname{B} \to \operatorname{A}), \operatorname{Function}.\operatorname{LeftInverse} \operatorname{r} \operatorname{g} \to \forall (\operatorname{word} : \mathbb{N} \to \operatorname{A}) (\operatorname{k} \operatorname{n} : \mathbb{N}), \operatorname{binomialComplexity} (\operatorname{g} \circ \operatorname{word}) \operatorname{k} \operatorname{n} = \operatorname{binomialComplexity} \operatorname{word} \operatorname{k} \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.complexity_map_eq_of_leftInverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.12 (factor card map eq of injective).**

$$\forall \{\operatorname{A} : \operatorname{Type}\} \{\operatorname{B} : \operatorname{Type}\} [\operatorname{Fintype} \operatorname{A}] [\operatorname{DecidableEq} \operatorname{A}] [\operatorname{Fintype} \operatorname{B}] [\operatorname{DecidableEq} \operatorname{B}] (\operatorname{g} : \operatorname{A} \to \operatorname{B}), \operatorname{Function}.\operatorname{Injective} \operatorname{g} \to \forall (\operatorname{word} : \mathbb{N} \to \operatorname{A}) (\operatorname{n} : \mathbb{N}), (\operatorname{wordFactorSet} (\operatorname{g} \circ \operatorname{word}) \operatorname{n}).\operatorname{card} = (\operatorname{wordFactorSet} \operatorname{word} \operatorname{n}).\operatorname{card}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.factor_card_map_eq_of_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Definition 1.13 (pairCode).**

$$(\operatorname{pairCode} (\operatorname{false}, \operatorname{false}) = 0) \land (\operatorname{pairCode} (\operatorname{false}, \operatorname{true}) = 1) \land (\operatorname{pairCode} (\operatorname{true}, \operatorname{false}) = 2) \land (\operatorname{pairCode} (\operatorname{true}, \operatorname{true}) = 3)$$

*Formalization.* `D5/S1/Words/Complexity/LacunaryBinomialMarkers.pairCode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines pairCode.

**Definition 1.14 (pairDecode).**

$$\forall (\operatorname{a} : \operatorname{Fin} 4), \operatorname{pairDecode} \operatorname{a} = (\operatorname{decide} (2 \leq \operatorname{a}.\operatorname{val}), \operatorname{decide} (\operatorname{a}.\operatorname{val} \operatorname{mod} 2 = 1))$$

*Formalization.* `D5/S1/Words/Complexity/LacunaryBinomialMarkers.pairDecode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines pairDecode. The operator / denotes natural-number floor division; mod denotes Nat.mod.

**Theorem 1.15 (pairCode leftInverse).**

$$\operatorname{Function}.\operatorname{LeftInverse} \operatorname{pairDecode} \operatorname{pairCode}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.pairCode_leftInverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Definition 1.16 (boolCode).**

$$(\operatorname{boolCode} \operatorname{false} = 0) \land (\operatorname{boolCode} \operatorname{true} = 1)$$

*Formalization.* `D5/S1/Words/Complexity/LacunaryBinomialMarkers.boolCode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines boolCode.

**Definition 1.17 (boolDecode).**

$$\forall (\operatorname{a} : \operatorname{Fin} 4), \operatorname{boolDecode} \operatorname{a} = \operatorname{decide} (\operatorname{a}.\operatorname{val} = 1)$$

*Formalization.* `D5/S1/Words/Complexity/LacunaryBinomialMarkers.boolDecode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines boolDecode.

**Theorem 1.18 (boolCode leftInverse).**

$$\operatorname{Function}.\operatorname{LeftInverse} \operatorname{boolDecode} \operatorname{boolCode}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.boolCode_leftInverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.19 (singleton counts total).**

$$\forall (\operatorname{u} : \operatorname{List} \operatorname{Bool}), \operatorname{scatteredCount} [\operatorname{false}] \operatorname{u} + \operatorname{scatteredCount} [\operatorname{true}] \operatorname{u} = \operatorname{u}.\operatorname{length}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.singleton_counts_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.20 (profile one eq of true count).**

$$\forall \{\operatorname{n} : \mathbb{N}\} \{\operatorname{u} \operatorname{v} : \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}\}, \operatorname{scatteredCount} [\operatorname{true}] (\operatorname{List}.\operatorname{ofFn} \operatorname{u}) = \operatorname{scatteredCount} [\operatorname{true}] (\operatorname{List}.\operatorname{ofFn} \operatorname{v}) \to \operatorname{binomialProfile} 1 \operatorname{u} = \operatorname{binomialProfile} 1 \operatorname{v}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.profile_one_eq_of_true_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Definition 1.21 (Lacunary).**

$$\forall (\operatorname{p} : \operatorname{Nat} \to \operatorname{Nat}), \operatorname{Lacunary} \operatorname{p} \iff (0 < \operatorname{p} 0 \land \forall (\operatorname{i} : \operatorname{Nat}), 3 * \operatorname{p} \operatorname{i} \leq \operatorname{p} (\operatorname{i} + 1))$$

*Formalization.* `D5/S1/Words/Complexity/LacunaryBinomialMarkers.Lacunary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines Lacunary.

**Definition 1.22 (marker).**

$$\forall (\operatorname{n} : \operatorname{Nat}), \operatorname{marker} \operatorname{n} = \operatorname{Nat}.\operatorname{fib} (3 * \operatorname{n} + 2)$$

*Formalization.* `D5/S1/Words/Complexity/LacunaryBinomialMarkers.marker` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines marker.

**Theorem 1.23 (marker lacunary).**

$$\operatorname{Lacunary} \operatorname{marker}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.marker_lacunary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.24 (scaled lacunary).**

$$\forall \{\operatorname{p} : \mathbb{N} \to \mathbb{N}\}, \operatorname{Lacunary} \operatorname{p} \to \forall (\operatorname{q} : \mathbb{N}), 0 < \operatorname{q} \to \operatorname{Lacunary} \operatorname{fun} \operatorname{i} \mapsto \operatorname{q} * \operatorname{p} \operatorname{i}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.scaled_lacunary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Definition 1.25 (markerWord).**

$$\forall (\operatorname{p} : \operatorname{Nat} \to \operatorname{Nat}) (\operatorname{n} : \operatorname{Nat}), \operatorname{markerWord} \operatorname{p} \operatorname{n} = (\operatorname{if} \exists (\operatorname{i} : \operatorname{Nat}), \operatorname{p} \operatorname{i} = \operatorname{n} \operatorname{then} \operatorname{true} \operatorname{else} \operatorname{false})$$

*Formalization.* `D5/S1/Words/Complexity/LacunaryBinomialMarkers.markerWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines markerWord.

**Theorem 1.26 (markerWord eq true).**

$$\forall (\operatorname{p} : \operatorname{Nat} \to \operatorname{Nat}) (\operatorname{n} : \operatorname{Nat}), \operatorname{markerWord} \operatorname{p} \operatorname{n} = \operatorname{true} \iff \exists (\operatorname{i} : \operatorname{Nat}), \operatorname{p} \operatorname{i} = \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.markerWord_eq_true` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.27 (marker profile two injective).**

$$\forall \{\operatorname{p} : \mathbb{N} \to \mathbb{N}\}, \operatorname{Lacunary} \operatorname{p} \to \forall (\operatorname{n} : \mathbb{N}), \operatorname{Set}.\operatorname{InjOn} (\operatorname{binomialProfile} 2) (\operatorname{CoeTC}.\operatorname{coe} (\operatorname{wordFactorSet} (\operatorname{markerWord} \operatorname{p}) \operatorname{n}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.marker_profile_two_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.28 (marker complexity two).**

$$\forall \{\operatorname{p} : \mathbb{N} \to \mathbb{N}\}, \operatorname{Lacunary} \operatorname{p} \to \forall (\operatorname{n} : \mathbb{N}), \operatorname{binomialComplexity} (\operatorname{markerWord} \operatorname{p}) 2 \operatorname{n} = (\operatorname{wordFactorSet} (\operatorname{markerWord} \operatorname{p}) \operatorname{n}).\operatorname{card}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.marker_complexity_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.29 (marker unbounded abelian).**

$$\forall \{\operatorname{p} : \mathbb{N} \to \mathbb{N}\}, \operatorname{Lacunary} \operatorname{p} \to \forall (\operatorname{bound} : \mathbb{N}), \exists \operatorname{n}, \operatorname{bound} < \operatorname{binomialComplexity} (\operatorname{markerWord} \operatorname{p}) 1 \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.marker_unbounded_abelian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.30 (marker zero intervals).**

$$\forall \{\operatorname{p} : \mathbb{N} \to \mathbb{N}\}, \operatorname{Lacunary} \operatorname{p} \to \forall (\operatorname{R} : \mathbb{N}), \exists \operatorname{s}, \forall (\operatorname{q} : \mathbb{N}), \operatorname{s} \leq \operatorname{q} \to \operatorname{q} < \operatorname{s} + \operatorname{R} \to \operatorname{markerWord} \operatorname{p} \operatorname{q} = \operatorname{false}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.marker_zero_intervals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.31 (marker strict one two).**

$$\forall \{\operatorname{p} : \mathbb{N} \to \mathbb{N}\}, \operatorname{Lacunary} \operatorname{p} \to \forall (\operatorname{n} : \mathbb{N}), 2 \leq \operatorname{n} \to \operatorname{binomialComplexity} (\operatorname{markerWord} \operatorname{p}) 1 \operatorname{n} < \operatorname{binomialComplexity} (\operatorname{markerWord} \operatorname{p}) 2 \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.marker_strict_one_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.32 (golden true count).**

$$\forall (\operatorname{n} \operatorname{i} : \mathbb{N}), \operatorname{scatteredCount} [\operatorname{true}] (\operatorname{List}.\operatorname{ofFn} (\operatorname{wordFactor} \operatorname{goldenWord} \operatorname{n} \operatorname{i})) = \operatorname{goldenWindowTrueCount} \operatorname{i} \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.golden_true_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.33 (golden pair count).**

$$\forall (\operatorname{n} \operatorname{i} : \mathbb{N}), \operatorname{scatteredCount} [\operatorname{true}, \operatorname{false}] (\operatorname{List}.\operatorname{ofFn} (\operatorname{wordFactor} \operatorname{goldenWord} \operatorname{n} \operatorname{i})) = \operatorname{goldenTrueFalseCount} \operatorname{i} \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.golden_pair_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.34 (golden profile two injective).**

$$\forall (\operatorname{n} : \mathbb{N}), \operatorname{Set}.\operatorname{InjOn} (\operatorname{binomialProfile} 2) (\operatorname{CoeTC}.\operatorname{coe} (\operatorname{wordFactorSet} \operatorname{goldenWord} \operatorname{n}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.golden_profile_two_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

**Theorem 1.35 (golden abelian bound).**

$$\forall (\operatorname{n} : \mathbb{N}), \operatorname{binomialComplexity} \operatorname{goldenWord} 1 \operatorname{n} \leq 3$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LacunaryBinomialMarkers.golden_abelian_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Scattered subword counts separate factors whose marked positions grow by a factor of at least three. Projection and coding preserve the necessary binomial profiles.

## References

- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.Lacunary`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.boolCode`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.boolCode_leftInverse`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.boolDecode`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.complexity_eq_factor_iff`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.complexity_lt_of_split`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.complexity_map_eq_of_leftInverse`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.complexity_map_le`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.constant_tag_factors_of_recurrence`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.factor_card_map_eq_of_injective`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.golden_abelian_bound`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.golden_pair_count`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.golden_profile_two_injective`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.golden_true_count`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.marker`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.markerWord`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.markerWord_eq_true`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.marker_complexity_two`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.marker_lacunary`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.marker_profile_two_injective`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.marker_strict_one_two`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.marker_unbounded_abelian`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.marker_zero_intervals`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.pairCode`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.pairCode_leftInverse`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.pairDecode`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.product_profile_injective`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.profile_eq_iff`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.profile_eq_map`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.profile_eq_mono`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.profile_one_eq_of_true_count`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.scaled_lacunary`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.singleton_counts_total`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.split_of_complexity_lt`
- Truth anchor: `D5/S1/Words/Complexity/LacunaryBinomialMarkers.strict_lifts_through_constant_tag`
- Dependency: [D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore](ExactDecks/Growth/ExactDeckCore.md)
- Dependency: [D5/S1/Words/Complexity/ExactDecks/Growth/PositiveWordBall](ExactDecks/Growth/PositiveWordBall.md)
- Dependency: [D5/S1/Words/Complexity/MorseHedlund](MorseHedlund.md)
- Dependency: [D5/S1/Words/Complexity/VivionBinomialConverseFails](VivionBinomialConverseFails.md)
- Dependency: [D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity](../GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.md)
- Dependency: [D5/S1/Words/GoldenWord](../GoldenWord.md)
