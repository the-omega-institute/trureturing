# Hindley-Rosen Confluence

## Abstract

Strong commutation lifts to closures and makes the union of confluent reductions confluent.

**Theorem 1.1 (Strong commutation lifts to closures).**

$$(\forall h, a, b, r(h, a) \land s(h, b) \Rightarrow \exists c, s(a, c) \land r(b, c)) \Rightarrow (\forall h, a, b, \operatorname{ReflTransGen}(r)(h, a) \land \operatorname{ReflTransGen}(s)(h, b) \Rightarrow \exists c, \operatorname{ReflTransGen}(s)(a, c) \land \operatorname{ReflTransGen}(r)(b, c).)$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/HindleyRosen.reflTransGen_commute_of_strong_commute` (`✓ std3`). ∎

*Citation.* M. H. A. Newman (1942). *On Theories with a Combinatorial Definition of "Equivalence"*. DOI: [10.2307/1968867](https://doi.org/10.2307/1968867).

*Commentary.*

The proof first moves one s-step across an r-closure, then inducts over the s-closure. Each square retains the stated r/s orientation.

**Theorem 1.2 (Confluence of a strongly commuting union).**

$$\operatorname{Confluent}(r) \land \operatorname{Confluent}(s) \land \text{r and s strongly commute} \Rightarrow \operatorname{Confluent}(r \lor s).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/HindleyRosen.hindley_rosen_confluent` (`✓ std3`). ∎

*Citation.* M. H. A. Newman (1942). *On Theories with a Combinatorial Definition of "Equivalence"*. DOI: [10.2307/1968867](https://doi.org/10.2307/1968867).

*Commentary.*

The union closure is embedded into the closure of alternating r- and s-blocks. Same-color peaks use the two confluence premises, while mixed peaks use lifted commutation; Relation.church_rosser then joins all paths.

**Theorem 1.3 (Church-Rosser for a strongly commuting union).**

$$\operatorname{Confluent}(r) \land \operatorname{Confluent}(s) \land \text{r and s strongly commute} \Rightarrow (\forall a, b, \operatorname{EqvGen}(r \lor s)(a, b) \iff \operatorname{Join} \operatorname{ReflTransGen}(r \lor s)(a, b).)$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/HindleyRosen.hindley_rosen_church_rosser` (`✓ std3`). ∎

*Citation.* Alonzo Church and J. B. Rosser (1936). *Some Properties of Conversion*. DOI: [10.1090/S0002-9947-1936-1501858-0](https://doi.org/10.1090/S0002-9947-1936-1501858-0).

*Commentary.*

This theorem composes Hindley-Rosen union confluence with the frozen confluence-iff-Church-Rosser equivalence.

## References

- Truth anchor: `D5/S0/Rewriting/HindleyRosen.hindley_rosen_church_rosser`
- Truth anchor: `D5/S0/Rewriting/HindleyRosen.hindley_rosen_confluent`
- Truth anchor: `D5/S0/Rewriting/HindleyRosen.reflTransGen_commute_of_strong_commute`
- Dependency: [D5/S0/Rewriting/ChurchRosser](ChurchRosser.md)
