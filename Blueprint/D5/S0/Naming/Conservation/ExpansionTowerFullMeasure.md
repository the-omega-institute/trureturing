# Anonymous Full Measure Along Expansion Towers

## Abstract

Atomless probability naming systems and their expansion limits remain anonymous almost everywhere.

**Theorem 1.1 (Naming expansions preserve full-measure anonymity).**

$$\forall X: \operatorname{Type},\ [\operatorname{MeasureSpace}(X)],\ [\operatorname{Uncountable}(X)],\ [\operatorname{NoAtoms}(\mu)],\ [\operatorname{IsProbabilityMeasure}(\mu)],\\(\forall N: \operatorname{NamingSystem}(X),\ \mu(\operatorname{anonymous}(N))=1) \land\\(\forall T: \operatorname{ExpansionTower}(X),\ \mu(\operatorname{limitAnonymous}(T))=1).$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/Conservation/ExpansionTowerFullMeasure.naming_expansion_full_measure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A naming system's anonymous set is the complement of the image of its partial assignment. An expansion tower consists of successor embeddings of name types whose assignments agree with the previous stage; its limit named set is the union over all finite stages.

The first conjunct quantifies over every naming system independently. The second quantifies over every compatible countable expansion tower. Thus both clauses of the named source statement are retained, including probability normalization and the limit-system carrier.

The proof applies the frozen countable-tower full-measure theorem twice: first to the singleton-indexed family and then to the stages of the tower. Pinned Mathlib's probability-measure identity changes the measure of the whole carrier to one.

## References

- Truth anchor: `D5/S0/Naming/Conservation/ExpansionTowerFullMeasure.naming_expansion_full_measure`
- Dependency: [D5/S0/Naming/Conservation/NamingTowerConservation](NamingTowerConservation.md)
