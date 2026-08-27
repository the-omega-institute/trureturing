# Dominance Nontransitivity Countermodel

## Abstract

A real phenotype on three unordered diploid genotypes makes complete dominance cyclic and nontransitive.

**Theorem 1.1 (Complete dominance need not be transitive).**

$$\exists a, b, d\in Fin(3), \exists P: Sym2(Fin(3)) \Rightarrow \mathbb{R},\\{}a \neq b \land b \neq d \land a \neq d \land\\{}P(s(a, a)) = 0 \land P(s(a, b)) = 0 \land P(s(b, b)) = 1 \land\\{}P(s(b, d)) = 1 \land P(s(d, d)) = 2 \land P(s(a, d)) = 2 \land\\{}(\operatorname{ker}(P, s(a, a), s(a, b)) \land \neg \operatorname{ker}(P, s(a, b), s(b, b))) \land (\operatorname{ker}(P, s(b, b), s(b, d)) \land \neg \operatorname{ker}(P, s(b, d), s(d, d))) \land\\{}\neg (\operatorname{ker}(P, s(a, a), s(a, d)) \land \neg \operatorname{ker}(P, s(a, d), s(d, d))) \land (\operatorname{ker}(P, s(d, d), s(d, a)) \land \neg \operatorname{ker}(P, s(d, a), s(a, a))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementAlgebra/DominanceNontransitivityCountermodel.complete_dominance_not_transitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed real phenotype is defined on the canonical symmetric square of three alleles. Each dominance edge is displayed using the source kernel condition, including the closing edge of the directed cycle.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementAlgebra/DominanceNontransitivityCountermodel.complete_dominance_not_transitive`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
