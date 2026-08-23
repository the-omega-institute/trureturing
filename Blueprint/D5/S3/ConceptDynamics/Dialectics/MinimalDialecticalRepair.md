# Minimal Dialectical Repair

## Abstract

An explicit carry forces the least target-complete refinement of a current concept.

**Definition 1.1 (Explicit carry witness).**

Lean statement: `D5/S3/ConceptDynamics/Dialectics/MinimalDialecticalRepair.IsCarryWitness`

*Formalization.* `D5/S3/ConceptDynamics/Dialectics/MinimalDialecticalRepair.IsCarryWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A carry witness consists of two states with equal current readouts and unequal target readouts after the process. It is a concrete counterexample to current target-closure, not a contradictory proposition.

**Theorem 1.2 (Least target-complete repair).**

$$\begin{gathered}\forall X, B, Y: \operatorname{Type}, C: X \to B, F: X \to X, K: X \to Y,\\{}\operatorname{Refines}\left(C, \operatorname{conceptJoin}\left(C, {K \circ F}\right)\right) \land\\{}\operatorname{Refines}\left({K \circ F}, \operatorname{conceptJoin}\left(C, {K \circ F}\right)\right) \land\\{}(\forall D: \operatorname{Type}, Q: X \to D, \operatorname{Refines}\left(C, Q\right) \land \operatorname{Refines}\left({K \circ F}, Q\right) \Rightarrow \operatorname{Refines}\left(\operatorname{conceptJoin}\left(C, {K \circ F}\right), Q\right)) \land\\{}(\forall x, y\in X, \operatorname{IsCarryWitness}\left(C, F, K, x, y\right) \Rightarrow \neg\operatorname{Refines}\left({K \circ F}, C\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Dialectics/MinimalDialecticalRepair.minimal_dialectical_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The current concept, process, and target are independent source primitives. Their repair is constructed directly as the joint readout of the current value and the target consequence.

The first two public conjuncts preserve every current distinction and make the target consequence decidable. The third is the universal minimality property among all readouts with those two refinements.

The final public conjunct states the negative step: any explicit carry witness refutes factorization of the target consequence through the current readout. The canonical concept-join theorem supplies the three positive clauses directly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Dialectics/MinimalDialecticalRepair.IsCarryWitness`
- Truth anchor: `D5/S3/ConceptDynamics/Dialectics/MinimalDialecticalRepair.minimal_dialectical_repair`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
