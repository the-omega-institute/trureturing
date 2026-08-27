# Well-Founded Recursive Closure

## Abstract

Well-founded dependency equations have unique solutions, while a self-loop admits a fixed-point gap.

**Theorem 1.1 (Well-founded dependency equations have unique solutions).**

$$\forall edge: V \to V \to Prop, seed, first, second: \operatorname{Set}\left(V\right),\\{}(\operatorname{WellFounded}\left(edge\right) \land \operatorname{SatisfiesDependencyEquation}\left(edge, seed, first\right) \land\\{}\operatorname{SatisfiesDependencyEquation}\left(edge, seed, second\right)) \Rightarrow\\{}first = second.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/WellFoundedRecursiveClosure.dependencyEquation_solution_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the dependency relation is well-founded and two sets both solve the same local equation with the same seed. The two solution sets are equal.

Well-foundedness and both solution predicates are displayed antecedents. The theorem establishes uniqueness, not existence of a solution.

**Theorem 1.2 (The unseeded self-loop has two distinct solutions).**

$$\exists first, second: \operatorname{Set}\left(Unit\right),\\{}(first \neq second \land\\{}\operatorname{SatisfiesDependencyEquation}\left(selfLoop, \emptyset, first\right) \land\\{}\operatorname{SatisfiesDependencyEquation}\left(selfLoop, \emptyset, second\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/WellFoundedRecursiveClosure.selfLoop_has_fixedPoint_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the one-point self-loop and empty seed, there exist two distinct sets that satisfy the dependency equation.

The witnesses are existentially packaged. The theorem states their distinctness and both solution conditions without claiming that every non-well-founded relation has this gap.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/WellFoundedRecursiveClosure.dependencyEquation_solution_unique`
- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/WellFoundedRecursiveClosure.selfLoop_has_fixedPoint_gap`
