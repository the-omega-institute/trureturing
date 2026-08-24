# Finite Partition Algebra Duality

## Abstract

Equivalence relations and finite unital pointwise algebras of real functions determine each other, and both finiteness and each closure condition are necessary.

**Theorem 1.1 (Partition functions recover every relation).**

$$\begin{gathered}\forall X: \operatorname{Type}, R: \operatorname{Setoid}\left(X\right),\\{}\operatorname{Indistinguishable}\left(\operatorname{partitionAlgebra}\left(R\right)\right) = R.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Algebra/FinitePartitionAlgebraDuality.indistinguishability_partitionAlgebra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Functions constant on the classes of a relation cannot separate related states, and the indicator of one class separates any unrelated pair. The relation is therefore reconstructed exactly.

This direction needs no finiteness hypothesis on the state type and no closure hypothesis on the algebra.

**Theorem 1.2 (Finite unital algebras recover exactly their own blocks).**

$$\begin{gathered}\forall X: \operatorname{Type}, \operatorname{Fintype} X,\\{}A: \operatorname{Subalgebra}\left(R, X \to R\right),\\{}\operatorname{partitionAlgebra}\left(\operatorname{indistinguishabilitySetoid}\left(A\right)\right) = A.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Algebra/FinitePartitionAlgebraDuality.partitionAlgebra_indistinguishability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every member of the algebra is constant on its indistinguishability classes, giving one inclusion with no extra hypothesis.

For the reverse inclusion, a finite state type has finitely many classes. Each class indicator lies in the algebra, and a function constant on classes is the finite linear combination of those indicators weighted by its class values, hence lies in the algebra.

**Lemma 1.3 (Dropping finiteness breaks the algebra round trip).**

$$\operatorname{partitionAlgebra}\left(\operatorname{indistinguishabilitySetoid}\left(\operatorname{eventuallyConstantAlgebra}\right)\right) \neq \operatorname{eventuallyConstantAlgebra}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Algebra/FinitePartitionAlgebraDuality.finiteness_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the natural numbers the eventually constant real sequences form a unital algebra closed under linear combinations and products, and they separate every pair of indices.

Its indistinguishability relation is therefore equality, whose partition algebra is all real sequences. The identity sequence is constant on singleton classes yet is not eventually constant, so the round trip strictly enlarges the algebra.

**Lemma 1.4 (Dropping the constants breaks the algebra round trip).**

$$\begin{gathered}\exists A: \operatorname{Set}\left(Bool \to R\right),\\{}\operatorname{ClosedUnderLinearCombinations}\left(A\right) \land \operatorname{ClosedUnderPointwiseMultiplication}\left(A\right) \land\\{}\operatorname{RelationInvariantFunctions}\left(\operatorname{Indistinguishable}\left(A\right)\right) \neq A.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Algebra/FinitePartitionAlgebraDuality.constants_are_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The family containing only the zero function on a two-element state type is closed under linear combinations and under pointwise products, but contains no nonzero constant.

It separates nothing, so its indistinguishability relation is total and its partition algebra is every constant function. That algebra strictly contains the original family.

**Lemma 1.5 (Dropping linear combinations breaks the algebra round trip).**

$$\begin{gathered}\exists A: \operatorname{Set}\left(Bool \to R\right),\\{}\operatorname{ContainsConstants}\left(A\right) \land \operatorname{ClosedUnderPointwiseMultiplication}\left(A\right) \land\\{}\operatorname{RelationInvariantFunctions}\left(\operatorname{Indistinguishable}\left(A\right)\right) \neq A.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Algebra/FinitePartitionAlgebraDuality.linear_combinations_are_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a two-element state type the constants together with the scalar multiples of one block indicator are closed under pointwise products and already separate the two states.

That family omits the sums of its own members, so its partition algebra is strictly larger. Closure under linear combinations is therefore not removable.

**Lemma 1.6 (Dropping pointwise products breaks the algebra round trip).**

$$\begin{gathered}\exists A: \operatorname{Set}\left(\operatorname{Fin}\left(3\right) \to R\right),\\{}\operatorname{ContainsConstants}\left(A\right) \land \operatorname{ClosedUnderLinearCombinations}\left(A\right) \land\\{}\operatorname{RelationInvariantFunctions}\left(\operatorname{Indistinguishable}\left(A\right)\right) \neq A.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Algebra/FinitePartitionAlgebraDuality.pointwise_multiplication_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The affine functions of the coordinate on a three-element state type contain the constants, are closed under linear combinations, and separate all three states.

The square of the coordinate is constant on the resulting singleton classes yet is not affine, so the partition algebra strictly contains the family. Closure under products is therefore not removable.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Algebra/FinitePartitionAlgebraDuality.constants_are_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Algebra/FinitePartitionAlgebraDuality.finiteness_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Algebra/FinitePartitionAlgebraDuality.indistinguishability_partitionAlgebra`
- Truth anchor: `D5/S3/ConceptDynamics/Algebra/FinitePartitionAlgebraDuality.linear_combinations_are_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Algebra/FinitePartitionAlgebraDuality.partitionAlgebra_indistinguishability`
- Truth anchor: `D5/S3/ConceptDynamics/Algebra/FinitePartitionAlgebraDuality.pointwise_multiplication_is_necessary`
