# Controlled Finite Stability

## Abstract

Finite controlled observations stabilize at the maximal common invariant relation.

**Theorem 1.1 (Controlled refinement stabilizes at the maximal common congruence).**

$$\begin{gathered}\forall Y, U, O,\\{}\operatorname{FiniteNonempty}(Y), \operatorname{FiniteNonempty}(U), \operatorname{FiniteNonempty}(O),\\{}F: U \to Y \to Y, q: Y \to O, \operatorname{Surjective}(q),\\{}(\forall m\in \mathbb{N}, \operatorname{R}(F, q, m) = \operatorname{R}(F, q, m+1) \Rightarrow \forall r\in \mathbb{N}, \operatorname{R}(F, q, m+r) = \operatorname{R}(F, q, m)) \land\\{}(\operatorname{RInfinity}(F, q) = \operatorname{gfp}(\operatorname{RefinementOperator}(F, q))) \land\\{}(\operatorname{IsGreatest}(\operatorname{CommonStableEquivalences}(F, q), \operatorname{RInfinity}(F, q))) \land\\{}((\operatorname{R}(F, q, m_{*}^{U}) = \operatorname{R}(F, q, m_{*}^{U}+1)) \land (\forall m\in \mathbb{N}, \operatorname{R}(F, q, m) = \operatorname{R}(F, q, m+1) \Rightarrow m_{*}^{U} \leq m)) \land\\{}(m_{*}^{U} \leq \operatorname{card}(\operatorname{quotient}(Y, \operatorname{RInfinity}(F, q))) - \operatorname{card}(O)) \land\\{}(\operatorname{card}(\operatorname{quotient}(Y, \operatorname{RInfinity}(F, q))) - \operatorname{card}(O) \leq \operatorname{card}(Y) - \operatorname{card}(O)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability.controlled_finite_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the state, input, and realized readout carriers be finite and nonempty. Construct every bounded relation from equality of readouts after all input words up to the stated length, and construct the complete relation from all finite input words. Surjectivity of the readout records that the output carrier is its realized image.

If two consecutive bounded relations agree, the relation is a fixed point of the controlled refinement operator, so every later bounded relation agrees with it. The complete relation is the operator's greatest fixed point and the greatest equivalence contained in the current-readout kernel that is preserved by every input transition.

The least stable depth is characterized publicly by stability and minimality. Before that depth every strict refinement increases the finite quotient class count. The count begins at the number of realized readouts, ends at the complete behavior quotient, and never exceeds the state count, giving both displayed bounds.

Repository search found and directly reuses the controlled-word semantics, the bounded relation recursion, the recursive signature correctness theorem, and the complete behavior quotient. Pinned Mathlib supplied Fintype.card_le_of_surjective, Fintype.bijective_iff_surjective_and_card, and Nat.sInf_mem. No single packaged theorem containing the branching fixed-point and quotient-bound clauses was found.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability.controlled_finite_stability`
- Dependency: [D5/S1/Dynamics/KnasterTarski](../../../S1/Dynamics/KnasterTarski.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/ControlledRelationRecursion](ControlledRelationRecursion.md)
