# Root factors of successor cycles

## Abstract

Squaring-compatible unit assignments are finite, and their exact cardinality is the product of the successor-cycle root factors.

SquareAssignments(beta) consists of functions v from Q to the units of the field K satisfying v(beta(q))=v(q)^2. Iteration gives v(beta^j(q))=v(q)^(2^j). A return of length l therefore forces v(q)^(2^l-1)=1.

**Theorem 1.1 (Finiteness before cardinality).**

$$\forall Q \in Typeu,\; \forall K \in Typeu,\; \operatorname{Field}\left(K\right) \Rightarrow \left(\operatorname{Finite}\left(Q\right) \Rightarrow \left(\forall beta \in \operatorname{Perm}\left(Q\right),\; \operatorname{Finite}\left(\operatorname{SquareAssignments}\left(K, beta\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SuccessorPowerAssignments.square_assignments_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The order of a finite permutation is positive and is a common return time. Evaluation embeds the assignment type into a finite product of groups of roots of unity. This proves finiteness independently of any natural-cardinality bound.

**Definition 1.2 (The cycle root product).**

$$\forall Q \in Typeu,\; \operatorname{Finite}\left(Q\right) \Rightarrow \left(\forall beta \in \operatorname{Perm}\left(Q\right),\; \operatorname{cycleWeight}\left(beta\right) = \operatorname{CycleRootProduct}\left(beta\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/SuccessorPowerAssignments.cycleWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CycleRootProduct is the product over Mathlib cycleFactorsFinset of 2 raised to the support cardinality of the cycle, minus one. The omitted fixed-point cycles have length one and factor one. No cycle partition of a larger ambient vertex set is substituted.

**Definition 1.3 (Independent cycle-root realization).**

$$\forall Q \in Typeu,\; \forall K \in Typeu,\; \operatorname{Field}\left(K\right) \Rightarrow \left(\operatorname{Fintype}\left(Q\right) \Rightarrow \left(\operatorname{DecidableEq}\left(Q\right) \Rightarrow \left(\forall beta \in \operatorname{Perm}\left(Q\right),\; \operatorname{Equiv}\left(\operatorname{SquareAssignments}\left(K, beta\right), \operatorname{CycleRootTuples}\left(K, beta\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/SuccessorPowerAssignments.cycleEvaluationEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CycleRootTuples(K,beta) is the dependent product, over c in beta.cycleFactorsFinset, of rootsOfUnity(2^card(support(c))-1,K). Choose one representative in each nontrivial cycle. Evaluation records the value there. To realize a tuple, put z^(2^j) at position j in its cycle and one off that cycle, then multiply these disjoint contributions. The root equation proves wraparound, and disjoint supports give both inverse laws. This is a genuine equivalence over every field, including the empty carrier.

**Theorem 1.4 (Exact complex cycle factors).**

$$\forall Q \in Typeu,\; \operatorname{Fintype}\left(Q\right) \Rightarrow \left(\operatorname{DecidableEq}\left(Q\right) \Rightarrow \left(\forall beta \in \operatorname{Perm}\left(Q\right),\; \operatorname{card}\left(\operatorname{SquareAssignments}\left(Complex, beta\right)\right) = \operatorname{CycleRootProduct}\left(beta\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SuccessorPowerAssignments.square_assignments_cycle_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite decidable Q and every permutation beta, the equivalence gives exact cardinality. Complex.card_rootsOfUnity gives 2^l-1 for each cycle of length l; fixed points have the unique value one. There is no surjectivity hypothesis on evaluation or independent realizability: both inverse laws are proved in cycleEvaluationEquiv.

**Theorem 1.5 (The exact cycle root cardinality).**

$$\forall Q \in Typeu,\; \operatorname{Finite}\left(Q\right) \Rightarrow \left(\forall beta \in \operatorname{Perm}\left(Q\right),\; \operatorname{card}\left(\operatorname{SquareAssignments}\left(Complex, beta\right)\right) = \operatorname{cycleWeight}\left(beta\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SuccessorPowerAssignments.square_assignments_weight_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation and realization are inverse bijections. For a root z on a cycle of length l, the coordinate at position k is z^(2^k). The equation z^(2^l-1)=1 gives exactly the wraparound relation. Independent cycle assignments are multiplied pointwise; disjoint supports ensure that evaluation recovers each chosen root separately. Fixed-point coordinates equal one, so singleton cycles contribute mu_1={1}. Complex.card_rootsOfUnity counts every nontrivial cycle factor exactly. The cycles belong to the successor permutation itself.

## References

- Truth anchor: `D5/S3/FiniteGroups/SuccessorPowerAssignments.cycleEvaluationEquiv`
- Truth anchor: `D5/S3/FiniteGroups/SuccessorPowerAssignments.cycleWeight`
- Truth anchor: `D5/S3/FiniteGroups/SuccessorPowerAssignments.square_assignments_cycle_card`
- Truth anchor: `D5/S3/FiniteGroups/SuccessorPowerAssignments.square_assignments_finite`
- Truth anchor: `D5/S3/FiniteGroups/SuccessorPowerAssignments.square_assignments_weight_card`
- Dependency: [D5/S3/FiniteGroups/SuccessorQuotient](SuccessorQuotient.md)
