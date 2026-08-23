# Finite Defect Termination

## Abstract

Strict defect removal on a finite carrier stops within the initial defect count.

**Theorem 1.1 (Finite strict defect repair terminates).**

$$\forall W: \operatorname{Type}, defects: Nat \to \operatorname{Set}(W),\\{}(\operatorname{Finite}(W) \land\\{}(\forall n: Nat, \operatorname{defects}(n) \neq \emptyset \Rightarrow \operatorname{defects}(n + 1) \neq \operatorname{defects}(n)) \land\\{}(\forall n: Nat, \operatorname{defects}(n + 1) \subseteq \operatorname{defects}(n))) \Rightarrow\\{}\exists n: Nat, n \leq \operatorname{ncard}(\operatorname{defects}(0)) \land \operatorname{defects}(n) = \emptyset.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Termination/FiniteDefectTermination.finite_defect_repairs_terminate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The defect sequence is an independent source primitive on the finite carrier. Its initial set determines the public stopping bound.

Strict change while defects remain and no-new-defects inclusion are separate public premises; together they give proper set descent.

Strict inclusion lowers finite set cardinality at every nonterminal step. After at most the initial cardinality, zero cardinality forces the defect set to be empty.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Termination/FiniteDefectTermination.finite_defect_repairs_terminate`
