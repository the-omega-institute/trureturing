# Local Deterministic CHSH Separation

## Abstract

Local deterministic answer tables obey the classical bound and cannot match the fixed Bell witness.

**Theorem 1.1 (Local deterministic CHSH separation).**

$$\begin{aligned}\forall Fiber: \operatorname{Type}, [\operatorname{Fintype}(Fiber)], [\operatorname{Nonempty}(Fiber)],\\\forall preparation: \operatorname{FinitePreparation}(Fiber), model: \operatorname{DeterministicFiberModel}(Fiber), table: \operatorname{DeterministicAnswerTable}(Fiber),\\(\forall fiber: Fiber, \left\lVert \operatorname{chshAt}(model, fiber) \right\rVert \le 2) \land\\\left\lVert \operatorname{classicalCHSH}(\operatorname{weight}(preparation), model) \right\rVert \le 2 \land\\\operatorname{Tr}(bellDensity \cdot chshOperator) = 2 \cdot \sqrt{2} \land\\\neg \operatorname{IsNoncontextual}(table) \land \neg \operatorname{ReproducesBellCHSH}(preparation, table).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/Designs/LocalDeterministicCHSHSeparation.local_deterministic_chsh_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Fiber be finite and inhabited. A finite preparation consists of nonnegative weights summing to one, a local model supplies two Boolean answers on each side, and one preparation-independent table supplies both its window and local branches.

Exhausting the four Boolean answers proves the pointwise absolute bound. The frozen finite-mixture theorem transports it through the preparation weights.

The exact frozen Bell-state calculation gives two times square root two. The frozen shared-table theorem then excludes both a window-algebra character and reproduction of that Bell value by the local branch.

## References

- Truth anchor: `D5/S3/QuantumBounds/Designs/LocalDeterministicCHSHSeparation.local_deterministic_chsh_separation`
- Dependency: [D5/S3/Observer/ClassicalAnswerTableExclusion](../../Observer/ClassicalAnswerTableExclusion.md)
