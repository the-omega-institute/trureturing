# Swap on the Self-Application Diagonal

## Abstract

Boolean swap changes every value selected along a self-application diagonal.

**Theorem 1.1 (Swap changes every self-diagonal value).**

$$\forall I, P: I\to I\to \operatorname{Bool},\ \forall i:I,\ \operatorname{not}(P(i,i)) \neq P(i,i).$$

*Proof.* Machine-checked in Lean as `D5/S0/Conventions/DiagonalSwap.swap_changes_self_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two-state swap is instantiated by Boolean negation. For every binary-valued assignment and every index, the theorem selects the self-application value P(i,i) and states that its swap is unequal to that value.

This is an honest partial closure of the source theorem's mathematical engine clause. The claims that removing the swap deprives three cited results of statement qualification, and the concluding claim about the load borne by the minimal dichotomy, remain unresolved.

Pinned Mathlib was searched before proving. Bool.not_ne_self was an exact hit for the fixed-point-free swap primitive; Bool.not_eq_iff and Bool.not_ne_id were related hits. Repository searches found no existing declaration for the self-diagonal family statement, so the proof is the thin wrapper obtained by applying Bool.not_ne_self to P(i,i).

## References

- Truth anchor: `D5/S0/Conventions/DiagonalSwap.swap_changes_self_diagonal`
