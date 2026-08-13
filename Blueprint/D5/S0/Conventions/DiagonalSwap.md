# Swap on the Self-Application Diagonal

## Abstract

Boolean swap changes every value selected along a self-application diagonal.

**Theorem 1.1 (Swap changes every self-diagonal value).**

$$\forall I, P: I\to I\to \operatorname{Bool},\ \forall i:I,\ \operatorname{not}(P(i,i)) \neq P(i,i).$$

*Proof.* Machine-checked in Lean as `D5/S0/Conventions/DiagonalSwap.swap_changes_self_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two-state swap is instantiated by Boolean negation. For every binary-valued assignment and every index, the theorem selects the self-application value P(i,i) and states that its swap is unequal to that value.

The Index quantifier is fully general, including an empty type where the pointwise conclusion is vacuous. The module therefore compiles PUnit as a nonempty index witness and a constant-false PUnit assignment, making the self-application diagonal concrete without weakening the theorem.

Pinned Mathlib was searched before proving. Bool.not_ne_self was an exact hit for the fixed-point-free swap primitive; Bool.not_eq_iff and Bool.not_ne_id were related hits. Repository searches found no existing declaration for the self-diagonal family statement, so the proof is the thin wrapper obtained by applying Bool.not_ne_self to P(i,i).

This remains a partial closure of the source theorem. The present declaration proves only the shared swap-on-self-diagonal engine. It does not yet prove the deletion test saying identity loses the mismatch, nor the converse claim that universal diagonal escape forces the minimal Boolean swap. Those two obligations require the stronger hosted declaration before the atom can be treated as fully represented.

## References

- Truth anchor: `D5/S0/Conventions/DiagonalSwap.swap_changes_self_diagonal`
