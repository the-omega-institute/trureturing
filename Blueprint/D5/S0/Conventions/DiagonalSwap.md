# Swap on the Self-Application Diagonal

## Abstract

Boolean swap changes every value selected along a self-application diagonal.

**Theorem 1.1 (Swap changes every self-diagonal value).**

$$\forall I, P: I\to I\to \operatorname{Bool},\ \forall i:I,\ \operatorname{not}(P(i,i)) \neq P(i,i).$$

*Proof.* Machine-checked in Lean as `D5/S0/Conventions/DiagonalSwap.swap_changes_self_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two-state swap is instantiated by Boolean negation. For every binary-valued assignment and every index, the theorem selects the self-application value P(i,i) and states that its swap is unequal to that value.

The Index quantifier is fully general, including an empty type where the pointwise conclusion is vacuous. The module compiles Bool as a nonempty index witness and a constant-false assignment, making the self-application diagonal concrete without weakening the theorem.

The proof computes the swap using the two Boolean constructors in OmegaInit. Transporting the proposition that is true at false and false at true along a hypothetical equality of the two constructors yields a contradiction.

This remains a partial closure of the source theorem. The present declaration proves only the shared swap-on-self-diagonal engine. It does not yet prove the deletion test saying identity loses the mismatch, nor the converse claim that universal diagonal escape forces the minimal Boolean swap. Those two obligations require the stronger hosted declaration before the atom can be treated as fully represented.

## References

- Truth anchor: `D5/S0/Conventions/DiagonalSwap.swap_changes_self_diagonal`
