# Binary Patch Families

## Abstract

Binary choices on distinct off-record slots produce distinct functions that preserve every recorded value.

**Theorem 1.1 (Binary patches are distinct and preserve the record).**

$$\forall D,Y, \forall ell \in N, \forall record \in \operatorname{Finset}(D),\ \forall prescribed,base: D \to Y,\ \forall slot: Fin(ell) \to D, \forall twist: Y \to Y,\ ((\forall d \in record, base(d) = prescribed(d)) \land \operatorname{Injective}(slot) \land (\forall j, \neg(slot(j) \in record)) \land (\forall y, twist(y) \neq y)) \Rightarrow\ (\operatorname{Injective}(patchedFamily(base,slot,twist)) \land (\forall word,d \in record,\ patchedFamily(base,slot,twist,word)(d) = prescribed(d))).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/BinaryPatchFamily.binary_patch_family_injective_and_consistent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let record be a finite set of observed positions and base a function that agrees with the prescribed observations. An injective slot map places every patch outside record. At each slot a binary word chooses between the base value and its image under a fixed-point-free twist.

Evaluating equal patched functions at each designated slot recovers every binary choice, so the patch-family map is injective. Away from the slot range, Mathlib's Function.extend returns base; consequently every member of the family preserves the complete finite record.

This is an honest partial closure of the construction clause in source theorem 6.7. Computability of the patched functions, program descriptions, complexity estimates, the budget-dependent word length, and the final asymptotic lower bound remain unresolved.

## References

- Truth anchor: `D5/S0/Rewriting/BinaryPatchFamily.binary_patch_family_injective_and_consistent`
