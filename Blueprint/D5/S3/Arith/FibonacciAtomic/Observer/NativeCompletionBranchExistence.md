# Actual infinite branches of native completion trees

## Abstract

NativeCompletionBranchExistence

**Theorem 1.1 (Every completion outside the finite embedding has an infinite branch).**

$$\forall T: CompletionTree, (((\exists t: Source, (\operatorname{embed}\left(t\right) = T)) \implies (False)) \implies (\operatorname{HasInfiniteBranch}\left(T\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeCompletionBranchExistence.infinite_of_not_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The completion is the unrestricted final coalgebra PFunctor.M for Boolean leaves and ordered binary nodes. Source is the existing finite FreeMagma Bool carrier, and embed preserves the actual constructors and four-valued address readout. The premise excludes exactly the image of that finite embedding. It does not mean that the tree has infinitely many different subtree values.

Child(S,T) means that T is an actual node and S is one of its two children. Accessibility for this relation reconstructs a finite source by induction: a leaf supplies its Boolean source leaf, and the two inductive source preimages combine into a source pair. The resulting embedding equals the original completion itself, not merely a selected finite approximation.

The contrapositive gives nonaccessibility. Mathlib's not_acc_iff_exists_descending_chain then supplies one infinite chain of actual children starting at the given completion. A direction is selected for each chain edge. Induction on the length of the direction prefix preserves every subsequent address readout: reading prefix followed by a in the original tree equals reading a in the current chain tree. Its root is present, so every finite prefix of the single direction sequence is present in the original tree.

Left and right children may coincide, and the child relation may have loops. A fully branching self-similar tree is therefore included. No default subtree is substituted for an invalid address, no regularity or computability of the completion is assumed, and no finite procedure for deciding membership in the finite embedding is claimed. The argument combines the classical descending-chain theorem with the native constructor and readout correspondence; no literature originality is claimed.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCompletionBranchExistence.infinite_of_not_finite`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeCompletionPrefixLifting](NativeCompletionPrefixLifting.md)
