# Prefix-menu reconstruction

## Abstract

Prefix-menu reconstruction

PrefixClosed requires every prefix, including epsilon and the member itself, to be selected. The empty menu is prefix-closed. Initial and future vectors use exactly the original list order. A nonempty closed menu contains the root, and both child menus remain prefix-closed.

Reconstruct uses the supplied root reply. Alpha or beta is accepted only when every selected strict descendant is absent. An absent root is rejected. A branch recursively reconstructs the two child menus and pairs their actual representatives. An empty menu returns alpha without inspecting any reply. At zero fuel a nonempty menu rejects.

The depth hypothesis is strict length(q)<h. Every branch descent reduces both fuel and target length. The theorem supplies one actual representative for the whole vector; its code and every future reply agree simultaneously with the original tree. It does not assign independent signatures to coordinates.

**Theorem 1.1 (Every attained vector reconstructs correctly).**

$$\forall h: Nat, (\forall S: Menu, (\forall u: Source, (\forall f: Address \to Reply, (((\operatorname{PrefixClosed}\left(S\right)) \land (\forall q: Address, ((q \in S) \implies (\operatorname{length}\left(q\right) < h))) \land (\forall q: Address, ((q \in S) \implies (\operatorname{f}\left(q\right) = \operatorname{readout}\left(q, u\right))))) \implies (\exists t: Source, ((\operatorname{reconstruct}\left(h, S, f\right) = \operatorname{some}\left(t\right)) \land (\operatorname{height}\left(t\right) \leq h) \land (\operatorname{code}\left(S, t\right) = \operatorname{code}\left(S, u\right)) \land (\forall q: Address, ((q \in S) \implies (\forall k: Nat, (\operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, k, t\right)\right) = \operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, k, u\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuReconstruction.prefix_menu_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on h accepts actual leaves with all selected strict descendants absent. For an actual branch the child induction hypotheses give two representatives of height at most h-1. Pairing preserves the original mixed-radix code. Native substitution preserves a reached branch, so each future selected reply reduces to the corresponding child equality at the same count.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuReconstruction.prefix_menu_reconstruction`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate](../ActualImageAddressCertificate.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuCode](NativeFiniteMenuCode.md)
