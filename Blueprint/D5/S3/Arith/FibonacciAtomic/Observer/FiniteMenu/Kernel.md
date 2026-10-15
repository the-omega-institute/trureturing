# The original all-menu native trajectory kernel

## Abstract

The original all-menu native trajectory kernel

Source is FreeMagma Bool. Alpha is of(true), beta is of(false), and mul is an actual ordered pair. Substitution sends alpha to beta and beta to the pair (beta,alpha), extending homomorphically to every finite source. Addresses are finite Boolean lists with false=L and true=R. Readout has exactly four replies: alpha, beta, branch and absent.

A menu S is any finite ordered list of addresses. The original child menus keep their order and multiplicity. The original rank code uses the branch digits iL*N(SR)+iR before its leaf tags. The predicate Same(S,u,v) means equality of the actual reply at every q in S and every common natural count k, starting each side from its own one fixed source. No prefix closure, source-height bound or attained-vector premise is imposed.

For each address q, every source gives a branch by count pathCost(q)+2. For atomic sources this follows from guarded atomic navigation and the native Fibonacci pair recurrence. For an initial pair, descent at its first letter reduces to the corresponding actual child at the same count; induction on the remaining address proves the bound for arbitrary sources. Atomic navigation also excludes a branch before that bound on alpha. Thus a selected epsilon separates alpha from a pair immediately, and any selected nonempty address separates them by the earlier branch bound of the pair's selected child.

The two leaves differ at each selected address at the common count pathCost(q)+1: alpha gives beta and beta gives branch. Beta can agree with a pair only when every selected address lies strictly below L. Epsilon separates at zero; L separates absent from a present root at zero; a right-starting address separates at the child's branch bound. When eta(S)=false, every selected word is Lr with r nonempty. The pair recurrence gives equality of beta and pair(alpha,alpha) at every positive count, and at zero both replies are absent. For an empty menu this equality is vacuous. In particular a uniform beta/pair classification includes S=[]; eta=false alone never forces a nonempty left child menu.

Induction on an address-depth bound combines these semantic cases. For two pairs, synchronized substitution and literal child navigation identify equality of the complete trajectories with equality in both child menus. The existing finite product equivalence makes equality of the original branch ranks equivalent to equality of the two bounded digits. Alpha has its separate tag. Beta has a separate tag when eta=true, and otherwise has exactly the rank of pair(alpha,alpha). Induction in the child menus therefore proves both implications for the original numerical code.

**Theorem 1.1 (Exact original code kernel for every menu and source).**

$$\forall S: Menu, (\forall u: Source, (\forall v: Source, ((\operatorname{code}\left(S, u\right) = \operatorname{code}\left(S, v\right)) \iff (\forall q: Address, ((q \in S) \implies (\forall k: Nat, (\operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, k, u\right)\right) = \operatorname{readout}\left(q, \operatorname{iterate}\left(substitution, k, v\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/Kernel.original_menu_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Empty menus, epsilon, repeated targets, nested targets, mixed sides, asymmetric child menus and missing prefixes all remain included. Both sources and the count have their original unrestricted domains. This result is the trajectory-kernel clause of the finite-menu normal form; it asserts no alphabet, memory, computational or acquisition optimum.

A fixed menu's equivalence need not survive an arbitrary tree context. With S=[LL], beta and pair(alpha,alpha) have the same selected trajectory. Placing each as the left child of a pair whose right child is alpha exposes absent versus alpha at LL at count zero. This contextual separation is compatible with the stated kernel because the context changes the sources observed by the fixed menu.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/Kernel.original_menu_kernel`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuObstruction](../NativeFiniteMenuObstruction.md)
