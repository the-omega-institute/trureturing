# Original ordered-menu branch-first codes

## Abstract

Original ordered-menu branch-first codes

Addresses are finite Boolean lists, with false denoting L and true denoting R. The actual Source is FreeMagma Bool, with true denoting alpha and false denoting beta. Menu is a list in the fixed public order. Child selection removes one matching leading bit and preserves that order. Repetition changes no rank rule; no lexicographic sorting occurs.

For a nonempty menu eta is zero exactly when every selected target has the form Lr with nonempty r. Empty menus have count one and code zero. Write J(S)=N(SL)N(SR) and bit(eta(S)) for the Boolean indicator as a natural number. The equations below are exactly the branch-first count and rank. The beta overlap rank is the branch rank of pair(alpha,alpha).

The recursion decreases the sum of length(q)+1 over the menu. Its range bound is proved jointly over the two child menus. Strictly positive child counts make the mixed-radix digits injective. A nonempty menu separates alpha and beta even in the overlap case: alpha has the outer leaf tag, while the overlap beta rank lies strictly inside the branch interval.

**Lemma 1.1 (Ordered child membership).**

$$\forall b: Bool, (\forall S: Menu, (\forall r: Address, ((r \in \operatorname{child}\left(b, S\right)) \iff (\operatorname{cons}\left(b, r\right) \in S))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuCode.mem_child` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Filtering matching heads is equivalent to membership of the original address with that head. This identity connects recursive reconstruction and path-context propagation to the same menu.

**Theorem 1.2 (Exact grammar and all-source range).**

$$\forall S: Menu, (((S = \operatorname{nil}\left(\right)) \implies ((\operatorname{N}\left(S\right) = 1) \land (\forall u: Source, (\operatorname{code}\left(S, u\right) = 0)))) \land ((S \neq \operatorname{nil}\left(\right)) \implies ((\operatorname{N}\left(S\right) = \operatorname{N}\left(\operatorname{child}\left(false, S\right)\right) \times \operatorname{N}\left(\operatorname{child}\left(true, S\right)\right) + 1 + \operatorname{bit}\left(\operatorname{eta}\left(S\right)\right)) \land (\forall x, y: Source, (\operatorname{code}\left(S, \operatorname{pair}\left(x, y\right)\right) = \operatorname{code}\left(\operatorname{child}\left(false, S\right), x\right) \times \operatorname{N}\left(\operatorname{child}\left(true, S\right)\right) + \operatorname{code}\left(\operatorname{child}\left(true, S\right), y\right))) \land (\operatorname{code}\left(S, \operatorname{of}\left(true\right)\right) = \operatorname{N}\left(\operatorname{child}\left(false, S\right)\right) \times \operatorname{N}\left(\operatorname{child}\left(true, S\right)\right)) \land (\operatorname{code}\left(S, \operatorname{of}\left(false\right)\right) = \operatorname{if}\left(\operatorname{eta}\left(S\right), \operatorname{N}\left(\operatorname{child}\left(false, S\right)\right) \times \operatorname{N}\left(\operatorname{child}\left(true, S\right)\right) + 1, \operatorname{code}\left(\operatorname{child}\left(false, S\right), \operatorname{of}\left(true\right)\right) \times \operatorname{N}\left(\operatorname{child}\left(true, S\right)\right) + \operatorname{code}\left(\operatorname{child}\left(true, S\right), \operatorname{of}\left(true\right)\right)\right)))) \land (0 < \operatorname{N}\left(S\right)) \land (\forall u: Source, (\operatorname{code}\left(S, u\right) < \operatorname{N}\left(S\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuCode.original_code_grammar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Branch ranks occupy the product interval. Alpha follows that interval, and beta follows alpha when eta is one. When eta is zero beta takes the specified branch rank. The range proof includes arbitrary actual trees, empty menus, epsilon and nested targets.

**Theorem 1.3 (One actual context preserves the rank distinction).**

$$\forall S: Menu, (\forall a, r: Address, ((\operatorname{append}\left(a, r\right) \in S) \implies (\operatorname{code}\left(S, \operatorname{spine}\left(a, \operatorname{of}\left(true\right)\right)\right) \neq \operatorname{code}\left(S, \operatorname{spine}\left(a, \operatorname{of}\left(false\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuCode.original_code_context_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The FM.21 context puts alpha at each side sibling and the chosen tree at address a. A selected extension makes the residual menu nonempty. The leaf distinction at the hole propagates through each branch digit using positive radices and cancellation. The same two trees are used by the future-vector obstruction.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuCode.mem_child`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuCode.original_code_context_separation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuCode.original_code_grammar`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition](../ActualTreeReadoutAcquisition.md)
