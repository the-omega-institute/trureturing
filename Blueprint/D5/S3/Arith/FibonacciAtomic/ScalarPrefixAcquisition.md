# Ordered prefix acquisition

## Abstract

The ordered digit protocol identifies a prime-power residue with at most e(p-1) complete valuation queries and retains its decoded value at termination.

**Theorem 1.1 (The exact digit loop preserves its prefix and query budget).**

$$\forall p \in \mathbb{N}, \forall e \in \mathbb{N}, \left(\operatorname{Prime}\left(p\right) \land 1 \leq e\right) \Rightarrow \forall h \in \mathbb{N}, \forall s \in \mathbb{N}, \forall r \in \mathbb{N}, \left(s+h = e\right) \Rightarrow \forall y \in \operatorname{ZMod}\left(p^{e}\right), \left(\operatorname{mod}\left(\operatorname{val}\left(y\right), p^{s}\right) = r\right) \Rightarrow \operatorname{Eval}\left(\operatorname{A}\left(p, e, h, s, r\right), y\right) = y \land \operatorname{len}\left(\operatorname{Trace}\left(\operatorname{A}\left(p, e, h, s, r\right), y\right)\right) \leq h\left(p-1\right) \land \operatorname{Legal}\left(\operatorname{A}\left(p, e, h, s, r\right), y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ScalarPrefixAcquisition.scalar_prefix_acquisition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be prime, e be positive, and X=ZMod(p^e). The complete readout q(c,y) is the greatest j at most e such that y and c are congruent modulo p^j. Testing center c therefore returns the capped valuation of y-c; equivalently it tests the shift -c. Depth e includes the zero difference.

A decorated program ends at a leaf containing a decoded residue, or queries a center and continues according to its complete natural-number response. Eval(T,y) is the decoded leaf reached on y. Trace(T,y) is the complete center-response list after erasing the leaf labels. Every query contributes one entry.

A(p,e,h,s,r) starts with h remaining digits and known prefix r at depth s. For h=0 it ends with decoded value r. Otherwise it tests centers r+a p^s in the order a=0,...,p-2. A response greater than s selects that digit; it calls A(p,e,h-1,s+1,r+a p^s). A response not greater than s advances a only. After all p-1 failures it selects digit p-1 without another query and makes the same recursive call. Both updated coordinates use the old s. Extra depth beyond s+1 is discarded.

Legal(T,y) states along the actual query path that each stored prefix r equals y mod p^s and every response is at least its stored depth s. At a decoded leaf the stored center has saturated response e. With r=y mod p^s, the next digit is (floor(y/p^s) mod p). A query matches precisely that digit. All earlier failures preserve the lower bound on the untried digit. After p-1 failures only p-1 remains. Each selected digit gives the new prefix y mod p^(s+1). Induction proves the decoded value and the remaining budget h(p-1), including p=2 and y=0.

The initial program is A(p,e,e,0,0), with no given digit. A matching final-digit response is saturated at e. A terminated program retains its decoded residue: padding further rounds with that residue as center yields known saturated responses without changing the decoded value.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ScalarPrefixAcquisition.scalar_prefix_acquisition`
- Dependency: [D5/S3/Observer/Budget/PrimePowerNonadaptiveResolution](../../Observer/Budget/PrimePowerNonadaptiveResolution.md)
- Dependency: [D5/S3/Observer/Budget/ResidueLeafOptimality](../../Observer/Budget/ResidueLeafOptimality.md)
