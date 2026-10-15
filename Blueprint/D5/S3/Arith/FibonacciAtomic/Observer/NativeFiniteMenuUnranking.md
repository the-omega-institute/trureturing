# Native representatives of every ordered-menu rank

## Abstract

Native representatives of every ordered-menu rank

Source is the existing FreeMagma Bool: of(true) is alpha, of(false) is beta, and mul pairs two actual full binary trees. Addresses use false for L and true for R. A menu is an arbitrary finite ordered list of addresses. Empty lists, epsilon, repeated targets, mixed sides, nested targets and menus lacking prefixes are all included.

For a menu S, let d be the maximum address length, with maximum zero for the empty list. In Lean this is S.toFinset.sup List.length. Passing to a finite set is used only for this maximum; the original ordered child menus, count N, overlap bit eta and numerical code are unchanged. The unrank procedure uses d+1 recursive levels. Each call returns alpha for an empty menu or an invalid natural index.

For a nonempty menu put J=N(SL)N(SR). If i<J, the inverse of finProdFinEquiv supplies the left digit i/N(SR) and right digit i modulo N(SR), each within its original child radix. Recursively build the two child representatives and pair them in one actual tree. The existing equivalence numbers this pair as iL*N(SR)+iR, after commuting addition and multiplication. Index J returns alpha. The sole remaining valid index is J+1 and returns beta; the grammar forces eta to be one in that case. When eta is zero there is no extra beta tag: its original code already belongs to the branch interval.

Correctness is proved by induction on the finite recursion depth. Every child address has one fewer letter, so the induction hypothesis applies simultaneously to both digits. The branch equation and the product equivalence recover i. The two leaf cases use the exact original grammar. A separate induction bounds height by the available recursion depth: leaves have height zero and pairing adds one to the maximum of the child heights. Thus the bound concerns actual tree height, rather than FreeMagma.length.

**Theorem 1.1 (Total original-rank representatives and height).**

$$\forall S: Menu, (\forall i: Nat, (((\operatorname{N}\left(S\right) \leq i) \implies (\operatorname{unrank}\left(S, i\right) = \operatorname{of}\left(true\right))) \land ((S = \operatorname{nil}\left(\right)) \implies ((\operatorname{unrank}\left(S, i\right) = \operatorname{of}\left(true\right)) \land (\operatorname{height}\left(\operatorname{unrank}\left(S, i\right)\right) = 0))) \land ((i < \operatorname{N}\left(S\right)) \implies (\operatorname{code}\left(S, \operatorname{unrank}\left(S, i\right)\right) = i)) \land ((S \neq \operatorname{nil}\left(\right)) \implies (\operatorname{height}\left(\operatorname{unrank}\left(S, i\right)\right) \leq 1 + \operatorname{sup}\left(\operatorname{toFinset}\left(S\right), \operatorname{length}\left(\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuUnranking.original_menu_unranking` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every valid original label is attained by the returned tree, without an attained-vector input, a source-height hypothesis or prefix closure. The empty menu always returns height-zero alpha. The nonempty height bound holds even for invalid indices, since their fixed default is alpha.

This is the representative and height part of the finite-menu normal form. It supplies common native realizations of branch digit pairs. It does not establish the converse trajectory classification, a minimum retained alphabet, or physical, runtime and memory optimality.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuUnranking.original_menu_unranking`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate](../ActualImageAddressCertificate.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuCode](NativeFiniteMenuCode.md)
