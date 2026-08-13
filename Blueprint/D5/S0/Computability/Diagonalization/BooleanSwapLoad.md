# The Load Carried by the Boolean Swap

## Abstract

Boolean negation is exactly the operation that carries universal self-diagonal escape.

**Theorem 1.1 (The Boolean swap carries universal diagonal escape).**

$$\forall \sigma: Bool\to Bool, ((\forall (History : Type) (V : History\to History\to Bool) (h : History), \sigma(V(h,h)) \neq V(h,h)) \iff \sigma = \operatorname{Bool.not})\\ \land \neg(\forall (History : Type) (V : History\to History\to Bool) (h : History), \operatorname{id}(V(h,h)) \neq V(h,h)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Diagonalization/BooleanSwapLoad.boolean_swap_carries_diagonal_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let sigma be an operation on the minimal binary carrier Bool. The first conjunct isolates the engine shared by the source diagonal consequences: for every history type, every total Boolean evaluator V, and every self-coordinate h, applying sigma to V(h,h) changes that value exactly when sigma is Boolean negation.

The second conjunct records the source's deletion test explicitly. Replacing the swap by identity fails on the constant-false evaluator over Unit, so the diagonal contradiction has no statement after the swap is removed. Conversely, Bool.not_ne_self supplies the mismatch for negation; testing any universally escaping operation on the two constant diagonals forces both of its values and hence forces the operation itself to be Bool.not.

The neighboring DiagonalSwap theorem proves the forward mismatch for a fixed natural-number assignment. This theorem quantifies over every history type and evaluator, proves the converse characterization, and includes the identity deletion witness, so it is not a renamed duplicate.

## References

- Truth anchor: `D5/S0/Computability/Diagonalization/BooleanSwapLoad.boolean_swap_carries_diagonal_escape`
- Dependency: [D5/S0/Conventions/DiagonalSwap](../../Conventions/DiagonalSwap.md)
