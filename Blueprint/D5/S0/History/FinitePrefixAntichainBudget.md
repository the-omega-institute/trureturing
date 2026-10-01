# Finite Prefix Antichain Budget

## Abstract

Finite prefix antichains inherit local child budgets at the root.

**Theorem 1.1 (Local budgets bound every finite prefix antichain).**

$$\sum_{h\in K} m(h)\leq m(nil)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/FinitePrefixAntichainBudget.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be any type with decidable equality and V an additive commutative monoid with a preorder preserved by addition. Suppose that, for every word h and every finite set C of letters, the sum of m(h ++ [a]) over a in C is at most m(h). For every finite set K of words such that a prefix relation between two members forces equality, the sum of m over K is then at most m of the empty word. No finite alphabet, subtraction, scalar multiplication, lattice or topology is assumed.

The proof inducts on a finite upper bound for word lengths. A member equal to the empty word forces a singleton. Otherwise the words partition by their occurring first letters. Removing that letter gives shorter prefix antichains; the shifted budget inherits the local hypothesis. Finite sum regrouping and monotonicity combine their inductive bounds, and the root local bound finishes. The empty antichain is included because the empty child selection implies nonnegativity. This is a mathematical supplier, not a claim that an actual controller satisfies its hypothesis.

## References

- Truth anchor: `D5/S0/History/FinitePrefixAntichainBudget.result`
