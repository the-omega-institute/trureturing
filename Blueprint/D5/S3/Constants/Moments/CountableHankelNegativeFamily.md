# Uniform complete-spectrum negative polynomial families

## Abstract

Uniform complete-spectrum negative polynomial families

**Theorem 1.1 (A common head and exponent control every real combination).**

Lean statement: `D5/S3/Constants/Moments/CountableHankelNegativeFamily.exists_real_negative_family`

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CountableHankelNegativeFamily.exists_real_negative_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every index type iota, complex node and weight maps z,w, and permutation c, assume every node has norm at most one, z is injective, z(c(i)) is conjugate(z(i)), w(c(i)) is conjugate(w(i)), the norms of all weights are summable, and every positive-radius node superlevel set is finite. For every natural k and selector s from Fin k to iota, require s injective, s(a) unequal to c(s(b)) for every a,b, and every selected weight nonzero. There exists one real polynomial family p indexed by Fin k such that, for every real vector t on Fin k, the real part of the complete sum over i of w(i) times the ordinary complex square of the evaluation of sum_j t(j) p(j) is at most minus sum_j t(j) squared. This includes t=0 and k=0.

Pair separation and node injectivity imply each selected node is nonreal, and hence nonzero; neither is an extra assumption. For k greater than zero take rho to be the minimum selected node norm. The one finite head contains every node with norm at least rho/4 and is conjugation closed. The existing pair_polynomial and peak constructions are reused for every selected pair on this same head. Choose b(j) with w(s(j)) b(j) squared equal to minus one. Every peak uses the same exponent m. Disjoint pairs make the head form exactly minus twice sum_j t(j) squared.

Outside the head each row evaluation is bounded by B(j) times (1/4) to power m. Finite Cauchy-Schwarz bounds the squared norm of every combined evaluation by sum_j B(j) squared times (1/16) to power m times sum_j t(j) squared. Absolute summability controls the entire complement by its common absolute mass W. One m makes W times sum_j B(j) squared times (1/16) to power m less than one, independently of t. The proof uses square_summable before splitting the full sum. No finite spectrum replaces the original one.

This conditional negative-subspace construction does not assert that any such pair exists for a zeta spectrum and proves no Riemann hypothesis statement. Repeated analytic multiplicities must already be combined into the exact existing weights; the selector requires distinct nodes. The existence argument is classical and supplies no effective degree or coefficient search bound.

## References

- Truth anchor: `D5/S3/Constants/Moments/CountableHankelNegativeFamily.exists_real_negative_family`
- Dependency: [D5/S3/Constants/Moments/CountableHankelNegativeWitness](CountableHankelNegativeWitness.md)
