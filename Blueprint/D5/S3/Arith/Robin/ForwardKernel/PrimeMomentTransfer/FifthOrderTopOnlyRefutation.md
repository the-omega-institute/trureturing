# Fifth-order top-only transfer fails

## Abstract

The top distinct-index fifth moment alone does not imply fifth-moment transfer.

**Definition 1.1 (The proposed fifth-moment implication).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FifthOrderTopOnlyRefutation.claim`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FifthOrderTopOnlyRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every fixed real C at least one and every sequence of finite algebraic moment data, assume ell(1)=1, ell(y times y) is nonnegative for every algebra element y, ell(Y_d)=0, Y_d squared equals a times Y_d plus b times one, one at most L at most H, absolute values of a and b at most C L, and index cardinality at most C H. At each order r from two through four, every real coefficient family bounded in absolute value by one has distinct-index moment at most C times sqrt(H L) to the r in absolute value. Every bounded coefficient family of order five has distinct-index moment zero. The asserted implication says that L/H tending to zero forces the full fifth moment with all coefficients one, divided by sqrt(H L) to the fifth, to tend to zero.

**Theorem 1.2 (Refutation by a positive probability model).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FifthOrderTopOnlyRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FifthOrderTopOnlyRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set N=n+9, H=N, L=1, a=0, b=1 and C=11. First sample Z taking values minus two, one and three with probabilities 8/22, 13/22 and 1/22. Conditional on Z, sample N independent signs with mean Z/sqrt(N). Since N is at least nine, these are probability distributions. Let Y_d be the coordinate signs and ell be expectation. Thus ell(1)=1, ell(y squared) is nonnegative, ell(Y_d)=0 and Y_d squared equals one.

The moments of Z at orders zero through five are 1, 0, 27/11, minus 12/11, 111/11 and 0. Every product of r distinct coordinate signs has expectation E(Z to the r)/sqrt(N) to the r. This gives the required lower distinct-moment bounds with C=11, while every distinct fifth moment is exactly zero.

In a product of five coordinate signs, even multiplicities cancel. The number of coordinates with odd multiplicity is one, three or five; only three gives a nonzero expectation, namely minus 12/(11 sqrt(N) cubed). Every ordered injective quadruple produces such a tuple by repeating its first coordinate twice and taking the remaining three coordinates once. There are at least N(N-1)(N-2)(N-3) such tuples. Dividing by N to the fourth gives at least 8/27, since each of the last three factors is at least 2N/3. Consequently the full fifth moment divided by sqrt(N) to the fifth is at most minus 3/11 for every n. It cannot tend to zero, although L/H does.

This positive probability model gives the fifth-order obstruction in Proposition 500.4 of FIBONACCI_ANALYTIC_FRONTIER_INTERFACES_II. The construction and its mathematical interpretation are repository-derived.

The biased-cube mixture construction is shared with the sixth-order refutation. The fifth-order example uses an asymmetric mixing law; the sixth-order example uses a symmetric law and isolates the missing fourth-order pairing defect.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FifthOrderTopOnlyRefutation.claim`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FifthOrderTopOnlyRefutation.result`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas](MixtureMomentLemmas.md)
