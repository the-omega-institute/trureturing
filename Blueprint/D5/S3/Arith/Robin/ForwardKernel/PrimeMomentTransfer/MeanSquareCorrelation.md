# Mean-square prime correlations

## Abstract

Mean-square raw correlation errors yield total absolute error estimates.

Chan, A note on primes in short intervals, International Journal of Number Theory 2 (2006), 105–110, DOI 10.1142/S1793042106000437, supplies the mean-square weakening for single-interval moments. The finite-set formulation here is used for overlapping mixed moments. Only cutoffs between N and 2N occur in the hypothesis.

**Definition 1.1 (Raw finite-set correlation error).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MeanSquareCorrelation.correlationError`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MeanSquareCorrelation.correlationError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real-valued function SS on finite natural shift sets, a real cutoff y and a finite set D, the raw error is the sum over positive integers n at most floor y of the product of von Mangoldt(n+d) for d in D, minus y SS(D).

**Definition 1.2 (Mean-square hypothesis through a prescribed order).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MeanSquareCorrelation.MeanSquareHL`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MeanSquareCorrelation.MeanSquareHL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural maximal order q, MeanSquareHL(q,SS,beta) requires the uniform mean-square raw error bound C N^(1+2 epsilon) K^r for every order 1<=r<=q. For each epsilon>0 and M>=1, one positive C and one threshold work for all such r, natural 1<=K<=M N^beta and real N<=y<=2N.

**Definition 1.3 (The four-point mean-square instance).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MeanSquareCorrelation.MeanSquareHL4`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MeanSquareCorrelation.MeanSquareHL4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each positive epsilon and each real M at least one, there are a positive C and a real threshold N0 such that, for every real N at least N0, every integer order r from one through four, every natural K with 1<=K<=M N^beta, and every real y with N<=y<=2N, the sum of squared absolute raw errors over all injective ordered r-tuples in {1,...,K} is at most C N^(1+2 epsilon) K^r. The raw error is exactly the ordered correlation error in HL4.

**Theorem 1.4 (Absolute errors over unordered shift sets).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MeanSquareCorrelation.meanSquare_correlation_l1`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MeanSquareCorrelation.meanSquare_correlation_l1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume MeanSquareHL(q,SS,beta). For every positive epsilon and M>=1 there is A>=0 such that, for all sufficiently large real N>=2, all r from one through q, all natural 1<=K<=M N^beta, and N<=y<=2N, the sum of absolute correlationError(SS,y,D) over all r-element subsets D of {1,...,K} is at most A N^(1/2+epsilon) K^r. Every such subset has an injective enumeration. Cauchy–Schwarz and the bound K^r on their number supply the estimate.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MeanSquareCorrelation.MeanSquareHL`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MeanSquareCorrelation.MeanSquareHL4`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MeanSquareCorrelation.correlationError`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MeanSquareCorrelation.meanSquare_correlation_l1`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ArithmeticTransferDefs](ArithmeticTransferDefs.md)
