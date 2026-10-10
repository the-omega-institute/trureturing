# Exterior Discrepancy and Common Balance

## Abstract

One deterministic majority classifier balances all teachers in every rare-count class.

For each reduced word, exteriorSelector selects a label with maximal total teacher votes. Outside the reservoir, Ez(m,z,i) is the sum of left-teacher error minus right-teacher error over words with z rare symbols. The subtraction compares the two teachers at the same prefix coordinate i.

Write L(m) for the sum of the positive prefix slices of length m-1 through floor(m/3). The complete exterior discrepancy polynomial is 2 X squared times (2+X), multiplied by ((2+3X)L(m) minus 4((2+3X)^(m-1)-(2+X)^(m-1))). Its coefficient at z is Ez(m,z,i), independently of i.

Positive prefix fibers split according to one endpoint bit. Coin balance halves each fiber uniformly. Pairing the anchor configurations then gives the same signed discrepancy for each teacher. The zero-prefix fiber cancels separately.

The reservoir and discrepancy polynomials have even integer coefficients; coefficient extraction identifies their halves with the capacity sequences. The two-sided capacity bound makes the required reservoir split a legal integer in every rare-count class.

In each rare-count class choose a reservoir subset of the required size. A single classifier labels this subset two and its reservoir complement zero, and uses the exterior majority selector elsewhere. Both reservoir labels maximize votes. Prefix permutation symmetry equalizes positions, and the split equation equalizes the two layers. This gives an existence construction, with no computable or lexicographic selection rule asserted.

**Theorem 1.1 (One majority classifier with classwise equal errors).**

$$\forall \left(m: Nat\right), \left(0 < m\right) \implies \left(\exists \left(f: \operatorname{Function}\left(\operatorname{Input}\left(m+3\right), \operatorname{Fin}\left(3\right)\right)\right), \left(\forall \left(x: \operatorname{Input}\left(m+3\right)\right), \forall \left(c: \operatorname{Fin}\left(3\right)\right), \operatorname{actualVotes}\left(x, c\right) \le \operatorname{actualVotes}\left(x, \operatorname{f}\left(x\right)\right)\right) \land \left(\forall \left(z: Nat\right), \forall \left(i: \operatorname{Fin}\left(m\right)\right), \forall \left(j: \operatorname{Fin}\left(m\right)\right), \left(\operatorname{errorCount}\left(z, false, i, f\right) = \operatorname{errorCount}\left(z, false, j, f\right)\right) \land \left(\operatorname{errorCount}\left(z, false, i, f\right) = \operatorname{errorCount}\left(z, true, j, f\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionExteriorCapacity.uniform_mass_balanced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the coin fibers and extracting coefficients gives the actual exterior error difference. The capacity estimate then supplies each reservoir split. The same classifier is a pointwise majority choice and balances both layers at every position, simultaneously for all rare-count classes.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionExteriorCapacity.uniform_mass_balanced`
- Dependency: [D5/S3/Arith/FibonacciAtomic/HeterogeneousTeacherSeparation](../HeterogeneousTeacherSeparation.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts](CommonPredictionWordCounts.md)
