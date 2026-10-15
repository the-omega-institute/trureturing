# Finite first entry into actual closed classes

## Abstract

FiniteEntranceDecomposition

Let P be a finite real row-stochastic matrix. Its actual terminal communicating classes C are disjoint, and their complement T is the transient state type. Q is the restriction of the original P to T; R_C is its restriction to C. Write s_m(x) for the row sum of Q^m at a transient start x. All restrictions and classes are determined by P, including when the ambient or transient type is empty.

The first-entry weight e_C(n,x,z) is sum over v in T of Q^n(x,v) P(v,z). It records exactly n transient steps followed by entry into C at time n+1. The killed powers agree with the original powers at transient targets, and closed classes cannot return to the transient set or enter a different class.

For every natural horizon H and target y in C, P^H(x,y) equals sum over n<H and z in C of e_C(n,x,z) R_C^(H-(n+1))(z,y). The horizon zero sum is empty. At horizon one the class power is the identity and the weight is e_C(0,x,y)=P(x,y). The formula follows by separating the last transition into an entrance from T and evolution within C, then inducting on H.

Summing the formula over targets in C gives sum over n<H and z in C of e_C(n,x,z) = sum over y in C of P^H(x,y). Thus cumulative first-entry mass is precisely the original matrix's probability of occupying C at that horizon.

All weights are nonnegative. For each x,C,z their series has sum equal to sum over v in T of (I-Q)^(-1)(x,v) P(v,z). Summability follows from the substochastic Neumann series and finite sums, with the actual escape bound of Q.

At time n+1, the sum of entry weights over all classes and entrance states is s_n(x)-s_(n+1)(x). Consequently the mass of entry by time H is 1-s_H(x), the full first-entry law has total probability one, and the mass of entry at time M+1 or later equals s_M(x). The latter tends to zero because every entry of Q^M tends to zero and the state type is finite.

The contribution to P^H(x,y) from entry times M+1 through H is the sum over n<H-M and z in C of e_C(n+M,x,z) R_C^(H-(n+M+1))(z,y). It is nonnegative and at most s_M(x), uniformly in H,C,y. This bound uses that every class-power entry lies between zero and one.

For a genuine period p and phase map phi on C, psiTransient(x,j) sums e_C(n,x,z) exactly when phi(z)-(n+1)=j modulo p. Each filtered series is summable and every phase mass is nonnegative. Summing over j gives the absorption probability of C, sum over z in C and n of e_C(n,x,z); it need not equal one for an individual class. The entry-time shift remains n+1 throughout.

**Theorem 1.1 (Actual finite first-entry law).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteEntranceDecomposition.actual_entrance`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteEntranceDecomposition.actual_entrance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

EntranceLaw contains the convolution, class-occupancy identity, entrywise series, step and cumulative mass identities, total probability one, exact vanishing tail, uniform late-contribution bound, and phase-series facts under precisely the row-stochastic hypothesis.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteEntranceDecomposition.actual_entrance`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteClosedClassLimits](FiniteClosedClassLimits.md)
