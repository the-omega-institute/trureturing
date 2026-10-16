# Closed-class stationary rows and periodic limits

## Abstract

FiniteClosedClassLimits

For every actual closed class C of an arbitrary finite real row-stochastic matrix P, the theorem constructs its genuine period data K, proves Blocks(K), and supplies ClassLimit(K). Put A=restriction(P,C), p=period(A,K.base) and phi=K.phase. The stationaryRow pi:C->Real is nonnegative, sums to one and satisfies pi vecMul A=pi. It is the unique row with these three properties, and pi(y)>0 for every y in C.

**Theorem 1.1 (Closed-class stationary rows and periodic limits).**

$$\forall X:Type, ([\operatorname{Fintype}(X)][\operatorname{DecidableEq}(X)]\forall P:\operatorname{Matrix}(X, X, \mathbb{R}), (\operatorname{RowStochastic}(P)\implies \forall C:\operatorname{ClosedClass}(P), (\exists K:\operatorname{ClassPeriods}(P, C), \operatorname{Blocks}(K)\land \operatorname{Nonempty}(\operatorname{ClassLimit}(K)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteClosedClassLimits.actual_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every j in ZMod(p), the sum of pi(y) over the actual phase phi(y)=j is 1/p. For every positive natural d with p dividing d, every natural i, and all starts x and targets y in C, the actual ambient (P^(d*n+i))(x,y) tends as n tends to infinity to p*pi(y) if phi(x)+i=phi(y), and to zero otherwise. No restriction i<d or minimality of d is present. Blocks(K) additionally gives identically zero contributions from starts in distinct actual closed classes.

Stationary existence directly uses FiniteStochasticMixing.stationary_distribution_exists, whose original Cesaro argument consumes the existing native stationary suppliers. Its original multi_step_stationary propagates stationarity to all powers. Each positive return class is nonempty, so this application asserts no normalized row on an empty state type. Positive mass at one state and an actual positive path to any target, combined with power stationarity, prove strict positivity.

The exact phase-row sum is one precisely for the allowed residue and zero otherwise. Applying the stationary equation moves each phase mass to the next phase. Surjective cyclic labels and normalization give equal masses 1/p. Consequently p*pi restricted to each phase is a stationary probability row of its actual p-step block. FiniteStochasticMixing.primitive_convergence on the proved blocks identifies this row, proves phase convergence and yields uniqueness of the original class row.

Write d=p*q with q>0. The identity P^(d*n+i)=P^i P^(p*q*n), restricted to C, expresses each entry as a finite sum over the target phase. Actual block powers give the second factor; primitive convergence along q*n gives p*pi(y). The first factor sums to one or zero by the exact phase-row law, proving the stated ambient limit for every natural i.

These assertions supply the genuine-period, stationary-row and recurrent-start inputs to PH38.2. They do not assert transient-start first-entry convolution, lifted-chain absorption probabilities, a simultaneous arithmetic denominator or its cardinality bound. No denominator depending on d, escape times or minimum positive transitions is introduced. Phase indices are used only for mathematical analysis and establish no clock or installation-cost waiver.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteClosedClassLimits.actual_limits`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteCyclicBlocks](FiniteCyclicBlocks.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteStochasticMixing](FiniteStochasticMixing.md)
