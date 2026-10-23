# Pointwise minimax upper bounds for ground energy

## Abstract

Finite atomic probability laws admit a deterministic ground-energy estimator with a uniform dimension and precision rate.

**Definition 1.1 (The original measure class).**

Lean statement: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.AtomicLaw`

*Formalization.* `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.AtomicLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real Elo, Ehi, eta, natural d, Borel measure mu and ground g, AtomicLaw means mu is a probability measure, mu({g}) >= ofReal(eta), and its actual topological support equals a finite set s with card(s) <= d, g in s, and every support point x in [Elo,Ehi] with g <= x. Repeated atomic labels are represented by their combined measure mass.

**Definition 1.2 (Measure-valued Laplace observations).**

Lean statement: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.measureCurve`

*Formalization.* `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.measureCurve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every Borel measure mu and real time t, measureCurve(mu,t) is the Bochner integral of exp(-t x) against mu.

**Definition 1.3 (The joint dimension and precision rate).**

Lean statement: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.rateAll`

*Formalization.* `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.rateAll` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural d and real epsilon, rateAll is the supremum over integers 1 <= m <= d of epsilon^(1/(2m-1))/m^2, using real powers. In the theorems d >= 1 and epsilon > 0, so this is the maximum of a nonempty finite family.

**Definition 1.4 (The window rate).**

Lean statement: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.rateWindow`

*Formalization.* `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.rateWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural d and real epsilon and U, rateWindow is the supremum over 1 <= m <= d of min(1,epsilon^(1/(2m-1))*max(1,(2m-1)/U))/m^2. The minimax theorem uses U=Ehi*T > 0.

**Definition 1.5 (Deterministic pointwise minimax risk).**

Lean statement: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.minimaxRisk`

*Formalization.* `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.minimaxRisk` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* C. A. Micchelli and T. J. Rivlin (1977). *A Survey of Optimal Recovery*. DOI: [10.1007/978-1-4684-2388-4_1](https://doi.org/10.1007/978-1-4684-2388-4_1). URL: <https://doi.org/10.1007/978-1-4684-2388-4_1>.

*Commentary.*

For every parameter tuple Elo,Ehi,eta,d,D,epsilon, minimaxRisk is the infimum over all estimators G:(D -> real)->real of the supremum of ofReal(|G(Y)-g|), over every AtomicLaw mu,g and every arbitrary observation function Y on D with |Y(t)-measureCurve(mu,t)| <= epsilon at each t. The risk uses extended nonnegative reals. No continuity, stochastic noise law or computational restriction is imposed on Y or G.

**Lemma 1.6 (Exact finite reconstruction of the measure).**

Lean statement: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.atomic_law_representation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.atomic_law_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every AtomicLaw has g in [Elo,Ehi] and a nonnegative finitely supported real weight function w of total mass 1, supported in [g,Ehi], with w(g) >= eta and at most d support points. The original measure equals sum_x ofReal(w(x)) dirac(x), and for every real t its measureCurve equals atomicLaplace(w,t). This is an exact representation, including support collisions and all times.

**Definition 1.7 (Ground energies compatible with one observation).**

Lean statement: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.compatibleGrounds`

*Formalization.* `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.compatibleGrounds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every observation Y on D, compatibleGrounds is the set of all g for which some AtomicLaw mu,g obeys the pointwise epsilon noise constraint for that same Y.

**Definition 1.8 (The midpoint of the compatible grounds).**

Lean statement: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.midpointEstimator`

*Formalization.* `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.midpointEstimator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* C. A. Micchelli and T. J. Rivlin (1977). *A Survey of Optimal Recovery*. DOI: [10.1007/978-1-4684-2388-4_1](https://doi.org/10.1007/978-1-4684-2388-4_1). URL: <https://doi.org/10.1007/978-1-4684-2388-4_1>.

*Commentary.*

The estimator assigns Y the midpoint of the infimum and supremum of compatibleGrounds, with value Elo when that set is empty. For every feasible Y the set is nonempty and bounded by [Elo,Ehi].

**Theorem 1.9 (One estimator works for every feasible law and observation).**

Lean statement: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.exists_window_estimator`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.exists_window_estimator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. A. Micchelli and T. J. Rivlin (1977). *A Survey of Optimal Recovery*. DOI: [10.1007/978-1-4684-2388-4_1](https://doi.org/10.1007/978-1-4684-2388-4_1). URL: <https://doi.org/10.1007/978-1-4684-2388-4_1>.

*Commentary.*

For every 0 <= Elo < E, 0 < eta < 1, d >= 1, T > 0 and epsilon > 0, there exists one estimator G on arbitrary functions on [0,T] such that for every AtomicLaw mu,g and every pointwise epsilon-accurate observation Y, |G(Y)-g| <= (1024E/eta^2) rateWindow(d,epsilon,E*T). The midpoint estimator supplies this common choice; the joint Laplace certificate bounds the diameter of its compatible set.

**Theorem 1.10 (A uniform finite-window minimax upper bound).**

Lean statement: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.minimax_window_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.minimax_window_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. A. Micchelli and T. J. Rivlin (1977). *A Survey of Optimal Recovery*. DOI: [10.1007/978-1-4684-2388-4_1](https://doi.org/10.1007/978-1-4684-2388-4_1). URL: <https://doi.org/10.1007/978-1-4684-2388-4_1>.

*Commentary.*

For every 0 <= Elo < E, 0 < eta < 1, d >= 1, T > 0 and epsilon > 0, minimaxRisk on [0,T] is at most ofReal((1024E/eta^2) rateWindow(d,epsilon,E*T)). The constant is independent of d and T. This holds also when E*T < 1 and epsilon >= 1.

**Theorem 1.11 (A uniform all-time minimax upper bound).**

Lean statement: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.minimax_all_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.minimax_all_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. A. Micchelli and T. J. Rivlin (1977). *A Survey of Optimal Recovery*. DOI: [10.1007/978-1-4684-2388-4_1](https://doi.org/10.1007/978-1-4684-2388-4_1). URL: <https://doi.org/10.1007/978-1-4684-2388-4_1>.

*Commentary.*

For every 0 <= Elo < E, 0 < eta < 1, d >= 1 and epsilon > 0, minimaxRisk on all t >= 0 is at most ofReal((1024E/eta^2) rateAll(d,epsilon)). In particular the dimension-precision matching upper-bound question holds for all 0 < epsilon < 1 with epsilon0=1. The result concerns finite atomic probability laws with a prescribed ground mass; it makes no bound for an unrestricted positive residual tail.

## References

- Truth anchor: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.AtomicLaw`
- Truth anchor: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.atomic_law_representation`
- Truth anchor: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.compatibleGrounds`
- Truth anchor: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.exists_window_estimator`
- Truth anchor: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.measureCurve`
- Truth anchor: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.midpointEstimator`
- Truth anchor: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.minimaxRisk`
- Truth anchor: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.minimax_all_upper`
- Truth anchor: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.minimax_window_upper`
- Truth anchor: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.rateAll`
- Truth anchor: `D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.rateWindow`
- Dependency: [D5/S3/Analytic/Interpolation/UniformCoefficientBudget](../Interpolation/UniformCoefficientBudget.md)
