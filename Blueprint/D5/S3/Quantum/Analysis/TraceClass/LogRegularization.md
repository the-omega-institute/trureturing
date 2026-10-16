# Positive trace pairing and logarithmic regularization

## Abstract

Actual bounded logarithmic trace energies on positive trace-class contractions.

**Theorem 1.1 (Strict positivity of every positive shift).**

$$\operatorname{PositiveShiftOfNonnegativeOperatorIsStrictlyPositive}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.shift_strictlyPositive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

For every bounded nonnegative operator T and every positive real epsilon, T+epsilon I is strictly positive. The nonnegative-add rule and strict positivity of the positive scalar operator prove this directly. Shifted CFC logarithms therefore have no singular spectrum at zero.

**Theorem 1.2 (Noncommuting positive trace pairing).**

$$\forall H \in CompleteComplexHilbertSpace, A \in \operatorname{BoundedComplexOperator}\left(H\right), rho \in \operatorname{TraceClass}\left(H\right),\; \left(\operatorname{Nonnegative}\left(A\right) \land \operatorname{Nonnegative}\left(rho\right)\right) \Rightarrow \operatorname{Nonnegative}\left(\operatorname{Re}\left(\operatorname{tracePairing}\left(A, rho\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.tracePairing_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

For a bounded positive A and a positive trace-class rho, Re Tr(A rho) is nonnegative. With R equal to sqrt A, the trace-class ideal makes R rho trace class. Bounded-factor cyclicity gives Tr(A rho) = Tr(R rho R), and the latter operator is positive. The argument retains self-adjointness of R and requires no commutation or trace-class square root of rho.

Positivity and normalization also imply rho is an operator contraction: the trace norm equals the real trace, and the operator norm is bounded by the trace norm.

**Theorem 1.3 (Lower semicontinuity of the regularized supremum).**

$$\forall H \in CompleteComplexHilbertSpace, rho \in \operatorname{TraceClass}\left(H\right),\; \operatorname{LowerSemicontinuous}\left(\operatorname{regularizedSupremumAt}\left(rho, \operatorname{Reference}\left(H\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.lowerSemicontinuous_regularizedSupremum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

The reference space consists of actual positive trace-class contractions and carries the topology from the genuine trace norm. For epsilon positive, B_epsilon(T) = log(1+epsilon) I - log(T+epsilon I) is a bounded positive self-adjoint operator. The pairing Re Tr(B_epsilon(T) rho) is continuous in T for every fixed trace-class rho.

The auxiliary regularizedSupremum is the ENNReal supremum of these actual trace pairings at epsilon_n = 1/(n+1). Continuity of each term gives lower semicontinuity of the supremum. For positive rho the same supremum reverses Loewner order, including noncommuting references.

SpectralEnergy separately identifies this auxiliary supremum with an actual singular spectral series, while KernelEnergy identifies its actual kernel obstruction. The auxiliary definition alone supplies neither result. The logarithm theorems are supplied by pinned Mathlib, and the analytic trace-class infrastructure is attributed to Tom Ole Diem's Physlib.

**Theorem 1.4 (CFC action on actual eigenvectors).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{BoundedComplexOperator}\left(H\right), s \in Real, v \in H, f \in \operatorname{Function}\left(Real, Real\right),\; \left(\operatorname{IsSelfAdjoint}\left(T\right) \land \left(\operatorname{apply}\left(T, v\right) = \operatorname{smul}\left(\operatorname{complexOfReal}\left(s\right), v\right) \land \operatorname{ContinuousOn}\left(f, \operatorname{spectrumReal}\left(T\right)\right)\right)\right) \Rightarrow \operatorname{apply}\left(\operatorname{cfc}\left(f, T\right), v\right) = \operatorname{smul}\left(\operatorname{complexOfReal}\left(\operatorname{apply}\left(f, s\right)\right), v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.cfc_apply_eigenvector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

For a self-adjoint bounded operator T, a real scalar s, and any vector v satisfying T(v)=s v, the real continuous functional calculus sends v to f(s) v. Continuity is required only on the actual real spectrum. The zero-vector case is separate; a nonzero eigenvector supplies spectrum membership. The equality locus in the continuous functions on the compact spectrum is closed and contains constants, the coordinate function, sums and products, so Stone-Weierstrass induction proves the assertion. No compactness, basis, separability, inverse or spectral gap is required.

**Theorem 1.5 (Bounded logarithmic eigenvector action).**

$$\forall H \in CompleteComplexHilbertSpace, epsilon \in Real, T \in \operatorname{BoundedComplexOperator}\left(H\right), s \in Real, v \in H,\; \left(\operatorname{Positive}\left(epsilon\right) \land \left(\operatorname{Nonnegative}\left(T\right) \land \operatorname{apply}\left(T, v\right) = \operatorname{smul}\left(\operatorname{complexOfReal}\left(s\right), v\right)\right)\right) \Rightarrow \operatorname{apply}\left(\operatorname{logRegularization}\left(epsilon, T\right), v\right) = \operatorname{smul}\left(\operatorname{complexOfReal}\left(\operatorname{subtract}\left(\operatorname{log}\left(\operatorname{add}\left(1, epsilon\right)\right), \operatorname{log}\left(\operatorname{add}\left(s, epsilon\right)\right)\right)\right), v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.logRegularization_apply_eigenvector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

For epsilon>0 and an actual nonnegative operator T, B_epsilon(T) acts on an eigenvector v with real eigenvalue s by [log(1+epsilon)-log(s+epsilon)]v. The representation as a real CFC of T uses continuity of the shifted scalar logarithm on the actual nonnegative spectrum. The general CFC eigenvector theorem is applied directly, including zero vectors and zero eigenvalues.

**Theorem 1.6 (Order as the parameter decreases).**

$$\forall H \in CompleteComplexHilbertSpace, a \in Real, b \in Real, T \in \operatorname{BoundedComplexOperator}\left(H\right),\; \left(\operatorname{Positive}\left(a\right) \land \left(a \le b \land \left(\operatorname{Nonnegative}\left(T\right) \land T \le 1\right)\right)\right) \Rightarrow \operatorname{logRegularization}\left(b, T\right) \le \operatorname{logRegularization}\left(a, T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.logRegularization_parameter_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

For 0<a<=b and 0<=T<=I, B_b(T)<=B_a(T). On the real spectrum, 0<=x<=1 implies (1+b)/(x+b)<=(1+a)/(x+a); scalar logarithm monotonicity and genuine CFC order give the operator inequality.

**Theorem 1.7 (Increasing trace energy grid).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right), rho \in \operatorname{TraceClass}\left(H\right),\; \operatorname{Nonnegative}\left(rho\right) \Rightarrow \operatorname{Monotone}\left(\operatorname{regularizedEnergyGrid}\left(T, rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.monotone_regularizedEnergy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

For a positive trace-class rho, the real trace energies on epsilon_n=1/(n+1) increase with n. This follows from operator parameter order and positive trace pairing.

**Theorem 1.8 (Finite positive linearity).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right), rho \in \operatorname{TraceClass}\left(H\right), gamma \in \operatorname{TraceClass}\left(H\right), a \in Real, b \in Real,\; \left(\operatorname{Nonnegative}\left(rho\right) \land \left(\operatorname{Nonnegative}\left(gamma\right) \land \left(\operatorname{Nonnegative}\left(a\right) \land \operatorname{Nonnegative}\left(b\right)\right)\right)\right) \Rightarrow \operatorname{regularizedSupremum}\left(T, \operatorname{add}\left(\operatorname{smul}\left(\operatorname{complexOfReal}\left(a\right), rho\right), \operatorname{smul}\left(\operatorname{complexOfReal}\left(b\right), gamma\right)\right)\right) = \operatorname{add}\left(\operatorname{multiply}\left(\operatorname{ofReal}\left(a\right), \operatorname{regularizedSupremum}\left(T, rho\right)\right), \operatorname{multiply}\left(\operatorname{ofReal}\left(b\right), \operatorname{regularizedSupremum}\left(T, gamma\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.regularizedSupremum_nonneg_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

The actual bounded trace pairing is linear in rho. Nonnegativity permits ENNReal.ofReal to preserve the finite sums and scalar products. Both energy sequences are increasing on the same grid, so synchronized supremum addition yields the displayed formula. Zero coefficients and infinite energies obey ENNReal arithmetic, including zero times infinity. This finite formula makes no assertion about countable decompositions.

**Definition 1.9 (Positive contraction scaling).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right), w \in Real,\; \left(\operatorname{Positive}\left(w\right) \land w \le 1\right) \Rightarrow \operatorname{underlyingOperator}\left(\operatorname{scaleReference}\left(T, w\right)\right) = \operatorname{smul}\left(\operatorname{complexOfReal}\left(w\right), \operatorname{underlyingOperator}\left(T\right)\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.scaleReference` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

Multiplying the actual trace-class operator by a real w in (0,1] preserves positivity and the contraction inequality.

**Theorem 1.10 (Scaling a singular reference).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{Reference}\left(H\right), rho \in \operatorname{TraceClass}\left(H\right), w \in Real,\; \left(\operatorname{Nonnegative}\left(rho\right) \land \left(\operatorname{Positive}\left(w\right) \land w \le 1\right)\right) \Rightarrow \operatorname{regularizedSupremum}\left(\operatorname{scaleReference}\left(T, w\right), rho\right) = \operatorname{add}\left(\operatorname{regularizedSupremum}\left(T, rho\right), \operatorname{multiply}\left(\operatorname{ofReal}\left(\operatorname{Re}\left(\operatorname{trace}\left(rho\right)\right)\right), \operatorname{ofReal}\left(\operatorname{negate}\left(\operatorname{log}\left(w\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.regularizedSupremum_scaleReference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

For epsilon>0 the operator T+(epsilon/w)I is strictly positive even when T has a kernel. The supplied log-scalar theorem therefore gives B_epsilon(wT)=B_(epsilon/w)(T)+log((1+epsilon)/(w+epsilon))I. Every positive sequence tending to zero is cofinal for this energy supremum. Use epsilon_n=w/(n+1); the remaining scalar correction increases to -log w. Synchronized supremum addition then gives the formula with the actual unnormalized real trace mass. This result concerns the same auxiliary operator supremum; SpectralEnergy separately proves its identity with the singular eigenvalue series.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.cfc_apply_eigenvector`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.logRegularization_apply_eigenvector`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.logRegularization_parameter_antitone`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.lowerSemicontinuous_regularizedSupremum`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.monotone_regularizedEnergy`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.regularizedSupremum_nonneg_linear`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.regularizedSupremum_scaleReference`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.scaleReference`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.shift_strictlyPositive`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/LogRegularization.tracePairing_nonneg`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Pairing](Pairing.md)
