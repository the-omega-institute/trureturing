# Ordered logarithmic energy

## Abstract

Noncommuting logarithmic increments and a positive extended energy identity.

**Theorem 1.1 (A single-operator logarithmic difference).**

$$\forall H \in CompleteComplexHilbertSpace, A \in \operatorname{BoundedComplexOperator}\left(H\right), c \in Real,\; \left(\operatorname{IsStrictlyPositive}\left(A\right) \land \operatorname{Nonnegative}\left(c\right)\right) \Rightarrow \operatorname{subtract}\left(\operatorname{operatorLog}\left(\operatorname{addScalarIdentity}\left(A, c\right)\right), \operatorname{operatorLog}\left(A\right)\right) = \operatorname{operatorLog}\left(\operatorname{add}\left(1, \operatorname{realSmul}\left(c, \operatorname{ringInverse}\left(A\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/OrderedEnergy.log_add_sub_log_eq_log_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

For an actually strictly positive bounded operator A and c>=0, log(A+cI)-log(A)=log(I+c Ring.inverse(A)). The real spectrum of A is strictly positive. On that spectrum, the assertion is the scalar identity log(x+c)-log(x)=log(1+c/x). The CFC addition, inverse and composition theorems transfer this single-variable identity. All logarithm inputs have positive spectra. No product law for noncommuting operators is used, and c=0 is included.

**Theorem 1.2 (Ordered increments increase at smaller epsilon).**

$$\forall H \in CompleteComplexHilbertSpace, a \in Real, b \in Real, P \in \operatorname{BoundedComplexOperator}\left(H\right), Q \in \operatorname{BoundedComplexOperator}\left(H\right),\; \left(\operatorname{Positive}\left(a\right) \land \left(a \le b \land \left(\operatorname{Nonnegative}\left(P\right) \land P \le Q\right)\right)\right) \Rightarrow \operatorname{orderedIncrement}\left(b, P, Q\right) \le \operatorname{orderedIncrement}\left(a, P, Q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/OrderedEnergy.orderedIncrement_parameter_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

For 0<=P<=Q and 0<a<=b, define R_e=log(Q+eI)-log(P+eI). Logarithm monotonicity makes R_e nonnegative. With c=b-a, the single-operator difference formula identifies each shift difference with log(I+c Ring.inverse(T+aI)). Actual inverse order gives inverse(Q+aI)<=inverse(P+aI). Multiplication by c and operator logarithm monotonicity therefore order the shift differences. Rearranging yields R_b<=R_a, without assuming P and Q commute. Every shifted input is actually strictly positive.

**Theorem 1.3 (Trace-norm lower semicontinuity).**

$$\forall H \in CompleteComplexHilbertSpace, P \in \operatorname{Reference}\left(H\right), Q \in \operatorname{Reference}\left(H\right),\; \operatorname{LowerSemicontinuous}\left(\operatorname{orderedEnergy}\left(P, Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/OrderedEnergy.lowerSemicontinuous_orderedEnergy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

orderedEnergy(P,Q,rho) is the ENNReal supremum of ofReal(Re Tr(R_epsilon_n rho)), with epsilon_n=1/(n+1). Each bounded observable pairs continuously with the actual trace-class Banach space. The supremum is lower semicontinuous in rho's trace norm. For ordered references and positive rho, these are actual nonnegative increasing expectations.

**Theorem 1.4 (Global singular energy decomposition).**

$$\forall H \in CompleteComplexHilbertSpace, P \in \operatorname{Reference}\left(H\right), Q \in \operatorname{Reference}\left(H\right), rho \in \operatorname{TraceClass}\left(H\right),\; \left(\operatorname{operator}\left(P\right) \le \operatorname{operator}\left(Q\right) \land \operatorname{Nonnegative}\left(rho\right)\right) \Rightarrow \operatorname{spectralEnergy}\left(P, rho\right) = \operatorname{add}\left(\operatorname{orderedEnergy}\left(P, Q, rho\right), \operatorname{spectralEnergy}\left(Q, rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/OrderedEnergy.spectralEnergy_eq_orderedEnergy_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

For positive trace-class contraction references P<=Q and any positive trace-class rho, the SAME singular spectral energy satisfies E_P(rho)=F_(P,Q)(rho)+E_Q(rho) in ENNReal. The operator equality B_e(P)=R_e+B_e(Q) holds with the common positive regularization log(1+e)I-log(T+eI). Actual bounded trace additivity and positivity turn it into an ENNReal equality at each e. Both sequences increase on the same grid, so synchronized supremum addition gives the identity. It includes either or both singular energies being infinite and uses no subtraction of infinite values.

**Theorem 1.5 (Equal singular references).**

$$\forall H \in CompleteComplexHilbertSpace, P \in \operatorname{Reference}\left(H\right), rho \in \operatorname{TraceClass}\left(H\right),\; \operatorname{orderedEnergy}\left(P, P, rho\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/OrderedEnergy.orderedEnergy_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathlib contributors (2026). *Operator logarithms through the continuous functional calculus*. URL: <https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog>.

*Commentary.*

When P=Q, every actual increment is zero and F_(P,P)(rho)=0, even when E_P(rho) is infinite. Support inclusion alone supplies no finiteness conclusion. The decomposition is a supplier for common-reference continuity; local entropy-center construction and the final full-Hilbert-space Hamiltonian remain additional obligations.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/OrderedEnergy.log_add_sub_log_eq_log_inverse`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/OrderedEnergy.lowerSemicontinuous_orderedEnergy`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/OrderedEnergy.orderedEnergy_self`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/OrderedEnergy.orderedIncrement_parameter_antitone`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/OrderedEnergy.spectralEnergy_eq_orderedEnergy_add`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy](SpectralEnergy.md)
