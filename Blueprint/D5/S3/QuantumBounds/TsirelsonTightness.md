# Tightness of the Fixed CHSH Witness

## Abstract

The positive Tsirelson value is the attained maximum state expectation of the fixed CHSH witness.

**Theorem 1.1 (The positive Tsirelson value is the greatest fixed-witness expectation).**

$$\operatorname{IsGreatest}(\left\{\Re(\operatorname{tr}(\rho S)) \mid \operatorname{PosSemidef}(\rho) \land \operatorname{tr}(\rho)=1\right\},\ 2 \sqrt{2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/TsirelsonTightness.bell_chsh_state_expectation_is_greatest` (`✓ std3`). ∎

*Citation.* B. S. Cirel'son (1980). *Quantum generalizations of Bell's inequality*. DOI: [10.1007/BF00417500](https://doi.org/10.1007/BF00417500).

*Commentary.*

Fix S to be CHSHWitness.chshOperator, built from the Pauli Z and X observables and the two fixed Bob observables of CHSHWitness. Among positive-semidefinite two-qubit matrices rho with trace one, the real trace expectation Re(tr(rho S)) has greatest value two times square root two. The IsGreatest conclusion includes both attainment and the upper bound for every state in this fixed state space.

Attainment is supplied by CHSHWitness.bellDensity and the exact calculation CHSHWitness.bell_chsh_value. For the upper-bound half, the proof rewrites S as the CHSH combination of the lifted observables, applies mathlib's tsirelson_inequality to their certified CHSH tuple, and transports the resulting matrix order through the positive trace pairing with rho.

The value and its sharpness are the classical Tsirelson bound, attested by B. S. Cirel'son, Quantum generalizations of Bell's inequality, Letters in Mathematical Physics 4 (1980), 93-100. The declaration does not characterize maximizing states, prove a converse, or optimize over varying observables: the four observables and S are fixed throughout.

## References

- Truth anchor: `D5/S3/QuantumBounds/TsirelsonTightness.bell_chsh_state_expectation_is_greatest`
- Dependency: [D5/S3/QuantumBounds/CHSHWitness](CHSHWitness.md)
