# Calibrated unitary groups

## Abstract

An operator-norm differentiable unitary group determines a Hamiltonian after independent calibration.

**Theorem 1.1 (The generator determines the exponential evolution).**

$$(\forall H: \operatorname{CompleteComplexInnerProductSpace}\left(\right), (\forall U: \operatorname{Map}\left(\operatorname{Real}\left(\right), \operatorname{ContinuousComplexLinearEnd}\left(H\right)\right), (\forall G: \operatorname{ContinuousComplexLinearEnd}\left(H\right), (((((\operatorname{apply}\left(U, 0\right) = \operatorname{Identity}\left(H\right)) \land (\forall s: \operatorname{Real}\left(\right), (\forall t: \operatorname{Real}\left(\right), (\operatorname{apply}\left(U, \operatorname{add}\left(s, t\right)\right) = \operatorname{compose}\left(\operatorname{apply}\left(U, s\right), \operatorname{apply}\left(U, t\right)\right))))) \land (\forall t: \operatorname{Real}\left(\right), (\operatorname{compose}\left(\operatorname{adjoint}\left(\operatorname{apply}\left(U, t\right)\right), \operatorname{apply}\left(U, t\right)\right) = \operatorname{Identity}\left(H\right)))) \land \operatorname{HasDerivAt}\left(U, G, 0\right)) \implies (\forall hbar: \operatorname{Real}\left(\right), ((hbar \neq 0) \implies ((\operatorname{IsSelfAdjoint}\left(\operatorname{calibratedHamiltonian}\left(hbar, G\right)\right) \land (\forall t: \operatorname{Real}\left(\right), (\operatorname{apply}\left(U, t\right) = \operatorname{exp}\left(\operatorname{scale}\left(\operatorname{negativeITOverHbar}\left(t, hbar\right), \operatorname{calibratedHamiltonian}\left(hbar, G\right)\right)\right)))) \land (\forall t: \operatorname{Real}\left(\right), \operatorname{HasDerivAt}\left(U, \operatorname{scale}\left(\operatorname{negativeIOverHbar}\left(hbar\right), \operatorname{compose}\left(\operatorname{calibratedHamiltonian}\left(hbar, G\right), \operatorname{apply}\left(U, t\right)\right)\right), t\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CalibratedUnitaryGroup.calibrated_group` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vittorio Giovannetti; Seth Lloyd; Lorenzo Maccone (2015). *Quantum Time*. DOI: [10.1103/PhysRevD.92.045033](https://doi.org/10.1103/PhysRevD.92.045033). URL: <https://arxiv.org/abs/1504.04215>.

*Commentary.*

Let H be a complete complex inner product space. Let U(t) be a continuous complex linear operator for each real t, with U(0)=I, U(s+t)=U(s)U(t), and U(t)*U(t)=I for every t. Assume the operator-valued map has real derivative G at zero in the operator norm. These assumptions include the original finite-dimensional differentiable unitary group, since finite-dimensional complex inner product spaces are complete. They do not assume a Hamiltonian or its equation of motion.

The group law writes U(s)=U(s-t)U(t). Differentiating at s=t proves U'(t)=G U(t) for every real t. Differentiating U(t)*U(t)=I at zero gives G*+G=0. The derivative of F(t)=exp(-tG)U(t) is therefore zero, and the mean-value constancy theorem gives F(t)=F(0)=I. Multiplying by exp(tG), whose product with exp(-tG) is I by the commuting exponential identity, proves U(t)=exp(tG). These steps construct the generator relation and the exponential representation from the original assumptions.

For an independently supplied nonzero real hbar, define Hamiltonian=i hbar G. Skew adjointness of G makes Hamiltonian self-adjoint. Scalar normalization gives U(t)=exp((-i t/hbar) Hamiltonian) and U'(t)=(-i/hbar) Hamiltonian U(t). Applying the continuous evaluation map at any initial vector psi gives the Schrodinger equation for U(t)psi; the evaluation is an exact compiled application, not another retained theorem. The original finite history, clock conditioning and all-input restoration applications remain in FinitePropagationHistory. Neither a continuous time parameter nor hbar follows from discrete gate count, and this theorem makes no claim about an unbounded generator of a merely strongly continuous group.

Giovannetti, Lloyd and Maccone discuss conditional-clock dynamics. The bounded, norm-differentiable generator argument here is a formal reuse and synthesis of standard differentiation, adjoint and exponential results, not a literature novelty claim.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/CalibratedUnitaryGroup.calibrated_group`
