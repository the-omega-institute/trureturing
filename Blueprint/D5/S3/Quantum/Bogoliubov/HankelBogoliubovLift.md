# Hankel Bogoliubov Lift

## Abstract

A finite contractive singular-value family has a canonical Bogoliubov lift.

**Theorem 1.1 (Finite contractive singular values have a Bogoliubov lift).**

$$\forall n \in \mathbb{N}, \sigma \in \operatorname{Fin}(n)to\mathbb{R}, {\forall j \in \operatorname{Fin}(n), 0 \le \sigma_{j} \land \sigma_{j} < 1} \Rightarrow {}let \alpha_{j} = \operatorname{cosh}(\operatorname{artanh}(\sigma_{j}));{}let \beta_{j} = \operatorname{sinh}(\operatorname{artanh}(\sigma_{j}));{\forall j \in \operatorname{Fin}(n), \alpha_{j}^{{2}} - \beta_{j}^{{2}} = 1 \land \forall j \in \operatorname{Fin}(n), \left|\alpha_{j}\right| = \frac{1}{\operatorname{sqrt}(1 - \sigma_{j}^{{2}})} \land \forall j \in \operatorname{Fin}(n), \left|\beta_{j}\right| = \frac{\sigma_{j}}{\operatorname{sqrt}(1 - \sigma_{j}^{{2}})} \land \forall j \in \operatorname{Fin}(n), \beta_{j}^{{2}} = \frac{\sigma_{j}^{{2}}}{1 - \sigma_{j}^{{2}}}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Bogoliubov/HankelBogoliubovLift.hankel_bogoliubov_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite indexed family of Hankel singular values with 0 <= sigma_j < 1, define r_j = artanh(sigma_j), alpha_j = cosh(r_j), and beta_j = sinh(r_j).

The diagonal coefficient operators satisfy the canonical CCR identity pointwise. The strict interval hypothesis makes the square-root denominator positive and yields the displayed amplitude and particle-number formulas.

The pointwise CCR is the finite diagonal form of alpha_H^* alpha_H - beta_H^* beta_H = I; no infinite-dimensional operator is assumed.

## References

- Truth anchor: `D5/S3/Quantum/Bogoliubov/HankelBogoliubovLift.hankel_bogoliubov_lift`
- Dependency: [D5/S3/Quantum/Bogoliubov/BogoliubovNormConservation](BogoliubovNormConservation.md)
