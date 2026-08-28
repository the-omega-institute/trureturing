# Task-Family Law Kernel Criterion

## Abstract

Separating loss expectations identify predictive laws, while finite event indicators identify probability mass functions.

**Theorem 1.1 (Measure-determining tasks recover the predictive kernel).**

$$\begin{gathered}\forall H, Law, Y, T, A, Z: Type,\\{}\operatorname{Fintype}(Z),\\{}Psi: H \to Law,\\{}E: Law \to {Y \to \mathbb{R}} \to \mathbb{R},\\{}ell: T \to A \to Y \to \mathbb{R},\\{}{\forall mu, nu: Law, (\forall t: T, a: A, \operatorname{E}(mu, (y \mapsto \operatorname{ell}(t, a, y))) = \operatorname{E}(nu, (y \mapsto \operatorname{ell}(t, a, y)))) \Rightarrow mu = nu} \Rightarrow\\{}\operatorname{ker}(Psi) = \operatorname{ker}((h \mapsto (t \mapsto (a \mapsto \operatorname{E}(Psi(h), (y \mapsto \operatorname{ell}(t, a, y))))))) \land \forall mu, nu: \operatorname{PMF}(Z),\\{}(\forall B: \operatorname{Set}(Z), \sum_{z: Z} \operatorname{indicator}(B, (z \mapsto \operatorname{toReal}(mu(z))), z) = \sum_{z: Z} \operatorname{indicator}(B, (z \mapsto \operatorname{toReal}(nu(z))), z)) \Rightarrow mu = nu.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/TaskFamilyLawKernelCriterion.task_family_law_kernel_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The risk profile is constructed from the predictive law, the expectation operator, and every loss and action coordinate. If those coordinates determine allowed laws, its equality kernel is exactly the predictive law kernel.

For a finite outcome carrier, agreement on the expectation of every event indicator includes agreement on singleton events and therefore determines every probability mass.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/TaskFamilyLawKernelCriterion.task_family_law_kernel_criterion`
