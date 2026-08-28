# Posterior Mixture Kernel Realization

## Abstract

A Bayes-plausible finite posterior mixture is realized by its canonical signal kernel.

**Theorem 1.1 (Bayes-plausible posterior mixtures are realizable).**

$$\forall World \in Type, Signal \in Type,\; \left(\operatorname{Fintype}\left(World\right) \land \operatorname{Fintype}\left(Signal\right)\right) \Rightarrow \left(\forall mu \in \operatorname{PMF}\left(World\right), muPost \in Signal \to \operatorname{PMF}\left(World\right), lambda \in \operatorname{PMF}\left(Signal\right),\; \left(\forall omega \in World,\; 0 < \operatorname{toReal}\left(mu\left(omega\right)\right)\right) \Rightarrow \left(\left(\forall omega \in World,\; \sum_{s \in Signal} \operatorname{toReal}\left(lambda\left(s\right)\right) \cdot \operatorname{toReal}\left(muPost\left(s, omega\right)\right) = \operatorname{toReal}\left(mu\left(omega\right)\right)\right) \Rightarrow \operatorname{let} kappa : World \to \left(Signal \to \mathbb{R}\right) := (omega,s) \mapsto \frac{\operatorname{toReal}\left(lambda\left(s\right)\right) \cdot \operatorname{toReal}\left(muPost\left(s, omega\right)\right)}{\operatorname{toReal}\left(mu\left(omega\right)\right)}; \operatorname{let} jointLaw : Signal \times World \to \mathbb{R} := (s,omega) \mapsto \operatorname{toReal}\left(mu\left(omega\right)\right) \cdot kappa\left(omega, s\right); \left(\forall omega \in World, s \in Signal,\; 0 \le kappa\left(omega, s\right)\right) \land \left(\left(\forall omega \in World,\; \sum_{s \in Signal} kappa\left(omega, s\right) = 1\right) \land \left(\operatorname{marginal}\left(jointLaw\right) = (s \mapsto \operatorname{toReal}\left(lambda\left(s\right)\right)) \land \left(\forall s \in Signal,\; 0 < \operatorname{toReal}\left(lambda\left(s\right)\right) \Rightarrow \operatorname{conditional}\left(jointLaw, s\right) = (omega \mapsto \operatorname{toReal}\left(muPost\left(s, omega\right)\right))\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMixtureKernelRealization.posterior_mixture_kernel_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prior, every prescribed posterior, and the signal weights are finite PMFs. Thus the nonnegativity and unit-mass requirements on the posterior family and weights are part of their public carriers.

The theorem exposes the canonical signal kernel as the prescribed signal weight times posterior mass, divided by the positive prior mass. The accompanying joint law is induced from that kernel and prior.

The posterior-mixture equation normalizes the kernel at every world. Posterior normalization gives the prescribed signal marginal, and division by a positive signal weight recovers its posterior.

The imported forward plausibility theorem uses the same canonical marginal and conditional operations. Repository search found no prior reverse realization theorem containing all displayed clauses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMixtureKernelRealization.posterior_mixture_kernel_realization`
- Dependency: [D5/S3/ConceptDynamics/ObservationOrder/BayesPlausibility](BayesPlausibility.md)
