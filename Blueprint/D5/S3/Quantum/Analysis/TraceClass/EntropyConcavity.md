# Extended entropy and real strong concavity

## Abstract

Full weighted quantitative entropy concavity in the trace-class Banach space.

**Theorem 1.1 (Real entropy on its actual domain).**

$$\operatorname{RealEntropyEqualsSpectralEntropyToRealOnReferences}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/EntropyConcavity.realEntropy_reference` (`✓ std3`). ∎

*Citation.* George Androulakis and Tiju Cherian John (2023). *Quantum f-divergences via Nussbaum-Szkoła Distributions and Applications to f-divergence Inequalities*. DOI: [10.48550/arXiv.2308.02929](https://doi.org/10.48550/arXiv.2308.02929). URL: <https://arxiv.org/html/2308.02929>.

*Commentary.*

For every actual positive trace-class contraction rho, realEntropy of its underlying trace-class operator equals the real value of its actual spectral entropy. This is the domain restriction in the definition. Applications interpreting the value as finite entropy supply a separate finiteness premise.

**Theorem 1.2 (All weights, singular references and infinite entropy).**

$$\forall H \in CompleteComplexHilbertSpace, rho \in \operatorname{Reference}\left(H\right), sigma \in \operatorname{Reference}\left(H\right), a \in Real, b \in Real,\; \left(\operatorname{PositiveTraceOne}\left(rho\right) \land \left(\operatorname{PositiveTraceOne}\left(sigma\right) \land \left(0 \le a \land \left(0 \le b \land \operatorname{add}\left(a, b\right) = 1\right)\right)\right)\right) \Rightarrow \operatorname{add}\left(\operatorname{add}\left(\operatorname{multiply}\left(\operatorname{ofReal}\left(a\right), \operatorname{spectralEntropy}\left(rho\right)\right), \operatorname{multiply}\left(\operatorname{ofReal}\left(b\right), \operatorname{spectralEntropy}\left(sigma\right)\right)\right), \operatorname{ofReal}\left(\operatorname{divide}\left(\operatorname{multiply}\left(\operatorname{multiply}\left(a, b\right), \operatorname{square}\left(\operatorname{traceNorm}\left(\operatorname{subtract}\left(rho, sigma\right)\right)\right)\right), 4\right)\right)\right) \le \operatorname{spectralEntropy}\left(\operatorname{mixture}\left(rho, sigma, a, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/EntropyConcavity.spectralEntropy_mixture` (`✓ std3`). ∎

*Citation.* George Androulakis and Tiju Cherian John (2023). *Quantum f-divergences via Nussbaum-Szkoła Distributions and Applications to f-divergence Inequalities*. DOI: [10.48550/arXiv.2308.02929](https://doi.org/10.48550/arXiv.2308.02929). URL: <https://arxiv.org/html/2308.02929>.

*Commentary.*

For actual positive trace-one References rho and sigma, let a,b be nonnegative real numbers with a+b=1. mixture is the actual trace-class linear combination a rho+b sigma. Positivity and the trace calculation prove normalization, and density_le_one proves the contraction bound. No entropy identity or energy inequality is an assumed field.

Apply the Hellinger trace-norm energy bound to rho relative to the mixture and to sigma relative to the same mixture. Multiply by a and b and add in ENNReal. Actual nonnegative first-slot linearity and self energy identify the upper bound with the spectral entropy of the mixture.

The exact norm identities are norm(rho-tau)=b norm(rho-sigma) and norm(sigma-tau)=a norm(rho-sigma). Their weighted squared rewards add to a b norm(rho-sigma) squared divided by four, since a+b=1. There is no subtraction of infinite values and no finiteness premise on cross energy or entropy. Both zero weights and the zero times infinity convention are included.

For a=1-t and b=t this is the full inequality for every t in [0,1]. At the midpoint the reward is norm(rho-sigma) squared divided by sixteen. The arguments may be noncommuting and either may have a nontrivial kernel.

**Theorem 1.3 (Real entropy has modulus one half).**

$$\forall H \in CompleteComplexHilbertSpace, A \in \operatorname{Set}\left(\operatorname{TraceClass}\left(H\right)\right),\; \left(\operatorname{Convex}\left(A\right) \land \left(\operatorname{AllPositiveTraceOne}\left(A\right) \land \operatorname{AllFiniteSpectralEntropy}\left(A\right)\right)\right) \Rightarrow \operatorname{StrongConcaveOn}\left(A, \operatorname{divide}\left(1, 2\right), realEntropy\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/EntropyConcavity.strongConcaveOn_realEntropy` (`✓ std3`). ∎

*Citation.* George Androulakis and Tiju Cherian John (2023). *Quantum f-divergences via Nussbaum-Szkoła Distributions and Applications to f-divergence Inequalities*. DOI: [10.48550/arXiv.2308.02929](https://doi.org/10.48550/arXiv.2308.02929). URL: <https://arxiv.org/html/2308.02929>.

*Commentary.*

realEntropy is the real value of the actual extended spectral entropy on positive trace-class contractions and is extended by zero outside that domain. Let A be any convex subset of TraceClass H consisting of actual positive trace-one densities. Assume their actual spectral entropies are finite. No compactness, entropy boundedness or upper semicontinuity is inferred from these hypotheses.

The convex mixture belongs to A, so its entropy is finite as well. Applying the ENNReal real-value map to the full weighted inequality is justified by these genuine finiteness hypotheses. Real scalar multiplication on TraceClass is the restriction of its complex scalar multiplication, and its norm remains the trace norm.

Mathlib defines StrongConcaveOn A m with reward a b times m/2 times the squared distance. The coefficient one fourth therefore gives modulus m=1/2. This is the full weighted condition, rather than a midpoint-only assertion. The result supplies strong concavity; existence of entropy centers and the original Shirokov common-energy and full-Hamiltonian conclusions still require their other hypotheses and constructions.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/EntropyConcavity.realEntropy_reference`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/EntropyConcavity.spectralEntropy_mixture`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/EntropyConcavity.strongConcaveOn_realEntropy`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/HellingerEnergy](HellingerEnergy.md)
