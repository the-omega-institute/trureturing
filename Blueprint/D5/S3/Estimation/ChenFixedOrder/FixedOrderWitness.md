# Chen's fixed-order inclusion conjecture

## Abstract

Fixed-order inclusion agreement permits distinct weak limits of a common estimator.

At stage m, Population(m) has two equal strata, each of size sampleSize(m) cubed, with values +1 and -1. The sample size is (m+1)^2. Sample(m) is the type of all subsets of Population(m) of that size. The estimator is the sample mean minus the population mean, multiplied by the square root of the sample size.

The event inclusion(m,A) consists of the samples at stage m that contain A. The uniform measure assigns equal mass to all samples of the prescribed size. The map sends each design through the common estimator, and convergence of probability measures is weak convergence.

**Definition 1.1 (The proposition).**

$$\begin{aligned}fixedOrderWitness \iff\\\begin{aligned}\operatorname{Tendsto}\left(sampleSize, \operatorname{atTop}, \operatorname{atTop}\right) \land \operatorname{Tendsto}\left(m \mapsto \operatorname{Fintype.card}\left(\operatorname{Population}\left(m\right)\right), \operatorname{atTop}, \operatorname{atTop}\right) \land\\\left(\forall m: \mathbb{N}, \operatorname{populationMean}\left(m\right) = 0\right) \land\\\left(\begin{aligned}\forall r: \mathbb{N}, 0 < r \Rightarrow \\\quad\exists P,Q: \prod_{m:\mathbb{N}} \operatorname{ProbabilityMeasure}\left(\operatorname{Sample}\left(m\right)\right), \nu : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \left(\begin{aligned}\left(\forall m: \mathbb{N}, \left(\operatorname{P}\left(m\right) : \operatorname{Measure}\left(\operatorname{Sample}\left(m\right)\right)\right) = \operatorname{uniformOn}\left(\operatorname{Set.univ}\right)\right) \land\\\left(\begin{aligned}\forall m: \mathbb{N}, \forall A: \operatorname{Finset}\left(\operatorname{Population}\left(m\right)\right), \operatorname{card}\left(A\right) \leq r \Rightarrow\\\quad\left(\operatorname{P}\left(m\right) : \operatorname{Measure}\left(\operatorname{Sample}\left(m\right)\right)\right)\left(\operatorname{inclusion}\left(m, A\right)\right) = \left(\operatorname{Q}\left(m\right) : \operatorname{Measure}\left(\operatorname{Sample}\left(m\right)\right)\right)\left(\operatorname{inclusion}\left(m, A\right)\right)\end{aligned}\right) \land\\\operatorname{Tendsto}\left(m \mapsto \operatorname{ProbabilityMeasure.map}\left(\operatorname{P}\left(m\right), \operatorname{estimator}\left(m\right)\right), \operatorname{atTop}, \operatorname{nhds}\left(\operatorname{standardGaussian}\right)\right) \land\\\operatorname{Tendsto}\left(m \mapsto \operatorname{ProbabilityMeasure.map}\left(\operatorname{Q}\left(m\right), \operatorname{estimator}\left(m\right)\right), \operatorname{atTop}, \operatorname{nhds}\left(\nu\right)\right) \land \nu \neq \operatorname{standardGaussian}\end{aligned}\right)\end{aligned}\right)\end{aligned}\end{aligned}$$

*Formalization.* `D5/S3/Estimation/ChenFixedOrder/FixedOrderWitness.fixedOrderWitness` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jiahua Chen (2026). *Low-Order Inclusion Probabilities Do Not Determine Asymptotic Normality*. URL: <https://arxiv.org/abs/2610.09168v1>.

*Commentary.*

Chen poses the question for every fixed order in Sections 1 and 6. The proposition specifies the balanced populations, a uniform baseline, and distinct weak limits of the same estimator under the two designs.

**Theorem 1.2 (Existence for every fixed positive order).**

$$\begin{aligned}\operatorname{Tendsto}\left(sampleSize, \operatorname{atTop}, \operatorname{atTop}\right) \land \operatorname{Tendsto}\left(m \mapsto \operatorname{Fintype.card}\left(\operatorname{Population}\left(m\right)\right), \operatorname{atTop}, \operatorname{atTop}\right) \land\\\left(\forall m: \mathbb{N}, \operatorname{populationMean}\left(m\right) = 0\right) \land\\\left(\begin{aligned}\forall r: \mathbb{N}, 0 < r \Rightarrow \\\quad\exists P,Q: \prod_{m:\mathbb{N}} \operatorname{ProbabilityMeasure}\left(\operatorname{Sample}\left(m\right)\right), \nu : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \left(\begin{aligned}\left(\forall m: \mathbb{N}, \left(\operatorname{P}\left(m\right) : \operatorname{Measure}\left(\operatorname{Sample}\left(m\right)\right)\right) = \operatorname{uniformOn}\left(\operatorname{Set.univ}\right)\right) \land\\\left(\begin{aligned}\forall m: \mathbb{N}, \forall A: \operatorname{Finset}\left(\operatorname{Population}\left(m\right)\right), \operatorname{card}\left(A\right) \leq r \Rightarrow\\\quad\left(\operatorname{P}\left(m\right) : \operatorname{Measure}\left(\operatorname{Sample}\left(m\right)\right)\right)\left(\operatorname{inclusion}\left(m, A\right)\right) = \left(\operatorname{Q}\left(m\right) : \operatorname{Measure}\left(\operatorname{Sample}\left(m\right)\right)\right)\left(\operatorname{inclusion}\left(m, A\right)\right)\end{aligned}\right) \land\\\operatorname{Tendsto}\left(m \mapsto \operatorname{ProbabilityMeasure.map}\left(\operatorname{P}\left(m\right), \operatorname{estimator}\left(m\right)\right), \operatorname{atTop}, \operatorname{nhds}\left(\operatorname{standardGaussian}\right)\right) \land\\\operatorname{Tendsto}\left(m \mapsto \operatorname{ProbabilityMeasure.map}\left(\operatorname{Q}\left(m\right), \operatorname{estimator}\left(m\right)\right), \operatorname{atTop}, \operatorname{nhds}\left(\nu\right)\right) \land \nu \neq \operatorname{standardGaussian}\end{aligned}\right)\end{aligned}\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ChenFixedOrder/FixedOrderWitness.fixedOrderWitness_holds` (`✓ std3`). ∎

*Resolves.* `Problems/chen-2026-fixed-order-inclusion` (proved) by `D5/S3/Estimation/ChenFixedOrder/FixedOrderWitness.fixedOrderWitness_holds`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chen-2026-fixed-order-inclusion","declaration_gid":"D5/S3/Estimation/ChenFixedOrder/FixedOrderWitness.fixedOrderWitness_holds","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jiahua Chen (2026). *Low-Order Inclusion Probabilities Do Not Determine Asymptotic Normality*. URL: <https://arxiv.org/abs/2610.09168v1>.

*Commentary.*

The uniform law on fixed-size subsets yields the Gaussian limit. At a fixed order r, tilt each uniform estimator law by the bounded adjugate density of order max(r,2). The density has total integral one and its difference from one integrates to zero against powers through that order.

Lift the tilt to the original sample space by evaluating the density at the common estimator. The finite density bridge gives exact inclusion-event equality and identifies the resulting estimator law with the real tilt. Weak continuity of the tilt gives the second limit. The Gaussian separation theorem gives a strictly larger expectation of the residual test under that limit, proving the limits unequal.

## References

- Truth anchor: `D5/S3/Estimation/ChenFixedOrder/FixedOrderWitness.fixedOrderWitness`
- Truth anchor: `D5/S3/Estimation/ChenFixedOrder/FixedOrderWitness.fixedOrderWitness_holds`
- Dependency: [D5/S3/Analytic/Probability/ChenDensityBridge](../../Analytic/Probability/ChenDensityBridge.md)
- Dependency: [D5/S3/Analytic/Probability/MomentPerturbation](../../Analytic/Probability/MomentPerturbation.md)
- Dependency: [D5/S3/Estimation/ChenFixedOrder/GaussianLimit](GaussianLimit.md)
