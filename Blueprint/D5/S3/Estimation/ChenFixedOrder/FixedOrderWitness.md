# Chen's fixed-order inclusion conjecture

## Abstract

Fixed-order inclusion agreement permits distinct weak limits of a common estimator.

At stage m, the population U(m) has two equal strata, each of size n(m)^3, with values +1 and -1. The sample size n(m) is (m+1)^2. S(m) is the set of all subsets of U(m) of size n(m). The population mean is mean(m), and X(m) is the sample mean minus mean(m), multiplied by the square root of n(m).

Prob denotes probability measures. For a prescribed subset A, E(m,A) is the event that the sample contains A. Uniform assigns equal probability to all members of S(m). The subscript star denotes pushforward, and gamma is the standard Gaussian. Every arrow takes m to infinity. The arrows for probability laws denote weak convergence.

**Definition 1.1 (The proposition).**

$$\begin{aligned}fixedOrderWitness \iff\\\operatorname{n}\left(m\right) \to \infty \land \lvert \operatorname{U}\left(m\right) \rvert \to \infty \land (\forall m:\mathbb{N}, \operatorname{mean}\left(m\right) = 0) \land\\\forall r:\mathbb{N}, 0 < r \Rightarrow \\\quad\exists P,Q: \prod_{m:\mathbb{N}} \operatorname{Prob}\left(\operatorname{S}\left(m\right)\right), \nu : \operatorname{Prob}\left(\mathbb{R}\right), \\\quad(\forall m:\mathbb{N}, \operatorname{P}\left(m\right) = \operatorname{Uniform}\left(\operatorname{S}\left(m\right)\right)) \land\\\quad(\forall m:\mathbb{N}, \forall A: \operatorname{Finset}\left(\operatorname{U}\left(m\right)\right), \lvert A \rvert \leq r \Rightarrow \operatorname{P}\left(m\right)(\operatorname{E}\left(m, A\right)) = \operatorname{Q}\left(m\right)(\operatorname{E}\left(m, A\right))) \land\\\quad\operatorname{X}\left(m\right)_{*} \operatorname{P}\left(m\right) \to \gamma \land \operatorname{X}\left(m\right)_{*} \operatorname{Q}\left(m\right) \to \nu \land \nu \neq \gamma\end{aligned}$$

*Formalization.* `D5/S3/Estimation/ChenFixedOrder/FixedOrderWitness.fixedOrderWitness` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jiahua Chen (2026). *Low-Order Inclusion Probabilities Do Not Determine Asymptotic Normality*. URL: <https://arxiv.org/abs/2610.09168v1>.

*Commentary.*

Chen poses the question for every fixed order in Sections 1 and 6. The proposition specifies the balanced populations, a uniform baseline, and distinct weak limits of the same estimator under the two designs.

**Theorem 1.2 (Existence for every fixed positive order).**

$$\begin{aligned}\operatorname{n}\left(m\right) \to \infty \land \lvert \operatorname{U}\left(m\right) \rvert \to \infty \land (\forall m:\mathbb{N}, \operatorname{mean}\left(m\right) = 0) \land\\\forall r:\mathbb{N}, 0 < r \Rightarrow \\\quad\exists P,Q: \prod_{m:\mathbb{N}} \operatorname{Prob}\left(\operatorname{S}\left(m\right)\right), \nu : \operatorname{Prob}\left(\mathbb{R}\right), \\\quad(\forall m:\mathbb{N}, \operatorname{P}\left(m\right) = \operatorname{Uniform}\left(\operatorname{S}\left(m\right)\right)) \land\\\quad(\forall m:\mathbb{N}, \forall A: \operatorname{Finset}\left(\operatorname{U}\left(m\right)\right), \lvert A \rvert \leq r \Rightarrow \operatorname{P}\left(m\right)(\operatorname{E}\left(m, A\right)) = \operatorname{Q}\left(m\right)(\operatorname{E}\left(m, A\right))) \land\\\quad\operatorname{X}\left(m\right)_{*} \operatorname{P}\left(m\right) \to \gamma \land \operatorname{X}\left(m\right)_{*} \operatorname{Q}\left(m\right) \to \nu \land \nu \neq \gamma\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ChenFixedOrder/FixedOrderWitness.fixedOrderWitness_holds` (`✓ std3`). ∎

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
