# Circle Primal Equivalence

## Abstract

The budgeted circle primal is the attained maximal normalized-Haar floor, equivalently the attained maximal coefficient in a positive residual decomposition.

**Theorem 1.1 (The circle primal and residual programs have the same attained maximum).**

$$\begin{aligned}a > 0, \forall i, \int \operatorname{apply}(Gamma, i) \mathrm{d}m_{T} = 2a\operatorname{apply}(c, i),\\\mathcal{M}_{C} \neq \emptyset \Rightarrow \exists \mu,\alpha, \mu\in\mathcal{M}_{C} \land \alpha m_{T} \leq \mu,\\Lambda = 2a\max_{\mu\in\mathcal{M}_{C}}\operatorname{hfloor}(\mu) = 2a\alpha,\\\frac{Lambda}{2a} = \alpha = \max_{\alpha\geq0}\left\{\alpha: \exists \sigma\geq0, \alpha+\operatorname{mass}(\sigma) \leq C, \forall i, 2a\alpha\operatorname{apply}(c, i)+\int \operatorname{apply}(Gamma, i) \mathrm{d}\sigma = \operatorname{apply}(W, i)\right\}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/CirclePrimalEquivalence.circle_primal_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The continuous moment family is normalized so that its Haar integral is twice a times the designated center evaluation. The positivity assumption on a is required when dividing the primal identity by twice a; without it Lean's totalized division would collapse that quotient to zero.

The existing full-circle attainment theorem supplies a feasible measure and a globally greatest dominated Haar coefficient. Taking the measure difference constructs a positive residual and gives the displayed budget and moment equations.

Conversely, adding any positive residual to the Haar component constructs a feasible measure dominating that coefficient. Thus the measure floor maximum and the explicit residual maximum have exactly the same feasible coefficients and the same attained optimizer.

## References

- Truth anchor: `D5/S3/Weil/Budget/CirclePrimalEquivalence.circle_primal_equivalence`
- Dependency: [D5/S3/Weil/Budget/FullCirclePrimalAttainment](FullCirclePrimalAttainment.md)
