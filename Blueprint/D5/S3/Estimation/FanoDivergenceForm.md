# Reference-Divergence and Hypothesis-Counting Forms of Finite Fano

## Abstract

Positive normalized observation references bound finite mutual information by product-reference divergence; a positive observation marginal attains the family, and Fano yields hypothesis-counting forms.

**Theorem 1.1 (Every positive normalized observation reference upper-bounds mutual information).**

$$\begin{gathered}\forall Y, X\ [\operatorname{Fintype}(Y)] [\operatorname{Fintype}(X)],\\\forall p: Y\times X\to \mathbb{R}, u: Y\to \mathbb{R},\\((\forall z, 0\le p(z)) \land \sum _{z} p(z)=1) \land (\forall y, 0< u(y)) \land \sum _{y} u(y)=1) \Rightarrow \\\operatorname{mutualInformation}(p)\le \operatorname{klDivergence}(p, ((y, x)\mapsto u(y) \cdot \operatorname{marginal}((x, y)\mapsto p(y, x))(x)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/FanoDivergenceForm.mutual_information_le_product_reference_divergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The preceding Fano error floor is stated in terms of mutual information, which may be awkward to evaluate directly. The already frozen theorem demon_average_divergence_eq writes the displayed joint-to-product-reference divergence as mutualInformation p plus klDivergence (marginal p) u. Discarding the latter term gives the displayed upper bound while leaving the observation reference u free. This step is a one-line consequence of that frozen identity and Gibbs nonnegativity; it is not presented as a new information inequality.

The inequality has a strictly stronger hypothesis than the identity from which it is derived. The identity requires u only to be strictly positive. Discarding klDivergence (marginal p) u additionally requires that term to be nonnegative, and Gibbs nonnegativity applies only when both arguments are distributions. Consequently u must also have total mass one. Strict positivity supplies discrete absolute continuity for free, but it does not supply normalization.

Normalization is necessary rather than cosmetic. On the one-point space, the divergence of the unit mass from the constant reference 2 is -log 2, which is negative. Thus a merely positive, nonnormalized reference can make the remainder in the frozen decomposition negative; discarding it would reverse the intended comparison. The compiled counterexample records exactly D(1 || 2) = -log 2.

The companion exists_observation_marginal_reference_attaining shows that this family of upper bounds is attained. If the observation marginal of p is strictly positive at every point, take u to be that marginal. Its total mass is one because p is a joint distribution, and the discarded divergence is then the divergence of a distribution from itself, hence zero. The resulting product-reference divergence equals mutualInformation p. The positivity assumption is genuine: if the marginal has zeros, the equality still holds, but this witness does not belong to the admissible strictly-positive reference family.

The theorem fano_error_probability_lower_bound_divergence makes the corresponding short monotone substitution in the previous uniform-prior Fano floor. It assumes that p is a nonnegative law of total mass one, that u is strictly positive and normalized, that 2 <= card X, and that the hidden-coordinate marginal is the constant law 1/card X. For every estimator g, its error mass is at least 1 minus the sum of the displayed product-reference divergence and log 2, divided by log(card X). The passage from mutual information to divergence is a short corollary, not an independently weighted result.

The change of direction is expressed first by fano_hypothesis_count_product_bound_uniform. Under the same law and uniform-hidden-marginal assumptions, if the error mass of an arbitrary estimator is at most epsilon, then (1-epsilon) log(card X) is at most mutualInformation p + log 2. This product form is primary and has no epsilon < 1 hypothesis. Its companion fano_hypothesis_count_bound_uniform adds exactly epsilon < 1 and divides to obtain log(card X) at most (mutualInformation p + log 2)/(1-epsilon).

The declarations fano_hypothesis_count_product_bound_divergence and fano_hypothesis_count_bound_divergence enlarge the same two information budgets to the product-reference divergence. Both retain the law, uniform-hidden-marginal, error, strict-positivity, and normalization hypotheses. The divergence product form again has no epsilon < 1 side condition; only its quotient companion assumes epsilon < 1, because only that statement divides by 1-epsilon.

This orientation counts resolvable hypotheses rather than bounding error: for epsilon < 1, an observation carrying I nats cannot reliably distinguish more than approximately exp((I + log 2)/(1-epsilon)) candidates at target error epsilon. In the compiled informative regime I = 0 and epsilon = 1/2, so the logarithmic budget is log 2 divided by 1/2, namely log 4. For M >= 1, the exact implication log M <= log 4 therefore gives M <= 4. The ceiling binds and permits at most four candidates.

At the opposite endpoint, I = 0 and epsilon = 1 make the product form read 0 <= log 2 for every M, so it imposes no cardinality ceiling. This is the correct vacuous regime: an estimator permitted always to be wrong constrains nothing. Exhibiting both regimes is necessary. A ceiling that binds nowhere would be worthless, while one that remained binding at error one would be false to the estimation problem.

The first inequality is a one-line corollary of a frozen decomposition, and the divergence-form error floor is a short monotone substitution. The content of this module is instead the normalization hypothesis and its concrete negative-divergence counterexample, the admissible attainment witness, and the hypothesis-counting orientation with its side-condition-free product forms. All seven declarations are finite and nats-valued. The module introduces no definition and claims no new information identity, estimator construction, minimax theorem, sample-complexity theorem, or measure-theoretic analogue.

## References

- Truth anchor: `D5/S3/Estimation/FanoDivergenceForm.mutual_information_le_product_reference_divergence`
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](../Divergence/GrandmotherTheorem.md)
- Dependency: [D5/S3/Entropy/Feedback/DemonIdentity](../Entropy/Feedback/DemonIdentity.md)
- Dependency: [D5/S3/Estimation/FanoErrorBound](FanoErrorBound.md)
