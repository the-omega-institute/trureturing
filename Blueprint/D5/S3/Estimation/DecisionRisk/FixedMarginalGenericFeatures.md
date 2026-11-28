# Fixed-marginal generic features

## Abstract

A fixed data marginal relates universal signed-loss quality to one randomized reconstruction rule.

**Theorem 1.1 (Universal decision quality and reconstruction).**

$$\forall X, Z, q, phi, epsilon, {\operatorname{Fintype}\left(X\right) \land \operatorname{Fintype}\left(Z\right) \land \operatorname{Nonnegative}\left(q\right) \land \operatorname{sum}\left(q\right) = 1 \land \operatorname{IsRowStochastic}\left(phi\right) \land 0 < epsilon} \Rightarrow {\operatorname{GenericQuality}\left(q, phi, epsilon\right) \Leftrightarrow \exists d: \operatorname{FiniteMarkovKernel}\left(Z, X\right), \operatorname{reconstructionError}\left(q, phi, d\right) \leq \frac{epsilon}{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/FixedMarginalGenericFeatures.generic_quality_iff_reconstruction` (`✓ std3`). ∎

*Citation.* Brendan van Rooyen; Robert C. Williamson (2014). *Le Cam meets LeCun: Deficiency and Generic Feature Learning*. DOI: [10.48550/arXiv.1402.4884](https://doi.org/10.48550/arXiv.1402.4884). URL: <https://arxiv.org/abs/1402.4884v2>.

*Commentary.*

Here X : Type u and Z : Type v are finite types, q : X → ℝ, phi : X → Z → ℝ and epsilon : ℝ. The decoder d : FiniteMarkovKernel Z X has an underlying row-stochastic array of type Z → X → ℝ. GenericQuality quantifies finite hypothesis types Theta : Type w and nonempty finite action types A : Type t, with prior pi : Theta → ℝ, experiment T : Theta → X → ℝ and loss L : Theta → A → ℝ; u, v, w and t are independent universes.

Let X and Z be arbitrary finite types, q a nonnegative real mass of total one on X, and phi a row-stochastic encoder from X to Z. For epsilon greater than zero, universal quality means that every finite hypothesis type, normalized prior, nonempty finite action type, compatible experiment with data marginal q, and real signed loss has feature Bayes risk minus data Bayes risk at most epsilon times the maximum absolute loss. All four type universes are independent.

The Bayes risk is the real sInf of finiteBayesCost over every row-stochastic randomized decision. Negative losses remain signed. The finite maximum is lossNorm, the real supremum of the finite nonempty set of absolute loss values. Normalization supplies nonemptiness of the data and hypothesis types; the encoder then supplies nonemptiness of the feature type. No support condition is imposed on any entry.

This universal quality condition holds precisely when a single stochastic decoder from Z to X has q-weighted mismatch probability at most epsilon divided by two. The decoder is common to all compatible decision problems. Its error is the sum over x, z and y of q(x) phi(x,z) d(z,y) times the indicator of y different from x.

For the forward transport estimate, compose an optimal data decision with the decoder. Its conditional expected loss lies between minus and plus the maximum absolute loss. Replacing x by a reconstructed y changes this conditional loss by at most twice that maximum, and changes nothing when y equals x. Averaging against the common joint law and using its marginal q gives twice the reconstruction error as the normalized risk bound.

For necessity, relabel the data type into finite hypothesis and action types in their independent universes. Use the identity experiment and the signed loss minus one for correct reconstruction and plus one for a mismatch. Its data Bayes risk is minus one, and its feature risk is twice the minimum mismatch probability minus one. A finite observationwise argmin attains this real minimum, including on null observation fibers. Applying universal quality yields an attaining decoder at half the quality bound.

The source is van Rooyen and Williamson, Le Cam meets LeCun: Deficiency and Generic Feature Learning, arXiv:1402.4884v2, Definition 3 and Theorem 3; Section 2 specifies signed loss normalization and Section 7.5 uses full l1 variational distance. The mismatch indicator and factor two here follow from the signed reconstruction loss directly. The result concerns finite stochastic experiments and makes no measurable infinite-space claim.

**Lemma 1.2 (Expected cost as a coefficient table).**

$$\forall p, L, T, d, \operatorname{finiteBayesCost}\left(p, L, T, d\right) = \operatorname{sum}\left(x, \operatorname{sum}\left(a, \operatorname{entry}\left(d, x, a\right) \cdot \operatorname{sum}\left(theta, \operatorname{entry}\left(p, theta\right) \cdot \operatorname{entry}\left(T, theta, x\right) \cdot \operatorname{entry}\left(L, theta, a\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/FixedMarginalGenericFeatures.finite_bayes_cost_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here Theta, O and A are arbitrary finite types; p : Theta → ℝ, L : Theta → A → ℝ, T : Theta → O → ℝ and d : O → A → ℝ. The sum indices are theta : Theta, x : O and a : A.

For arbitrary finite state, observation and action types, the real expected loss equals the sum over observations and actions of the decision entry times its unnormalized posterior loss coefficient. This finite-sum identity is valid for arbitrary real arrays and does not require stochasticity or signs.

**Lemma 1.3 (Finite real Bayes costs attain a minimum).**

$$\forall Theta, O, A, \operatorname{Fintype}\left(Theta\right) \land \operatorname{Fintype}\left(O\right) \land \operatorname{Fintype}\left(A\right) \land \operatorname{Nonempty}\left(A\right) \Rightarrow \forall p, L, T, \exists d: \operatorname{FiniteMarkovKernel}\left(O, A\right), \forall k: \operatorname{FiniteMarkovKernel}\left(O, A\right), \operatorname{finiteBayesCost}\left(p, L, T, d\right) \leq \operatorname{finiteBayesCost}\left(p, L, T, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/FixedMarginalGenericFeatures.finite_bayes_cost_minimizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here Theta, O and A are finite types with Nonempty A; p : Theta → ℝ, L : Theta → A → ℝ and T : Theta → O → ℝ. The decisions d, k : FiniteMarkovKernel O A have underlying row-stochastic arrays of type O → A → ℝ, with theta : Theta, x : O and a : A indexing states, observations and actions.

For arbitrary finite state and observation types and a nonempty finite action type, every real coefficient table has an observationwise minimizing action. The corresponding point-mass decision minimizes finiteBayesCost over all stochastic decisions. The prior, experiment and loss need not have nonnegative entries for this finite linear minimization statement. In a statistical decision problem the prior and experiment satisfy their usual stochastic laws, and signed losses remain allowed.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/FixedMarginalGenericFeatures.finite_bayes_cost_expansion`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/FixedMarginalGenericFeatures.finite_bayes_cost_minimizer`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/FixedMarginalGenericFeatures.generic_quality_iff_reconstruction`
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer](../SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.md)
