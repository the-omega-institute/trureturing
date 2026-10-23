# Even coefficients and derivatives of a stopped Bernoulli output

## Abstract

Even coefficients and derivatives of a stopped Bernoulli output.

Use the seeded filtration and P(p)=nu times the iid Bernoulli(p) stream law, with arbitrary measurable Seed and seed probability nu. For a fixed p0 in (0,1), X_i=1_{bit_i=true}-p0 and A(m)=((2^(2m+1)*(2m)^2)^m)*2^(2m). The r-th elementary symmetric coefficient e_r(v) is the evaluation of MvPolynomial.esymm at the finite vector v; it vanishes above the vector length. All four statements quantify over the same natural-valued seeded stopping time tau, bound tau<=n everywhere, and natural m>0.

**Theorem 1.1 (The random-degree even coefficient budget).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget.bernoulli_stopped_even_coefficient_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget.bernoulli_stopped_even_coefficient_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every nu, p0, tau, n and m satisfying the preceding hypotheses, E_{P(p0)}^+[ofReal(|e_{2m}((X_i)_{i<tau})|)] <= ofReal(2A(m)+1) E_{P(p0)}^+[ofReal(tau^m)]. The elementary symmetric polynomial has the random degree tau. Newton identities relate its coefficients to the same stopped score and bounded higher power sums.

**Theorem 1.2 (Bounded multipliers and a fixed slope).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget.bernoulli_stopped_even_derivative_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget.bernoulli_stopped_even_derivative_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

Under the same hypotheses, for every real q and real function f on Seed times the Boolean stream with |f(omega)|<=1 everywhere, E_{P(p0)}^+[ofReal(|f times D^{2m}_{t=0} product_{i<tau}(1+t q X_i)|)] <= ofReal((2m)! |q|^(2m) (2A(m)+1)) E_{P(p0)}^+[ofReal(tau^m)]. No measurability assumption on f is imposed in this pointwise derivative budget.

**Theorem 1.3 (Differentiating the integrated output polynomial).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget.bernoulli_stopped_output_derivative_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget.bernoulli_stopped_output_derivative_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

Under the same stopping hypotheses, for every real q and measurable real f with |f|<=1 everywhere, ofReal(|D^{2m}_{t=0} E_{P(p0)}[f product_{i<tau}(1+t q X_i)]|) <= ofReal((2m)! |q|^(2m) (2A(m)+1)) E_{P(p0)}^+[ofReal(tau^m)]. Bounded stopping pads the random-degree product to a fixed finite degree, permitting coefficientwise integration.

**Theorem 1.4 (Affine parameter families are smooth at interior points).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget.bernoulli_stopped_affine_iterated_differentiable`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget.bernoulli_stopped_affine_iterated_differentiable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every bounded seeded stopping time, affine slope gamma, interior base point p0 and x+h gamma=p0, every iterated derivative of the projected affine-law expectation of a bounded stopped observation is differentiable at h. The projection is locally inactive because p0 lies in (0,1).

**Theorem 1.5 (Derivatives of the actual affine parameter law).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget.bernoulli_stopped_affine_derivative_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget.bernoulli_stopped_affine_derivative_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

Under the same stopping hypotheses, for every real gamma,x,h with x+h gamma=p0 and real f strongly measurable for the stopping-time sigma algebra with |f|<=1 everywhere, ofReal(|D^{2m}_{t=h} E_{P(proj_[0,1](x+t gamma))}[f]|) <= ofReal((2m)! |gamma/(p0(1-p0))|^(2m) (2A(m)+1)) E_{P(p0)}^+[ofReal(tau^m)]. The projection keeps the parameter law defined for every real t. Since p0 is interior, it agrees locally with x+t gamma at h; the derivative is for the actual stopped-observation law.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget.bernoulli_stopped_affine_derivative_budget`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget.bernoulli_stopped_affine_iterated_differentiable`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget.bernoulli_stopped_even_coefficient_budget`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget.bernoulli_stopped_even_derivative_budget`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget.bernoulli_stopped_output_derivative_budget`
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment](SeededBernoulliStoppedMoment.md)
