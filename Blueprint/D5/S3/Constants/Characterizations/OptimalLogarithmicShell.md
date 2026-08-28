# Optimal Logarithmic Shell

## Abstract

The exponential unit is the unique global minimizer of cost per logarithmic scale.

**Theorem 1.1 (The logarithmic shell cost is uniquely minimized at exp(1)).**

$$\operatorname{IsMinOn}((\beta: \mathbb{R}) \to \frac{\beta}{\log(\beta)}, (1, \infty), \operatorname{exp}(1)) \land\\\forall \beta\in \mathbb{R}, 1 < \beta, \frac{\beta}{\log(\beta)} = \frac{\operatorname{exp}(1)}{\log(\operatorname{exp}(1))} \Rightarrow \beta = \operatorname{exp}(1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Characterizations/OptimalLogarithmicShell.exp_one_unique_logarithmic_shell_minimizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The objective is displayed literally as beta divided by log beta on the source domain beta greater than one. It is not introduced as a target-shaped definition.

After substituting x = log beta, Mathlib's exponential tangent bound gives the global minimum. Equality would make log(beta/exp(1)) equal to beta/exp(1) - 1; the strict logarithm bound forces that ratio to one.

## References

- Truth anchor: `D5/S3/Constants/Characterizations/OptimalLogarithmicShell.exp_one_unique_logarithmic_shell_minimizer`
