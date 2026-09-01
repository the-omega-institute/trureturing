# Golden Shell Moment Discretization

## Abstract

Golden geometric shells recover every positive finite defect moment within a fixed factor.

**Theorem 1.1 (Golden shells give a multiplicative moment sandwich).**

$$\begin{gathered}\forall \iota,\\m, \delta: \iota\to \mathbb{R},\\n: \iota\to \mathbb{N}, s\in\mathbb{R},\\\operatorname{Finite}(\iota) \land \left(0 < s \land \left(\left(\forall i \in \iota,\; 0 \le m\left(i\right)\right) \land \left(\forall i \in \iota,\; \omega\left(n\left(i\right) + 1\right) < \delta\left(i\right) \land \delta\left(i\right) \le \omega\left(n\left(i\right)\right)\right)\right)\right) \Rightarrow\\\varphi^{-2s} \cdot \left(\mathcal{G}_{\perp}\right)\left(s\right) \le \left(\zeta_{\perp}\right)\left(s\right) \land \left(\zeta_{\perp}\right)\left(s\right) \le \left(\mathcal{G}_{\perp}\right)\left(s\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/GoldenShellMomentDiscretization.golden_shell_moment_sandwich` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite family of defects carry nonnegative real weights. Assign each defect delta(i) to the unique supplied shell n(i), between the successive radii omega(n(i)+1) and omega(n(i)). For every positive real exponent s, its exact weighted moment lies between the golden shell transcript and phi^(-2s) times that transcript.

The shell radius is omega(n)=(1/2) phi^(-2n). Consecutive radii differ by the positive ratio phi^(-2). Positive real powers preserve each pointwise shell inequality, nonnegative weights preserve order, and finite summation gives the displayed sandwich.

Finite indexing is the finite-support specialization of the source's shell charges. It removes convergence assumptions without changing the regrouped weighted sum. The positive-exponent and nonnegative-weight hypotheses are explicit because reversing either sign can reverse the claimed inequalities.

The module also proves the exponent-two factor phi^(-4). A singleton at delta=1/2 computes both second moments as 1/4; moving it to delta=1 breaks the shell premise and computes the exact moment as 1 while the transcript remains 1/4, so the upper conclusion is false.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/GoldenShellMomentDiscretization.golden_shell_moment_sandwich`
