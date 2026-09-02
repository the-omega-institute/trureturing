# Cauchy KL Closed Form and Horizon Free Energy

## Abstract

The displayed Cauchy KL closed form is symmetric, nonnegative, rigid at zero, and reduces to the scalar horizon free energy for shifted scales.

**Definition 1.1 (Cauchy KL closed form).**

$$\forall gamma_{1}, delta_{1}, gamma_{2}, delta_{2} \in \mathbb{R},\ D_{C}(gamma_{1}, delta_{1} \Vert gamma_{2}, delta_{2}) = \operatorname{log}(\frac{\left(delta_{1} + delta_{2}\right)^{2} + \left(gamma_{1} - gamma_{2}\right)^{2}}{4 \cdot delta_{1} \cdot delta_{2}}).$$

*Formalization.* `D5/S3/Divergence/CauchyClosedForm.cauchyKL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For centers gamma-one and gamma-two and real scales delta-one and delta-two, cauchyKL is defined as the logarithm of the displayed rational expression. The divergence theorems below assume both scales are positive.

Mathlib provides cauchyMeasure and the measure-valued klDiv API, but the pinned library has no theorem evaluating klDiv between two non-identical Cauchy measures and no integral theorem for the required shifted logarithmic quadratic. Accordingly this is the atom's closed form as a real-valued definition, not a claim that the missing measure integral has been evaluated.

**Definition 1.2 (Scalar horizon free energy).**

$$\forall sigma \in \mathbb{R},\ F(sigma) = -\operatorname{log}(1 - sigma^{2}).$$

*Formalization.* `D5/S3/Divergence/CauchyClosedForm.horizonFreeEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a scalar singular-value ratio sigma, the horizon expression is minus log of one minus sigma squared. This definition records the rank-one scalar specialization; it does not introduce a Hankel operator or formalize the determinant in formula (1398.5).

**Theorem 1.3 (The Cauchy KL closed form is symmetric).**

$$\forall gamma_{1}, delta_{1}, gamma_{2}, delta_{2} \in \mathbb{R},\ D_{C}(gamma_{1}, delta_{1} \Vert gamma_{2}, delta_{2}) = D_{C}(gamma_{2}, delta_{2} \Vert gamma_{1}, delta_{1}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CauchyClosedForm.cauchy_kl_divergence_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Swapping the two laws preserves the squared scale sum, changes the location difference only by a sign before squaring, and merely reorders the two scale factors in the denominator. Hence this one-dimensional Cauchy closed form is symmetric, unlike KL divergence in general.

**Proposition 1.4 (The logarithm argument is at least one).**

$$\forall gamma_{1}, delta_{1}, gamma_{2}, delta_{2} \in \mathbb{R},\ (0 < delta_{1} \land 0 < delta_{2}) \Rightarrow 1 \le \frac{\left(delta_{1} + delta_{2}\right)^{2} + \left(gamma_{1} - gamma_{2}\right)^{2}}{4 \cdot delta_{1} \cdot delta_{2}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CauchyClosedForm.one_le_cauchy_kl_argument` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive scales the denominator is positive. After clearing it, the desired inequality is exactly the nonnegativity of the sum of the squared scale difference and squared center difference.

**Theorem 1.5 (The Cauchy KL closed form is nonnegative).**

$$\forall gamma_{1}, delta_{1}, gamma_{2}, delta_{2} \in \mathbb{R},\ (0 < delta_{1} \land 0 < delta_{2}) \Rightarrow 0 \le D_{C}(gamma_{1}, delta_{1} \Vert gamma_{2}, delta_{2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CauchyClosedForm.cauchy_kl_divergence_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The preceding lower bound places the logarithm argument at least at one, so monotonicity of the real logarithm gives nonnegativity.

**Theorem 1.6 (Zero Cauchy KL characterizes equal parameters).**

$$\forall gamma_{1}, delta_{1}, gamma_{2}, delta_{2} \in \mathbb{R},\ (0 < delta_{1} \land 0 < delta_{2}) \Rightarrow ((D_{C}(gamma_{1}, delta_{1} \Vert gamma_{2}, delta_{2}) = 0) \Leftrightarrow (gamma_{1} = gamma_{2} \land delta_{1} = delta_{2})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CauchyClosedForm.cauchy_kl_divergence_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The argument bound rules out the zero and minus-one branches of the real-logarithm zero theorem. The remaining equality at one reduces to a sum of two nonnegative squares being zero, forcing equality of both centers and both positive scales. The converse evaluates the logarithm at one.

**Theorem 1.7 (Shifted Cauchy KL equals the scalar horizon free energy).**

$$\forall gamma, delta, omega \in \mathbb{R},\ (0 < omega \land omega < delta) \Rightarrow D_{C}(gamma, delta - omega \Vert gamma, delta + omega) = F(\frac{omega}{delta}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CauchyClosedForm.shifted_cauchy_kl_eq_horizon_free_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For zero-less-than omega-less-than delta, the shifted scales delta minus omega and delta plus omega are both positive. Substitution into the equal-center Cauchy formula reduces its argument to the inverse of one minus (omega/delta) squared.

Taking the logarithm of that inverse yields minus log of one minus the squared ratio, exactly the scalar horizon free energy. This formalizes formulas (1398.2)--(1398.4). The source atom ends after displaying the separate operator determinant formula (1398.5), so no absent operator-level bridge is asserted.

## References

- Truth anchor: `D5/S3/Divergence/CauchyClosedForm.cauchyKL`
- Truth anchor: `D5/S3/Divergence/CauchyClosedForm.cauchy_kl_divergence_eq_zero_iff`
- Truth anchor: `D5/S3/Divergence/CauchyClosedForm.cauchy_kl_divergence_nonneg`
- Truth anchor: `D5/S3/Divergence/CauchyClosedForm.cauchy_kl_divergence_symm`
- Truth anchor: `D5/S3/Divergence/CauchyClosedForm.horizonFreeEnergy`
- Truth anchor: `D5/S3/Divergence/CauchyClosedForm.one_le_cauchy_kl_argument`
- Truth anchor: `D5/S3/Divergence/CauchyClosedForm.shifted_cauchy_kl_eq_horizon_free_energy`
