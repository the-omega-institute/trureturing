# Innerness Self-Improvement

## Abstract

Iterated strict improvement whose thresholds converge to zero upgrades eventual innerness beyond one half to innerness at every positive width.

**Theorem 1.1 (Convergent threshold improvement reaches zero).**

$$\begin{aligned}\forall innerAt: \mathbb{R} \to \operatorname{Prop}, F: \mathbb{R} \to \mathbb{R},\\(\forall omega\in\mathbb{R}, \frac{1}{2} < omega \Rightarrow innerAt\left(omega\right)) \land (\forall a\in\mathbb{R}, 0 < a \land a \leq \frac{1}{2} \Rightarrow 0 < F\left(a\right) < a) \land\\(\forall a\in\mathbb{R}, 0 < a \land a \leq \frac{1}{2} \Rightarrow (\forall omega\in\mathbb{R}, a < omega \Rightarrow innerAt\left(omega\right)) \Rightarrow (\forall omega\in\mathbb{R}, F\left(a\right) < omega \Rightarrow innerAt\left(omega\right))) \land\\\operatorname{Tendsto}\left((n\mapsto\operatorname{iterate}\left(F, n, \frac{1}{2}\right)), 0\right) \Rightarrow\\\forall omega\in\mathbb{R}, 0 < omega \Rightarrow innerAt\left(omega\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Toroidal/InnernessSelfImprovement.innerness_self_improvement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write I(a) for innerness at every width omega greater than a. The initial hypothesis is I(1/2). At every positive threshold at most one half, F remains positive, is strictly smaller, and transports I(a) to I(F(a)).

Induction gives I at every iterate of one half while keeping each iterate in the positive half interval. Convergence to zero then places an iterate below any prescribed positive omega, whose I-property gives innerness at omega.

The convergence hypothesis repairs a gap in the source statement: strict decrease of an arbitrary, possibly discontinuous map does not imply that its iterates converge to zero. The nearby frozen threshold identity supplies context but no iterative improvement theorem.

## References

- Truth anchor: `D5/S3/Analytic/Toroidal/InnernessSelfImprovement.innerness_self_improvement`
