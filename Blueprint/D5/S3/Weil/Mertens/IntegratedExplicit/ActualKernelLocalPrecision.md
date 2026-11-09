# Actual arithmetic local precision controls

## Abstract

Literal arithmetic derivative and cusp controls for the actual complete kernel, including strict log convexity of its negative first derivative.

**Definition 1.1 (Literal third derivative expression).**

$$\forall t \in \mathbb{R},\; \operatorname{D3}\left(t\right) = \frac{\operatorname{D1}\left(t\right)}{4} - \frac{\operatorname{Real.exp}\left(\frac{t}{2}\right)}{2} - \frac{\operatorname{Real.exp}\left(\frac{-t}{2}\right)}{2 \cdot \left(\operatorname{Real.exp}\left(2 \cdot t\right) - 1\right)} - \frac{2 \cdot \operatorname{Real.exp}\left(\frac{3 \cdot t}{2}\right)}{\left(\operatorname{Real.exp}\left(2 \cdot t\right) - 1\right)^{2}}$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPrecision.D3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D3(t)=D1(t)/4-exp(t/2)/2-exp(-t/2)/(2*(exp(2*t)-1))-2*exp(3*t/2)/(exp(2*t)-1)^2. This definition is a new literal formula and is not an assumption about the actual K.

**Lemma 1.2 (Differentiate the actual second derivative).**

$$\forall t \in \mathbb{R},\; \left(0 < t \land t < \operatorname{Real.log}\left(2\right)\right) \Rightarrow \operatorname{HasDerivAt}\left(\operatorname{D2}, \operatorname{D3}\left(t\right), t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPrecision.hasDerivAt_D2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every 0<t<log(2), the public D2 has derivative D3(t). The proof differentiates K(t)/4-exp(t/2)+exp(-t/2)/(exp(2*t)-1), using the actual public hasDerivAt_K and the strictly positive denominator. The exponential identity exp(3*t/2)=exp(-t/2)*exp(2*t) gives precisely the displayed expression.

**Theorem 1.3 (A common arithmetic derivative-control window).**

$$\exists delta \in \mathbb{R},\; \left(\left(\left(\left(\left(0 < delta \land delta < \operatorname{Real.log}\left(2\right)\right) \land delta \le \operatorname{Real.exp}\left(-1\right)\right) \land \left(\forall t \in \operatorname{Set.Ioc}\left(0, delta\right),\; \left(\left(\left(\left(\left(\frac{\operatorname{K}\left(0\right)}{2} \le \operatorname{K}\left(t\right) \land \operatorname{D1}\left(t\right) < 0\right) \land \frac{1}{4 \cdot t} \le \operatorname{D2}\left(t\right)\right) \land \operatorname{D2}\left(t\right) \le \frac{1}{t}\right) \land -\operatorname{D1}\left(t\right) \le \operatorname{Real.log}\left(\frac{1}{t}\right)\right) \land 0 < \operatorname{K}\left(t\right) \cdot \operatorname{D2}\left(t\right) - \operatorname{D1}\left(t\right)^{2}\right) \land 0 < -\operatorname{D1}\left(t\right) \cdot \left(-\operatorname{D3}\left(t\right)\right) - \left(-\operatorname{D2}\left(t\right)\right)^{2}\right)\right) \land \left(\forall t \in \operatorname{Set.Ioo}\left(0, delta\right),\; \operatorname{HasDerivAt}\left(\operatorname{D2}, \operatorname{D3}\left(t\right), t\right)\right)\right) \land \operatorname{StrictConvexOn}\left(\mathbb{R}, \operatorname{Set.Icc}\left(0, delta\right), (\lambda t \mapsto \operatorname{Real.log}\left(\operatorname{K}\left(t\right)\right))\right)\right) \land \operatorname{StrictConvexOn}\left(\mathbb{R}, \operatorname{Set.Ioo}\left(0, delta\right), (\lambda t \mapsto \operatorname{Real.log}\left(-\operatorname{D1}\left(t\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPrecision.exists_derivative_control_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists one 0<delta<log(2), with delta<=exp(-1), on which K(t)>=K(0)/2, D1(t)<0, 1/(4*t)<=D2(t)<=1/t, -D1(t)<=log(1/t), and both displayed logarithmic-curvature numerators are positive. The derivative identity for D2 holds throughout the open interval. Strict convexity of log(K) is proved on the CLOSED interval [0,delta], using continuity at 0; strict convexity of log(-D1) is proved on (0,delta), without assigning a continuous derivative value at 0.

$\left(\left(\left(\left(\operatorname{Filter.Tendsto}\left((\lambda t \mapsto \frac{-\operatorname{D1}\left(t\right)}{\operatorname{Real.log}\left(\frac{1}{t}\right)}), \operatorname{nhdsGT}\left(0\right), \operatorname{nhds}\left(\frac{1}{2}\right)\right) \land \operatorname{Filter.Tendsto}\left((\lambda t \mapsto t \cdot \operatorname{D2}\left(t\right)), \operatorname{nhdsGT}\left(0\right), \operatorname{nhds}\left(\frac{1}{2}\right)\right)\right) \land \operatorname{Filter.Tendsto}\left((\lambda t \mapsto t \cdot \operatorname{D1}\left(t\right)^{2}), \operatorname{nhdsGT}\left(0\right), \operatorname{nhds}\left(0\right)\right)\right) \land \operatorname{Filter.Tendsto}\left((\lambda t \mapsto t^{2} \cdot \operatorname{D3}\left(t\right)), \operatorname{nhdsGT}\left(0\right), \operatorname{nhds}\left(-\frac{1}{2}\right)\right)\right) \land \operatorname{Filter.Tendsto}\left((\lambda t \mapsto t \cdot \left(\operatorname{K}\left(t\right) \cdot \operatorname{D2}\left(t\right) - \operatorname{D1}\left(t\right)^{2}\right)), \operatorname{nhdsGT}\left(0\right), \operatorname{nhds}\left(\frac{\operatorname{K}\left(0\right)}{2}\right)\right)\right) \land \operatorname{Filter.Tendsto}\left((\lambda t \mapsto \frac{t^{2} \cdot \left(-\operatorname{D1}\left(t\right) \cdot \left(-\operatorname{D3}\left(t\right)\right) - \left(-\operatorname{D2}\left(t\right)\right)^{2}\right)}{\operatorname{Real.log}\left(\frac{1}{t}\right)}), \operatorname{nhdsGT}\left(0\right), \operatorname{nhds}\left(\frac{1}{4}\right)\right)$

All displayed limits are right limits as t approaches 0. The proof directly reuses ActualKernelLocalPositivity.exp_ratio_limit for t/(exp(2*t)-1)->1/2 and its weighted_D1_limit and weighted_D2_limit for the weighted derivative limits. The public log_argument_ratio_limit gives log(1-exp(-2*t))+log(1/t)->-log(1/2). Substituting into the literal D1 gives (-D1)/log(1/t)->1/2. The literal term multiplying exp(-t/2) is log(2*pi)+log(1-exp(-2*t))/2: log(2*pi) is not halved.

$\forall t \in \mathbb{R},\; \operatorname{D1}\left(t\right) = \frac{\operatorname{K}\left(t\right)}{2} - \operatorname{Real.exp}\left(\frac{t}{2}\right) + \operatorname{Real.exp}\left(\frac{-t}{2}\right) \cdot \left(\operatorname{Real.log}\left(2 \cdot \operatorname{Real.pi}\right) + \frac{\operatorname{Real.log}\left(1 - \operatorname{Real.exp}\left(-\left(2 \cdot t\right)\right)\right)}{2}\right)$

The proof separately derives t*D1(t)^2->0 from t*log(1/t)^2->0 and the normalized D1 limit. It does not infer this square estimate merely from t*D1(t)->0. Multiplying the reused t*D2(t)->1/2 by continuity of K yields t*(K*D2-D1^2)->K(0)/2. Differentiating D2 gives t^2*D3(t)->-1/2. With h=-D1, h'=-D2 and h''=-D3, the normalized h-curvature tends to 1/4.

The private log-convexity helpers use the actual quotient derivative f'/f, the numerator f*f''-(f')^2, and Mathlib.strictConvexOn_of_deriv2_pos. The closed-endpoint K proof uses continuity of log(K) at 0 and differentiates only in the interior. Positivity of K(0) directly reuses ActualKernelLocalPositivity.K_zero_pos, with no RH premise.

The arithmetic application uses v=K(0)-K, h=-D1 and g=D2. The generic module proves v(t)=integral from 0 to t of h, positivity and v(t)<=t*log(exp(1)/t), using logarithmic integrability and the actual endpoint limit of v. The positive-definite input is the existing public exists_window_posDef, whose conclusion is COMPLEX Matrix.PosDef. The transient example first applies real_posDef_of_complex and only then passes a real matrix to the generic criterion. Evenness follows from the public literal definition of K.

$\exists delta \in \mathbb{R},\; 0 < delta \land \left(\forall x \in \operatorname{Fin}\left(4\right) \to \mathbb{R},\; \left(\operatorname{Function.Injective}\left(x\right) \land \left(\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \left|x\left(i\right) - x\left(j\right)\right| \le delta\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; i \ne j \Rightarrow \left((\lambda i \mapsto (\lambda j \mapsto \operatorname{K}\left(x\left(i\right) - x\left(j\right)\right)))^{-1}\right)\left(i, j\right) < 0\right)\right)$

The derivative controls and both logarithmic convexities hold on one common local window. Together with real positive definiteness they imply the uniform four-node precision signs. They do not supply an arbitrary-dimensional precision theorem or a global representation.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPrecision.D3`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPrecision.exists_derivative_control_window`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPrecision.hasDerivAt_D2`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity](ActualKernelLocalPositivity.md)
