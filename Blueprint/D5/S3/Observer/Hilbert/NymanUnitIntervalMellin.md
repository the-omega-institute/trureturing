# Unit-Interval Mellin Separation

## Abstract

The unit-interval Mellin functional and the constrained Nyman distance obstruction.

Let mu be Lebesgue measure restricted to the open interval (0,1), and let H be the complex Hilbert space Lp(C,2,mu). The target 1 is the class of the constant function one. For every real theta, v_theta is the class of x |-> fract(theta/x), regarded as complex-valued. All almost-everywhere equalities and integrability statements below use mu. Complex powers on positive real bases use the real logarithm.

$H=\operatorname{Lp}(\mathbb{C},2,\mu), v_{\theta}(x)=_{\operatorname{ae}}\operatorname{fract}(\frac{\theta}{x})$

B_0 is exactly the set of finite complex sums below. The length n is any natural number, including zero; u ranges over Fin n to C and theta over Fin n to R. Every parameter satisfies zero less than theta_j at most one. The bar denotes closure in the metric of H.

$f\in B_{0}\iff \exists n\in \mathbb{N}, \exists u:\operatorname{Fin}(n)\to\mathbb{C}, \exists \theta:\operatorname{Fin}(n)\to\mathbb{R}, (\forall j,0<\theta_{j}\le1)\land \sum_{j}u_{j}\theta_{j}=0\land f=\sum_{j}u_{j}v_{\theta_{j}}$

**Theorem 1.1 (The constant representative).**

$$1=_{\operatorname{ae}}(x\mapsto 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.unitTarget_coe_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Lp target has the constant-one representative almost everywhere.

**Theorem 1.2 (Bounded measurable fractional parts).**

$$\forall \theta\in \mathbb{R}, \operatorname{MemLp}((x\mapsto \operatorname{fract}(\frac{\theta}{x})),2,\mu)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.source_memLp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fractional part is measurable and lies between zero and one. Finite measure therefore gives MemLp for every real theta, without a positivity restriction.

**Theorem 1.3 (The source representative).**

$$\forall \theta\in \mathbb{R}, v_{\theta}=_{\operatorname{ae}}(x\mapsto \operatorname{fract}(\frac{\theta}{x}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.source_coe_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source class is represented by the actual fractional-part function.

**Theorem 1.4 (Representatives of finite sums).**

$$\forall n,u,\theta, \sum_{j}u_{j}v_{\theta_{j}}=_{\operatorname{ae}}(x\mapsto \sum_{j}u_{j}\operatorname{fract}(\frac{\theta_{j}}{x}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.finite_sum_coe_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural length n, every u : Fin n to C, and every theta : Fin n to R, the Lp sum has the displayed function representative. This identity needs no coefficient constraint or parameter bounds.

**Theorem 1.5 (The empty sum).**

$$0\in B_{0}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.zero_mem_B0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum indexed by Fin zero satisfies the coefficient constraint and is zero.

**Theorem 1.6 (Nonempty metric closure).**

$$\overline{B_{0}}\neq\emptyset$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.closure_B0_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closure contains zero. Its metric infimum distance is therefore the distance to a nonempty set.

For real part of s greater than one half, k_s is the Lp class of x to the power conjugate(s) minus one. Define L_s f as the inner product of k_s with f. The inner product is conjugate-linear in its first argument and complex-linear in its second, so L_s is a continuous complex-linear functional.

$\forall s\in \mathbb{C}, \frac{1}{2}<\Re s\Rightarrow k_{s}(x)=_{\operatorname{ae}}x^{\overline{s}-1}, L_{s}(f)=\langle k_{s},f\rangle$

**Theorem 1.7 (Square integrability of the Riesz kernel).**

$$\forall s\in \mathbb{C}, \frac{1}{2}<\Re s\Rightarrow \operatorname{MemLp}((x\mapsto x^{\overline{s}-1}),2,\mu)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.kernel_memLp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The squared absolute value is x to the power 2 Re(s) minus 2, whose integral is finite precisely in the stated half-plane.

**Theorem 1.8 (The conjugated kernel representative).**

$$\forall s\in \mathbb{C}, \frac{1}{2}<\Re s\Rightarrow k_{s}=_{\operatorname{ae}}(x\mapsto x^{\overline{s}-1})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.kernel_coe_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Riesz vector has the stated representative almost everywhere.

**Theorem 1.9 (Integrability of the analytic pairing).**

$$\forall s\in \mathbb{C}, \frac{1}{2}<\Re s\Rightarrow \forall f\in H, \operatorname{Integrable}((x\mapsto f(x)x^{s-1}),\mu)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.pairing_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The L2 inner-product integrability theorem applies to k_s and every f in H. Conjugating the kernel gives the analytic power x to the power s minus one.

**Theorem 1.10 (Integrability for any equal representative).**

$$\forall s\in \mathbb{C}, \frac{1}{2}<\Re s\Rightarrow \forall f\in H, \forall g:\mathbb{R}\to\mathbb{C}, f=_{\operatorname{ae}}g\Rightarrow \operatorname{Integrable}((x\mapsto g(x)x^{s-1}),\mu)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.pairing_integrable_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every function almost everywhere equal to the Lp representative has an integrable pairing, with no additional measurability hypothesis.

**Theorem 1.11 (The actual Mellin integral).**

$$\forall s\in \mathbb{C}, \frac{1}{2}<\Re s\Rightarrow \forall f\in H, L_{s}(f)=\int_{0}^{1}f(x)x^{s-1}\,dx$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.mellinFunctional_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The continuous functional equals the literal Lebesgue integral over the open unit interval.

**Theorem 1.12 (Independence of representatives).**

$$\forall s\in \mathbb{C}, \frac{1}{2}<\Re s\Rightarrow \forall f\in H, \forall g:\mathbb{R}\to\mathbb{C}, f=_{\operatorname{ae}}g\Rightarrow L_{s}(f)=\int_{0}^{1}g(x)x^{s-1}\,dx$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.mellinFunctional_apply_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replacing the representative by any almost everywhere equal function leaves the integral unchanged.

**Theorem 1.13 (Exact squared kernel norm).**

$$\forall s\in \mathbb{C}, \frac{1}{2}<\Re s\Rightarrow \Vert k_{s}\Vert^{2}=\frac{1}{2\Re s-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.kernel_norm_sq_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integrating x to the power 2 Re(s) minus 2 gives the exact squared Hilbert norm.

**Theorem 1.14 (Exact squared operator norm).**

$$\forall s\in \mathbb{C}, \frac{1}{2}<\Re s\Rightarrow \Vert L_{s}\Vert^{2}=\frac{1}{2\Re s-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.mellinFunctional_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Riesz map is isometric, so the squared operator norm equals the squared kernel norm.

**Theorem 1.15 (Exact operator norm).**

$$\forall s\in \mathbb{C}, \frac{1}{2}<\Re s\Rightarrow \Vert L_{s}\Vert=\frac{1}{\sqrt{2\Re s-1}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.mellinFunctional_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both sides are nonnegative and their squares agree. The square root is positive in this half-plane.

**Theorem 1.16 (Evaluation on the target).**

$$\forall s\in \mathbb{C}, \frac{1}{2}<\Re s\Rightarrow L_{s}(1)=\frac{1}{s}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.mellinFunctional_unitTarget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unit-interval integral of x to the power s minus one is one over s. The half-plane condition excludes s equal to zero.

**Theorem 1.17 (Evaluation on every real-parameter source).**

$$\forall \theta\in \mathbb{R}, 0<\theta\le1\Rightarrow \forall s\in \mathbb{C}, \frac{1}{2}<\Re s\Rightarrow \Re s<1\Rightarrow L_{s}(v_{\theta})=\frac{\theta}{s-1}-\frac{\theta^{s}\zeta(s)}{s}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.mellinFunctional_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fractional-part Mellin identity evaluates the actual source for every real theta in (0,1], in the strip one half less than Re(s) less than one.

**Theorem 1.18 (Annihilation of constrained finite sums).**

$$\forall \rho\in \mathbb{C}, \zeta(\rho)=0\land \frac{1}{2}<\Re \rho<1\Rightarrow \forall f\in B_{0},L_{\rho}(f)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.mellinFunctional_B0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a zero the zeta term vanishes. Complex linearity reduces each finite sum to the coefficient constraint divided by rho minus one.

**Theorem 1.19 (Annihilation of the entire closure).**

$$\forall \rho\in \mathbb{C}, \zeta(\rho)=0\land \frac{1}{2}<\Re \rho<1\Rightarrow \forall f\in \overline{B_{0}},L_{\rho}(f)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.mellinFunctional_closure_B0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kernel of a continuous linear functional is closed, and contains B_0, hence contains its metric closure.

**Theorem 1.20 (Distance obstruction in the explicit strip).**

$$\forall \rho\in \mathbb{C}, \zeta(\rho)=0\land \frac{1}{2}<\Re \rho<1\Rightarrow \frac{\sqrt{2\Re \rho-1}}{\Vert \rho\Vert}\le \operatorname{infDist}(1,\overline{B_{0}})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.nyman_unitInterval_zero_obstruction_of_strip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every f in the closure, the operator norm bounds the absolute value of L_rho(1-f). Its value is one over rho. Positivity of the norm of rho and of the square root permits division, and the nonempty-set characterization of infimum distance gives the result.

**Theorem 1.21 (Domain of a nontrivial zero).**

$$\forall \rho\in \mathbb{C}, \operatorname{IsNontrivialZero}(\rho)\Rightarrow \Re \rho<1\land \rho\neq0\land \rho\neq1\land 0<\Vert \rho\Vert$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.nontrivial_zero_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

IsNontrivialZero is the canonical Zeta23 predicate: zeta(rho) equals zero and zero less than Re(rho) less than one. This gives the upper strip bound, excludes zero and one, and makes the denominator positive.

**Theorem 1.22 (The canonical-zero distance obstruction).**

$$\forall \rho\in \mathbb{C}, \operatorname{IsNontrivialZero}(\rho)\Rightarrow \frac{1}{2}<\Re \rho\Rightarrow \frac{\sqrt{2\Re \rho-1}}{\Vert \rho\Vert}\le \operatorname{infDist}(1,\overline{B_{0}})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.nyman_unitInterval_zero_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual nontrivial zero with real part greater than one half gives the stated lower bound on the unit-interval distance. This is conditional and asserts no existence of such a zero.

**Theorem 1.23 (Mellin identity and zero obstruction together).**

$$\begin{gathered}(\forall \theta\in \mathbb{R}, 0<\theta\le1\Rightarrow \forall s\in \mathbb{C}, 0<\Re s<1\Rightarrow \int_{0}^{1}\operatorname{fract}(\frac{\theta}{x})x^{s-1}\,dx=\frac{\theta}{s-1}-\frac{\theta^{s}\zeta(s)}{s})\\\land (\forall \rho\in \mathbb{C}, \operatorname{IsNontrivialZero}(\rho)\Rightarrow \frac{1}{2}<\Re \rho\Rightarrow \Vert L_{\rho}\Vert=\frac{1}{\sqrt{2\Re \rho-1}}\land L_{\rho}(1)=\frac{1}{\rho}\land (\forall f\in \overline{B_{0}}, L_{\rho}(f)=0)\land \frac{\sqrt{2\Re \rho-1}}{\Vert \rho\Vert}\le \operatorname{infDist}(1,\overline{B_{0}}))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.nyman_unitInterval_mellin_and_zero_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first conjunct states the fractional-part identity for every real theta in (0,1] and every complex s with zero less than Re(s) less than one. Independently, the second conjunct quantifies over all canonical nontrivial zeros with real part greater than one half, and states the exact norm, target value, annihilation of the whole closure, and distance lower bound. The underlying functional and all source vectors are those on H defined above.

## References

- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.closure_B0_nonempty`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.finite_sum_coe_ae`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.kernel_coe_ae`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.kernel_memLp`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.kernel_norm_sq_exact`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.mellinFunctional_B0`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.mellinFunctional_apply`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.mellinFunctional_apply_representative`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.mellinFunctional_closure_B0`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.mellinFunctional_norm`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.mellinFunctional_norm_sq`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.mellinFunctional_source`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.mellinFunctional_unitTarget`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.nontrivial_zero_domain`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.nyman_unitInterval_mellin_and_zero_obstruction`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.nyman_unitInterval_zero_obstruction`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.nyman_unitInterval_zero_obstruction_of_strip`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.pairing_integrable`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.pairing_integrable_representative`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.source_coe_ae`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.source_memLp`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.unitTarget_coe_ae`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.zero_mem_B0`
- Dependency: [D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin](../../Weil/ZetaPntBounds/NymanFractionalMellin.md)
