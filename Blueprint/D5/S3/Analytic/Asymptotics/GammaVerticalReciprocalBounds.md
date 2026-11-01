# Reciprocal Gamma on vertical strips

## Abstract

The reciprocal Gamma function has polynomial-exponential growth on bounded vertical strips.

**Theorem 1.1 (Uniform reciprocal Gamma bound).**

$$\forall X \in Real,\; \exists C \in Real,\; \exists K \in Nat,\; \forall x \in Real,\; \left(-(X) \le x \land x \le X\right) \Rightarrow \left(\forall y \in Real,\; \left\lVert \frac{1}{ComplexGamma\left((x+(\operatorname{ComplexI}*y))\right)} \right\rVert \le ((C*(1+\left|y\right|)^{K})*exp\left(\frac{(\pi *\left|y\right|)}{2}\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/GammaVerticalReciprocalBounds.exists_norm_recip_Gamma_le` (`✓ std3`). ∎

*Citation.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

For every real X there are a real constant C and a natural K such that the bound holds for all real x in [-X,X] and every real y. ComplexGamma denotes complex Gamma, pi the circle constant and i the imaginary unit. The inverse is totalized, so zeros of reciprocal Gamma are included. The proof compares the Gamma modulus product with its half-integer value cosh(pi*y), then uses the entire reciprocal-Gamma recurrence to cover the bounded strip.

**Theorem 1.2 (Integrable polynomial-exponential majorant).**

$$\forall c \in Real,\; 0 < c \Rightarrow \left(\forall K \in Nat,\; Integrable\left((y:Real \mapsto ((1+\left|y\right|)^{K}*exp\left(-((c*\left|y\right|))\right)))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/GammaVerticalReciprocalBounds.integrable_one_add_abs_pow_mul_exp_neg` (`✓ std3`). ∎

*Citation.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

For every positive real c and natural K the displayed real function is Lebesgue integrable. Half of the exponential decay absorbs the polynomial; the remaining half is the two-sided exponential integral.

**Theorem 1.3 (The retained real Gamma denominator).**

$$\forall x \in Real,\; \frac{1}{2} \le x \Rightarrow \left(\forall y \in Real,\; \left\lVert \frac{1}{ComplexGamma\left((x+(\operatorname{ComplexI}*y))\right)} \right\rVert^{2} \le \frac{exp\left((\pi *\left|y\right|)\right)}{RealGamma\left(x\right)^{2}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/GammaVerticalReciprocalBounds.norm_recip_Gamma_sq_le` (`✓ std3`). ∎

*Citation.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

The existing squared estimate retains Gamma(x)^2 for all real x at least one half. The literal Barnes moving-left estimate consumes it directly, including arbitrarily large x.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/GammaVerticalReciprocalBounds.exists_norm_recip_Gamma_le`
- Truth anchor: `D5/S3/Analytic/Asymptotics/GammaVerticalReciprocalBounds.integrable_one_add_abs_pow_mul_exp_neg`
- Truth anchor: `D5/S3/Analytic/Asymptotics/GammaVerticalReciprocalBounds.norm_recip_Gamma_sq_le`
- Dependency: [D5/S3/Analytic/Asymptotics/ExponentialAbsIntegrability](ExponentialAbsIntegrability.md)
