# Horizontal transport of conjugate-pair slopes

## Abstract

Entire complex functions obey horizontal transport of their actual conjugate-pair divided differences on the closed unit disk.

**Definition 1.1 (The original closed-disk norm).**

$$(\forall g : \mathbb{C} \to \mathbb{C}, \operatorname{M}\left(g\right) = \operatorname{sSup}\left(\operatorname{normSecondDerivativeImageOfClosedUnitDisk}\left(g\right)\right))$$

*Formalization.* `D5/S3/Analytic/Interpolation/SchurConjugateSlope.diskNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

M(g) is the real supremum of the norms of the complex second derivative over the closed unit disk. For entire g the image is nonempty and bounded, by continuity and compactness.

**Definition 1.2 (The actual divided difference).**

$$(\forall g : \mathbb{C} \to \mathbb{C}, (\forall a : \mathbb{R}, (\forall b : \mathbb{R}, \operatorname{S}\left(g, a, b\right) = \frac{\operatorname{g}\left(a+bi\right)-\operatorname{g}\left(a-bi\right)}{2bi})))$$

*Formalization.* `D5/S3/Analytic/Interpolation/SchurConjugateSlope.slope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two values are evaluated independently at a+ib and a-ib. No relation between those values is assumed. The denominator is nonzero when b>0.

**Definition 1.3 (The original two-node Lagrange expression).**

$$(\forall g : \mathbb{C} \to \mathbb{C}, (\forall a : \mathbb{R}, (\forall b : \mathbb{R}, (\forall z : \mathbb{C}, \operatorname{interpolant}\left(g, a, b, z\right) = \frac{z-(a-bi)}{2bi}\operatorname{g}\left(a+bi\right)+\frac{(a+bi)-z}{2bi}\operatorname{g}\left(a-bi\right)))))$$

*Formalization.* `D5/S3/Analytic/Interpolation/SchurConjugateSlope.interpolant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For b>0 the displayed affine polynomial interpolates g at the distinct conjugate nodes. The formula uses complex division.

**Definition 1.4 (The actual nodal polynomial).**

$$(\forall a : \mathbb{R}, (\forall b : \mathbb{R}, (\forall z : \mathbb{C}, \operatorname{nodalPolynomial}\left(a, b, z\right) = (z-(a+bi))(z-(a-bi)))))$$

*Formalization.* `D5/S3/Analytic/Interpolation/SchurConjugateSlope.nodalPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial is the original product (z-(a+ib))(z-(a-ib)). Its derivative is 2(z-a), including for every nonreal unit-circle pair.

**Definition 1.5 (The original nodal derivative norm).**

$$(\forall a : \mathbb{R}, (\forall b : \mathbb{R}, \operatorname{nodalDerivativeNorm}\left(a, b\right) = \operatorname{sSup}\left(\operatorname{nodalDerivativeNormValues}\left(a, b\right)\right)))$$

*Formalization.* `D5/S3/Analytic/Interpolation/SchurConjugateSlope.nodalDerivativeNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real supremum is over the norms of the actual complex derivative at real x in the closed interval [-1,1]. The value set is nonempty and bounded and its supremum is attained.

**Theorem 1.6 (The Lagrange derivative).**

$$(\forall g : \mathbb{C} \to \mathbb{C}, (\forall a : \mathbb{R}, (\forall b : \mathbb{R}, (\forall z : \mathbb{C}, \operatorname{deriv}\left(\operatorname{interpolant}\left(g, a, b\right), z\right) = \operatorname{S}\left(g, a, b\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/SchurConjugateSlope.interpolant_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every complex test point the derivative is the original divided difference. This identity is algebraic and does not require analyticity of g.

**Theorem 1.7 (Horizontal transport for every entire function).**

$$(\forall g : \mathbb{C} \to \mathbb{C}, (\forall a : \mathbb{R}, (\forall b : \mathbb{R}, \operatorname{Entire}\left(g\right) \land 0 < b \land a^{2} + b^{2} \le 1 \implies \operatorname{norm}\left(\operatorname{S}\left(g, a, b\right)-\operatorname{S}\left(g, 0, b\right)\right) \le \operatorname{abs}\left(a\right)\operatorname{M}\left(g\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/SchurConjugateSlope.slope_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let g be entire, let a and b be real, b>0 and a squared plus b squared at most one. Then |S(g,a,b)-S(g,0,b)| <= |a| M(g). Both signs of a and all closed-segment endpoints are included. The derivative of g is M(g)-Lipschitz on the closed disk. At each horizontal coordinate s between zero and a, the vertical divided difference of g prime therefore has norm at most M(g). Applying the real mean value bound to the actual slope gives the estimate. There is no real-coefficient hypothesis and no use of conjugation of function values.

**Definition 1.8 (The original entire-function class).**

$$(\forall g : \mathbb{C} \to \mathbb{C}, \operatorname{member}\left(g, \operatorname{E}\left(\right)\right) \iff \operatorname{Entire}\left(g\right) \land \operatorname{M}\left(g\right) \le 1)$$

*Formalization.* `D5/S3/Analytic/Interpolation/SchurConjugateSlope.entireClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E consists of all complex-coefficient entire functions g with M(g) at most one. The norm is on the original closed disk.

**Definition 1.9 (The inner value set).**

$$(\forall g : \mathbb{C} \to \mathbb{C}, (\forall a : \mathbb{R}, (\forall b : \mathbb{R}, \operatorname{V}\left(g, a, b\right) = \operatorname{image}\left(\operatorname{actualError}\left(g, a, b\right), \operatorname{Icc}\left(-1, 1\right)\right))))$$

*Formalization.* `D5/S3/Analytic/Interpolation/SchurConjugateSlope.innerValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

V(g,a,b) is the image of the closed real interval [-1,1] under x mapped to the norm of g prime at x minus the actual Lagrange derivative at x.

**Definition 1.10 (The outer value set).**

$$(\forall a : \mathbb{R}, (\forall b : \mathbb{R}, \operatorname{W}\left(a, b\right) = \operatorname{image}\left(\operatorname{innerSupremum}\left(a, b\right), \operatorname{E}\left(\right)\right)))$$

*Formalization.* `D5/S3/Analytic/Interpolation/SchurConjugateSlope.outerValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

W(a,b) is the image of the original entire-function class under g mapped to the real supremum of V(g,a,b).

**Definition 1.11 (The original nested uniform supremum).**

$$(\forall a : \mathbb{R}, (\forall b : \mathbb{R}, \operatorname{uniformError}\left(a, b\right) = \operatorname{sSup}\left(\operatorname{W}\left(a, b\right)\right)))$$

*Formalization.* `D5/S3/Analytic/Interpolation/SchurConjugateSlope.uniformError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supremum over g is outside the supremum over x, exactly as in Definition 9.1. No limit or supremum is interchanged.

**Theorem 1.12 (Bounded original suprema and an actual quadratic witness).**

$$(\forall a : \mathbb{R}, (\forall b : \mathbb{R}, 0 < b \land a^{2}+b^{2} \le 1 \implies \operatorname{Nonempty}\left(\operatorname{E}\left(\right)\right) \land ((\forall g : \mathbb{C} \to \mathbb{C}, \operatorname{member}\left(g, \operatorname{E}\left(\right)\right) \implies \operatorname{Nonempty}\left(\operatorname{V}\left(g, a, b\right)\right) \land \operatorname{BddAbove}\left(\operatorname{V}\left(g, a, b\right)\right) \land (\exists z \in \operatorname{closedBall}\left(0, 1\right), \operatorname{M}\left(g\right) = \operatorname{normSecondDerivative}\left(g, z\right)) \land \exists x \in \operatorname{Icc}\left(-1, 1\right), \operatorname{sSup}\left(\operatorname{V}\left(g, a, b\right)\right) = \operatorname{actualError}\left(g, a, b, x\right))) \land \operatorname{Nonempty}\left(\operatorname{W}\left(a, b\right)\right) \land \operatorname{BddAbove}\left(\operatorname{W}\left(a, b\right)\right) \land 1+\operatorname{abs}\left(a\right) \le \operatorname{uniformError}\left(a, b\right) \land \operatorname{uniformError}\left(a, b\right) \le 2 \land \exists g \in \operatorname{E}\left(\right), g = \operatorname{quadratic}\left(\right) \land \operatorname{M}\left(g\right) = 1 \land \operatorname{S}\left(g, a, b\right) = a \land ((\forall x : \mathbb{R}, \operatorname{actualError}\left(g, a, b, x\right) = \operatorname{abs}\left(x-a\right))) \land \operatorname{sSup}\left(\operatorname{V}\left(g, a, b\right)\right) = 1+\operatorname{abs}\left(a\right) \land \operatorname{nodalDerivativeNorm}\left(a, b\right) = 2(1+\operatorname{abs}\left(a\right)) \land \frac{1}{2}\operatorname{nodalDerivativeNorm}\left(a, b\right) = 1+\operatorname{abs}\left(a\right) \land \exists x \in \operatorname{Icc}\left(-1, 1\right), \operatorname{nodalDerivativeNorm}\left(a, b\right) = \operatorname{normNodalDerivative}\left(a, b, x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/SchurConjugateSlope.original_suprema_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every admissible a,b both original value sets are nonempty and bounded. For every member, compactness gives an actual point attaining the disk norm and an actual real point attaining the inner supremum. The existential witness is explicitly the entire quadratic quadratic(z)=z squared divided by two. It has disk norm one, slope a, error |x-a| and inner supremum 1+|a|. This value is attained at -1 for a nonnegative and at 1 for a nonpositive, with both endpoints when a=0. The actual nodal derivative norm is 2(1+|a|), so its half-norm is 1+|a|; a real endpoint attains the norm. The norm value set is nonempty and bounded. The coarse estimate uses the horizontal transport theorem and the imaginary-axis bound sqrt(1+b squared) M(g), whose sum with |a| M(g) is at most 2 M(g). This gives uniformError at most two. The following classification supplies the sharp upper estimate uniformError at most 1+|a|.

**Theorem 1.13 (The complete original uniform identity).**

$$(\forall a : \mathbb{R}, (\forall b : \mathbb{R}, 0 < b \land a^{2}+b^{2} \le 1 \implies \operatorname{uniformError}\left(a, b\right) = 1+\operatorname{abs}\left(a\right) \land \operatorname{uniformError}\left(a, b\right) = \frac{1}{2}\operatorname{nodalDerivativeNorm}\left(a, b\right) \land (\forall g \in \operatorname{E}\left(\right), (\forall x \in \operatorname{Icc}\left(-1, 1\right), \operatorname{actualError}\left(g, a, b, x\right) \le 1+\operatorname{abs}\left(a\right))) \land \operatorname{Nonempty}\left(\operatorname{E}\left(\right)\right) \land (\forall g \in \operatorname{E}\left(\right), \operatorname{Nonempty}\left(\operatorname{V}\left(g, a, b\right)\right) \land \operatorname{BddAbove}\left(\operatorname{V}\left(g, a, b\right)\right) \land (\exists z \in \operatorname{closedBall}\left(0, 1\right), \operatorname{M}\left(g\right) = \operatorname{normSecondDerivative}\left(g, z\right)) \land (\exists x \in \operatorname{Icc}\left(-1, 1\right), \operatorname{sSup}\left(\operatorname{V}\left(g, a, b\right)\right) = \operatorname{actualError}\left(g, a, b, x\right))) \land \operatorname{Nonempty}\left(\operatorname{W}\left(a, b\right)\right) \land \operatorname{BddAbove}\left(\operatorname{W}\left(a, b\right)\right) \land (\exists g \in \operatorname{E}\left(\right), g = \operatorname{quadratic}\left(\right) \land \operatorname{M}\left(g\right) = 1 \land \operatorname{S}\left(g, a, b\right) = a \land (\forall x : \mathbb{R}, \operatorname{actualError}\left(g, a, b, x\right) = \operatorname{abs}\left(x-a\right)) \land \operatorname{sSup}\left(\operatorname{V}\left(g, a, b\right)\right) = \operatorname{uniformError}\left(a, b\right) \land (0 \le a \implies \operatorname{actualError}\left(g, a, b, -1\right) = \operatorname{uniformError}\left(a, b\right)) \land (a \le 0 \implies \operatorname{actualError}\left(g, a, b, 1\right) = \operatorname{uniformError}\left(a, b\right)) \land (\exists x \in \operatorname{Icc}\left(-1, 1\right), \operatorname{nodalDerivativeNorm}\left(a, b\right) = \operatorname{normNodalDerivative}\left(a, b, x\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/SchurConjugateSlope.complete_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a,b with b>0 and a squared plus b squared at most one, every member of the original arbitrary-complex entire class and every real x in the closed interval obey the sharp pointwise error bound 1+|a|. The original nested supremum equals 1+|a| and half the actual nodal derivative norm. The entire class and the inner and outer value sets are nonempty and bounded. Every entire member attains its disk norm and inner supremum on the original compact domains. The actual entire quadratic g(z)=z squared divided by two belongs to the original class, has disk norm one and slope a, and has error |x-a| for every real x. Its inner supremum equals the outer supremum, so it attains the outer optimization. The far endpoint -1 attains that value for a>=0 and the endpoint 1 does so for a<=0; both endpoints attain it at a=0. A real endpoint also attains the actual nodal derivative norm. To obtain the upper estimate, take h=g double prime and H=g prime minus g prime at zero. The actual vertical-segment FTC identifies the normalized primitive average with S(g,0,b)-g prime at zero. The sharp primitive bound gives |g prime(x)-S(g,0,b)|<=M(g). Actual horizontal transport adds |a|M(g). Multiplying by M(g)<=1 bounds each member and each point. The two suprema are then bounded in their original order; no limit is exchanged with a supremum. The quadratic gives the reverse inequality. All equalities and estimates use the closed admissibility inequality throughout, including b=1, x=-1, x=1 and every nonreal unit-circle conjugate pair.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/SchurConjugateSlope.complete_classification`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurConjugateSlope.diskNorm`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurConjugateSlope.entireClass`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurConjugateSlope.innerValues`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurConjugateSlope.interpolant`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurConjugateSlope.interpolant_deriv`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurConjugateSlope.nodalDerivativeNorm`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurConjugateSlope.nodalPolynomial`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurConjugateSlope.original_suprema_bounded`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurConjugateSlope.outerValues`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurConjugateSlope.slope`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurConjugateSlope.slope_transport`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurConjugateSlope.uniformError`
- Dependency: [D5/S3/Analytic/Interpolation/SchurIntegratedKernel](SchurIntegratedKernel.md)
