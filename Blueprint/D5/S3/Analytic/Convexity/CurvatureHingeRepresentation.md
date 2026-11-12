# Convex curvature and finite hinge remainders

## Abstract

Every real convex function on the positive ray has a locally finite Stieltjes curvature and a two-sided hinge representation.

Positive is the subtype of strictly positive real numbers. Subtype coercions are suppressed in the formulas. The derivative is always the actual right derivative. Curvature is the Stieltjes measure of that derivative on Positive. Its total mass, and its mass near zero, may be infinite. No smoothness, atomlessness, absolute continuity or full-support hypothesis is used. The measure in every displayed curvature integral is curvature h.

**Definition 1.1 (Positive).**

$$\operatorname{Positive}\left(\right) = (\operatorname{Ioi}\left(0\right))$$

*Formalization.* `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.Positive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The open positive ray, equipped with its induced order, Borel structure and topology.

**Definition 1.2 (rightDeriv).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall x : \mathbb{R}, (\operatorname{rightDeriv}\left(f, x\right) = (\operatorname{derivWithin}\left(f, \operatorname{Ioi}\left(x\right), x\right))))$$

*Formalization.* `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.rightDeriv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The one-sided derivative is selected by Mathlib's derivative within the strict right ray.

**Definition 1.3 (curvatureDistribution).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\forall x : \operatorname{Positive}\left(\right), (\operatorname{curvatureDistribution}\left(h, x\right) = (\operatorname{rightDeriv}\left(f, x\right)))))$$

*Formalization.* `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.curvatureDistribution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Monotonicity comes from convexity. Right continuity is proved by squeezing the derivative between its value at the base point and nearby secant slopes to a fixed positive point. This is the actual derivative, rather than an assumed or unverified regularization.

**Definition 1.4 (curvature).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\operatorname{curvature}\left(h\right) = (\operatorname{StieltjesFunctionmeasure}\left(\operatorname{curvatureDistribution}\left(h\right)\right))))$$

*Formalization.* `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.curvature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib constructs a positive Borel Stieltjes measure. The instance curvature_locallyFinite certifies local finiteness on Positive; it makes no claim of finite total curvature.

**Theorem 1.5 (curvature_Ioc).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\forall a : \operatorname{Positive}\left(\right), (\forall b : \operatorname{Positive}\left(\right), (\operatorname{curvature}\left(h\right)\left(\operatorname{Ioc}\left(a, b\right)\right) = (\operatorname{ENNRealofReal}\left((\operatorname{rightDeriv}\left(f, b\right)) - (\operatorname{rightDeriv}\left(f, a\right))\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.curvature_Ioc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a below b, the mass of (a,b] is exactly the increment of the right derivative. The formula is also valid for reversed endpoints, where both sides vanish.

**Theorem 1.6 (scalar_remainder_right).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\forall a : \operatorname{Positive}\left(\right), (\forall b : \operatorname{Positive}\left(\right), ((a \le b) \Rightarrow (\operatorname{f}\left(b\right) = (((\operatorname{f}\left(a\right)) + ((\operatorname{rightDeriv}\left(f, a\right)) \cdot ((b) - (a)))) + (\int_{t \in \operatorname{Ioc}\left(a, b\right)} ((b) - (t)) \operatorname{dcurvature}\left(h\right)t)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.scalar_remainder_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a compact positive interval, the right-derivative fundamental theorem of calculus gives f(b)-f(a). Fubini applied to the bounded indicator t <= x identifies the integral of the derivative increment with the curvature potential. The only curvature involved is the finite measure restricted to (a,b].

**Theorem 1.7 (scalar_remainder_left).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\forall a : \operatorname{Positive}\left(\right), (\forall b : \operatorname{Positive}\left(\right), ((a \le b) \Rightarrow (\operatorname{f}\left(a\right) = (((\operatorname{f}\left(b\right)) + ((\operatorname{rightDeriv}\left(f, b\right)) \cdot ((a) - (b)))) + (\int_{t \in \operatorname{Ioc}\left(a, b\right)} ((t) - (a)) \operatorname{dcurvature}\left(h\right)t)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.scalar_remainder_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The left remainder uses the right derivative at the upper endpoint. Subtracting the complementary triangle potential from the constant interval potential includes the full atom at that endpoint.

**Theorem 1.8 (negative_hinge_integrable).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\forall a : \operatorname{Positive}\left(\right), (\forall s : \operatorname{Positive}\left(\right), (\operatorname{IntegrableOn}\left(t \mapsto (\operatorname{max}\left((t) - (s), 0\right)), \operatorname{Iic}\left(a\right), \operatorname{curvature}\left(h\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.negative_hinge_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative hinge vanishes below s, so its restriction to t <= a is supported inside the compact positive interval between s and a.

**Theorem 1.9 (positive_hinge_integrable).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\forall a : \operatorname{Positive}\left(\right), (\forall s : \operatorname{Positive}\left(\right), (\operatorname{IntegrableOn}\left(t \mapsto (\operatorname{max}\left((s) - (t), 0\right)), \operatorname{Ioi}\left(a\right), \operatorname{curvature}\left(h\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.positive_hinge_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive hinge vanishes above s. Local finiteness suffices even when the positive tail has infinite curvature mass.

**Theorem 1.10 (scalar_hinge_representation).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\forall a : \operatorname{Positive}\left(\right), (\forall s : \operatorname{Positive}\left(\right), (\operatorname{f}\left(s\right) = ((((\operatorname{f}\left(a\right)) + ((\operatorname{rightDeriv}\left(f, a\right)) \cdot ((s) - (a)))) + (\int_{t \in \operatorname{Iic}\left(a\right)} (\operatorname{max}\left((t) - (s), 0\right)) \operatorname{dcurvature}\left(h\right)t)) + (\int_{t \in \operatorname{Ioi}\left(a\right)} (\operatorname{max}\left((s) - (t), 0\right)) \operatorname{dcurvature}\left(h\right)t))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.scalar_hinge_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both finite-interval identities combine into the full scalar formula. The negative branch is Iic a and the positive branch is Ioi a. On the positive subtype these are respectively (0,a] and (a,infinity).

**Theorem 1.11 (scalar_hinge_at_one).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\forall s : \mathbb{R}, ((0 < s) \Rightarrow (\operatorname{f}\left(s\right) = ((((\operatorname{f}\left(1\right)) + ((\operatorname{rightDeriv}\left(f, 1\right)) \cdot ((s) - (1)))) + (\int_{t \in \operatorname{Iic}\left(1\right)} (\operatorname{max}\left((t) - (s), 0\right)) \operatorname{dcurvature}\left(h\right)t)) + (\int_{t \in \operatorname{Ioi}\left(1\right)} (\operatorname{max}\left((s) - (t), 0\right)) \operatorname{dcurvature}\left(h\right)t))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.scalar_hinge_at_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At base one, the affine term is f(1)+r(1)(s-1). The atom at one belongs to the negative branch. For abs(s-1), this is the convention consistent with right derivative one and curvature twice the Dirac mass at one.

**Theorem 1.12 (perspective_positive).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\forall u : \mathbb{R}, (\forall v : \mathbb{R}, ((0 < u) \Rightarrow ((0 < v) \Rightarrow ((v) \cdot (\operatorname{f}\left(\operatorname{div}\left(u, v\right)\right)) = (((((\operatorname{f}\left(1\right)) \cdot (v)) + ((\operatorname{rightDeriv}\left(f, 1\right)) \cdot ((u) - (v)))) + (\int_{t \in \operatorname{Iic}\left(1\right)} (\operatorname{max}\left(((t) \cdot (v)) - (u), 0\right)) \operatorname{dcurvature}\left(h\right)t)) + (\int_{t \in \operatorname{Ioi}\left(1\right)} (\operatorname{max}\left((u) - ((t) \cdot (v)), 0\right)) \operatorname{dcurvature}\left(h\right)t))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.perspective_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive scaling of the proved scalar identity gives the actual perspective in the open quadrant. Axis values and arbitrary-test cost integration require separate endpoint and integration results; they are not assumptions or conclusions of this theorem.

## References

- Truth anchor: `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.Positive`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.curvature`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.curvatureDistribution`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.curvature_Ioc`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.negative_hinge_integrable`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.perspective_positive`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.positive_hinge_integrable`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.rightDeriv`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.scalar_hinge_at_one`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.scalar_hinge_representation`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.scalar_remainder_left`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvatureHingeRepresentation.scalar_remainder_right`
