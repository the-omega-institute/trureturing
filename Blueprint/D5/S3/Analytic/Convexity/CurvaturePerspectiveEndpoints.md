# Extended endpoints, axes and cost integration

## Abstract

Extended convex endpoints and the closed perspective are obtained from actual positive Stieltjes curvature, including infinite costs.

Assume only that f is real valued and convex on the strictly positive ray. The curvature measure is the actual right-derivative Stieltjes measure constructed in CurvatureHingeRepresentation. The endpoint declarations retain that Lean namespace but are owned by the CurvaturePerspectiveEndpoints source module; each Describe handle selects that module and the declaration suffix. Integrals denoted LIntegral are extended nonnegative Lebesgue integrals. Finite real terms and nonnegative extended terms are embedded in EReal. No subtraction of infinite values occurs. The base one in each curvature domain is the positive subtype element one.

**Definition 1.1 (zeroEndpoint).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\operatorname{zeroEndpoint}\left(h\right) = (((\operatorname{f}\left(1\right)) - (\operatorname{rightDeriv}\left(f, 1\right))) + (\operatorname{LIntegral}\left(\operatorname{Iic}\left(1\right), t \mapsto (\operatorname{ENNRealofReal}\left(t\right)), \operatorname{curvature}\left(h\right)\right)))))$$

*Formalization.* `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.zeroEndpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero endpoint is a finite affine constant plus the possibly infinite first curvature moment over (0,1]. It is never minus infinity.

**Definition 1.2 (infinityEndpoint).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\operatorname{infinityEndpoint}\left(h\right) = ((\operatorname{rightDeriv}\left(f, 1\right)) + (\operatorname{curvature}\left(h\right)\left(\operatorname{Ioi}\left(1\right)\right)))))$$

*Formalization.* `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.infinityEndpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The asymptotic slope is a finite slope plus the possibly infinite total curvature on (1,infinity). Total curvature is not assumed finite.

**Theorem 1.3 (tendsto_zeroEndpoint).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\operatorname{Tendsto}\left(s \mapsto (\operatorname{ERealofReal}\left(\operatorname{f}\left(s\right)\right)), \operatorname{atBotPositive}\left(\right), \operatorname{nhds}\left(\operatorname{zeroEndpoint}\left(h\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.tendsto_zeroEndpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As the positive scalar decreases to zero, the lower curvature kernels increase to t. Monotone convergence first proves the limit along a cofinal sequence and monotonicity then proves the full filter limit. The finite affine term converges independently.

**Theorem 1.4 (tendsto_infinityEndpoint).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\operatorname{Tendsto}\left(s \mapsto (\operatorname{ERealofReal}\left(\operatorname{div}\left(\operatorname{f}\left(s\right), s\right)\right)), \operatorname{atTopPositive}\left(\right), \operatorname{nhds}\left(\operatorname{infinityEndpoint}\left(h\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.tendsto_infinityEndpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As s tends to infinity, the normalized upper curvature kernels (1-t/s)+ increase to one. Monotone convergence permits infinite tail mass and proves the actual asymptotic slope.

**Definition 1.5 (curvatureRemainder).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\forall u : \mathbb{R}, (\forall v : \mathbb{R}, (\operatorname{curvatureRemainder}\left(h, u, v\right) = ((\operatorname{LIntegral}\left(\operatorname{Iic}\left(1\right), t \mapsto (\operatorname{ENNRealofReal}\left(((t) \cdot (v)) - (u)\right)), \operatorname{curvature}\left(h\right)\right)) + (\operatorname{LIntegral}\left(\operatorname{Ioi}\left(1\right), t \mapsto (\operatorname{ENNRealofReal}\left((u) - ((t) \cdot (v))\right)), \operatorname{curvature}\left(h\right)\right)))))))$$

*Formalization.* `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.curvatureRemainder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The remainder is nonnegative and may be infinite on the axes. The atom at one is in the negative branch, whose domain is (0,1].

**Definition 1.6 (closedPerspective).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\forall u : \mathbb{R}, (\forall v : \mathbb{R}, (\operatorname{closedPerspective}\left(h, u, v\right) = (\operatorname{ite}\left(v = (0), (u) \cdot (\operatorname{infinityEndpoint}\left(h\right)), \operatorname{ite}\left(u = (0), (v) \cdot (\operatorname{zeroEndpoint}\left(h\right)), (v) \cdot (\operatorname{f}\left(\operatorname{div}\left(u, v\right)\right))\right)\right))))))$$

*Formalization.* `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.closedPerspective` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive u and v this is v f(u/v). On either nonzero axis it is the corresponding positive scalar times the proved convex endpoint limit. At the origin it is zero, including when the endpoint is infinite.

**Theorem 1.7 (closedPerspective_eq_affine_add_curvature).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\forall u : \mathbb{R}, (\forall v : \mathbb{R}, ((0 \le u) \Rightarrow ((0 \le v) \Rightarrow (\operatorname{closedPerspective}\left(h, u, v\right) = ((((\operatorname{f}\left(1\right)) \cdot (v)) + ((\operatorname{rightDeriv}\left(f, 1\right)) \cdot ((u) - (v)))) + (\operatorname{curvatureRemainder}\left(h, u, v\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.closedPerspective_eq_affine_add_curvature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This proves the scalar identity on the entire nonnegative quadrant. The interior follows from the finite scalar representation and integrability of the compactly supported hinges. On the axes, scaling the explicit endpoint curvature integrals gives the same identity; no infinite difference is formed.

**Theorem 1.8 (closedPerspective_origin).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\operatorname{closedPerspective}\left(h, 0, 0\right) = (0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.closedPerspective_origin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The corner contributes zero even when one or both convex endpoints are infinite.

**Theorem 1.9 (integral_curvatureRemainder).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\forall alpha : \operatorname{Type}\left(\right), (\forall m : \operatorname{MeasurableSpace}\left(alpha\right), (\forall nu : \operatorname{Measure}\left(alpha\right), (\forall p : (alpha \to \mathbb{R}), (\forall q : (alpha \to \mathbb{R}), ((\operatorname{SFinite}\left(nu\right)) \Rightarrow ((\operatorname{Measurable}\left(p\right)) \Rightarrow ((\operatorname{Measurable}\left(q\right)) \Rightarrow (\operatorname{LIntegral}\left(x \mapsto (\operatorname{curvatureRemainder}\left(h, \operatorname{p}\left(x\right), \operatorname{q}\left(x\right)\right)), nu\right) = ((\operatorname{LIntegral}\left(\operatorname{Iic}\left(1\right), t \mapsto (\operatorname{LIntegral}\left(x \mapsto (\operatorname{ENNRealofReal}\left(((t) \cdot (\operatorname{q}\left(x\right))) - (\operatorname{p}\left(x\right))\right)), nu\right)), \operatorname{curvature}\left(h\right)\right)) + (\operatorname{LIntegral}\left(\operatorname{Ioi}\left(1\right), t \mapsto (\operatorname{LIntegral}\left(x \mapsto (\operatorname{ENNRealofReal}\left((\operatorname{p}\left(x\right)) - ((t) \cdot (\operatorname{q}\left(x\right)))\right)), nu\right)), \operatorname{curvature}\left(h\right)\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.integral_curvatureRemainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any measurable space, s-finite measure nu and measurable real functions p,q, the integral of curvatureRemainder h (p x) (q x) equals the sum of the curvature integrals of the integrated negative and positive hockey-stick kernels. Both sides are extended nonnegative integrals. Joint measurability is proved from p and q, then Tonelli is applied to each branch. No cost finiteness assumption is used.

**Definition 1.10 (closedPerspectiveCost).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\forall alpha : \operatorname{Type}\left(\right), (\forall m : \operatorname{MeasurableSpace}\left(alpha\right), (\forall nu : \operatorname{Measure}\left(alpha\right), (\forall p : (alpha \to \mathbb{R}), (\forall q : (alpha \to \mathbb{R}), (\operatorname{closedPerspectiveCost}\left(h, nu, p, q\right) = ((\operatorname{Integral}\left(x \mapsto (((\operatorname{f}\left(1\right)) \cdot (\operatorname{q}\left(x\right))) + ((\operatorname{rightDeriv}\left(f, 1\right)) \cdot ((\operatorname{p}\left(x\right)) - (\operatorname{q}\left(x\right))))), nu\right)) + (\operatorname{LIntegral}\left(x \mapsto (\operatorname{curvatureRemainder}\left(h, \operatorname{p}\left(x\right), \operatorname{q}\left(x\right)\right)), nu\right))))))))))$$

*Formalization.* `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.closedPerspectiveCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For nonnegative densities, the pointwise closed-perspective representation proves that this is the actual perspective integral with finite affine subtraction. It is defined as the real integral of the affine support plus the extended nonnegative integral of curvatureRemainder. The latter may be infinite.

**Theorem 1.11 (closedPerspectiveCost_eq_mass).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\forall alpha : \operatorname{Type}\left(\right), (\forall m : \operatorname{MeasurableSpace}\left(alpha\right), (\forall nu : \operatorname{Measure}\left(alpha\right), (\forall p : (alpha \to \mathbb{R}), (\forall q : (alpha \to \mathbb{R}), ((\operatorname{SFinite}\left(nu\right)) \Rightarrow ((\operatorname{Measurable}\left(p\right)) \Rightarrow ((\operatorname{Measurable}\left(q\right)) \Rightarrow ((\operatorname{Integrable}\left(p, nu\right)) \Rightarrow ((\operatorname{Integrable}\left(q, nu\right)) \Rightarrow (\operatorname{closedPerspectiveCost}\left(h, nu, p, q\right) = ((((\operatorname{f}\left(1\right)) \cdot (\operatorname{Integral}\left(x \mapsto (\operatorname{q}\left(x\right)), nu\right))) + ((\operatorname{rightDeriv}\left(f, 1\right)) \cdot ((\operatorname{Integral}\left(x \mapsto (\operatorname{p}\left(x\right)), nu\right)) - (\operatorname{Integral}\left(x \mapsto (\operatorname{q}\left(x\right)), nu\right))))) + ((\operatorname{LIntegral}\left(\operatorname{Iic}\left(1\right), t \mapsto (\operatorname{LIntegral}\left(x \mapsto (\operatorname{ENNRealofReal}\left(((t) \cdot (\operatorname{q}\left(x\right))) - (\operatorname{p}\left(x\right))\right)), nu\right)), \operatorname{curvature}\left(h\right)\right)) + (\operatorname{LIntegral}\left(\operatorname{Ioi}\left(1\right), t \mapsto (\operatorname{LIntegral}\left(x \mapsto (\operatorname{ENNRealofReal}\left((\operatorname{p}\left(x\right)) - ((t) \cdot (\operatorname{q}\left(x\right)))\right)), nu\right)), \operatorname{curvature}\left(h\right)\right))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.closedPerspectiveCost_eq_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary measurable integrable densities, the affine term is f(1) times the q mass plus the right derivative at one times the difference of the p and q masses. Both nonnegative curvature integrals remain extended valued. There is no normalization of the inputs and no infinite subtraction.

**Theorem 1.12 (closedPerspectiveCost_eq).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), (\forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\forall alpha : \operatorname{Type}\left(\right), (\forall m : \operatorname{MeasurableSpace}\left(alpha\right), (\forall nu : \operatorname{Measure}\left(alpha\right), (\forall p : (alpha \to \mathbb{R}), (\forall q : (alpha \to \mathbb{R}), ((\operatorname{SFinite}\left(nu\right)) \Rightarrow ((\operatorname{Measurable}\left(p\right)) \Rightarrow ((\operatorname{Measurable}\left(q\right)) \Rightarrow ((\operatorname{Integrable}\left(p, nu\right)) \Rightarrow ((\operatorname{Integrable}\left(q, nu\right)) \Rightarrow ((\operatorname{Integral}\left(x \mapsto (\operatorname{p}\left(x\right)), nu\right) = (1)) \Rightarrow ((\operatorname{Integral}\left(x \mapsto (\operatorname{q}\left(x\right)), nu\right) = (1)) \Rightarrow (\operatorname{closedPerspectiveCost}\left(h, nu, p, q\right) = ((\operatorname{f}\left(1\right)) + ((\operatorname{LIntegral}\left(\operatorname{Iic}\left(1\right), t \mapsto (\operatorname{LIntegral}\left(x \mapsto (\operatorname{ENNRealofReal}\left(((t) \cdot (\operatorname{q}\left(x\right))) - (\operatorname{p}\left(x\right))\right)), nu\right)), \operatorname{curvature}\left(h\right)\right)) + (\operatorname{LIntegral}\left(\operatorname{Ioi}\left(1\right), t \mapsto (\operatorname{LIntegral}\left(x \mapsto (\operatorname{ENNRealofReal}\left((\operatorname{p}\left(x\right)) - ((t) \cdot (\operatorname{q}\left(x\right)))\right)), nu\right)), \operatorname{curvature}\left(h\right)\right))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.closedPerspectiveCost_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On any s-finite measure space with measurable integrable real densities p and q of integral one, the cost equals f(1) plus the two integrated hockey-stick remainders. For nonnegative densities this is the actual closed-perspective cost. Integrability justifies the finite affine integral, whose derivative term cancels; Tonelli justifies the two nonnegative curvature integrals even when the cost is infinite.

## References

- Truth anchor: `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.closedPerspective`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.closedPerspectiveCost`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.closedPerspectiveCost_eq`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.closedPerspectiveCost_eq_mass`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.closedPerspective_eq_affine_add_curvature`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.closedPerspective_origin`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.curvatureRemainder`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.infinityEndpoint`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.integral_curvatureRemainder`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.tendsto_infinityEndpoint`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.tendsto_zeroEndpoint`
- Truth anchor: `D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.zeroEndpoint`
- Dependency: [D5/S3/Analytic/Convexity/CurvatureHingeRepresentation](CurvatureHingeRepresentation.md)
