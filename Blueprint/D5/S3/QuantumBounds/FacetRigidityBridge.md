# From functional rigidity to a facet

## Abstract

Rigidity of vanishing functionals on saturating generators gives affine codimension one.

**Theorem 1.1 (The exposed face has affine codimension one).**

$$\forall E \in Type,\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(\mathbb{R}, E\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, E\right)] \forall s \in \operatorname{Set}\left(E\right),\; \forall I \in \operatorname{LinearMap}\left(\mathbb{R}, E, \mathbb{R}\right),\; \forall n \in \operatorname{LinearMap}\left(\mathbb{R}, E, \mathbb{R}\right),\; \forall b \in \mathbb{R},\; \forall o \in E,\; \forall t \in E,\; ((\forall z \in E,\; (z \in s) \Rightarrow (b \le \operatorname{I}\left(z\right))) \land ((\forall z \in E,\; (z \in s) \Rightarrow (\operatorname{n}\left(z\right) = 1)) \land ((o \in s) \land ((\operatorname{I}\left(o\right) = b) \land ((t \in s) \land ((\operatorname{I}\left(t\right) \ne b) \land (\forall ell \in \operatorname{LinearMap}\left(\mathbb{R}, E, \mathbb{R}\right),\; (\forall z \in E,\; (z \in s) \Rightarrow ((\operatorname{I}\left(z\right) = b) \Rightarrow (\operatorname{ell}\left(z\right) = 0))) \Rightarrow (\exists lam \in \mathbb{R},\; \forall z \in E,\; (z \in s) \Rightarrow (\operatorname{ell}\left(z\right) = lam \cdot (\operatorname{I}\left(z\right) - b)))))))))) \Rightarrow (\operatorname{Module}.\operatorname{finrank}\left(\mathbb{R}, \operatorname{vectorSpan}\left(\mathbb{R}, \{p:E\mid(p \in \operatorname{convexHull}\left(\mathbb{R}, s\right)) \land (\operatorname{I}\left(p\right) = b)\}\right)\right) + 1 = \operatorname{Module}.\operatorname{finrank}\left(\mathbb{R}, \operatorname{vectorSpan}\left(\mathbb{R}, \operatorname{convexHull}\left(\mathbb{R}, s\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/FacetRigidityBridge.rigidity_facet_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let s be any set in a finite-dimensional real module. The linear functional I is bounded below by b on s, and n normalises all its generators to one. The generator o attains the bound and t does not. If every linear functional vanishing on the saturating generators restricts to a scalar multiple of I−b on s, the exposed face of the convex hull has affine dimension one less than the hull. The notation vectorSpan is Mathlib's direction space of the affine span, so finrank here is affine dimension. A convex combination reaches the bound only through active saturating generators. The annihilator of the face direction space is the annihilator of the hull direction space plus the line through I; t shows that this line adds exactly one dimension.

## References

- Truth anchor: `D5/S3/QuantumBounds/FacetRigidityBridge.rigidity_facet_bridge`
