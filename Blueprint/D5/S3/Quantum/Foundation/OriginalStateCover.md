# Pure points, full exclusion balls and original affine diameters

## Abstract

Every original state lies between a pure point and its entire exclusion ball.

Let C be a closed generating cone in a nonzero finite-dimensional real normed space V, and let the original real-linear unit u be strictly positive on every nonzero element of C. Write K=C intersect {u=1}, P=ext(K), and use the entire effect interval E={f: 0<=f(c)<=u(c) for every c in C}. The set D(p) consists of every original state annihilated by some proper effect confirming the actual pure point p. Each D(p) is the image of an entire closed Euclidean unit ball under an injective affine chart, with arbitrary positive dimension depending on p. ExclusionInjective(C,u) means exactly that equality of the two entire sets D(p),D(q) implies equality of their original pure labels. PureExclusionHullUnion(C,u) denotes the union, over all p in P, of conv({p} union D(p)). The operation smul in the displayed formulas is real scalar multiplication. Pure-subtype coercions into V are implicit.

**Theorem 1.1 (A supporting contact of the maximal reflected body).**

$$\forall E \in Types,\; [NormedAddCommGroup\left(E\right)] [NormedSpace\left(Real, E\right)] \forall L \in Set\left(E\right),\; \left(IsCompact\left(L\right) \land \left(Convex\left(Real, L\right) \land \left(0 \in interior\left(L\right) \land \left(\exists z \in E,\; z \in L \land z \ne 0\right)\right)\right)\right) \Rightarrow \left(\exists t \in Real,\; \exists z \in E,\; \exists f \in ContinuousLinearMaps\left(Real, E, Real\right),\; 0 < t \land \left(z \in L \land \left(smul\left(-t, z\right) \in L \land \left(0 < f\left(smul\left(-t, z\right)\right) \land \left(f\left(z\right) < 0 \land \left(\left(\forall w \in E,\; w \in L \Rightarrow f\left(z\right) \le f\left(w\right)\right) \land \left(\forall w \in E,\; w \in L \Rightarrow f\left(w\right) \le f\left(smul\left(-t, z\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalStateCover.centered_affine_diameter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a compact convex L containing zero in its interior and at least one nonzero point, maximize t>=0 subject to -t L being contained in L. An interior ball and a bound on the norm give a strictly positive feasible t. Testing a fixed nonzero point bounds all feasible t, and their closed conditions make the maximum attained. If every reflected point were interior, compactness would give a common neighborhood of t in which every reflected point remains interior. This would admit a larger t, a contradiction. A nonzero Hahn-Banach support at a contact v=-t z has positive maximum because zero is interior. Applying the same support inequality to -t w for every w in L makes z a global minimum of the same functional. No smoothness, strict convexity, fixed dimension or regularity of the boundary is assumed.

This is a native proof of the classical affine-diameter existence argument, rather than a new convex-geometric existence assertion. The literature source is Barany, Hug and Schneider, Affine diameters of convex bodies, DOI 10.1090/proc12746, whose Section 5 cites Soltan's survey assertion 3.3. The result here retains the actual reflected contact and both global support inequalities needed for normalization. The proof uses compact extrema and Hahn-Banach separation from pinned Mathlib.

**Theorem 1.2 (Every original state and the complete radial decomposition of its same ball).**

$$\forall V \in Types,\; [NormedAddCommGroup\left(V\right)] [NormedSpace\left(Real, V\right)] [FiniteDimensional\left(Real, V\right)] [Nontrivial\left(V\right)] \forall C \in PointedCone\left(Real, V\right),\; \forall u \in LinearMaps\left(Real, V, Real\right),\; \left(IsClosed\left(C\right) \land \left(\left(\forall x \in V,\; \left(x \in C \land x \ne 0\right) \Rightarrow 0 < u\left(x\right)\right) \land \left(span\left(Real, C\right) = top \land \left(exclusionBalls\left(C, u\right) \land ExclusionInjective\left(C, u\right)\right)\right)\right)\right) \Rightarrow \left(base\left(C, u\right) = PureExclusionHullUnion\left(C, u\right) \land \left(\forall x \in V,\; x \in base\left(C, u\right) \Rightarrow \left(\exists p \in pure\left(C, u\right),\; \exists y \in V,\; \exists s \in Real,\; \exists f \in LinearMaps\left(Real, V, Real\right),\; y \in exclusion\left(C, u, p\right) \land \left(s \in Icc\left(0, 1\right) \land \left(proper\left(C, u, f\right) \land \left(f\left(p\right) = 1 \land \left(f\left(y\right) = 0 \land \left(x = smul\left(s, p\right)+smul\left(1-s, y\right) \land \left(\left(x \in intrinsicInterior\left(Real, base\left(C, u\right)\right) \Rightarrow s \in Ioo\left(0, 1\right)\right) \land \left(\forall b \in ExclusionChart\left(C, u, p\right),\; \exists q \in pure\left(C, u\right),\; \exists r \in pure\left(C, u\right),\; \exists t \in Real,\; q \in exclusion\left(C, u, p\right) \land \left(r \in exclusion\left(C, u, p\right) \land \left(t \in Icc\left(0, 1\right) \land \left(r = smul\left(2, param\left(b, 0\right)\right)-q \land \left(y = smul\left(t, q\right)+smul\left(1-t, r\right) \land x = smul\left(s, p\right)+smul\left(1-s, smul\left(t, q\right)+smul\left(1-t, r\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalStateCover.original_state_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conclusion is the exact equality K=union_p conv({p} union D(p)), together with an actual decomposition for every x in the entire K. It selects an original pure p, a state y in its entire D(p), a weight s in [0,1], and one proper effect f on all V satisfying f(p)=1 and f(y)=0. For an original relative interior x that same selected weight is strictly between zero and one. For every whole-ball chart b of this same D(p), there are original pure q,r in D(p) and t in [0,1] with r=2 b(0)-q, y=t q+(1-t)r, and x=s p+(1-s)(t q+(1-t)r). Thus the radial statement concerns the same y as the first decomposition, and every positive chart dimension is retained.

For an interior x, center K at x in the direction space of aff(K) and use the maximal reflected-body contact. Extend its support linearly to V and normalize its full minimum and maximum on K. OriginalWidthContact.normalized_effect proves that this single normalized functional is bounded between zero and u on the whole cone, not merely on the support chord. OriginalWidthContact.contact_face_subsingleton uses only the full-ball face classification and injectivity to make at least one contact face a pure singleton. Select that endpoint as p, and complement the same effect by u-f when reversing endpoints. The two possible weights are 1/(1+t) and t/(1+t).

A pure x is represented with p=x and weight one, using any point of the nonempty D(p). A nonpure boundary x belongs to an entire D(p) by MixedExclusionGeometry.frontier_covered and uses y=x and weight zero. Convexity gives the reverse hull inclusion. Within the selected chart, a nonzero coordinate v uses n=v/||v|| and weight (1+||v||)/2; the zero coordinate uses any unit coordinate vector and equal weights. OriginalFacePolarity.chart_boundary makes both chart antipodes actual original pure states. This covers dimension one, the ball center, the sphere, pure original states, boundary states and endpoint weights.

The assumptions contain no Pair condition, W, closed pure set, continuous pure selector, common ball center, PSD representation, fixed ambient dimension, joint completion or seed. Membership of q and r in D(p) supplies the original separate zero relations with p. The statement asserts neither distinguishability of q and r nor a three-outcome instrument. It is a mathematical consequence in the specified full-effect convex model; no physical realization or priority claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OriginalStateCover.centered_affine_diameter`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalStateCover.original_state_cover`
- Dependency: [D5/S3/Quantum/Foundation/MixedExclusionGeometry](MixedExclusionGeometry.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalWidthContact](OriginalWidthContact.md)
