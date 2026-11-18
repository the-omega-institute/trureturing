# Common positive extension on entire original exclusion balls

## Abstract

The original positive restriction cone has one intrinsic linear inverse; its signed image is exactly span(Z_p).

Source correspondence: original VII105.4 in QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII, with only the normal-form and least clauses of VII105.3. The consumer is VIII108.5 in QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII. V is the same nonzero finite dimensional real space, C the same closed generating pointed cone, u the same strictly positive original unit, K its entire normalized compact base, P all original extreme points, and proper effects the entire original interval [0,u] on ALL C. Exclusion dimensions may vary and include one. The only pair premise is weakPair on original orthogonal pairs.

**Definition 1.1 (The actual original annihilating positive cone).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall p \in \operatorname{pure}\left(C, u\right),\; \forall f \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; f\in \operatorname{zeroPositive}\left(C, u, p\right) \Leftrightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow 0 \le \operatorname{apply}\left(f, x\right)\right) \land \operatorname{apply}\left(f, p\right) = 0\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/CommonPositiveExtension.zeroPositive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Z_p contains every original positive linear functional vanishing at p. It is not a selected effect subset or the whole signed annihilator of p.

**Definition 1.2 (Positivity on the whole ball).**

Lean statement: `D5/S3/Quantum/Foundation/CommonPositiveExtension.ballPositive`

*Formalization.* `D5/S3/Quantum/Foundation/CommonPositiveExtension.ballPositive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula notation positiveAffineCone(b) denotes the set of all h with ballPositive h. ballPositive h means 0<=h(z) for every coordinate z with norm z<=1. Since each chart is injective and its whole field identifies its image with all D_p, affine coordinate functions represent intrinsic affine functions on the entire exclusion set. The closed ball affinely spans its coordinate space.

**Definition 1.3 (One linear restriction map).**

Lean statement: `D5/S3/Quantum/Foundation/CommonPositiveExtension.restriction`

*Formalization.* `D5/S3/Quantum/Foundation/CommonPositiveExtension.restriction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

restriction b is the real-linear map f -> f.toAffineMap composed with b.param. Both its source and target include all signed functions. Only its restriction to Z_p is initially asserted injective.

**Theorem 1.4 (Signed normals are differences of positive normals).**

Lean statement: `D5/S3/Quantum/Foundation/CommonPositiveExtension.positive_span_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CommonPositiveExtension.positive_span_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every member of the real span of the whole original positive annihilator cone is a difference of two members of that cone. This uses the standard reproducing-cone theorem in the actual span; it imposes no Pair or extension hypothesis.

**Definition 1.5 (The three extension laws).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall p \in \operatorname{pure}\left(C, u\right),\; \forall b \in \operatorname{ExclusionChart}\left(C, u, p\right),\; \forall Lambda \in \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{AffineMap}\left(\mathbb{R}, \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(\operatorname{dim}\left(b\right)\right)\right), \mathbb{R}\right), \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right)\right),\; \operatorname{PositiveLift}\left(b, Lambda\right) \Leftrightarrow \left(\left(\forall h \in \operatorname{AffineMap}\left(\mathbb{R}, \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(\operatorname{dim}\left(b\right)\right)\right), \mathbb{R}\right),\; \operatorname{apply}\left(\operatorname{restriction}\left(b\right), \operatorname{apply}\left(Lambda, h\right)\right) = h\right) \land \left(\left(\forall h \in \operatorname{AffineMap}\left(\mathbb{R}, \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(\operatorname{dim}\left(b\right)\right)\right), \mathbb{R}\right),\; \operatorname{apply}\left(\operatorname{apply}\left(Lambda, h\right), p\right) = 0\right) \land \left(\forall h \in \operatorname{AffineMap}\left(\mathbb{R}, \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(\operatorname{dim}\left(b\right)\right)\right), \mathbb{R}\right),\; \operatorname{ballPositive}\left(h\right) \Rightarrow \left(\forall x \in V,\; x\in C \Rightarrow 0 \le \operatorname{apply}\left(\operatorname{apply}\left(Lambda, h\right), x\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/CommonPositiveExtension.PositiveLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A real-linear map is a PositiveLift when restriction after it is the identity on every signed affine function, all its outputs vanish at p, and every nonnegative affine function has an output nonnegative on all C. These are conclusions of the construction, never premises replacing W.

**Definition 1.6 (Unit, inverses, order budget and intrinsic agreement).**

Lean statement: `D5/S3/Quantum/Foundation/CommonPositiveExtension.ExtensionLaws`

*Formalization.* `D5/S3/Quantum/Foundation/CommonPositiveExtension.ExtensionLaws` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ExtensionLaws includes PositiveLift and Lambda(1)=u-a_p; Lambda(res f)=f for EVERY f in Z_p; 0<=Lambda h<=u-a_p on every x in C whenever 0<=h<=1 on the entire ball; range Lambda=span(Z_p). For EVERY second actual chart c and EVERY positive real-linear right inverse Gamma vanishing at p, if h and k agree whenever b.param(z)=c.param(w), with both coordinates in their closed balls, then Lambda h=Gamma k. This is intrinsic chart independence, including signed functions and charts of arbitrary admissible dimensions.

**Definition 1.7 (The paid confirmation clauses).**

Lean statement: `D5/S3/Quantum/Foundation/CommonPositiveExtension.ConfirmationNormalForm`

*Formalization.* `D5/S3/Quantum/Foundation/CommonPositiveExtension.ConfirmationNormalForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original g in F_p there are original q,r in D_p with a_p+a_q+a_r=u, g=a_p+g(q)a_q+g(r)a_r, both coefficients in [0,1], and a_p(x)<=g(x) for every x in C. The proof chooses q,r as an actual chart diameter. This is the normal form and whole-cone leastness, not the full positive or signed dual spectral expansion of VII105.3.

**Theorem 1.8 (The original positive restriction-cone theorem).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow \left(x\neq 0 \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{exclusionBalls}\left(C, u\right) \Rightarrow \left(\operatorname{weakPair}\left(C, u\right) \Rightarrow \left(\exists a \in \operatorname{Function}\left(\operatorname{pure}\left(C, u\right), \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right)\right),\; \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \operatorname{common}\left(C, u, p, \operatorname{apply}\left(a, p\right)\right)\right) \land \left(\left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall f \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{common}\left(C, u, p, f\right) \Rightarrow f = \operatorname{apply}\left(a, p\right)\right) \land \left(\left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall g \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{confirms}\left(C, u, p, g\right) \Rightarrow \operatorname{ConfirmationNormalForm}\left(a, p, g\right)\right) \land \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall b \in \operatorname{ExclusionChart}\left(C, u, p\right),\; \operatorname{BijOn}\left(\operatorname{restriction}\left(b\right), \operatorname{zeroPositive}\left(C, u, p\right), \operatorname{positiveAffineCone}\left(b\right)\right) \land \left(\exists Lambda \in \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{AffineMap}\left(\mathbb{R}, \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(\operatorname{dim}\left(b\right)\right)\right), \mathbb{R}\right), \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right)\right),\; \operatorname{ExtensionLaws}\left(b, \operatorname{apply}\left(a, p\right), Lambda\right) \land \left(\forall Gamma \in \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{AffineMap}\left(\mathbb{R}, \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(\operatorname{dim}\left(b\right)\right)\right), \mathbb{R}\right), \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right)\right),\; \operatorname{ExtensionLaws}\left(b, \operatorname{apply}\left(a, p\right), Gamma\right) \Rightarrow Gamma = Lambda\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CommonPositiveExtension.whole_positive_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary a,a' in A_p and a fixed common effect d at a cyclic companion q, completion produces c=u-a-d in A_r, then u-a'-c=d+a-a' in A_q. The reverse completion concerns the SAME triple, as proved from its singleton intersections. At every original x in C the A_q readings are nonempty and bounded in [0,u(x)]. Taking their supremum forces a(x)<=a'(x); swapping them gives equality. Since C generates V, equality holds as linear maps. This consumes the supplied joint completion and proves actual common uniqueness without assuming least effects or a frame supplier.

A unit chart direction n gives an actual original pure q. Completion with p gives r. The public affine_zero_antipode theorem applied to 1-a_q, properness, and the completed zero readings force r to be the chart antipode. Thus a_q and a_r restrict to (1+inner(n,z))/2 and (1-inner(n,z))/2, and a_p+a_q+a_r=u on the whole V.

For EVERY original f>=0 with f(p)=0, compactness of K gives M>0 and f<=M u on ALL C. Align a diameter with its affine restriction and put lambda=f(q), mu=f(r). The residual k=u-f/M-(1-lambda/M)a_q-(1-mu/M)a_r has k(p)=1 and vanishes on the ENTIRE D_p. Its subtracted terms are nonnegative on ALL C, hence k<=u. Directly apply the supplied whole_exclusion_support, obtaining k in A_p; uniqueness gives k=a_p. The frame sum then reconstructs f=lambda a_q+mu a_r globally. The support normalization proof is reused, not copied or counted as new extension content.

Conversely, finite-dimensional Riesz representation aligns any affine h with one diameter. Its endpoint coefficients h(n),h(-n) are nonnegative when h is nonnegative on the whole ball. Their combination of original a_q,a_r is in Z_p and restricts to h. Reconstruction gives uniqueness of every positive fiber. This is the actual original positive restriction-cone bijection, not an assumed extension/additivity/injectivity interface.

The nonnegative affine cone generates all signed affine functions: a sufficiently large constant shifts any affine function to nonnegative values on the compact ball. The standard mathlib ConvexCone.IsReproducing.of_span_eq_top theorem, applied in span(Z_p), expresses each element as a difference of two elements of Z_p. Positive-cone injectivity then proves restriction injective on that span, and positive lifts of two affine parts prove it surjective. The standard mathlib LinearEquiv.ofBijective constructs the inverse; inclusion into V* is the single real-linear Lambda. This establishes decomposition independence through the actual span and does not assert injectivity on every signed functional vanishing at p.

The original u-a_p lies in Z_p and restricts to 1, giving the exact unit value. Applying positivity to h and 1-h gives the full-cone order budget. Any positive common right inverse has signed range in span(Z_p). Two chart descriptions of one intrinsic affine function therefore produce elements of that span with identical entire restrictions; injectivity proves chart independence. Applying reconstruction to u-g gives the stated confirmation normal form and whole-cone leastness.

**Definition 1.9 (The full all-space arc conclusion).**

Lean statement: `D5/S3/Quantum/Foundation/CommonPositiveExtension.ArcFamily`

*Formalization.* `D5/S3/Quantum/Foundation/CommonPositiveExtension.ArcFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For EVERY original q,p, EVERY entire exclusion chart b of D_q, EVERY unit e with b.param(e)=p, and EVERY nonzero coordinate tangent w with inner(e,w)=0, set n=w/norm(w). There exist an original r=b.param(-e), an all-real family gamma(t)=b.param(cos(t)e+sin(t)n) of original pure points, and ONE signed linear functional B on the original V. For ALL real t, a_gamma(t)=((1+cos(t))/2)a_p+((1-cos(t))/2)a_r+sin(t)B as linear functionals on ALL V. B(p)=B(r)=0, B(b.param.linear(w))=norm(w)/2=1/(2h) for h=1/norm(w), and B vanishes on the whole span({p} union D_p). These quantifiers include every nonzero actual tangent, through the chart's injective linear direction map.

**Theorem 1.10 (The common extension's whole-space arc consumer).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow \left(x\neq 0 \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{exclusionBalls}\left(C, u\right) \Rightarrow \left(\operatorname{weakPair}\left(C, u\right) \Rightarrow \left(\exists a \in \operatorname{Function}\left(\operatorname{pure}\left(C, u\right), \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right)\right),\; \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \operatorname{common}\left(C, u, p, \operatorname{apply}\left(a, p\right)\right)\right) \land \left(\left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall f \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{common}\left(C, u, p, f\right) \Rightarrow f = \operatorname{apply}\left(a, p\right)\right) \land \operatorname{ArcFamily}\left(a\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CommonPositiveExtension.whole_arc_effect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the SAME Lambda_q for the signed affine function H(y)=inner(n,y)/2 and define B=Lambda_q H. Every original canonical effect attached to a sphere point of D_q is in the actual Z_q. The inverse law and real linearity therefore lift the diameter identity from the whole ball to an identity on ALL V. Values at p,r and the tangent follow from restriction and the affine linear direction map.

To prove vanishing on D_p, use the rational circle coefficients c=(1-t^2)/(1+t^2), s=2t/(1+t^2). The all-space identity and original positive effects give a_r(x)t^2+2B(x)t>=0 for every real t and every x in D_p. The standard mathlib quadratic discriminant theorem forces B(x)=0. Together with B(p)=0 this gives vanishing on M_p, without introducing a global smoothness assumption or any projection interface.

Boundaries: full positive/signed spectral generation in VII105.3, all original positive image/kernel equalities and projection construction in VII105.5, exact VIII108.6 tangent disjointness and the VIII109 reconstruction goals remain downstream. No G, globalPair, numerical reciprocity, spectrality, PSD representation, physical implementation, or open-source claim is supplied. The construction is repository-derived; no literature novelty is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/CommonPositiveExtension.ArcFamily`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonPositiveExtension.ConfirmationNormalForm`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonPositiveExtension.ExtensionLaws`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonPositiveExtension.PositiveLift`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonPositiveExtension.ballPositive`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonPositiveExtension.positive_span_difference`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonPositiveExtension.restriction`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonPositiveExtension.whole_arc_effect`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonPositiveExtension.whole_positive_extension`
- Truth anchor: `D5/S3/Quantum/Foundation/CommonPositiveExtension.zeroPositive`
- Dependency: [D5/S3/Quantum/Foundation/OrthogonalJointCompletion](OrthogonalJointCompletion.md)
