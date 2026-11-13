# The unique joint contact pair of an attained original width

## Abstract

Every positive attained width on a whole original exclusion face determines one unique actual joint contact pair, with strict equal readings for all confirming effects when the width is below one.

V is an arbitrary finite dimensional real normed space. C is the original closed generating pointed convex cone, u is strictly positive on its nonzero vectors, K is the entire slice C intersect {u=1}, and P comprises every extreme point of K. Every effect is an original real-linear functional satisfying 0<=f<=u on the whole cone. Every entire exclusion D(p) is an injective affine image of a nondegenerate finite Euclidean closed ball, and equality of two such original exclusions forces equality of their pure labels. The result includes the original three-dimensional ball case. No inner product on V, closedness or compactness of P, pair-face hypothesis, unique confirmation premise or retraction is required.

Application: adjacent complete confirmation and the original normalized perturbation.

Keep this same entire K, cone, unit, full effect interval and injective exclusion-ball family. Fix arbitrary original pure labels p,q with q in F=D(p), and arbitrary complete confirmers a of q and e of p: a and e are proper, a(q)=e(p)=1, a vanishes on all of D(q), and e vanishes on all of F. The original sphere condition q in S(F) supplies such a pure q because F is an extreme face of K and the extreme points of a nondegenerate Euclidean ball are its sphere. Suppose M<1 and WidthBound(C,u,D(q),M). In the original global-width notation, W(D(r)) is the maximum oscillation over every proper original effect and M=sup_r W(D(r)); then f(x)-f(y)<=osc_D(q)(f)<=W(D(q))<=M for every proper original f and all x,y in D(q). This supplies precisely the local WidthBound premise, without restricting the effect domain or replacing the global supremum by a different quantity. The argument below applies to every such p,q,a,e.

Use top_subsingleton_of_zero_exclusion with the label q and effect a. Since a(q)=1, its whole one-value face is {q}. If y is any zero of a in K, the definition of exclusion puts y in D(q). Exclusion symmetry (FacetZeroGluing.exclusion_symmetric) gives p in D(q), so the width bound for the same original e gives 1-e(y)<=M and hence e(y)>=1-M>0. Also e(q)=0. Thus for every x,y in K with a(x)=1 and a(y)=0, e(x)<e(y). Only this inclusion of the zero face in D(q) is needed; no extra equality of faces is assumed.

There is an elementary compact-extrema route to the required perturbation. On the compact nonempty set T={(x,y) in K times K : e(y)<=e(x)}, let d=max_T(a(x)-a(y)). Compactness follows from base_compact, the compact-product and closed-intersection rules, and continuity of the two original effects; IsCompact.exists_isMaxOn supplies an actual maximizing pair. The diagonal makes T nonempty. The effect bounds give d<=1. Equality would force a(x)=1 and a(y)=0 at that pair, contradicting the preceding strict contact inequality. Hence d<1. Put t=(1-d)/2>0 and g=a+t e. If e(y)<=e(x), then g(x)-g(y)<=d+t=(1+d)/2<1. Otherwise t(e(x)-e(y))<0 and a(x)-a(y)<=1, again giving g(x)-g(y)<1. These are applications of compact extrema and real inequalities, with no differentiation of a moving family.

Take the actual minimum lo and maximum hi of this same g on the entire K, using IsCompact.exists_isMinOn and IsCompact.exists_isMaxOn, and set s=hi-lo. Their ordered pair gives s<1. The original exclusion_ball_faces result makes F a nondegenerate compact ball. Choose r in F distinct from q. Whole-face rigidity gives a(r)<a(q)=1, while e is zero on all of F, so g(q)-g(r)=1-a(r)>0 and therefore s>0. Define the original real-linear functional b=(g-lo u)/s. Its bounds 0<=b<=1 on K imply 0<=b<=u on the whole original cone by positive-unit rescaling, exactly as in the existing normalized_effect proof and CircuitBalancedConfirmation.cone_bound. Thus b belongs to the original full effect interval, with no change of unit or restriction of state space.

On the entire F, g=a because e vanishes there. Its normalization therefore gives osc_F(b)=osc_F(a)/s. Compactness supplies the actual extrema on F, and the same q,r show osc_F(a)>0. Since 0<s<1, osc_F(b)>osc_F(a)>0. This derives the original adjacent-complete-confirmation conclusion and the specified formula b=(a+t e-(min_K(a+t e))u)/(max_K(a+t e)-min_K(a+t e)). The minimum, maximum and positive parameter all refer to one common original realization. The compact-extrema results used here are in pinned Mathlib (Mathlib.Topology.Order.Compact); the full-cone and whole-face premises come from the existing project results.

This route establishes the finite positive-parameter conclusion within the stated convex model. It does not establish the distinct one-sided expansions max_X(b+t h)=max_X(b)+t max_argmax(b)(h)+o(t) and min_X(b+t h)=min_X(b)+t min_argmin(b)(h)+o(t) for arbitrary continuous b,h on an arbitrary nonempty compact X. In particular the perturbation argument alone supplies neither derivative statement. No model realizing the strict-width hypotheses, physical instrument implementation or literature priority is asserted.

**Theorem 1.1 (Normalize on the whole base and the whole cone).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalWidthContact.normalized_effect`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalWidthContact.normalized_effect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the original base K be compact and let u be strictly positive on every nonzero point of C. For arbitrary real-linear h and points a,z in V, suppose h(a)<=h(x)<=h(z) for every x in the entire K, and h(z)-h(a)>0. Then (h(z)-h(a)) inverse times (h-h(a)u) is a proper effect on the entire original cone. The points a,z are not required to belong to K. The original state-cover proof uses the actual attained extrema as a,z, after extending its support functional from the affine direction space.

**Theorem 1.2 (At least one whole contact face is a singleton).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalWidthContact.contact_face_subsingleton`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalWidthContact.contact_face_subsingleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the closed generating original cone and strictly positive unit, assume positive-dimensional entire exclusion balls and injectivity of the original exclusion map. If f is proper and x,y belong to K with f(x)=1 and f(y)=0, then either {z in K: f(z)=1} or {z in K: f(z)=0} is subsingleton. The nonempty zero face is either a pure singleton or an entire exclusion. In the latter case every pure point of the one face has that same entire exclusion, so injectivity and compact convex generation force its label. The affine-diameter decomposition uses this alternative to select an actual original pure endpoint.

**Theorem 1.3 (The whole original one-value face is exposed).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalWidthContact.top_exposed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalWidthContact.top_exposed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The one-value set of any original proper effect is an exposed face of the entire original base. The density label-limit proof uses this original-site result to derive purity of a cluster point after showing that this whole face is a singleton.

**Theorem 1.4 (Whole one-value-face rigidity).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalWidthContact.top_subsingleton_of_zero_exclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalWidthContact.top_subsingleton_of_zero_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With the original closed generating cone, strictly positive unit, full positive-dimensional exclusion balls and injective original exclusion map, any proper original effect vanishing on the entire D(p) has a subsingleton whole one-value face. Its actual pure maximizers all have the same full exclusion as p; injectivity and compact convex generation then control every state in that face. The label-limit proof starts its limit state in K and uses this whole-face result, without assuming that the state is pure.

**Definition 1.5 (The full effect width bound).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall F \in \operatorname{Set}\left(V\right),\; \forall M \in \mathbb{R},\; \operatorname{WidthBound}\left(C, u, F, M\right) \Leftrightarrow \left(\forall f \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{proper}\left(C, u, f\right) \Rightarrow \left(\forall x \in V,\; \forall y \in V,\; \left(x\in F \land y\in F\right) \Rightarrow \operatorname{sub}\left(\operatorname{apply}\left(f, x\right), \operatorname{apply}\left(f, y\right)\right) \le M\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/OriginalWidthContact.WidthBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

WidthBound(C,u,F,M) quantifies every original effect and every ordered pair of points of the entire F. Together with b(q)-b(r)=M for one proper b and q,r in F, it says exactly that M is the attained maximum ordered contrast. Thus it expresses W(F)=M without choosing a smaller effect or state domain.

**Theorem 1.6 (One actual pair, uniqueness and all strict confirming readings).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall b \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \left(\operatorname{IsClosed}\left(C\right) \land \left(\left(\forall x \in V,\; x\in C \Rightarrow \left(x\neq 0 \Rightarrow 0 < \operatorname{apply}\left(u, x\right)\right)\right) \land \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \land \left(\operatorname{exclusionBalls}\left(C, u\right) \land \left(\forall p1 \in \operatorname{pure}\left(C, u\right),\; \forall p2 \in \operatorname{pure}\left(C, u\right),\; \operatorname{exclusion}\left(C, u, p1\right) = \operatorname{exclusion}\left(C, u, p2\right) \Rightarrow p1 = p2\right)\right)\right)\right)\right) \Rightarrow \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall M \in \mathbb{R},\; 0 < M \Rightarrow \left(\operatorname{WidthBound}\left(C, u, \operatorname{exclusion}\left(C, u, p\right), M\right) \Rightarrow \left(\operatorname{proper}\left(C, u, b\right) \Rightarrow \left(\forall q \in V,\; \forall r \in V,\; \left(q\in \operatorname{exclusion}\left(C, u, p\right) \land \left(r\in \operatorname{exclusion}\left(C, u, p\right) \land \operatorname{sub}\left(\operatorname{apply}\left(b, q\right), \operatorname{apply}\left(b, r\right)\right) = M\right)\right) \Rightarrow \left(\exists xy \in \operatorname{Prod}\left(V, V\right),\; \left(\operatorname{fst}\left(xy\right)\in \operatorname{base}\left(C, u\right) \land \left(\operatorname{snd}\left(xy\right)\in \operatorname{base}\left(C, u\right) \land \left(\operatorname{apply}\left(b, \operatorname{fst}\left(xy\right)\right) = 1 \land \left(\operatorname{apply}\left(b, \operatorname{snd}\left(xy\right)\right) = 0 \land \operatorname{sub}\left(q, r\right) = \operatorname{smul}\left(M, \operatorname{sub}\left(\operatorname{fst}\left(xy\right), \operatorname{snd}\left(xy\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall zw \in \operatorname{Prod}\left(V, V\right),\; \left(\operatorname{fst}\left(zw\right)\in \operatorname{base}\left(C, u\right) \land \left(\operatorname{snd}\left(zw\right)\in \operatorname{base}\left(C, u\right) \land \left(\operatorname{apply}\left(b, \operatorname{fst}\left(zw\right)\right) = 1 \land \left(\operatorname{apply}\left(b, \operatorname{snd}\left(zw\right)\right) = 0 \land \operatorname{sub}\left(q, r\right) = \operatorname{smul}\left(M, \operatorname{sub}\left(\operatorname{fst}\left(zw\right), \operatorname{snd}\left(zw\right)\right)\right)\right)\right)\right)\right) \Rightarrow zw = xy\right) \land \left(M < 1 \Rightarrow \left(\forall e \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{confirms}\left(C, u, p, e\right) \Rightarrow \left(\left(\forall z \in V,\; z\in \operatorname{exclusion}\left(C, u, p\right) \Rightarrow \operatorname{apply}\left(e, z\right) = 0\right) \Rightarrow \left(0 < \operatorname{apply}\left(e, \operatorname{fst}\left(xy\right)\right) \land \left(\operatorname{apply}\left(e, \operatorname{fst}\left(xy\right)\right) = \operatorname{apply}\left(e, \operatorname{snd}\left(xy\right)\right) \land \left(\operatorname{apply}\left(e, \operatorname{snd}\left(xy\right)\right) < 1 \land \left(\operatorname{not}\left(\operatorname{fst}\left(xy\right)\in \operatorname{exclusion}\left(C, u, p\right)\right) \land \operatorname{not}\left(\operatorname{snd}\left(xy\right)\in \operatorname{exclusion}\left(C, u, p\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalWidthContact.original_width_contact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix the original p, F=D(p), M>0, an effect b and points q,r in F attaining the full width M. The conclusion selects one ordered pair (x,y) of original states. It has b(x)=1, b(y)=0 and q-r=M(x-y). Every other ordered pair with these same properties equals it. If M<1, this same pair satisfies 0<e(x)=e(y)<1 for every original confirmer e of p which vanishes on all of F. Both points are then outside F. No claim says that both contacts are pure or that different maximizing b have the same contacts.

For an arbitrary continuous linear functional h, compactness supplies its actual minimum a and maximum z on K. If its oscillation s=h(z)-h(a) is positive, the full-cone effect (h-h(a)u)/s has contrast at most M on q,r. Hence h((q-r)/M)<=s. If s=0, h(q)=h(r), giving the same inequality. The closed convex set K-K is the intersection of its containing half-spaces, so the same vector (q-r)/M lies in K-K. This gives one actual pair x,y in K. Its b contrast equals one, and the original effect bounds force b(x)=1 and b(y)=0. In particular the resulting member of X-Y satisfies every directional support inequality for X-Y; no directional optimizers are combined.

For any original full-amplitude effect, its two contact sets are compact convex faces. If the zero face is not a pure singleton, the original proper-face classification makes it an entire D(t). For every pure s in the one face, the same effect puts D(t) inside D(s). Whole-ball facial rigidity and injectivity of the exclusion labels force s=t. Krein-Milman then makes the entire one face a singleton. Thus at least one contact face is a singleton, and the fixed difference uniquely determines the other endpoint.

Every confirmer e vanishing on F annihilates q-r, so both contacts have equal readings. A common zero reading would put both contacts in F, where the original b would have contrast one, contradicting its full width M<1. A common reading one puts both contacts in the singleton one face of e, contradicting their b readings one and zero. This proves the strict bounds for all such e after the single pair has been fixed.

For the global maximum-width application, take the whole F supplied by the positive attained global maximum in the original width theorem 118.15 and use the same attained b and its actual two extrema. No new global maximum theorem is asserted here. The local conclusion applies to every positive attained whole-face width and requires no restriction of p to uniquely confirmed labels. It does not produce a common exclusion ball containing the two contacts, does not force M=1 and does not establish the global width-one or dense-triangle condition. This is a deduction in the specified full-effect convex model, with no claim of literature priority or physical instrument realization.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OriginalWidthContact.WidthBound`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalWidthContact.contact_face_subsingleton`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalWidthContact.normalized_effect`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalWidthContact.original_width_contact`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalWidthContact.top_exposed`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalWidthContact.top_subsingleton_of_zero_exclusion`
- Dependency: [D5/S3/Quantum/Foundation/ExclusionBallFaces](ExclusionBallFaces.md)
