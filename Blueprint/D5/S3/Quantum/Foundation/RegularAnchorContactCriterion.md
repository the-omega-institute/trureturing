# Regular-anchor contact and shell scale

## Abstract

The original regular-anchor system satisfies the complete width, minimum and actual shell-contact equivalence, with positive strict-scale distance.

This is Theorem 122.13, equation Q122.34. V is the original finite dimensional real normed space. C is the original closed generating convex cone, and u is strictly positive on every nonzero point of C. Strict positivity implies salience: x and -x cannot both be nonzero cone elements, since u(-x)=-u(x). No salience follows merely from the name PointedCone.

The entire original normalized base is K={x in C:u(x)=1}; P consists of all its extreme points. The effect interval E contains every original real-linear f with 0<=f<=u on all C. F_p={f in E:f(p)=1}, T_p(x)=min over F_p of f(x), and D_p={x in K:T_p(x)=0}. The existing comparison-attainment theorem identifies this set with the full exclusion, including its mixed states. A_p consists of all common effects e in F_p that vanish on all D_p. Regular(C,u,p) means A_p is a singleton. The supplied e is its member and therefore is exactly e_p.

EB3 asserts that every original pure label has a chart of its entire exclusion by the closed three-ball. Exclusion injectivity means D_p=D_q implies p=q for all original pure p,q. For the fixed anchor the supplied chart a has an injective affine map with a(closedBall(0,1))=D_p. In source notation c=a(0) and B=a.linear, so D_p=c+B closedBall(0,1). Its linear directions lie in ker(u). There is no assumption that the pure-state set is closed, and no pair, global leastness, matrix representation or dimension reduction premise.

Apply RegularAnchorNormalChart.regular_anchor_native to precisely these hypotheses, p,e and a. It derives the restriction isomorphism on the real span of N_p={h>=0 on C:h(p)=0}, the actual linear H with H(a(w))=w, H(p)=0 and each coordinate in span(N_p), and g=u-e. It proves g>0 on all K except p, g(a(w))=1 for every coordinate w, and a finite positive M with norm(H(x))<=M*g(x) on the whole cone. Thus the normal interface, its support bounds and its actual three-dimensional coordinates are conclusions.

Define Z={H(x)/g(x):x in K except p}, S=closure(Z), rho(v)=sup over Z of -inner(v,z), and delta=min over the entire unit sphere of rho. The same original state supplies both H(x) and g(x). RegularAnchorWidthAntipode.actual_image_bound and ball_subset_actual give boundedness and the entire unit ball in Z. The proved perspective construction gives convexity of Z. The shell is consequently compact and convex with nonempty ambient interior, and its support in direction -v is exactly rho(v).

The definitions width(a), minimum(n), shell(n) and boundaryDistance(n) are the original W(D_p), delta, S and set distance, respectively. Width takes the supremum of the entire original effect interval; width_attained proves that this is a maximum and supplies an actual effect and two antipodal chart states. The directional supremum is finite and Lipschitz. minimum_attained proves that its sphere infimum is a minimum and that delta>=1. boundaryDistance is the real infimum of dist(x,y) over the whole closed unit ball and the whole shell frontier; both sets are nonempty. The formula below uses smul for scalar multiplication of the whole set, intersection for set intersection and subset for set inclusion.

**Definition 1.1 (All contact and strict-scale clauses).**

$$\operatorname{ContactCriterion}\left(n\right) \Leftrightarrow \left(\left(\operatorname{width}\left(a\right) = 1 \Leftrightarrow \operatorname{minimum}\left(n\right) = 1\right) \land \left(\left(\operatorname{minimum}\left(n\right) = 1 \Leftrightarrow \operatorname{Nonempty}\left(\operatorname{intersection}\left(\operatorname{closedBall}\left(0, 1\right), \operatorname{frontier}\left(\operatorname{shell}\left(n\right)\right)\right)\right)\right) \land \left(1< \operatorname{minimum}\left(n\right) \Rightarrow \left(\operatorname{subset}\left(\operatorname{smul}\left(\operatorname{minimum}\left(n\right), \operatorname{closedBall}\left(0, 1\right)\right), \operatorname{shell}\left(n\right)\right) \land \left(\operatorname{subset}\left(\operatorname{closedBall}\left(0, 1\right), \operatorname{interior}\left(\operatorname{shell}\left(n\right)\right)\right) \land \left(\operatorname{minimum}\left(n\right)-1 \le \operatorname{boundaryDistance}\left(n\right) \land 0< \operatorname{minimum}\left(n\right)-1\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.ContactCriterion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here n is the derived normal chart for the same C,u,p,e,a. The displayed conjunction means width one if and only if minimum one, minimum one if and only if the closed unit ball meets the boundary of its actual shell, and the complete strict-delta conclusion. By transitivity it includes both directions between every pair of the three contact conditions. All boundaries and interiors are ambient in the actual coordinate space EuclideanSpace(R,Fin(3)).

**Theorem 1.2 (Complete criterion on the original telescope).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in V,\; \operatorname{mem}\left(x, C\right) \Rightarrow \left(x\neq 0 \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{EB3}\left(C, u\right) \Rightarrow \left(\operatorname{exclusionInjective}\left(C, u\right) \Rightarrow \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall e \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{common}\left(C, u, p, e\right) \Rightarrow \left(\operatorname{Regular}\left(C, u, p\right) \Rightarrow \left(\forall a \in \operatorname{FullBall3Chart}\left(C, u, p\right),\; \exists n \in \operatorname{NativeChart}\left(C, u, p, e, a\right),\; \operatorname{ContactCriterion}\left(n\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.regular_anchor_contact_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The notation exclusionInjective(C,u) in the display means injectivity of p -> exclusion(C,u,p) on the entire original pure carrier. NativeChart in the existential conclusion is derived from the original hypotheses; no normal chart, H, support representation, continuity or attained minimum is supplied as an additional premise.

For width one, width_attained gives a full original effect with oscillation one at a unit direction's antipodal states. The original effect bounds make its endpoint readings exactly one and zero. rho_one_iff_antipodal, using the original comparison and positive normal-body interfaces, gives rho(v)=1. Conversely rho(v)=1 supplies a full original separating effect, hence width one. This is width_one_iff_rho_one on the entire original effect domain. Since the attained sphere minimum is at least one, existence of a unit direction with rho(v)=1 is equivalent to delta=1, in both directions.

If rho(v)=1 for a unit v, the actual point -v belongs to Z and saturates -inner(v,z)<=1 on S. A neighborhood in S would contain a point farther in direction -v and violate that inequality, so -v is on the boundary. Conversely a contact z in closedBall(0,1) and frontier(S) has a supporting nonzero functional. Its normalized Riesz vector b satisfies 1<=inner(b,z)<=norm(z)<=1. Equality gives norm(z)=1 and b=z, and therefore rho(-z)=1. These are the exact signs of rho_one_frontier and ball_frontier_direction. minimum_one_iff_contact supplies the second displayed equivalence.

For delta>1, the proved separation theorem mem_shell_iff reconstructs the actual closed convex S from all its unit support halfspaces. Cauchy-Schwarz and delta<=rho(v) put every vector of norm at most delta in S, by minimum_ball_subset. Because delta is positive, the standard smul_unitClosedBall identity identifies this closed ball with delta times the entire closed unit ball. strict_margin puts the original unit ball in interior(S). Every frontier point has norm at least delta; the triangle inequality gives dist(x,y)>=delta-1 for every original inner-ball x and every frontier y. strict_boundary_distance takes the nonempty distance-value infimum and proves boundaryDistance>=delta-1>0.

This is a conditional mathematical statement on the declared original cone and effect system. It neither assumes smoothness, strict convexity or closedness of Z nor derives contact from those properties. It makes no physical realization or literature novelty claim.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.ContactCriterion`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.regular_anchor_contact_criterion`
- Dependency: [D5/S3/Quantum/Foundation/RegularAnchorShell](RegularAnchorShell.md)
