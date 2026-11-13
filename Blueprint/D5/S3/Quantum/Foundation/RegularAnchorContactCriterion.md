# Regular-anchor contact and shell scale

## Abstract

The original regular-anchor system satisfies the complete width, minimum and actual shell-contact equivalence, with positive strict-scale distance.

Let V be a finite dimensional real normed space, C its original closed generating cone, and u a linear functional strictly positive on every nonzero vector in C. Keep the entire normalized base K, all its extreme points P, and the entire original effect interval zero <= f <= u. Every original exclusion D(p) is the image of the entire closed Euclidean three-ball under an injective affine map. Assume that equality of exclusion sets implies equality of their original pure labels. No closedness of P, pair properness, least-confirmation law, matrix representation or dimension reduction is assumed.

**Definition 1.1 (Original coordinate space).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.ThreeSpace`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.ThreeSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate space is EuclideanSpace over the reals indexed by Fin 3, with its Euclidean inner product and norm.

**Definition 1.2 (Entire exclusion chart).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.FullBall3Chart`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.FullBall3Chart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A chart consists of an injective affine map a from the three-dimensional coordinate space to V whose image of the whole closed unit ball equals the original exclusion. Its center is c=a(0), and its linear part B is injective. The native chart conversion preserves the map and the exact whole-image equality.

**Definition 1.3 (All original exclusions are three-balls).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.EB3`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.EB3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every pure point of the entire original base there exists a full three-ball chart. This quantifies every original label and every mixed state in its exclusion.

**Definition 1.4 (Existing native chart carrier).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.nativeChart`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.nativeChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same affine map, injection and whole exclusion equality form an ExclusionChart with dimension exactly three.

**Definition 1.5 (Original regularity).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.Regular`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.Regular` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Regularity at p says that there exists exactly one original linear effect e confirming p and vanishing on every state of D(p). It is uniqueness in the entire common-confirmation family, rather than uniqueness of an exclusion label.

**Definition 1.6 (Signed original normal space).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.NormalSpan`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.NormalSpan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N(p) is the existing zeroPositive set of all original linear functionals nonnegative on the whole cone and zero at p. NormalSpan is its real linear span. Neither positivity nor a choice of effects replaces this signed span.

**Definition 1.7 (Actual constant and slope restriction).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.coordinates`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restriction coordinates of f are its value at the chart center and the existing Euclidean Riesz slope of f composed with B. The exact native slope formula gives f(a(w))=f(c)+inner(slope(f),w) for every coordinate vector, including vectors outside the unit ball.

**Definition 1.8 (All affine coordinate functions).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.affineCoordinates`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.affineCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The standard constant-plus-linear equivalence for affine maps and the finite dimensional Riesz equivalence identify all affine real functions on the coordinate space with a real constant and a coordinate vector.

**Definition 1.9 (Derived native chart laws).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.NativeChart`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.NativeChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The data include a linear equivalence from span N(p) onto all affine functions on the actual three-ball, with its forward map proved equal to original restriction. They include an original linear H:V->R^3 satisfying H(a(w))=w for all w, every coordinate functional of H in span N(p), and H(p)=0. For g=u-e they include g in N(p), g(a(w))=1, strict positivity of g on all K except p, and a finite positive M with norm(H(x))<=M*g(x) on the whole original cone. They also identify original comparison zero with the entire exclusion on K, prove source salience from the strict unit, prove u(Bw)=0 for all w, and give dim(span N(p))=4.

**Theorem 1.10 (Original regular-anchor restriction and uniform bound).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.regular_anchor_native`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.regular_anchor_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the original closed cone, strict unit, generation, full EB3, injective exclusion labels, an original pure p, its common confirmer e, actual regularity at p, and any full chart a of D(p). Then NativeChart data exist with exactly these original parameters. No restriction isomorphism, extension, positivity bound, support representation or shadow geometry is an input.

OriginalNormalRestriction.original_normal_restriction supplies the full affine restriction equivalence on the span of all positive continuous annihilators. Finite-dimensional linear-to-continuous equivalence transports that very span to NormalSpan. Its forward map is the original restriction, not a separately reproved bijection. The standard affine constant-plus-linear and Riesz equivalences give the actual constant and slope coordinates.

Pull back the three unit coordinate slopes to obtain H. Positive annihilators with slopes plus and minus r times each coordinate vector equal g plus and minus r times the corresponding coordinate functional of H. Whole-cone positivity gives absolute value of each H coordinate at most g/r; the Euclidean triangle inequality gives the finite bound M=3/r. Thus the bound includes every mixed original state and extends homogeneously to all cone vectors. For strict positivity of g on K except p, OriginalWidthContact.top_subsingleton_of_zero_exclusion applies to the same common effect e and proves that its entire maximum face is the singleton p.

ExclusionWidthCompactness.comparison_zero_iff identifies comparison(p,x)=0 with an actual original confirmer vanishing at x on the entire base, exactly the native exclusion definition. The construction establishes the original-domain input for normalized shadow ratios; width, directional support minima and boundary-distance conclusions require their additional arguments. These are consequences within the specified mathematical model; no physical realization or literature priority is asserted.

Application to the entire native qutrit family.

Take V=HermitianMat(Fin(3),C) with its existing real normed-space and finite-dimensional instances, C=HermitianExclusionKernel.cone, and u=HermitianExclusionKernel.unit, the real trace. This is the entire PSD cone and its whole trace-one base. HermitianMat.isClosed_nonneg proves closedness; HermitianMat.trace_pos gives strict positivity of u on every nonzero PSD element; the positive-part minus negative-part decomposition shows that this cone spans all of V.

The real Riesz equivalence represents every original real-linear functional f on V as X -> inner(E,X) for one Hermitian E. The original condition proper(C,u,f) is exactly 0<=E<=I, by self-duality of the PSD cone and the same trace pairing. Thus the full effect domain is retained. SectionROGFrame.whole_pure_carrier, applied to the whole Hermitian subspace and its PSD rank-one decomposition, identifies every extreme point of the entire trace-one base with rankOne(v) for a unit complex vector v. In particular v=(1,0,0) gives the actual original pure anchor p=diag(1,0,0).

HermitianExclusionKernel.exclusion_iff_kernel identifies the entire original D(rankOne(v)) with all PSD trace-one X satisfying Xv=0, including every mixed state and the original existential quantification over all proper real-linear effects. For PSD X, its zero-quadratic-form criterion and SectionROGFrame.pair_rankOne identify this kernel condition with inner(rankOne(v),X)=0. Consequently the normalized complement sigma(v)=(I-rankOne(v))/2 belongs to the same entire exclusion.

This complement also proves injectivity on every original pure label. If the full exclusions of rankOne(v) and rankOne(w) coincide, sigma(v) lies in both. Its zero pairing with rankOne(w), together with both unit-vector trace identities, gives inner(rankOne(w),rankOne(v))=1. SectionROGFrame.pairing_one_unique then forces the two pure matrices to be equal. No selected subset of pure labels is used.

The actual common effect at p is e(X)=inner(p,X), equal to Re(X(0,0)) on all of V. It confirms p and vanishes on the entire D(p). For any original common real-linear f, write f(X)=inner(E,X) by Riesz. Properness gives 0<=E<=I, confirmation gives inner(E,p)=1, and f(sigma(v))=0 gives trace(E)=1. The same frozen pairing_one_unique theorem forces E=p. Hence every common f equals this e: both common(C,u,p,e) and the original unique-existence predicate Regular(C,u,p) hold on their full domains.

For each original pure q, HermitianExclusionBall.all_pure_charts supplies an actual ExclusionChart of its entire exclusion with dimension exactly three. Substituting that dimension into the existing chart fields gives FullBall3Chart(C,u,q), proving EB3 on the entire original pure carrier. Choose any one of these actual charts at p as a. Applying regular_anchor_contact_criterion to the proved closedness, strict unit, generation, EB3, full exclusion injectivity, actual common e and Regular p yields one NativeChart(C,u,p,e,a) satisfying this document's complete ContactCriterion. Thus all hypotheses and the endpoint conclusion have one common native realization; no original-domain bridge is assumed.

This is an application of existing frozen kernel, full-chart and rank-one results to the conditional contact theorem. It establishes satisfiability of the complete original hypotheses. It supplies no example with delta>1, no classification of all admissible cones, no claim about a separate full regular-pure family or triangle condition, and no physical realization or literature priority claim.

This is Theorem 122.13, equation Q122.34. V is the original finite dimensional real normed space. C is the original closed generating convex cone, and u is strictly positive on every nonzero point of C. Strict positivity implies salience: x and -x cannot both be nonzero cone elements, since u(-x)=-u(x). No salience follows merely from the name PointedCone.

The entire original normalized base is K={x in C:u(x)=1}; P consists of all its extreme points. The effect interval E contains every original real-linear f with 0<=f<=u on all C. F_p={f in E:f(p)=1}, T_p(x)=min over F_p of f(x), and D_p={x in K:T_p(x)=0}. The existing comparison-attainment theorem identifies this set with the full exclusion, including its mixed states. A_p consists of all common effects e in F_p that vanish on all D_p. Regular(C,u,p) means A_p is a singleton. The supplied e is its member and therefore is exactly e_p.

EB3 asserts that every original pure label has a chart of its entire exclusion by the closed three-ball. Exclusion injectivity means D_p=D_q implies p=q for all original pure p,q. For the fixed anchor the supplied chart a has an injective affine map with a(closedBall(0,1))=D_p. In source notation c=a(0) and B=a.linear, so D_p=c+B closedBall(0,1). Its linear directions lie in ker(u). There is no assumption that the pure-state set is closed, and no pair, global leastness, matrix representation or dimension reduction premise.

Apply RegularAnchorContactCriterion.regular_anchor_native to precisely these hypotheses, p,e and a. It derives the restriction isomorphism on the real span of N_p={h>=0 on C:h(p)=0}, the actual linear H with H(a(w))=w, H(p)=0 and each coordinate in span(N_p), and g=u-e. It proves g>0 on all K except p, g(a(w))=1 for every coordinate w, and a finite positive M with norm(H(x))<=M*g(x) on the whole cone. Thus the normal interface, its support bounds and its actual three-dimensional coordinates are conclusions.

Define Z={H(x)/g(x):x in K except p}, S=closure(Z), rho(v)=sup over Z of -inner(v,z), and delta=min over the entire unit sphere of rho. The same original state supplies both H(x) and g(x). actual_image_bound and ball_subset_actual give boundedness and the entire unit ball in Z. The proved perspective construction gives convexity of Z. The shell is consequently compact and convex with nonempty ambient interior, and its support in direction -v is exactly rho(v).

The definitions width(a), minimum(n), shell(n) and boundaryDistance(n) are the original W(D_p), delta, S and set distance, respectively. Width takes the supremum of the entire original effect interval; width_attained proves that this is a maximum and supplies an actual effect and two antipodal chart states. The directional supremum is finite and Lipschitz. minimum_attained proves that its sphere infimum is a minimum and that delta>=1. boundaryDistance is the real infimum of dist(x,y) over the whole closed unit ball and the whole shell frontier; both sets are nonempty. The formula below uses smul for scalar multiplication of the whole set, intersection for set intersection and subset for set inclusion.

Keep the original finite dimensional real carrier V, closed generating cone C, strictly positive unit u, complete base K and full effect interval 0 <= f <= u. Every original exclusion has a full three-ball chart, and equality of exclusions identifies their pure labels. At the original regular anchor p the actual common confirmer e is unique. The NativeChart input is derived by RegularAnchorContactCriterion.regular_anchor_native from precisely these original hypotheses; it supplies neither a free positivity bridge nor a chosen subfamily of effects.

**Definition 1.11 (Entire actual ratio image).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.actualImage`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.actualImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Z is the image of every x in K other than p under H(x)/g(x), where g=u-e. NativeChart proves g is positive on this entire domain. No closedness of the pure state carrier is assumed.

**Theorem 1.12 (Convexity of the entire actual image).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.actual_image_convex`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.actual_image_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two original states x,y and nonnegative weights s,t summing to one, normalize s*x/g(x)+t*y/g(y) by d=s/g(x)+t/g(y). Both gaps are strictly positive, hence d is positive. The resulting original base state has gap 1/d and its actual ratio is the requested convex combination. It cannot be the anchor. Closure preserves convexity; the existing whole-image norm bound makes S compact. The entire actual unit ball lies in S, giving nonempty ambient interior.

**Definition 1.13 (Actual directional support).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rho(v) is the supremum of -inner(v,z) over the whole actual ratio image. It is the exact source supremum of -inner(v,H(x))/g(x) over all x in K other than p.

**Theorem 1.14 (Whole actual image is bounded).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.actual_image_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.actual_image_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a finite positive M bounding the norm of every actual ratio image. Divide the proved whole-cone NativeChart bound by the strictly positive gap on K except p.

**Theorem 1.15 (The whole inner ball is actual).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.ball_subset_actual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.ball_subset_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every vector w in the closed unit ball is the ratio image of the actual state a(w), with gap exactly one. This state cannot equal p, whose gap is zero.

**Theorem 1.16 (Every full support supremum is bounded).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_values_bdd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_values_bdd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every vector v the entire set of support readings on Z is bounded above by norm(v)*M. The real supremum therefore has its ordinary upper-bound meaning.

**Theorem 1.17 (Whole-base support bound).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_le_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_le_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r and every coordinate vector v, rho(v)<=r is equivalent to -inner(v,H(x))<=r*g(x) for every original base state x other than p. The whole-cone NativeChart bound proves that the defining supremum is finite.

**Theorem 1.18 (Actual inner-ball lower bound).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_unit_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_unit_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit v, rho(v)>=1 because the actual original chart point a(-v) has g=1 and H=-v. This uses an actual state in the original exclusion.

**Definition 1.19 (Original directional linear effect).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.direction`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.direction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real linear functional direction(v) on V is inner(v,H). Its coordinate expansion lies in the entire signed normal span. The proved restriction isomorphism, rather than an additional premise, reconstructs every normalized positive annihilator with slope v as g+direction(v).

**Theorem 1.20 (Exact actual antipodal criterion).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_one_iff_antipodal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_one_iff_antipodal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit v, rho(v)=1 exactly when some effect in the entire original interval takes one at a(v) and zero at a(-v). Positivity is derived on the full original cone from the ratio bound; ExclusionWidthCompactness.comparison_zero_iff identifies actual comparison zero with exclusion in both directions, so an arbitrary original separating effect enters the existing comparison and slope-body theorem. The source direction v and the actual chart antipodes are retained without reversing or replacing their carriers.

**Definition 1.21 (Entire exclusion oscillation).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.oscillation`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.oscillation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Oscillation is the supremum of f on the entire original exclusion minus its infimum there. This is ExclusionWidthCompactness.oscillation on the same entire exclusion. Every original real linear effect is continuous in the finite dimensional topology.

**Definition 1.22 (Full original effect width).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.width`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.width` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

W(D(p)) is the ExclusionWidthCompactness.width of the entire exclusion: the supremum of its oscillation over all effects in the full original interval 0<=f<=u. The attainment theorem proves this is the source maximum, so the supremum notation does not weaken the source definition or remove an effect.

**Theorem 1.23 (Actual full-effect width attainment).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.width_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.width_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist a real linear effect f on the original carrier and a unit coordinate vector v such that W(D(p))=f(a(v))-f(a(-v)). The same actual f maximizes at a(v) and minimizes at a(-v) over the whole exclusion. ExclusionWidthCompactness.width_attained supplies a maximizing effect and actual extrema on the compact entire exclusion. For that same effect, the affine slope formula supplies one unit direction with antipodal extrema, including the constant-slope case.

**Theorem 1.24 (Exact width and actual unit-support equivalence).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.width_one_iff_rho_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.width_one_iff_rho_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Width equals one if and only if an actual unit direction v satisfies rho(v)=1. If width is one, its attaining effect has actual readings one and zero at its antipodal extrema. Conversely any effect supplied by the unit-support criterion gives a full-exclusion oscillation of at least one, while ExclusionWidthCompactness.original_exclusion_width bounds the whole width by one. The reverse inequality applies ExclusionWidthCompactness.effect_difference_le_width to the same actual separating effect and chart antipodes. All quantifiers range over the original cone, base, effect interval and actual full chart.

Keep the same finite dimensional real carrier V, original cone C, unit u, entire base K, pure anchor p, actual common effect e and full three-ball chart a. NativeChart is the derived interface of RegularAnchorContactCriterion.regular_anchor_native, obtained from the original closedness, strict positivity, generation, EB3, exclusion injectivity and regularity hypotheses. Every result below applies to that very interface. The ratio image and rho are defined on this same original domain; neither is replaced by a model or a restricted state family.

**Definition 1.25 (Closed actual shell).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.shell`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.shell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

S is the closure of the image of every state x in K other than p under H(x)/g(x), with g=u-e. The actual image need not be closed.

actual_image_convex proves convexity of the entire actual ratio image by reweighting two original base states. Its closure is convex; the proved whole-image bound makes S compact, and the actual closed unit ball lies in S.

**Theorem 1.26 (Exact shell support relation).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.shell_support_le_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.shell_support_le_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real bound r and every vector v, all z in S satisfy -inner(v,z)<=r exactly when rho(v)<=r. Continuous linear evaluation extends the upper bound from the entire actual image to its closure. Thus the ordinary support of S at -v is precisely the original rho(v).

**Theorem 1.27 (Global directional Lipschitz bound).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_lipschitz`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite positive M bounds every ratio vector. Cauchy-Schwarz bounds each change of support reading by M times norm(v-w). Taking the bounded real supremum in both directions gives the absolute difference estimate for all vectors v,w, and therefore continuity on the whole coordinate space.

**Definition 1.28 (Entire sphere minimum).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.minimum`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.minimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real infimum is taken over rho evaluated on the entire unit sphere of the actual three-dimensional coordinate space.

**Theorem 1.29 (Attainment and inner-ball lower bound).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.minimum_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.minimum_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity on the nonempty compact sphere supplies an actual unit minimizing direction. Its value equals the defined infimum and is at least one; every other unit direction has value at least this same minimum. The infimum is therefore the source minimum, with no assumed attainment field.

**Theorem 1.30 (Actual contact point identifies the direction).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.ball_frontier_direction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.ball_frontier_direction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If z lies both in the closed inner ball and on the boundary of S, then norm(z)=1 and rho(-z)=1. A supporting functional exists because S is convex with nonempty interior. Riesz representation and normalization give its unit normal b. Inner-ball containment yields 1<=inner(b,z)<=norm(z)<=1; equality forces b=z. The direction in rho is exactly -z.

**Theorem 1.31 (Unit support gives the actual point -v).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_one_frontier`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_one_frontier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For unit v with rho(v)=1, the actual image already contains -v, supplied by the original chart state a(-v). This point belongs to S and saturates its supporting inequality. Any interior neighborhood would contain a slightly farther point in direction -v, contradicting that inequality. Hence -v belongs to the shell boundary.

**Theorem 1.32 (Exact sphere-minimum and ball-boundary equivalence).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.minimum_one_iff_contact`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.minimum_one_iff_contact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The minimum equals one exactly when the closed original coordinate unit ball meets the boundary of its actual shell. An attaining unit direction supplies the contact point -v. Conversely an actual contact z supplies the unit direction -z with rho(-z)=1, while the minimum is at least one. No smoothness, strict convexity or closedness of the actual ratio image is assumed.

**Theorem 1.33 (All unit support halfspaces reconstruct the actual shell).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.mem_shell_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.mem_shell_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A vector z belongs to S exactly when -inner(v,z)<=rho(v) for every unit v. For a point outside the actual closed convex S, strict separation supplies a real continuous functional. Its nonzero Riesz vector gives a unit direction contradicting the asserted inequality. This reconstruction is proved for the actual shell rather than supplied as a bridge premise.

**Theorem 1.34 (Containment at the minimum support radius).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.minimum_ball_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.minimum_ball_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entire closed ball of radius delta=minimum(rho) lies in S. For every unit support direction, Cauchy-Schwarz bounds the reading of a vector in this ball by delta, which is no greater than its actual directional support. The proved halfspace reconstruction gives containment. Since delta>=1, this closed ball is exactly delta times the closed unit ball.

**Theorem 1.35 (Strict containment and every boundary distance).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.strict_margin`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.strict_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If delta>1, the entire original closed unit ball lies in the ambient interior of S. Every boundary point has norm at least delta, since the open ball of radius delta lies in the shell interior. The triangle inequality then gives dist(x,y)>=delta-1 for every inner-ball x and every boundary y.

**Definition 1.36 (Distance of the whole ball from the whole boundary).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.boundaryDistance`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.boundaryDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set distance is the real infimum of all distances dist(x,y), with x in the entire closed unit ball and y on the entire boundary of S. Both sets are nonempty: S contains the unit ball and is a bounded proper convex body, so its boundary is nonempty.

**Theorem 1.37 (Positive distance from the actual boundary).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.strict_boundary_distance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.strict_boundary_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For delta>1, the set distance is at least delta-1, and delta-1 is strictly positive. Nonemptiness of the distance-value set gives the ordinary real-infimum lower bound; the estimate covers every pair of actual points in the specified sets.

**Definition 1.38 (All contact and strict-scale clauses).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall p \in \operatorname{pure}\left(C, u\right),\; \forall e \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall a \in \operatorname{FullBall3Chart}\left(C, u, p\right),\; \forall n \in \operatorname{NativeChart}\left(C, u, p, e, a\right),\; \operatorname{ContactCriterion}\left(n\right) \Leftrightarrow \left(\left(\operatorname{width}\left(a\right) = 1 \Leftrightarrow \operatorname{minimum}\left(n\right) = 1\right) \land \left(\left(\operatorname{minimum}\left(n\right) = 1 \Leftrightarrow \operatorname{Nonempty}\left(\operatorname{intersection}\left(\operatorname{closedBall}\left(0, 1\right), \operatorname{frontier}\left(\operatorname{shell}\left(n\right)\right)\right)\right)\right) \land \left(1< \operatorname{minimum}\left(n\right) \Rightarrow \left(\operatorname{subset}\left(\operatorname{smul}\left(\operatorname{minimum}\left(n\right), \operatorname{closedBall}\left(0, 1\right)\right), \operatorname{shell}\left(n\right)\right) \land \left(\operatorname{subset}\left(\operatorname{closedBall}\left(0, 1\right), \operatorname{interior}\left(\operatorname{shell}\left(n\right)\right)\right) \land \left(\operatorname{minimum}\left(n\right)-1 \le \operatorname{boundaryDistance}\left(n\right) \land 0< \operatorname{minimum}\left(n\right)-1\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.ContactCriterion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here n is the derived normal chart for the same C,u,p,e,a. The displayed conjunction means width one if and only if minimum one, minimum one if and only if the closed unit ball meets the boundary of its actual shell, and the complete strict-delta conclusion. By transitivity it includes both directions between every pair of the three contact conditions. All boundaries and interiors are ambient in the actual coordinate space EuclideanSpace(R,Fin(3)).

**Theorem 1.39 (Complete criterion on the original telescope).**

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
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.EB3`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.FullBall3Chart`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.NativeChart`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.NormalSpan`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.Regular`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.ThreeSpace`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.actualImage`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.actual_image_bound`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.actual_image_convex`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.affineCoordinates`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.ball_frontier_direction`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.ball_subset_actual`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.boundaryDistance`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.coordinates`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.direction`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.mem_shell_iff`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.minimum`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.minimum_attained`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.minimum_ball_subset`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.minimum_one_iff_contact`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.nativeChart`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.oscillation`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.regular_anchor_contact_criterion`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.regular_anchor_native`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_le_iff`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_lipschitz`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_one_frontier`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_one_iff_antipodal`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_unit_lower`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.rho_values_bdd`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.shell`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.shell_support_le_iff`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.strict_boundary_distance`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.strict_margin`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.width`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.width_attained`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.width_one_iff_rho_one`
- Dependency: [D5/S3/Quantum/Foundation/CommonPositiveExtension](CommonPositiveExtension.md)
- Dependency: [D5/S3/Quantum/Foundation/ExclusionWidthCompactness](ExclusionWidthCompactness.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalNormalRestriction](OriginalNormalRestriction.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalWidthContact](OriginalWidthContact.md)
