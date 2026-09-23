[Index](../../marked_head_profile.md) · [Complete J moments](241-one-original-j-head-controls-complete-square-and-factorial-moments.md) · [Actual J source](../129-192/130-the-whole-j-face-forces-source-anti-alignment.md) · [Arbitrary J head corrections](219-one-late-source-split-controls-complete-saturated-j-heads.md)

# The actual J survivor mass and H column sharpen the complete square

On both entire actual saturated J faces, every complete independently labelled
original357 test A satisfies the stronger square bound

    integral A^2 dmu <=5539/1200=4.615833333333... .

This improves241's371/80 by13/600. The measure is the same unnormalized
actual survivor mu, with mass3/20. The existing bounds

    integral A dmu <=16/25,
    integral Phi5(A)dmu <=6353/7200

remain available from241. The new square retains all12500 original six-label
layouts and every complete old and positive-seven tail. It adds one exact
joint-head dual. A complete52-cost numerator and denominator must still be
recomputed by any later consumer; these moments alone do not give a global
comparison or an off-face theorem.

## Actual measures supply the joint finite model

Use219's canonical J coordinates, with five cells c and first-five slots
s=(P,A,B,Q,H), root map(0,0,1,1,1), and

    eta=(1/18,1/9,1/9,1/9,1/9),
    q=(0,1/5,1/5,3/20,1/5),
    theta=1/135+(1/90-1/135)*t, 0<=t<=1.

The actual raw source Lambda and actual survivor mu induce25-cell masses

    x(c,s)=Lambda(cell c times slot s),
    y(c,s)=mu(cell c times slot s).

Let e3(c,s) be the projected actual virtual deletion from all pure3deep old
cofactors, and e5(c,s) the sum from deep pure5 and deep root5 old cofactors.
These are the two distinct complete deletion families in219. All four
arrays are nonnegative; the variable t is also nonnegative. Thus there are
25+25+25+25+1=101 nonnegative variables.

The same actual source obeys219's absolute cap table at theta and its exact
group masses:

    0<=x(c,s)<=cap_theta(c,s),
    sum_s x(0,s)=1/24,
    sum_s x(1,s)=1/12,
    sum_(c>=2,s)x(c,s)=1/8.

The retained density is the original J array

    w(c,s)=1-[1_(c<2)+1_(c=1)+1_(s=H)+1_(c>=2,s=H)]/5.

At saturation the actual deleted measure equals the sum of virtual
deletions. The four shallow families contribute exactly(1-w)*Lambda on
these rectangles. Removing e3 and e5 as well leaves only other nonnegative
deletions. Consequently, on each rectangle,

    y(c,s)+e3(c,s)+e5(c,s)<=w(c,s)*x(c,s).

The complete actual survivor mass and deletion marginals give

    sum_(c,s)y(c,s)=3/20,
    e3(c,s)=0 for c>=2,
    e3(0,s)+e3(1,s)=q_s/90,
    sum_s e5(c,s)=eta_c*(1+1_(c>=2))/100.

These are constraints on the actual source, survivor and deletion measures,
all at one common theta. Projected overlaps of different forbidden families
do not invalidate the inequality: saturation gives equality of the complete
deleted measure and the sum of their virtual measures before projection.
No arbitrary feasible LP vector is declared to be an actual family.

## The source-free H column is exact in every cell

Source130 proves that a saturated forbidden cofactor5 uses the source-free
first-five slot H. Its raw source cap is h/5, where h=sum eta_c=1/2, and
saturation gives Lambda(H)=h/5. On the other hand, each cell has

    Lambda(cell c times H)<=eta_c/5.

The sum of these five upper bounds is already h/5. Equality of the total
therefore forces equality in every cell:

    x(c,H)=eta_c/5, c=0,...,4.

This implication uses the actual cofactor's saturated capacity. It does not
infer equality merely from the relaxed source cap table. It is also the only
additional structure used here beyond the joint actual-mass/deletion model.
No finer product relation or slot-support constraint is imposed on e3 or e5.

With t<=1, the25 raw caps,25 linked mass inequalities and15 root1 e3 zero
constraints, the model has66 inequalities. Its equalities are the three raw
group masses, one survivor mass, five e3 slot marginals, five e5 cell
marginals and five exact H-column entries, for19 equalities.

## One exact rational dual on the entire theta interval

Retain241's original controlling layout

    ell=(r3,c9,s5,r15,s15,c45,s45)=(1,4,2,1,2,4,2).

Its original six-label head is

    B(c,s)=1+1_(ROOT(c)=r3)+1_(c=c9)+1_(s=s5)
             +1_(ROOT(c)=r15,s=s15)+1_(c=c45,s=s45).

The joint LP objective is sum_(c,s)B(c,s)^2*y(c,s). The exact certificate
provides nonnegative inequality prices u and unrestricted equality prices v.
Writing the finite model as Az<=b, Ez=e, z>=0, the checker verifies

    A^T*u+E^T*v>=objective

in every one of its101 columns, and evaluates

    u*b+v*e=2593/1800.

Multiplying valid inequalities by nonnegative prices and adding the equality
identities therefore proves

    integral B^2 dmu <=2593/1800

for every actual source embedded above. This is an exact arithmetic upper
certificate; neither numerical solver output nor a primal attainment claim
is required by the verifier. The normalized late parameter t is a genuine
variable in this LP. Thus the dual covers its entire interval directly.
No convexity or endpoint-only optimization of the new retained LP value is
assumed.

For comparison,241's separate head correction at theta=1/90 gives329/225.
The joint bound is smaller by13/600. In this dual the actual survivor-mass
equality has price1, the root1 raw-mass equality has price3, and the H-column
equalities in cells L and M have price-6/5 each. Negative equality prices
are permitted. The certificate retains every other price and all101 column
slacks, so the complete inequality is independently reconstructible.

## All complete crosses and tails remain on the same head

Use241's partition A=B+O+Z. Its complete old-tail operator T and complete raw
old-label row R_theta bound the two crosses by

    2 integral B*O dmu <=2T(wB),
    2 integral B*Z dmu <=(2/5)R_theta(B).

The complete ordered tail square remains5947/3600. For this fixed original
layout,241's raw cross expression is convex in theta: R_theta is a sum of
maxima of affine raw-source LP values, while T is independent of theta.
Its whole-interval upper, including the entire ordered tail, is

    max_theta[2T(wB)+(2/5)R_theta(B)+5947/3600]
       =11431/3600.

This endpoint reduction applies only to the inherited raw cross expression.
The new retained head is bounded on the full interval by the joint dual.
Both inequalities hold at the same actual source and theta, so their sum is
a valid uniform bound even though their relaxed optimizers need not agree:

    integral A^2 dmu <=2593/1800+11431/3600=5539/1200.

No saving is subtracted from a different measure or from a separately
optimized downstream numerator. The whole head-square term is replaced by
a valid joint bound, and every other term of the complete square is kept.

## All other original layouts and inherited moments

For each of the other12499 independently labelled original layouts, use
241's unchanged complete square bound over its entire theta interval. The
exact maximum over this remaining set is

    16439/3600=4.566388888888... <5539/1200.

Hence the new bound covers all12500 original layouts. The helper explicitly
reconstructs both old endpoint bounds for each layout and verifies this
partition. The original complete maximum371/80 is also recovered exactly.
Only the displayed controller requires the new joint dual; no other original
layout is dropped or implicitly assumed equivalent.

The existing root1 permutations transport every ordered distinct source
pair(L,M), and the root0 exchange transports the second J orientation. Raw
and survivor arrays, both deletion families, H-column equalities and original
test layouts transform together. Thus the same model and full inventory
cover both whole actual J faces. Every exponent tail is the convergent
complete cap series of241; its monotone and uniform-tail arguments supply
the same infinite-test and limiting-face interpretations here.

The factorial theorem6353/7200 is consumed directly from241. This result
does not claim an improvement to that factorial bound or use the new square
to replace any distinct-pair term in its proof. The original actual mass
3/20 and mean16/25 are retained on the same domain.

## Exact certificate and scope

The [helper](../../frontier/j-geometry/j_face_joint_retained_square.py) and
[certificate](../../certificates/source_norms/j-geometry/j_face_joint_retained_square.json)
retain the complete finite LP, one rational dual with all101 column margins,
both complete controller crosses, every inherited tail value, the remaining
layout maximum and its witnesses, and a digest of all12500 component records.
The full241 dependency closure is pinned. The verifier uses only Python's
standard library and exact rational arithmetic, including in optimization
mode; it does not call a numerical LP solver.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j-geometry/j_face_joint_retained_square.py --check
```

This is an ordinary mathematical bound with exact arithmetic verification
on saturated actual J faces. A later complete consumer must separately
include every original cost, signed mass contribution, AP survival block
and infinite count tail. No actual-family attainment, off-face transport,
Lean theorem or unrestricted Erdos7 resolution is asserted.
