[Index](../../marked_head_profile.md) · [Previous](08-all-integer-schedules-through23-for-the-fixed-scalar-feature-map.md) · [Next](10-separating-an-original-saturated-test-from-its-higher-labels.md)

<a id="fixed-convex-potentials-for-the-actual-cap-charge"></a>
### Fixed convex potentials for the actual-cap charge

This result uses the same normalized physical kernels, supported head law,
original modulus labels and complete test loads as AP1–AP5 and W1 in
`Problems/erdos-7-odd-covering-systems.md`. It is an ordinary analytic bridge.
No new Lean declaration or unrestricted-prime endpoint is asserted.

<a id="fixed-potential-envelope"></a>
#### Fixed-potential envelope

Fix an integer 2≤T<p−1 and W>0. Put

    d=p−1−T, a=(3p−1)/(p−1)², c=(p−1)/d,
    κ(z)=(p−1)/(p−1−min(z,T)), z≥1,
    H0(z,y)=W(z−T)_+/d+aκ(z)y², z,y≥1.

Choose real knots q1,…,qT with q1=0 and

    0≤q2−q1≤q3−q2≤…≤qT−q_(T−1)≤W/d.                (1)

Let P_q interpolate these knots linearly, and extend it for z≥T by

    P_q(z)=qT+W(z−T)/d.

Define

    V_q(y)=max_(1≤k≤T) {aκ(k)y²−qk}.                 (2)

Then P_q and V_q are nonnegative, increasing and convex on[1,∞), and

    H0(z,y)≤P_q(z)+V_q(y)                            (3)

for all real z,y≥1. More precisely,

    V_q(y)=sup_(z≥1) [H0(z,y)−P_q(z)].               (4)

For each fixed y, the expression on the right is convex in z inside each
unit cell belowT: κ is convex there and P_q is affine. Its maximum on each
cell is attained at an endpoint. For z≥T the expression is constantly
acy²−qT. This proves(4). Equation(2) then makes V_q an increasing convex
maximum of positive quadratics minus constants; its k=1 term is positive.
Condition(1) gives the assertions for P_q.

The global z-convexity of H0 is NOT needed. In particular this result does
not require the stronger W bound needed for the clipped joint cost H_K.

Define diagonal integer potentials by u(1)=v(1)=0 and

    u(k+1)−u(k)=H0(k+1,k)−H0(k,k),
    v(k+1)−v(k)=H0(k+1,k+1)−H0(k+1,k),

with linear interpolation. Supermodularity bounds H0 by H0(1,1)+u+v
on the integer grid; separate convexity inside every unit cell extends
that bound to real arguments. The u increments beforeT are
ak²[κ(k+1)−κ(k)], followed by W/d; those of v are
aκ(k+1)(2k+1). Thus u is convex provided
W≥a(T−1)²(p−1)/(d+1), while v is convex automatically.
These diagonal potentials are included. Whenever u is convex, choose
qk=u(k); this diagonal majorant implies V_q≤H0(1,1)+v. Thus this
family weakly improves that majorant. A different fixed q can improve it
strictly, as the exact p11 calculation below demonstrates.

<a id="physical-scalar-comparison-and-finite-survivor-criterion"></a>
#### Physical scalar comparison and finite survivor criterion

Let ν be the actual full old law at this prime. Let R be its original
weighted mixed load, w=c_actual its natural prefix-cap multiplier, and b
its conditional assigned mixed-union probability. The existing AP/SH26
estimates say

    w≤κ(1+R), b≤(1+R−T)_+/d.

For every complete old test A,

    Wb+a w A²≤P_q(1+R)+V_q(A).                        (5)

Let μ be the fixed full head law, and let N be the AP auxiliary multiplier
from the preceding tail primes. Write F_μ(g)=max_L E_μg(L), over complete
head tests fixed before sampling the head point. Applying the existing
scalar original-label comparison and Jensen separately to P_q and V_q gives

    Wβ+aΓ(wν)≤C_p(q),
    C_p(q)=E_N[F_μ(L↦P_q(NL))+F_μ(L↦V_q(NL))],       (6)

where β=E_νb. Both scalar comparisons use the same actual law and the same
distribution of N. No physical independence of R and A is asserted.
W1 then proves

    Γ_new+Wβ≤Γ_old+C_p(q).                            (7)

For a finite schedule with one fixed admissible q_p at each prime, summing
(7) gives

    Γ_final+WΣ_pβ_p≤G_head+Σ_pC_p(q_p).               (8)

Consequently

    G_head−1+Σ_pC_p(q_p)≤W                            (9)

is sufficient for positive final survivor mass and Γ_conditioned≤1+W,
using the existing SH28 witness and final conditioning. The full positive
cap energy is already included in C_p. Criterion(9) is a finite supported
probability result, not an infinite-prime noncoverage endpoint. A separate
valid tail theorem is needed to continue it to all remaining primes.

The feasible knot set(1) is compact. For a fixed full head law, C_p(q) is
convex in q: P_q(z) is affine in q and V_q(y) is a maximum of affine
functions of q; expectations and suprema preserve convexity. Quadratic
moment bounds give a uniform integrable envelope. Rational candidate knots
can therefore be checked independently of any numerical optimizer.

<a id="order-of-optimization-and-conditioning"></a>
#### Order of optimization and conditioning

In(5)–(6), q is fixed BEFORE scalar conditional comparison. Therefore

    inf_q E_N C(q,N)

is a valid optimized upper bound. The smaller expression

    E_N inf_q C(q,N)

does not follow from that proof. Choosing separate q_n after observing the
auxiliary N requires a genuine prior comparison of the physical JOINT cost
to a cost under that common auxiliary. Introducing an independent random q
only produces a second independent auxiliary variable in the scalar proof;
it does not justify matching the two indices.

All finite-n head observations must use the full actual head law. In the
SH18 construction write μ=λ(.|F), with λ(F)≥ρ0>0. For g=P_q or g=V_q,
if B_g(n) bounds max_L E_λg(nL), then

    F_μ(L↦g(nL))≤g(n)+[B_g(n)−g(n)]/ρ0.             (10)

Every complete L≥1 and g is increasing, so the numerator is nonnegative.
This saves the minimum cost on the deleted event. The original low315 law
cannot replace the conditional low marginal without this lifting and
conditioning argument. A scalar finite-cost representation with signed
hinge coefficients must use the correct upper/lower bounds for each sign.

<a id="complete-auxiliary-tail-the-threshold-depends-on-q"></a>
#### Complete auxiliary tail; the threshold depends on q

Set

    R_q=max_(1≤k<T) (qT−qk)/[a(c−κ(k))],
    m_q=min{m∈positive integers : m²≥R_q},
    B_q=max(T,m_q).

The denominators are positive. For y≥m_q, the k=T term in(2) dominates,
so V_q(y)=acy²−qT. For every integer n≥B_q, all complete L≥1 satisfy

    P_q(nL)=qT+W(nL−T)/d,
    V_q(nL)=acn²L²−qT.

Thus, for M≥max_LE_μL and G≥Γ(μ),

    F_μ(P_q(nL))+F_μ(V_q(nL))
        ≤W(nM−T)/d+acn²G.                           (11)

The qT constants cancel. Equality holds with exact M,G. Generic optimized
knots do NOT guarantee m_q≤T; assuming the old cutoff T without checking
R_q is invalid. The diagonal knots satisfy m_q≤T−1.

Let π_n=Pr(N=n), and form the exact tail probability and moments

    P_tail=1−Σ_(n<B_q)π_n,
    M_tail=E N−Σ_(n<B_q)nπ_n,
    S_tail=E N²−Σ_(n<B_q)n²π_n.

With certified finite costs U_n,V_n from(10) or a stronger whole-cost
calculation, a complete bound is

    C_p(q)≤Σ_(n<B_q)π_n(U_n+V_n)
       +W(M M_tail−T P_tail)/d+acG S_tail.            (12)

No auxiliary tail is discarded. AP supplies

    E N=Π_(r<p)[1+c_r/(r−1)],
    E N²=Π_(r<p)[1+c_r(3r−1)/(r−1)²].

<a id="original-zero-and-unit-labels-remain-available"></a>
#### Original zero and unit labels remain available

The fixed-q route also permits the existing FL1–FL4 order of operations.
Let h be an original old-tail exponent tuple and let A_h be the event
h≤K for the auxiliary height vector. Keep that tuple's head layout fixed
across every auxiliary outcome. Define

    g_h^P(z)=E[1_(A_h) P_q(Nz)/N],
    g_h^V(z)=E[1_(A_h) V_q(Nz)/N].

Collecting each original layout before maximizing yields the valid bounds

    Wβ+aΓ(wν)≤C_p^labels(q)
      :=Σ_h[F_μ(g_h^P)+F_μ(g_h^V)]≤C_p(q).            (13)

The mixed current-depth weights sum to1, exactly as in AP3–AP4. The tested
family has one completed head layout per old-tail tuple. No q depending
on the sampled N is introduced. Selected tuples, including the always
active zero tuple, can be evaluated before relaxing the remainder.

No new inverse-moment constant is necessary. Define

    Pcor(n,z)=P_q(nz)−Wnz/d−qT+WT/d,
    Vcor(n,z)=V_q(nz)−acn²z²+qT.

These are nonnegative; Pcor vanishes for n≥T and Vcor for n≥m_q. With
w_h=Pr(A_h), r_h=E[N1_(A_h)], and π_h(n)=Pr(A_h,N=n), put

    f_h^P(z)=(W/d)w_h z+Σ_(n<T)π_h(n)Pcor(n,z)/n,
    f_h^V(z)=ac r_h z²+Σ_(n<m_q)π_h(n)Vcor(n,z)/n.

They differ from g_h^P,g_h^V only by constants, hence retain convexity and
monotonicity. The identity Σ_h1_(A_h)=N gives exactly

    C_p^labels(q)=Σ_h[F_μ(f_h^P)+F_μ(f_h^V)]−WT/d.    (14)

The inverse-N constants cancel globally. This is a reorganization of the
existing original-label Jensen proof, not a new independence assertion.

<a id="a-separate-valid-route-allowing-q_n"></a>
#### A separate valid route allowing q_n

For a cutoff K0≥0 satisfying W≥aK0(p−1)/d, define

    H_K0(z,y)=W(z−T)_+/d
      +a[cy²−(c−κ(z))min(y²,K0)].

This majorizes H0 and is increasing, separately convex and supermodular;
it is also jointly convex under that condition. At a fixed head point,
form a tagged union of original mixed labels and NONUNIT test labels,
keeping the test unit class as a fixed offset1. The set functional is
H_K0(1+Σmixed,1+Σnonunit_test), so every intermediate subset remains in
the domain z,y≥1. Each tag adds a nonnegative amount to only one coordinate.
Separate convexity and
increasing differences make this Boolean set functional supermodular.
The existing `KernelChain.comparison` therefore compares both families
with ONE common vector of auxiliary heights.

After AP3 completion the coordinates are bounded by
Σ_(j,e)w_e L_(j,e) and Σ_j B_j on the same N active tuples. Joint Jensen,
or successive separate Jensen, proves

    E_νH0(1+R,A)
      ≤E_N max_(L,B) E_μH_K0(NL,NB).                 (15)

At this stage q_n MAY be selected separately for each n. Its right-hand
potential must majorize H_K0, namely

    V_(q,K0)(y)=max_(k≤T)
       {a[cy²−(c−κ(k))min(y²,K0)]−qk}.               (16)

Using the cutoff-free V_q in(16)'s place is not justified: it majorizes
H0, not necessarily H_K0. For n≥T the actual joint cost in(15) is already
exactly W(nL−T)/d+acn²B², so its tail uses(11) directly without potentials.
This distinguishes the valid clipped common-N route from the fixed-q
cutoff-free scalar route; it does not reject adaptive potentials wholesale.

<a id="exact-improvement-at11-on-the-sh18-probability"></a>
#### Exact improvement at11 on the SH18 probability

Fix `p=11,T=4,W=10000,a=8/25,c=5/3,d=6` and

    kappa(z)=10/(10-min(z,4)),
    q=(0,56/315,128/315,512/315).

Let `Pq` interpolate these four values linearly on[1,4], then continue
with slope `W/d`. Its consecutive slopes are56/315,72/315,384/315,W/d,
which are nonnegative and increasing. Define

    Vq(y)=max_(k=1,2,3,4) [a kappa(k)y²-q_k].

It is the maximum of four nonnegative-leading-coefficient increasing
quadratics and therefore increasing convex on y>=1. Its exact branches are

    (16/45)y²,                     1<=y<=2,
    (16/35)y²-128/315,             2<=y<=4,
    (8/15)y²-512/315,              y>=4.

The middle k=2 candidate only touches the maximum at y=2. In particular
`Vq(1)=16/45` and `Vq(y)-(8/15)y²` is nonincreasing.

For every real z,y>=1,

    W(z-4)_+/6 + a kappa(z)y² <= Pq(z)+Vq(y).

At integer z from1 to4 this follows from the definition ofVq. On each
unit interval below4, `a kappa(z)y²-Pq(z)` is convex in z, so its
maximum lies at an endpoint. Above4 both sides have identical z slope.
This proves the majorant on the actual pair, without a bivariate
conditional-comparison assertion. The q values are fixed before any
auxiliary outcome is sampled.

At the first later prime11 there are no earlier-prime multipliers.
The existing scalar original-label comparison therefore bounds the
same-law combined charge and weighted-cap contribution by

    C11=F_nu[Pq(L)]+F_nu[Vq(L)].

Here nu is exactly the77-point SH18 probability extended and conditioned
as specified by its hash-bound certificate, at arbitrary finite3/5/7
heights. The actual low weights and the survival denominator remain those of SH18.

For Pq, use centerPq(2), the nonnegative increasing convex cut
`(Pq(L)-Pq(2))_+`, and the existing exact affine-tail ratio toL²-1.
For Vq, use centerVq(1)=16/45. Each branch ofVq minus`(8/15)y²` is
nonincreasing, so their maximum is too. Consequently

    0<=Vq(L)-Vq(1)<=(8/15)(L²-1).

The complete omitted-depth square-minus-one budget is multiplied by8/15.
Only the nonnegative cuts are divided by the positive SH18 survival
denominator. Both finite-box maxima use the existing exact280²
singleton-elimination evaluator. All cost entries, maxima, geometric
remainders and final comparisons are rational or bounded integers,
without quantization or optimizer dependence.

The verifier also recomputes the previous diagonal-potential contribution
on the identical law. It establishes a strict improvement of thep11
upper-certificate contribution; it does not assert optimization over all
potentials or close the five-prime continuation. The five-step W=10000
experiment remains unsuccessful.

Run from any working directory with Python3 and NumPy:

    python3 -I -O verify_fixed_q_p11.py

The adjacent source directory (or an explicit --source-dir) must contain the three canonical prerequisites
named and SHA256-bound in`fixed_q_p11_certificate.json`. The verifier
imports only the bound canonical whole-cost module plus the standard
library and NumPy. It reconstructs both candidates'1080 depth-cost
observations and compares the full small certificate. No scratch module,
optimizer or saved floating search state is used.

The exact new contribution and saving are

    C11 ≤ 123671919835372486258252472/51821334214349426015625
        < 2386.505900,
    old diagonal bound − new bound
        = 310704719600900799682/4441828646944236515625
        > 0.069949731.

The largest integer intermediate bound is8015014558798784, below2^63.
This compares two upper-certificate formulas; it is not a decrease of the
actual system's assigned charge or a claim of optimality over all potentials.

<a id="support-dominance-reduces-the-complete-actual315-carrier-task"></a>
### Support dominance reduces the complete actual315 carrier task

Fix one of the six canonical old45 survivor sets S used by the existing actual-carrier classification. The pure7 digit0 is forbidden. The five distinct mixed labels are7d for d in(3,5,9,15,45); each may choose its own old cylinder and7digit. A carrier is encoded by the sorted multiset of its nonempty deletion masks U_y⊆S, y∈{1,…,6}. Repeated masks retain multiplicity and absent masks are empty. Its support is Ω_U={(x,y):x∈S\U_y}. The canonical classification contains965595 such states and170569 orbits under the permitted common CRT root maps.

The following finite reduction leaves56966 inclusion-minimal carrier orbits. It does not claim a moment bound for these remaining cases. The already proved PG1 law certifies232 carrier orbits by support inclusion, including exactly one of the56966 minimal orbits.

<a id="support-inclusion-and-the-actual-higher-family"></a>
#### Support inclusion and the actual higher family

For two carriers A,B on the same S, there exists one common7digit permutation with Ω_A⊆Ω_B after transport if and only if the nonempty masks of B inject into distinct nonempty masks of A, with B_i⊆A_j on each matched pair. Necessity follows by taking complements at each digit. Conversely, use those matched digits and then biject the remaining empty B masks to the remaining A digit positions. Padding to six digits makes this a permutation. A nonempty B mask cannot be assigned to an empty A mask. Duplicate masks remain distinct matching vertices.

Thus a Boolean matching problem on at most five nonempty vertices decides inclusion. The checker represents each target's eligible source digits by a bitmask and exhaustively chooses distinct eligible bits. It also considers the permitted old3/5 root maps. These preserve every cylinder family and extend to every finite higher prime-power depth, as established by the canonical classification.

The moment-bound transfer requires its quantifiers in the correct order. Suppose PG1 supplies a fixed low law μ_A on Ω_A and the stated bound for its uniform higher-digit lift, conditioned on **every** admissible actual higher357 forbidden family. Let T be an allowed coordinate map with TΩ_A⊆Ω_B. Now fix an arbitrary physical height Q and an arbitrary actual higher forbidden family H_B for the larger carrier. Pull H_B back through the extension of T to obtain H_A=T^−1H_B. Each residue cylinder is still a single cylinder of the same original modulus, so the original labels remain distinct and H_A is an admissible higher family.

Apply PG1 to μ_A and this H_A. Push the resulting conditional law forward by T. The pushed law is supported on Ω_B and avoids the actual H_B. It is precisely the uniform higher-digit lift of T_*μ_A conditioned on avoiding H_B. Complete test families pull back to complete test families with the same original modulus labels, so the same moment bound holds. This does not identify higher classes belonging to different carriers: their relation is explicitly the pullback through T, followed by the universal PG1 theorem.

The base law T_*μ_A may give zero mass to the extra points of Ω_B. All cylinder caps, selected higher deletion groups, and geometric-tail estimates are transported with that law. Their dependence is on the law, cylinder families, and original higher-modulus labels; they do not require retaining the source carrier's particular low forbidden residues as the target low family. No ambient uniform-density alternative is used and no geometric tail is truncated.

<a id="every-carrier-contains-an-essential-one"></a>
#### Every carrier contains an essential one

An original mixed label is redundant if its old mask is empty, its digit is0, or its old mask is contained in the union of the other masks at its digit. There is always an unused nonzero digit: only five mixed labels can occupy six available digits.

Move a redundant label to a nonempty old cylinder at an unused nonzero digit. Its old deletion was already supplied by the pure7 exclusion or other labels, so no old deletion is lost. At least one new actual low point is deleted. The original modulus label is unchanged. Repeating strictly increases an integer deletion count in a finite space, so the process terminates. At termination, every label has a private deleted point at its digit. The final carrier is a subset of the original carrier.

For a nonempty label subset J⊆{0,…,4}, enumerate its old cylinder choices. Retain a union U only when every chosen cylinder has a point outside the union of the other cylinders in that block. Partition all five labels into nonempty blocks and collect the resulting sorted union multisets. This enumerates exactly the carriers admitting an all-essential labelled realization. Taking the same old-coordinate quotient yields107695 essential carrier orbits. Any support theorem proved on those carriers applies to all170569 original carrier orbits by the preceding subset transfer. This is a sufficient reduction even when a carrier admits several different labelled realizations.

<a id="exact-five-label-resource-dp"></a>
#### Exact five-label resource DP

The essential reduction is not minimal: a carrier whose five labels are all essential can still contain another realizable carrier obtained by reallocating the coarse and fine original labels. The following DP decides this exactly.

For each nonempty label subset J, let V_J be all old masks obtainable as a union of one cylinder for each label in J. For a required nonempty target mask B define

    c_J(B)=max {|U|: U∈V_J and B⊆U},

with value infeasible if no such union exists. The program retains an actual union and original cylinder assignment attaining every finite maximum. Empty old cylinders need not be added when maximizing c_J: replacing one with a nonempty cylinder only increases its union and remains a valid choice of that original label.

Let B_1,…,B_k be the nonempty target digit masks, k≤5. Assign each B_i a nonempty label subset J_i, disjoint from all the others. The labels in J_i will occupy that target digit. If label j is left over, place it at a fresh unused nonzero digit and choose an old cylinder of maximum size m_j. The total number of occupied digits is at most

    k + (5−Σ_i |J_i|) ≤ 5 < 6.

Thus this completion is always physically realizable. It also handles labels that were originally absent, had empty old masks, or occupied digit0: their original deletion contributes nothing, and the maximization may place them on a fresh surviving digit.

The exact largest deletion count among all realizable carriers whose support lies inside Ω_B, up to one common7digit permutation, is

    D_max(B)=max_(disjoint nonempty J_i)
              [Σ_i c_(J_i)(B_i)+Σ_(j left over)m_j].

For the upper bound, align any containing-deletion carrier with the k target digits. The original labels occupying those digits form the disjoint nonempty J_i. Its deletion at digit i is at most c_(J_i)(B_i). All remaining digit unions together have cardinality at most the sum of the individual maxima m_j of their labels. For attainment, take a maximizing union for each J_i and place each remaining label at its own unused digit. CRT realizes every chosen old cylinder/digit pair with its original modulus7d. This proves equality, rather than merely an upper bound.

The recurrence uses a remaining-label mask R of size32:

    M((),R)=Σ_(j∈R)m_j,
    M((B_1,…,B_k),R)=max_(nonempty J⊆R)
                        [c_J(B_1)+M((B_2,…,B_k),R\J)].

A branch with fewer available labels than required nonempty digits is infeasible. Infeasible c_J terms are omitted. The result is D_max(B)=M((B_1,…,B_k),{0,…,4}). Replacing all c_J realizations by their maximizing union is valid because distinct digits have disjoint physical point sets and the rest of the recurrence depends only on the unused original labels.

Write D(B)=Σ_i|B_i|. The target carrier is feasible in its own maximization, so D_max(B)≥D(B). It is inclusion-minimal exactly when equality holds. If D_max(B)>D(B), a maximizing realization has a strictly smaller support contained in Ω_B. Every maximizing realization is itself inclusion-minimal: a still smaller realizable support would delete more than D_max(B), a contradiction.

Here the initial definition of minimality fixes S pointwise and allows one common7digit permutation. The resulting feasible carrier class is closed under the allowed old3/5 maps. Therefore allowing an old map in the domination relation gives the same minimality criterion: its image is already another feasible carrier in the DP domain. Minimality is consequently well defined on the combined old-map/global7digit orbits. No independent digit relabelling at separate old points is used.

<a id="complete-finite-counts"></a>
#### Complete finite counts

| Canonical old45 shape | All carrier orbits | Essential orbits | Inclusion-minimal orbits |
|---|---:|---:|---:|
| root1, same root / other column |31833|20144|9793|
| root1, other root / same column |15451|9593|5495|
| root1, other root / other column |40281|25613|15233|
| root2, same root / other column |36152|22987|12362|
| root2, other root / same column |12692|7834|3529|
| root2, other root / other column |34160|21524|10554|
| Total |170569|107695|56966|

The essential family has640932 states before old-coordinate quotienting. The resource DP finds strict support dominators for50729 of its107695 orbits. Since every original carrier first contains an essential one, these56966 minimal orbits are a complete sufficient domain for any universally transferable supported-law theorem at these six old geometries. Their numerical target remains to be proved casewise or by further uniform arguments.

For an explicit example in the root2, other-root/same-column shape, the carrier with deletion masks(1,16,16,1160,22866) has83 points and contains a79point carrier with masks(16,16,1160,5155,22866), after a common digit permutation. Its maximizing construction allocates each of the original cofactors3,5,9,15,45 exactly once. The certificate records corresponding actual cylinder masks by digit; their union and label-disjointness are checked.

<a id="the-pg1-law-covers232-carrier-orbits"></a>
#### The PG1 law covers232 carrier orbits

The canonical PG1 certificate gives the75point carrier in the root2, other-root/other-column shape and the exact bound

    Γ ≤ 105976769844774468812903/2920804491373837228125 < 3849/106.

Its nonempty deletion masks are(2320,32768,33808,38032,44378), with bit order given by that canonical old45 geometry. All75 supplied point weights are strictly positive. The checker reads the existing PG1 certificate, reconstructs its actual support, verifies the original low modulus set and raw integer weights, pins this inherited bound and target, and pins the canonical JSON representation of the complete published source certificate by SHA-256. The numerical PG1 proof is reused from the existing canonical `verify_point_geometry.py`; this dominance entry does not recompute its two moment oracles.

Considering the12 old-coordinate images and testing the exact digit-mask inclusion matching covers1648 carrier states, or232 combined carrier orbits. The PG1 carrier is itself inclusion-minimal, so exactly one of the56966 minimal orbits is covered by this inherited certificate. The other covered carriers are larger supports to which the quantifier-preserving transfer applies. This does not assert numerical bounds for the remaining minimal orbits.

<a id="reproduction-and-verification-boundary-1"></a>
#### Reproduction and verification boundary

Keep this entry point separate from the existing classifier and its certificate. With its files beside the canonical geometry classifier, canonical old-profile certificate, canonical PG1 certificate, and the mod3-conditioned certificate below, run

```sh
python3 -I -O verify_carrier_dominance.py
```

An external canonical directory can be selected with `--canonical-directory`; `--check` selects the small result certificate. The entry uses the canonical geometry module through an explicit adjacent path, which works under isolated Python. It imports only standard-library modules, uses unbounded integers and explicit guards, validates all consumed integer inputs, and pins the geometric domain and inherited PG1 bound.

The checker reconstructs all essential carrier states, verifies root-group orbit closure and accounting, recomputes the six exact resource DPs, verifies label-disjoint constructive witnesses, and hashes the reconstructed state/orbit sets without retaining large lists. For one minimal and one dominated target in each shape, it independently scans every essential carrier using only the injection matcher and confirms the DP's maximum deletion count. It also recomputes all232 PG1-covered orbits. The small certificate retains counts, hashes, and explicit witnesses. These are finite arithmetic results and ordinary support/all-height transport proofs; no new Lean admission or resolution of unrestricted Erdős #7 is claimed.

<a id="retaining-the-original-mod3-test-in-higher-deletion-energy"></a>
### Retaining the original mod3 test in higher-deletion energy

The actual probability in PG1 admits the stronger bound Γ≤69/2=34.5.
A second actual75point carrier admits Γ≤35, below3849/106, at arbitrary
finite original3/5/7 heights. The new estimate keeps the original mod3
test class in both the square bound and the energy removed by higher
forbidden classes. The signed deletion identity is the same one used
in(SD5); its present application retains a nonuniform actual315law and
the three-coordinate grouped deletion bound(SH15).

<a id="same-original-test-class-on-both-sides"></a>
#### Same original test class on both sides

Let μ be a probability on an actual low315survivor carrier Ω, let λ be
its independent uniform lift in all additional3/5/7digits, and let F
avoid every actual higher forbidden class. Write q_actual=λ(F).
All original exponent labels remain distinct. Let R_E(σ) be the
grouped deletion bound in(PG1), now evaluated on any nonnegative finite
low measure σ, without renormalizing it. The proof of(SH15) gives

    ∫_(Fᶜ) h(x) dλ ≤ R_E(h μ)                         (M3-1)

for every nonnegative function h of the low point. Indeed, the proof
is a pointwise conditional union bound followed by nonnegative sums
and maxima of linear integrals. It does not require that h μ have
mass one. Its cylinder caps and all three grouped contributions use
precisely h μ. Independently, R_E(μ)<1 ensures q_actual>0.

Fix a complete original test family L and let i be its residue for
the original modulus3. Then

    b_i=1+1_(x≡i mod3),       L≥b_i.

For K≥4, put h_i=K−b_i²=K−1−3·1_(x≡i mod3)≥0. If U_i bounds E_λL²
for every complete test whose original mod3 class is i, the exact
deletion identity and(M3-1) give

    q_actual(E_(λ|F)L²−K)
      = E_λL²−K + ∫_(Fᶜ)(K−L²)dλ
      ≤ U_i−K+R_E(h_i μ).                              (M3-2)

Consequently the finite criterion

    R_E(μ)<1,    U_i+R_E((K−1−3·1_(x≡i mod3))μ)≤K
                 for every original test root i       (M3-3)

implies Γ_(λ|F)≤K. The higher forbidden classes are arbitrary and
are not identified with the test classes. In particular their
maximizers in R_E are not constrained to the test root i.

<a id="why-the-all-height-comparison-preserves-this-label"></a>
#### Why the all-height comparison preserves this label

The saturated thresholds are h=(2,1,1). Projection d=3 has ternary
exponent1<2 and the other two exponents0<1, so it comes from exactly
one original label, modulus3, and w_3(Z)=1. Thus the saturated-prefix
comparison and the convex-hull maximization can keep this cylinder
fixed. For each fixed i the valid square comparison is

    E_λ L² ≤ E_Z F_i(Z),
    F_i(z)=max_(low layouts with C_3=i mod3)
                 E_μ(Σ_(d|315)w_d(z)1_Cd)².           (M3-4)

Other low cylinders may maximize separately at each z. The same i
is retained throughout the expectation and in(M3-2). One cannot
replace it by a z-dependent test root in the deletion term.

The two finite relaxations from(PG1) apply with only their non-seven
low layout A constrained to mod3 root i. The cofactor3 in B refers
to the original modulus21 and remains unrestricted. Denote their
pointwise minimum at the fixed law by H_i(z). No convexity of this
minimum is asserted. The genuine-layout increment gives

    F_i(z)≤F_i(0)+P(z)−P(0),

with the same complete nonnegative pair-cap polynomial P as in(PG1).
Therefore for B=[0,8]×[0,5]×[0,4], β=Pr(Z∈B), the exact full-tail bound is

    U_i=(1−β)H_i(0)+Σ_(z∈B)Pr(Z=z)H_i(z)
                         +Σ_d η_out(d)m_d.             (M3-5)

The coefficients η_out include all omitted geometric depths. Finite
physical heights, including heights appearing only in later-prime
moduli, are bounded by these infinite geometric moments. Both
specified carriers omit root0 at3; changing a test from that empty
root to either nonempty root increases L pointwise, even after
conditioning. It is therefore sufficient to check i=1,2.

For probability optimization, fix K and choose one of the two square
relaxations at each root and depth before optimizing μ. Each chosen
relaxation, each cylinder cap, and R_E(h_i μ) is a maximum of linear
functions of μ, with nonnegative combination coefficients. Thus
(M3-3) gives a finite convex feasibility problem on the actual point
weights. The pointwise minimum may still be used to evaluate a fixed
law, as in the certificate; it is not used as a convex outer oracle.

More generally, if g is increasing, V_i≥E_λg(L) and C≥g(2), the same
proof replaces h_i by

    C−g(b_i)=(C−g(1))−(g(2)−g(1))1_(x≡i mod3).

If g is also convex and has finite geometric expectation, the
fixed-i saturated comparison supplies V_i by the same convex-hull
argument. This general statement does not supply new numerical
hinge bounds by itself.

<a id="two-exact-actual-law-certificates"></a>
#### Two exact actual-law certificates

The first case uses the unchanged PG1 family and its75 integer
weights of total1000000007. The second family is

```
(3,0),(9,4),(5,0),(15,11),(45,1),(7,0),
(21,5),(35,4),(63,50),(105,59),(315,44).
```

Its actual complement has75points. The adjacent certificate lists
every point and nonnegative integer weight, with total999999994.
For each case the law λ|F is supported on this actual low carrier
and avoids every higher forbidden class, at every finite3/5/7height.

| Low carrier | Same-law unit-loss bound | New K | Independent lower bound for λ(F) |
|---|---:|---:|---:|
| PG1 |36.2834178589…|69/2|25428074957/48000000336|
| Second75point family above |36.7917311533…|35|25170030757/47999999712|

The minimum margins K−U_i−R_E(h_i μ) over both roots are respectively

    2637433975198231346789/55135363885947544500000 >0,
    697199872596794233/91892271948646365000 >0.

Thus both improve3849/106. Each comparison holds on one unchanged
probability: there is no root-dependent choice of μ or conditioning
event. The existing support-inclusion transport applies because
the result holds for every admissible higher forbidden family.

The second carrier lies in `root2_other_same_column`. Its canonical
nonempty deletion masks are(1,1057,1160,5155,42669), and it is another
inclusion-minimal orbit. Its18 old-coordinate images transfer the
Γ≤35 bound to2291 carrier states and152 carrier orbits. The source's
original-label realization is reconstructed from the eleven classes
above; support containment uses the same injective mask matcher as
the preceding dominance result.

These152 orbits are disjoint from the232 PG1 orbits, giving3939states
and384orbits with Γ≤35, including two of the56966minimal orbits.
An exact6×6 old-support embedding table has zero off-diagonal
entries. To verify completeness, the old projection has two ternary
roots with respectively two and three nonempty mod9 children, and
uses all four nonzero5columns. A cylinder-preserving embedding must
preserve these root types; its restrictions are among2!·3!·4!=288
row/column maps. Their exhaustive checks show that the two source
shapes cannot overlap or transfer to a third canonical old shape.
The revised dominance entry recomputes this table and both covered
sets, pins the complete mod3 source certificate, and retains its
original PG1 fields unchanged. It inherits the two numerical
endpoints from the new moment verifier; it does not reprove them.
The other56964minimal orbits and unrestricted-prime continuation
remain unresolved by these two certificates.

`verify_mod3_conditioned_geometry.py` reconstructs both actual
families and weights, both fixed-root square bounds at all270depths,
the independent survival bounds, the four nonnormalized weighted
deletion bounds, and the full geometric remainders. It uses the
adjacent geometry evaluator with optional original-root restriction;
the original PG1 verifier retains its unrestricted default behavior.
Run the new entry with `python3 -I -O`. Every final comparison is
integer or rational and all NumPy arithmetic has explicit signed64
range guards. These certificates accompany the ordinary all-height
proof above; they are not Lean kernel proofs of the new endpoints.
