# An all-height convex-source transport and the joint fibre data it needs

This is ordinary mathematics and exact finite verification, not Lean.
The new source below is constructed from the same pruned315 law used by
the recent shallow and old23 results. It releases all3/5/7 heights for the
THREE-PRIME CORE. It does not yet join that source to11,...,23 or to an
unbounded prime tail. Noncoverage for arbitrary three-prime heights was
already known here; [Chapter14](../../../problem-details/14-a-shared-parameter-improvement-for-arbitrary-three-prime-heights.md) even supplies a better square-moment bound.
The useful interface is the full increasing-convex transport, together
with explicit actual examples showing what a height boundary must retain.

## 1. Conditional full-convex height lifting

Let Q0=prod_(p in P)p^H_p, H_p>=1, and let mu avoid all actual originals
whose numerical modulus divides Q0. For every complete divisor query L
on Q0, assume the SAME law satisfies

    L under mu <=icx Y,

where Y>=1 is one auxiliary comparison variable. Query phases are arbitrary
and are independent choices of labels, not independently realized sources.
For every nonempty S subset P, also retain a bound

    E_mu F <= beta_S

for each partial divisor query F using only cofactors with vp(d)=H_p for
all p in S. Put k_p=H_p+1. Define independent auxiliary variables N_p by

    P(N_p>=t)=p^(-t), t=1,2,...,
    M=prod_(p in P)(1+N_p/k_p),
    lambda=sum_(nonempty S) beta_S prod_(p in S)1/(p-1).

For a fixed finite target carrier Q refining Q0, all geometric sums may
instead be truncated at the actual extra heights. If lambda<1, the uniform
fibre extension nu of mu to Q retains actual survivor mass rho>=1-lambda.
On this ONE actual survivor law mu'=nu restricted to survivors /rho,

    every complete fine query <=icx UpperTail_(1-lambda)(Y M).       (HICX)

UpperTail_delta means the distribution obtained by retaining the highest
delta probability mass, splitting a threshold atom fractionally if needed.
It is a comparison law, not a separately chosen actual survivor source.
This is an ordinary combination of the [projection mechanism](../../../problem-details/09-quantitative-extension-of-the-old-prime-powers.md),
convex concentration, and the [conditional upper-tail lemma](736-a-common-conditioned-convex-law-sharpens-the-same-source.md).
It does not assert lambda<1 for every arbitrary prime set.

### Raw query transport

First lift only p from height H to H+n. At extra height t>=1, the reduced
query block F_t contains one cylinder for each of its permitted numerical
cofactors, all saturated at p^H. Project each of these classes to its k=H+1
ancestors obtained by lowering the p-exponent. No numerical labels collide:
the outside cofactor identifies the original slot, and the p-exponent
identifies its projection. Completion to a full old query L_t gives

    k F_t <= L_t.

The complete fine query has its ordinary old block A plus these higher
blocks. Conditional on a coarse point, each extra-t event has probability
p^(-t) in the uniform fibre. The convex-increment concentration inequality
from the independent old23 review bounds it by nested cap events:

    E_fibre phi(Q) <= E_N phi(A+sum_(t<=min(N,n)) F_t)
                  <= E_N phi(A+(1/k)sum_(t<=min(N,n)) L_t).

For each FIXED N=j<=n, use weighted Jensen, with total weight1+j/k:

    phi(A+(1/k)sum_(t=1)^j L_t)
       <= [phi((1+j/k)A)+(1/k)sum_(t=1)^j phi((1+j/k)L_t)]
             /(1+j/k).

Each L_t can be a different query. Apply the uniform old comparison to
each term before averaging N. This yields raw fine-query comparison by
Y(1+min(N,n)/k), and therefore by Y(1+N/k). Positive-law comparison makes
this last pointwise increase legitimate. Repeating the argument for the
other primes composes the multiplicative factors; their auxiliary
independence encodes composition of these fixed operators only.

This keeps the essential factor1/(H+1) from distinct ancestor projections.
Using1+N without this factor discards real numerical-label information.
No supremum over query phases has been moved outside an auxiliary average.

### Actual original deletion and conditioning

Group each actual new modulus by its nonzero excess vector t and S=supp(t).
For fixed t, its reduction modulo Q0 identifies the numerical modulus
uniquely. Its total conditional fibre deletion is bounded by

    (prod_(p in S)p^(-t_p)) F_t(x).

The partial-query mean bounds therefore give union deletion at most lambda.
This includes actual pure classes and all mixed originals; none are replaced
by independently optimized phases. Restrict this single extended law once.
For every increasing convex phi and scalar a,

    E_mu' phi(Q) <= a + E_nu(phi(Q)-a)_+/rho
                 <= a + E(phi(YM)-a)_+/(1-lambda).

Choosing a at the appropriate upper-tail quantile proves(HICX), exactly as
in Report736. Finite cases give ordinary finite laws; infinite-height
majorants may have unbounded support. The geometric N variables have every
polynomial moment, so all current piecewise-affine penalties are integrable.

If mu <= D Haar_Q0, uniform fibre extension preserves D and restriction
gives mu' <= D/(1-lambda) Haar_Q. Thus an actual-source density bound is
transported alongside its query comparison. The source's coarse marginal
is reweighted by ACTUAL conditional fibre survival; preservation of the old
marginal is neither required nor generally possible.

## 2. The partial interface is substantially sharper than projecting a full load

For the six pruned315 shapes, the12-point comparison laws from the [old23 source](741-an-actual-full-height23-source-supports-six-fresh-primes.md) provide Y. Here we compute beta_S directly, rather than
bounding every partial mean by a scalar consequence of Y's total moments.

Let S45 be the shape's old45 survivors, n=|S45|, and let Nmin be the inherited
minimum pruned315 survivor count. Write D0={3,5,9,15,45}. For S not containing7,
let A and B be the zero-seven and positive-seven blocks of a partial saturated
query. They are queries on these45 numerical slots:

    S={3}:   {9,45},
    S={5}:   {5,15,45},
    S={3,5}: {45}.

Let m_S be the maximum of sum_x B(x). The deletion-sensitive sufficient
inequality for a mean bound g is

    6 sum_x A(x)+m_S
      +sum_(d in D0) max_(d-cylinder C) sum_(x in S45 intersect C)(g-A(x))_+
      <=6ng.

All our resulting g lie in[0,1]. Since A is integer valued, only its zero
set contributes to the positive part. Consequently each effective A gives
an exact sufficient ratio

    [6 sum A + m_S]
      /[6n-sum_d max_C |C intersect {A=0}|].

Taking the largest such ratio supplies beta_S. The checker also verifies
the original positive-part inequality directly at this rational cap.
If7 belongs to S, A=0 and the bound is m_S/Nmin. These queries use all old45
slots including the unit when S={7}; the other cases retain only the listed
saturated slots. This accounts for every relevant partial query on315.

| Shape | beta3 | beta5 | beta7 | beta35 | beta37 | beta57 | beta357 |
|---|---:|---:|---:|---:|---:|---:|---:|
| root1_same_other_column |35/83|7/9|6/11|1/11|5/77|9/77|1/77|
| root1_other_same_column |5/12|63/82|41/78|7/78|5/78|3/26|1/78|
| root1_other_other_column |5/12|63/82|41/78|7/78|5/78|3/26|1/78|
| root2_same_other_column |35/76|21/26|37/75|7/75|1/15|3/25|1/75|
| root2_other_same_column |35/76|21/26|19/37|7/74|5/74|9/74|1/74|
| root2_other_other_column |35/76|21/26|19/37|7/74|5/74|9/74|1/74|

All these bounds concern the same actual pruned315 source for that shape.
They do not require their extremizing query layouts to be simultaneously
attainable. They are uniform upper bounds, so they may be added in a union
estimate for the actual fixed family.

With P={3,5,7}, the resulting worst deletion majorant is

    lambda <= 474271/877344 <1,
    1-lambda >= 403073/877344.

Combining each shape's own Nmin/315 density factor with its own retention
bound gives actual full357 Haar survivor density at least

    403073/3734640.

The all-height comparison is

    UpperTail_(1-lambda_i)
      [Y_i (1+N3/3)(1+N5/2)(1+N7/2)].

This is an explicit infinite-support comparator with geometrically defined
weights. All finite actual heights are included. No claim of sharpness or
novel three-prime noncoverage is made.

## 3. Why the old marginal and individual cylinder masses are insufficient

Here are actual distinct-modulus families, not free symbolic fields.
Use the shared old originals

    (3,0),(9,4),(5,0),(15,1),(45,37),(7,0),
    (21,0),(35,0),(63,0),(105,0),(315,0).

The point2mod315 survives all of them. The last five classes are redundant
with the pure7 exclusion, but make the old315 inventory complete and preserve
distinct numerical labels. Consider its higher-digit fibre.

### One extra3 digit

Add the same numerical moduli27,135,189 to two families, with phases

    partition family:  (2,47,65),
    coincident family: (2,2,2).

Each new phase reduces to2 modulo its gcd with315, in both families. Each
individual new class removes exactly one third of the coarse fibre. The
three lifts of2mod315 modulo945 are2,317,632. The partition phases remove
one different lift each, leaving none. The coincident phases all remove
lift2 and leave the other two.

The full carrier945 still has272 and282 survivors respectively. Thus this
is an obstruction to the summary and to fixed-marginal lifting, not an
odd covering example. The first family admits no survivor law whose coarse
marginal assigns positive mass to2mod315.

### One extra5 digit

Similarly use moduli25,75,175,225,525. The partition phases are

    (2,17,107,47,212),

and the coincident phases are all2. All projected phases agree, and each
individual class has conditional fibre mass1/5. The partition kills all
five descendants of2mod315, while the coincident family leaves four. On the
whole carrier1575 the survivor counts are455 and486, respectively.

### Arbitrarily many extra7 digits

The six available45 cofactors1,3,5,9,15,45 give six distinct numerical
moduli at each new7 height. At every stage use them to delete six children
of the sole remaining branch of2mod315. After h extra heights, the conditional
survival is exactly7^(-h). Every phase still reduces to2 on its old315
cofactor. In a second family, set every new phase to2. Its higher cylinders
all lie in one first child, and conditional survival stays6/7.

For corresponding numerical labels, the individual conditional masses
are7^(-j) at extra height j in both families, and their old projected phases
are identical. The difference is the joint higher-prefix arrangement.
The point8 is an explicit global survivor of both families for every h.
The checker verifies h=1,...,5; the nested-branch induction proves the
formula for every finite h.

Therefore even when every finite7 fibre remains nonempty, no positive
height-independent lower bound on each fibre is possible. If the old
marginal at this fibre is forced to remain mu(2)>0, the density needed for
a survivor lift is at least

    315*mu(2)*7^h,

which is unbounded. A uniform Haar-domination constant therefore also
requires source reweighting or additional joint prefix information.

## 4. The remaining bridge is quantitative and joint

The conditional transport(HICX) is composable, but it does not prove that
its retention or its gate budget stays favorable indefinitely. For reference,
its unconditioned moment multipliers at3/5/7 are

    E M = 91/64,
    E M^2 = 6149/2592.

Using only the fixed threshold1 conditioning estimate gives square bounds
between62.74 and66.21 on the six shapes. Chapter14's existing actual uniform
full357 source has the better bound3849/106, about36.31. Thus the coarse
projection/Jensen transport is not a quantitative improvement in that metric.
The upper-tail comparator may sharpen the displayed threshold1 estimate;
no such improvement is claimed here without a separate computation.

The unresolved step is to obtain a full-convex or directly weighted-penalty
bound from a sufficiently good ACTUAL full357 source, retaining its common
cell and deletion data, and then control its simultaneous coupling to the
old11,...,23 originals. Replacing that problem by the separate best source
for each hinge or each outer modulus is invalid. Nor does the positive
three-prime retention bound guarantee the much smaller six-direction budget.

A precise sufficient next target is: for the actual full357 survivor source,
construct one common convex comparison or direct aggregate penalty estimate
that, after adjoining11,...,23 and conditioning all their original mixed
classes, remains below the19100 six-direction gate. The useful raw boundary
must include the saturated partial-query profile and enough joint prefix
information to distinguish the actual families of section3. The full field
transport(HICX) supplies an admissible propagation rule; positivity of the
needed joint budget remains unproved.

## 5. An explicit common-source test for joining the two height bridges

The [outside-prime source](742-a-common-source-for-subsets-of-five-old-prime-heights.md)
and the full357 source above are different restrictions of a common raw
law. Their separate positivity does not imply that their intersection
retains positive mass. Let J denote the unrestricted outside old axes,
theta_p=1/(p-2) on J and1/(p-1) otherwise, and let delta_(i,J) be the
outside source's retained fraction. If the high-core originals may also
bear every outside cofactor, the separately estimated additional debit is

    lambda_i product_(p=11,13,17,19,23)(1+theta_p).

The resulting union lower bound is

    delta_(i,J)-lambda_i product_p(1+theta_p).

Exact arithmetic makes this number negative in all32 subsets and six
shapes. This establishes failure of this particular sufficient estimate;
it proves neither an empty actual intersection nor nonexistence of a
better source. The additional exclusions and outside restriction must
be compared on their one actual common law.

A sufficient next interface is seven CONDITIONAL saturated partial-query
caps beta'_S on the actual outside survivor source, with all outside
cofactors retained, such that

    sum_(nonempty S subset{3,5,7}) beta'_S product_(p in S)1/(p-1)<1.

The conditional transport of section1 would then preserve a positive
actual source, though its later fresh-direction fee would still need a
bound. The scalar complete-query comparator alone does not imply this
inequality. For example, a comparator supported at least8 allows the
formal constant full load6 and saturated3 load2 with3F<=L; their single
ternary debit is already1. This is a relaxation witness, not an actual
CRT-family construction. Actual partial-query or joint-deletion geometry
must add a constraint.

## Exact consumer and scope

The [consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_core_height_joint_bridge.py)
and [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_core_height_joint_bridge.json)
check all six partial profiles, paired retention and density, the two
actual-family comparisons and both versions of the first five7 ladders.
They also check all192 separated intersection estimates on matched
shapes. The program pins the existing head and outside-source data;
it does not rerun their full source proofs.

A separate bitset implementation checks22974 numerical phase tuples,
including null and duplicate effective cylinders, and reproduces every
partial cap and all192 common-intersection arithmetic values.

The ordinary projection, convex-concentration and conditioning proof
supplies the all-height and all-query quantifiers. Finite checks do not
replace those deductions. The saturated-face interface is reusable;
noncoverage of the three-prime core was already established in Chapter14.
No new Lean verification or unrestricted covering conclusion is claimed.

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_core_height_joint_bridge.py
```
