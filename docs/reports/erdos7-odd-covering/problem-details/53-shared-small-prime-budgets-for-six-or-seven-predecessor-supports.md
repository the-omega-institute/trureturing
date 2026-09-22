[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Shared small-prime budgets for six or seven predecessor supports

Let a finite congruence family have pairwise distinct odd original numerical
moduli greater than one. Assign each original mixed class to its numerically
largest prime and count its distinct exact nonempty predecessor supports.
The following two sufficient conditions give noncoverage:

- At most six predecessor supports per stage, and at most six distinct full
  mixed supports containing 3.
- At most seven predecessor supports per stage, and at most seven distinct
  full mixed supports containing 3 and at most seven containing 5.

Each branch allows arbitrary original exponent heights, residues, support
ranks and total prime count, and supplies one complete joint law and a
full Haar density bound. In particular, the second branch gives noncoverage
when every prime belongs to at most seven distinct mixed supports.
The six-support branch permits unbounded incidence at 5; the seven-support
branch permits seven predecessor supports. Their hypotheses are separate.

The normalized kernels and full-exponent selected-cylinder interface are
reused from [Chapter 07](07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md),
[Chapter 08](08-arbitrary-head-transfer-by-the-joint-load-invariant.md), and
[Chapter 52](52-two-or-four-exact-predecessor-supports.md).
The unmodified fifth-coordinate first-moment fee also occurs in
[Chapter 41](41-natural-four-predecessor-orders-are-noncovering.md).
The additional deductions allocate the shared incidence budgets across
all prime stages under the same actual probability law. These are ordinary
proofs; unrestricted Erdős #7 remains open, and no new Lean or
historical-priority claim is made.

## Branch A: six supports with one shared ternary budget

### Statement

Let a finite family of congruence classes have pairwise distinct odd numerical
moduli greater than one. Retain every original exponent vector and residue.
Assign each mixed original to its numerically largest prime p, and let E_p
be the family of its distinct exact nonempty predecessor prime supports.
Assume |E_p|<=6 at every p, and that at most six distinct full mixed supports
contain 3. Then the family does not cover the integers.

In particular this applies when each prime belongs to at most six distinct
mixed supports. The statement itself permits unbounded incidence at other
primes and unbounded support rank, exponent height and total prime count.

There is one normalized sequential law P_* on the original full CRT space,
zero on pure exclusions, such that the complete survivor set U satisfies

    P_*(U) > 314761/16465680.

Its full Haar density is bounded by

    D=product_p kappa_p (p-1)/(p-2),

where kappa3=kappa5=1, kappa7=5/3 for an active assigned group, and kappa_p=2
for active assigned groups p>=11; unassigned coordinates have kappa=1.
Consequently H(U)>314761/(16465680 D), and conditioning once on U has
Haar density at most (16465680/314761) D.

### 1. Actual common probability and original labels

Use exactly the normalized sequential law of the four-predecessor-support
construction. At each prime remove its actual original pure-power classes,
and let nu_p be uniform on its actual survivors. Numerical distinctness
bounds their excluded Haar mass by sum_(j>=1)p^-j=1/(p-1), so

    nu_p <= c_p H_p,  c_p=(p-1)/(p-2).

Sample nu3 and nu5 without further distortion. Mixed classes assigned to5
have support {3,5}; their full exponent vectors are all distinct, and the
true independent nu3 times nu5 source bounds their union by 1/3. If there
is no such support, the fee is zero. Write f in {0,1} for its presence.
Every later normalized kernel preserves this complete joint marginal.

At7 use delta7=2/5; at p>=11 use delta_p=1/2. For the actual active union
F_p(x) on the new coordinate, with alpha=nu_p(F_p(x)), use density zero on
F and 1/(1-alpha) on its complement if alpha<=delta. Otherwise use
(alpha-delta)/(alpha(1-delta)) on F and 1/(1-delta) off F. This includes
alpha=1, is normalized on each actual earlier tuple, and is bounded by
kappa=1/(1-delta). Its actual assigned bad mass is

    (alpha-delta)_+/(1-delta) <= alpha^2/(4delta(1-delta)).

Every actual earlier full joint probability is preserved. Selected-cylinder
bounds follow by conditioning backwards along this same law, using one
kappa_q c_q q^-h_q for every selected coordinate, without independence of
the already distorted coordinates.

Expand the squared actual original-label load before completing exponent
sums. Two originals sharing q constrain one cylinder of exponent max(i,j),
or have incompatible residues and zero intersection. Thus shared positive
exponents contribute sum_(i,j>=1)q^-max(i,j)=(q+1)/(q-1)^2; a coordinate
present once contributes sum_(i>=1)q^-i=1/(q-1). The current coordinate
contributes two independent sums. Full numerical distinctness makes the
original full exponent vectors injective within each exact support. We get

    E alpha_p^2 <= G(E_p)/(p-2)^2,
    G(E)=sum_(S,T in E) W(S,T),
    W(S,T)=product_(q in S intersect T)d_q
           product_(q in S symmetric-difference T)t_q,
    d_q=kappa_q(q+1)/((q-1)(q-2)), t_q=kappa_q/(q-2).

This is the existing exact-support second-moment interface. It retains
original residues, labels, pure-survivor source and the full exponent sums.

### 2. Six largest nonternary diagonal monomials

Nominal factors dominating the actual stages are

    d3=2, t3=1;
    d5=1/2, t5=1/3;
    d7=4/9, t7=1/3;
    d_q=2(q+1)/((q-1)(q-2)), t_q=2/(q-2) for q>=11.

All nonternary d factors are at most1/2 and all t factors at most1/3.
Both decrease beyond11. For distinct nonempty nonternary supports R,T,

    W(R,T)<=1/6.

If they intersect, use one shared d<=1/2 and one differing t<=1/3; all
other factors are at most1. If disjoint, use one t from each, giving1/9.
Also W(empty,R)<=1/3 and W(R,R)<=1/2 for nonempty R.

The six largest distinct nonempty diagonal monomials product_(q in R)d_q
are, in decreasing order,

    1/2, 4/9, 4/15, 2/9, 7/33, 3/20.

They correspond to {5},{7},{11},{5,7},{13},{17}. Every omitted singleton
is at most d19=20/153<3/20. Every omitted pair is at most d5*d11=2/15<3/20.
Every rank at least three monomial is at most d5*d7*d11=8/135<3/20.
This proves the assertion on arbitrarily many primes and arbitrary ranks.
Let S_j be the sum of the first j numbers, with S_0=0. Thus j distinct
nonempty nonternary supports have total diagonal at most S_j, j<=6.
Missing primes or smaller actual kappas only reduce these quantities.

### 3. Stage Gram bound remembers how often3 is used

At a stage p>=11 let a be the number of predecessor supports containing3,
b the number not containing3, and e in {0,1} indicate whether {3} occurs.
Then a+b<=6, e<=a. Delete3 from the a supports; the images remain distinct,
and exactly e of them are empty. The b other supports are nonempty and
distinct. Split the ordered Gram sum into these two groups.

For the ternary group, its within-group bound A is

    e=0: A=2 S_a + a(a-1)/3;
    e=1: A=2+2 S_(a-1)+(a-1)(a+2)/3.

Indeed the common3 multiplies every term by2. In the second case the
empty image has diagonal1, its 2(a-1) ordered cross terms are at most1/3,
and remaining distinct nonempty cross terms are at most1/6.
The other group's bound is

    B=S_b+b(b-1)/6.

Between the groups, at most min(a-e,b) image pairs can agree, because
each image family is internally distinct. Matching nonempty images have
weight at most1/2 instead of the generic1/6. The e*b pairs involving an
empty image have weight at most1/3. The factor for differing membership
of3 is t3=1. Counting both orders gives

    2C <= ab/3 + 2 min(a-e,b)/3 + eb/3.

Therefore G<=A+B+2C. This expression is nondecreasing in b, so replace
b by6-a and maximize over e. For a=0 only e=0 is allowed. The resulting
rational upper bounds G_a, for a=0,...,6, are

    299/44, 3403/330, 373/30, 443/30,
    491/30, 521/30, 3073/165.

Write Delta_a=G_a-G_0. They are nonnegative, with Delta_0=0. These are
uniform upper bounds, not claims that their separate extremizers can all
be attained by a common arithmetic configuration.

### 4. Allocate the finite ternary budget once

The full supports containing3 are uniquely assigned to their maximum
prime. Thus f+a7+sum_(p>=11)a_p<=6. Here a7 counts the chosen supports
containing3 at stage7. Its only possible predecessor supports are
{3},{5},{3,5}. For each of their eight subfamilies J, let g(J) be its
exact nominal Gram computed with d3=2,d5=1/2,t3=1,t5=1/3.
Stage7 has fee at most g(J)/24. The full three-support family has
 g=13/2, fee13/48, and a7=2.

The existing infinite-tail estimate gives

    sum_(p>=13 prime)(p-2)^-2 <1/35.

It follows by retaining all42 primes13 through211, and enclosing the
remaining primes by the two progressions p-2=213+6j or215+6j. Convex
centered-cell integration bounds their tails by1/1260 and1/1272.
The finite rational sum plus these integrals is less than1/35.

The total baseline fee at stages p>=11 is strictly less than

    G_0(1/81+1/35)=8671/31185.

The remaining fee is bounded by sum Delta_(a_p)/(p-2)^2. Put
B=6-f-a7. At most B of these stages have a_p>0. Order those active primes
p_1<...<p_m. Their ith prime is at least the ith prime of11,13,17,19,23,29.
Since each Delta is nonnegative, replacing their denominators by these
earlier primes can only increase the sum. This is a numerical relaxation;
it does not assert that moving the underlying support to an earlier prime
is a legal operation on the congruence family.

Consequently the sharp value of this relaxed budget is the finite maximum

    V_B=max{ sum_(i=1)^B Delta_(u_i)/(r_i-2)^2 :
             u_i are nonnegative integers, sum u_i<=B },
    r=(11,13,17,19,23,29),  0<=B<=6.

There are finitely many allocations (at most924 for any B). Exact rational
arithmetic over these allocations and the16 choices of(f,J) gives

    f/3+g(J)/24+8671/31185+V_(6-f-a7)
       <=16150919/16465680 <1.

The largest relaxed bound has f=1, all three7-supports, B=3, with two
remaining ternary incidences at11 and one at13. In that case

    V_3=29011/294030.

This finite maximum is justified by the preceding reduction of the entire
prime range and all support ranks. It is not finite evidence for an
unproved infinite truncation.

### 5. Conclude on the same actual source

Each original mixed violation is assigned once. Every later kernel
preserves its whole prefix event probability; pure violations have
probability zero. Summing their actual probabilities under P_* and using
the strict baseline estimate gives

    P_*(U^c)<16150919/16465680.

Hence the announced positive reserve and noncoverage follow. The product
of pointwise local density caps bounds P_* by D times full original Haar;
one final conditioning on U yields the full survivor law. Every statement
is uniform in original exponent heights and actual residues.

The total ternary budget is essential to this proof: it prevents charging
six ternary-containing supports independently at every prime. The new
statement does not include all four-predecessor-support families, since
those may contain arbitrarily many full supports through3. Conversely,
the complete pair-support graph on3,5,7,11,13,17,19 satisfies the new
hypotheses and has stages with five and six predecessors, outside that
four-support hypothesis. Arbitrary full exponent inventories remain
allowed in both comparisons.

The known sixteen-support negative Shearer example also meets this
criterion (and already meets the four-predecessor criterion). Its negative
support-envelope polynomial is thus compatible with actual noncoverage.
That example refutes a sufficient method, not the arithmetic assertion.

## Branch B: seven supports with two shared small-prime budgets

### Statement and the actual common source

Let a finite original family have pairwise distinct odd numerical moduli
>1 and arbitrary residues. Assign each mixed original to its numerically
largest prime p and let E_p be its distinct exact nonempty predecessor
supports, without merging original exponent vectors. Suppose

- |E_p|<=7 for every p;
- at most7 distinct full mixed supports contain3;
- at most7 distinct full mixed supports contain5.

Then the original family is a noncover. In particular maximum prime
incidence at most7 suffices. Other prime incidences and all original
support ranks, exponents, residues and total prime counts remain unrestricted
in the more general statement.

Use the same actual pure-survivor sequential law as the six-support result:
keep3 and5 undistorted, use delta7=2/5 and delta_p=1/2 for assigned p>=11.
Thus kappa3=kappa5=1, active kappa7=5/3, later active kappa_p=2; inactive
stages have kappa=1. That law, its original-label cylinder bound, its full
exponent expansion and its whole-prefix preservation do not depend on
whether support counts are six or seven. In particular

    P_p(assigned violation) <= G(E_p)/(p-2)^2       (p>=11),
    P_7(assigned violation) <= G(E_7)/24,
    P_5(assigned violation) <= f/3,

where f indicates the support{3,5}, and

    G(E)=sum_(S,T in E) product_(S intersect T)d_q
                         product_(S symmetric-difference T)t_q.

The factors are bounded by d3=2,t3=1 and

    q=5: d=1/2, t=1/3;
    q=7: d=4/9, t=1/3;
    q>=11: d=2(q+1)/((q-1)(q-2)), t=2/(q-2).

The old complete probability is never changed by separately optimizing
a prefix law. Each support vertex is one exact full prime set; all its
original exponent vectors remain within its load.

We prove

    P_*(U) > 630132709/12596245200.

With D=product_p kappa_p(p-1)/(p-2), full original Haar H therefore has
H(U)>630132709/(12596245200 D). Final conditioning has full density
at most (12596245200/630132709)D. The common-law construction is the same
supplier as the six-support branch; all new work is the global budget.

### 1. Infinite nonternary families have finite row-bound certificates

We require two domains: all odd primes>=5 (denote +), and the same domain
with5 removed (denote -). On either domain put

    D(R)=product_(q in R)d_q,
    W(R,T)=product_(R intersect T)d_q product_(R symmetric-difference T)t_q

for nonempty finite supports. The nominal d,t are in(0,1), t_q<=d_q, and
 t_q/d_q=(q-1)/(q+1).
For a family of j distinct nonempty supports, the row of R is bounded by

    h_j(R)=D(R)+(j-1)m(R),
    m(R)=sup_(nonempty T!=R) W(R,T).

If R={p}, any different nonempty T must contain an outside prime. Taking
T={p,q} at the largest outside t_q attains

    m({p})=d_p max_(q!=p)t_q.

If R={p,q}, p<q, deletion of q to T={p} gives d_p t_q. A proper nonempty
subset removes one coordinate; the largest deletion ratio is t_q/d_q,
because (q-1)/(q+1) increases with q. Any T containing an outside prime
has weight <=D(R)/3, while t_q/d_q>=3/4 on these pairs. Consequently

    m({p,q})=d_p t_q,
    h_j({p,q})=d_p(d_q+(j-1)t_q).

For rank at least3, replacing an overlap factor d by t cannot increase it,
and adding outside factors cannot increase it. Thus W(R,T)<=D(R) for
all T, whence h_j(R)<=jD(R). In particular

    h_j(R)<= j times the product of the three largest singleton d factors.

This bounds every higher rank, without truncating any original support.

For the + domain use the eight-prime carrier

    5,7,11,13,17,19,23,29,     next omitted prime31.

For the - domain use

    7,11,13,17,19,23,29,31,    next omitted prime37.

Evaluate h_j on every singleton and pair in the carrier. For each j=1,...,7,
let theta_j be its jth largest value. The retained rational certificate
checks all three strict comparisons

    theta_j > j d_(first)d_(second)d_(third),
    theta_j > j d_(first)d_(next),
    theta_j > d_(next)(1+(j-1)t_(first)).

The first excludes all higher-rank supports. A pair using an omitted prime
has D(R)<=d_(first)d_(next), hence is bounded by the second. An omitted
singleton has d<=d_(next) and outside t<=t_(first), hence is bounded by
the third. Monotonicity of d,t on the remaining primes justifies the
uniform tails. Therefore the j largest h_j over the entire infinite domain
are in this finite list. Let M_j be their sum and M_0=0. Summing row bounds
over the j distinct actual supports proves G<=M_j.

The exact tables, with entries indexed j=0,...,7, are

    M^- = (0,4/9,364/405,1283/891,1046/495,
              2573/891,16598/4455,9179/1980),
    M^+ = (0,1/2,34/27,115/54,283/90,
              1159/270,905/162,386/55).

These are row-sum upper bounds; simultaneous attainment is not asserted.
They are nondecreasing in j: every h_j increases with j, and summing
another nonnegative row cannot decrease the maximum sum.

### 2. Ternary-sensitive stage bounds with and without5

In either nonternary domain, enumerate all nonempty subsets of its
same eight-prime carrier. Let D_i and T_i be respectively the seven largest
distinct-support diagonal and t monomials, in decreasing order. The
certificate checks that each seventh value strictly exceeds the factor
of the next omitted prime. Any monomial involving an omitted prime is
at most that factor, because all other factors are<=1. Thus these are the
seven largest monomials over the full infinite domain. Define

    R_j=sum_(i<=j)T_i,
    C_j=sum_(i<=j)max(D_i-1/6,0),   R_0=C_0=0.

For p>=13, let a count the predecessors containing3, let b count those
not containing3, and e indicate whether the singleton{3} occurs. Removing3
from its group leaves r=a-e nonempty distinct supports, and e empty one.
As before unequal nonempty nonternary pair terms are at most1/6. The
within-group contribution is now bounded by

    A<=2M_r + e(2+4R_r),
    B<=M_b.

At most min(r,b) cross pairs have equal nonempty images. Each such diagonal
improves the generic1/6 estimate by at most its positive excess above1/6.
The matched images are distinct, so their total excess is at most C_min(r,b).
The empty image has total t weight at most R_b. Counting both orders gives

    2 cross <=rb/3 +2C_min(r,b)+2eR_b.

Combining, maximizing over e and using b<=7-a and monotonicity gives

    G(E_p)<=G_a^s,
    G_a^s=max_(e=0,1; e<=a)
      [2M_(a-e)^s+e(2+4R_(a-e)^s)+M_(7-a)^s
        +(a-e)(7-a)/3+2C_min(a-e,7-a)^s+2eR_(7-a)^s].

Here s=- applies if no predecessor contains5, and s=+ is the general bound.
The actual family has one of these two forms; no projected originals are
merged to apply the estimate. The rational tables are

    G^-=(9179/1980,4184374/530145,856481/75735,59236/4455,
         21667/1485,67454/4455,1140742/75735,7308458/530145),
    G^+=(386/55,1549507/151470,39701/2970,48589/2970,
         1633/90,28294/1485,56137/2970,1398037/75735).

Put g0=G_0^-=9179/1980. For a=0,...,7 and v in{0,1} define

    Delta_(a,v)=max(0,G_a^s-g0),   s=- if v=0, + if v=1.

Then Delta_(0,0)=0 and all increments are nonnegative. A stage with a
ternary predecessors and any5 predecessor (v=1) costs at most
(g0+Delta_(a,v))/(p-2)^2. Counting presence of5 as only one unit RELAXES
its true count; it does not increase the available resource.

### 3. Exact small head and allocation of two global budgets

Stage5 has f in{0,1}. Stage7 uses any subfamily J of the three nonempty
subsets of{3,5}; stage11 uses any subfamily K of the seven nonempty
subsets of{3,5,7}. These give2*8*128=2048 head configurations. Compute
their exact nominal Grams g(J),g(K) using the same factors as above.
Let

    B3=7-f-#{S in J:3 in S}-#{S in K:3 in S},
    B5=7-f-#{S in J:5 in S}-#{S in K:5 in S}.

Full supports containing3 or5 are distinct and each has exactly one largest
prime. Thus at all later stages

    sum a_p<=B3,   sum v_p<=B5.

The second follows because each stage with v_p=1 consumes at least one
of the remaining full supports containing5. The actual count, possibly
larger, is never replaced by a larger budget. Pure powers are outside these
mixed-support inventories.

The same proved entire prime tail gives sum_(p>=13)(p-2)^-2<1/35, so the
common baseline fee is strictly less than g0/35.
At most B3+B5<=14 later stages have (a_p,v_p)!=(0,0). Ordering those stages
and replacing their primes by the first14 primes>=13 can only increase
the nonnegative extra fees. As in the six-support proof, this is a scalar
relaxation, not a claim that arithmetic supports can be moved to earlier
primes. Write

    r=(13,17,19,23,29,31,37,41,43,47,53,59,61,67).

For each B3,B5 define the finite resource-allocation value

    V_(B3,B5)=max sum_(i=1)^14 Delta_(a_i,v_i)/(r_i-2)^2
      subject to a_i in{0,...,7}, v_i in{0,1},
                 sum a_i<=B3, sum v_i<=B5.

This maximum is computed by an exact rational dynamic program over stage
index and the two used budgets. Its transition appends every legal(a,v),
including(0,0), and keeps the largest value for each used-budget pair.
Induction on stage index proves the dynamic program equals the displayed
finite maximum. An independent recurrence or enumeration can audit it;
it is not a floating-point optimization assertion.

For each of the2048 head configurations the certificate verifies

    f/3+g(J)/24+g(K)/81+g0/35+V_(B3,B5)
       <=11966112491/12596245200 <1.

The largest relaxed bound has f=1, all three7 supports, and six11 supports
(all seven possibilities except{3,5,7}). It leaves B3=B5=1; its best extra
allocation is (a13,v13)=(1,1), of value154057/3332340.

### 4. Complete same-source conclusion and scope

Every original bad event retains its actual probability after later
normalized kernels. Summing over the unique largest-prime assignments,
using the strict infinite-tail bound, gives

    P_*(U^c)<11966112491/12596245200,
    P_*(U)>630132709/12596245200>0.

The density and noncoverage conclusions follow on the original full CRT
carrier, uniformly over all its exponent heights and residues. The new
restrictions are on distinct full mixed supports, never on the number
of original labels in a support. Their exponent inventories remain arbitrary.

The general six-support branch allows infinitely large finite5-incidence
and is not subsumed by this seven-support branch. The seven-support branch
allows seven predecessors and therefore is not subsumed by the six-support
branch. Its maximum-incidence-seven corollary does strengthen the degree-six
corollary. Neither implies unrestricted odd noncoverage when support
inventories are unbounded.

## Degree six already lies outside this uniform support-Shearer bound

The [incidence-five theorem](50-prime-support-incidence-at-most-five.md) is sharp for the universal positivity statement using the support weights

    w(E)=product_(p in E)1/(p−2).

This is a sharp boundary of that sufficient method, not a sharp boundary for arithmetic noncoverage.

On the seven primes3,5,7,11,13,17,19, take the fifteen pair supports

    {3,5}, {3,7}, {3,11}, {3,13}, {3,17},
    {5,7}, {5,11}, {5,13}, {5,17},
    {7,11}, {7,13}, {7,19},
    {11,13}, {11,17}, {11,19},

and the single triple support

    {3,5,7}.

These are sixteen distinct nonsingleton supports. In increasing prime order their incidence degrees are

    (6,6,6,6,4,3,2).

The corresponding squarefree numerical moduli are all distinct:

    15,21,33,39,51,35,55,65,85,77,91,133,143,187,209,105.

There are respectively1,16,53,30 pairwise-disjoint matchings of sizes0,1,2,3. Larger matchings are impossible because four nonsingleton supports would require at least eight primes. Their signed total weights give

    Z(F)=1−9266/8415+12847/126225−338/378675
        =−92/378675<0.

Thus universal induced-polynomial positivity already fails at maximum prime incidence six, even with support rank at most three. In this particular sixteen-support family all65535 proper support subfamilies have positive polynomials; their minimum is83/126225, attained by deleting {11,19}.

The exact certificate enumerates disjoint matchings directly, with common integer denominator378675, and then uses the finite subset-sum transform to check every induced subfamily. It does not depend on floating-point optimization or a recurrence that assumes positivity.

No forbidden residues realizing a cover are asserted. The weights above are uniform upper bounds after completing all original exponent inventories, and a negative polynomial at those bounds does not establish an arithmetic covering. The witness shows that incidence six cannot be obtained merely by proving the same universal support-Shearer positivity premise; additional arithmetic information, sharper attainable event bounds, or a different argument would be required.

Assigning each support to its numerically largest prime gives exact predecessor-support counts
(0, 1, 3, 3, 4, 3, 2) at the primes (3, 5, 7, 11, 13, 17, 19), respectively.
Thus [Chapter 52, Branch B](52-two-or-four-exact-predecessor-supports.md#branch-b-four-exact-predecessor-supports-in-numerical-prime-order)
proves noncoverage for every finite congruence family with pairwise distinct odd numerical moduli greater than one whose mixed original supports belong to these sixteen supports, with arbitrary original exponents and residues; pure prime-power classes may also be included.
The negative uniform-weight polynomial is therefore compatible with arithmetic noncoverage throughout this class.


## A ten-prime seven-budget palette with negative complete-support Shearer envelope

Take every pair support on `P0={3,5,7,11,13,17,19,23}`, except replace
`{19,23}` by `{19,23,29,31}`. There are 28 distinct mixed supports over ten
primes. Every old prime has support incidence seven; the two new primes
have incidence one. All numerical ending groups have at most six supports,
with counts in increasing prime order

    (0,1,2,3,4,5,6,6,0,1).

Thus the seven-budget theorem applies (3 and 5 each have incidence seven),
while the six-budget theorem's total ternary budget fails. Any finite
collection of distinct original exponent vectors on these supports, with
arbitrary actual residues and optional pure classes, lies in the new class.
Require all supports to occur when using the following separations.

For the complete support envelopes `w(E)=product_(p in E)1/(p-2)`, exact
rational calculation gives

    Z_K8 = -113684/2650725,
    Z_modified = -9849844/230613075 < 0,
    sum_E w(E) = 5549956/4521825 > 1.

The polynomial is also independently checked by the one-edge replacement
identity. Removing every event meeting `{19,23}` leaves K6 on
`{3,5,7,11,13,17}`, with polynomial `52/825`, so

    Z_modified
      = Z_K8 + [1/(17*21) - 1/(17*21*27*29)](52/825).

Hence both the ordinary complete support-union bound and the complete
support-envelope Shearer criterion fail for this palette. Under the new
seven-budget proof, all its actual finite distinct odd congruence families
remain noncovering at arbitrary original exponent heights and residues.
The negative polynomial is not an actual arithmetic covering example and
does not rule out Shearer applications using finer events or sharper actual
probabilities. The failure concerns precisely these complete support envelopes.

The structural comparisons are stronger than for a plain pair K8:

- One rank-four support violates [Schroeder's at-most-three-prime-factors endpoint](../../../../Library/Arith/schroeder2026noncoverage.md); ten total primes violate the [at-most-eight-primes endpoint](../../../../Library/Arith/schroeder2026nine.md).
- Incidence seven violates the established degree-five class.
- Numerical ending counts five and six at primes 17,19,23 violate Chapter52's
  four-support condition, including its condition below `10^6`.
- The retained pair subgraph is K8 minus one edge, of minimum degree six.
  In any order, its last vertex has at least six distinct singleton
  predecessor supports. Thus no order has at most two predecessor supports,
  or at most four earlier prime neighbours.
- The added rank-four support restores edge `{19,23}` in the co-occurrence
  graph and joins the two new primes to both 19 and 23. The resulting graph
  is connected without articulation vertices, so it is one ten-vertex block.
  Eight-prime-core plus single-prime-attached smaller blocks does not apply.
- The grouped incidence graph has cycle rank 21, so it is not a forest or
  pseudoforest. Deleting spine `{3,5}` leaves six old primes joined by pair
  supports, which cannot occupy disjoint private pages of size at most two.

These statements compare named hypotheses and the indicated quantitative
certificates. They are not a repository-wide claim that no other existing
specialized derivation could prove this one palette noncovering. No historical
priority claim or new Lean verification is made. The seven-support branch supplies the all-height conclusion above.

[support_shearer_boundaries.py](../frontier/cover-geometry/support_shearer_boundaries.py) uses standard-library exact fractions and checks
active under optimized Python. It verifies the counts, one ten-vertex graph
block, cycle rank, union weight, both exact polynomials, and the independent
one-edge replacement identity. It does not rerun the new global-budget proof.


## Exact original-family certificates

The [six-support checker](../frontier/cover-geometry/predecessor_support_six.py)
and [seven-support checker](../frontier/cover-geometry/predecessor_support_seven.py)
retain the complete exact scalar calculations and original CRT labels.
They compress actual coordinate carriers only by the exact truth values
of original cylinder predicates, then check every normalized kernel,
whole-prefix marginal preservation, assigned loss, original squared load,
selected paired cylinders, full joint density and survivor conditioning.
The finite checks support the general arguments; the infinite-range and
arbitrary-rank reductions are proved in the preceding branches.

### Six-support branch

The 7 actual families include 1,929 exact paired-cylinder checks.

| Original family | Full CRT period | Exact compressed cells | Original survivors | Joint survivor mass |
| --- | ---: | ---: | ---: | --- |
| K7 pair supports with repeated original exponent inventories | 1237947185475 | 9216 | 259771493880 | 5/6 |
| actual mixed-rank family with negative support-Shearer polynomial | 800224425 | 3888 | 173556900 | 7/8 |
| six high-rank predecessor supports and higher original digits | 48522699225 | 7488 | 15327932880 | 1 |
| six small predecessor supports with killed fibres and shared budget | 280665 | 1176 | 80190 | 527/648 |
| six nonternary supports with absent3 | 37182145 | 224 | 17663616 | 1 |
| 5 absent | 3003 | 80 | 1247 | 1 |
| 7 absent | 2145 | 80 | 791 | 7/8 |

### Seven-support branch

The 8 actual families include 4,885 exact paired-cylinder checks.

| Original family | Full CRT period | Exact compressed cells | Original survivors | Joint survivor mass |
| --- | ---: | ---: | ---: | --- |
| K8 pair supports with higher original exponents | 28472785265925 | 20736 | 5608092631365 | 5/6 |
| both budgets consumed across5,7,11,13 including killed fibres | 237161925 | 5040 | 62548200 | 527/648 |
| seven high-rank original supports with both budgets exhausted | 48522699225 | 8640 | 15327932592 | 1 |
| K8 with absent3 | 1078282205 | 256 | 417715785 | 1 |
| K8 with absent5 | 646969323 | 256 | 186951645 | 1 |
| K8 with absent7 | 462120945 | 256 | 117896553 | 7/8 |
| K8 with absent3,5 | 6685349671 | 256 | 3417649605 | 1 |
| ten-prime mixed-rank incidence7 family with support-union envelope above1 | 100280245065 | 1024 | 20134510200 | 7/8 |

The pair-support fixtures exercise original exponent inventories and
stage counts beyond four. Their noncoverage also lies within the
[existing Schroeder source](../../../../Library/Arith/schroeder2026noncoverage.md)
for at most three distinct prime factors per modulus. The mixed-rank fixtures exercise the quantified support-rank hypotheses
and the actual joint law. A support-union bound above one records failure
of that first-moment estimate; it does not establish failure of another
avoidance criterion. These finite examples carry no literature-priority
claim.

The [support-Shearer boundary checker](../frontier/cover-geometry/support_shearer_boundaries.py)
checks the seven-budget replacement identity and graph comparisons, and
independently enumerates every matching monomial and all 65,535 proper
subfamilies of the sixteen-support example. It also counts the exact
predecessor supports at every actual prime, verifying the comparison to
Chapter 52. Its negative support-envelope polynomial makes no assertion
of an arithmetic covering.

All three programs use only the standard library and explicit exceptions
active under Python optimization. Their complete canonical outputs are
[predecessor_support_six.json](../certificates/source_norms/cover-geometry/predecessor_support_six.json),
[predecessor_support_seven.json](../certificates/source_norms/cover-geometry/predecessor_support_seven.json), and
[support_shearer_boundaries.json](../certificates/source_norms/cover-geometry/support_shearer_boundaries.json).
From the repository root:

```sh
python3 -B -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/predecessor_support_six.py --check
python3 -B -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/predecessor_support_seven.py --check
python3 -B -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/support_shearer_boundaries.py --check
```
