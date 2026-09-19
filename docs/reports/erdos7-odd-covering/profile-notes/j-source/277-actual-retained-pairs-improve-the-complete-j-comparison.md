[Index](../../marked_head_profile.md) · [Previous complete comparison](275-generalized-factorial-observations-improve-the-complete-j-comparison.md) · [Actual retained-pair source bounds](276-actual-retained-tail-pairs-strengthen-original-j-costs-and-square.md)

# Actual retained pair information improves the complete J comparison

On both entire actual saturated J faces, the unchanged original52-cost
comparison satisfies

    comparison <= 413.54753902911324189861297407581645... .                   (PC1)

This improves275 by3.1175085282486892838186941072404383....
All52 costs, their positive weights, signed mass, outside square,
four AP11 blocks, AP13 and the complete infinite count tail remain.
Fresh feasible moment witnesses give the independent-method bound

    comparison_method >= 413.54753902911039399603557547833482... .            (PC2)

The exact width is2.84790257739859748162759153508198485204...*10^-12.
Both bounds remain above403. The saturated J comparison is still open.
These bounds do not assert actual-source attainment.

## Four stronger bounds in the same26-observation basis

Keep275's raw mass1/4, survivor mass S=3/20, entire common late interval
[1/135,1/90], original labels and all26 scalar functions. Source276
strengthens exactly four existing upper bounds:

| Basis function | Previous bound | Updated bound |
| --- | ---: | ---: |
|cost48|14458716500149327837/3969000000000000000|402172082863385623/113400000000000000|
|cost49|207467385335349113/52920000000000000|3045114520043616887/793800000000000000|
|square|1813/400|17653307900058777407/3969000000000000000|
|factorial5|6103/7200|4552688500270367/5670000000000000|

There are no new scalar dimensions. Write H_t(n)=(n-t)_+ and
Phi_k(n)=(n-k)_+*(n-k+1)_+/2. For every positive integer n,

    cost48(n)=5*H_3(n)+2*Phi_3(n),
    cost49(n)=(31/16)*H_2(n)+(17/16)*H_3(n)+2*Phi_2(n),
    n^2=1+H_1(n)+2*Phi_1(n).                              (PC3)

The fourth function is Phi5 itself, with zero constant and an empty
hinge sum. The consumer checks finite transitions and the complete
polynomial continuation of each unchanged function before updating its
bound. A source target bound and a scalar-basis bound are checked in
their separate roles; no earlier method witness is reused unchecked.

For A=B+O+Z, source276 uses the whole-load inequality

    Phi_k(A)<=Phi_k(B)+(B-k+1)_+*(O+Z)+binom(O+Z,2).      (PC4)

It preserves the complete exponent tails, retained raw/survivor crosses
and the one actual common late coordinate. In the final pair term,
15 retained old-old pairs and42 selected old-positive-seven blocks
replace only their exact assigned payments8857/202500 and5402/91875.
Every complementary pair remains. Conditional positive-seven pairs
use complete independent raw heads at depths1 and2 and the full later
constant31/1470; their two endpoint maxima give a valid convex secant.
The original model remains3306 variables,6354 inequalities and18
equalities. Four full source scans cover250,000,000 original choices,
with1359 exact duals and4492854 domination-column checks.

## Exact upper envelopes and fresh lower witnesses

Write the common scalar constraints as

    <1,mu>=S,    <b_j,mu><=B_j for j!=mass.                (PC5)

Every source inequality is uniform in the original labels, so all26
constraints apply to a load from any admissible label choice. Different
targets retain independent choices and need not share one optimizer.

For each of52 original costs and seven outside targets, retain rational
coefficients y_j with

    f(n)<=sum_j y_j*b_j(n) for every integer n>=1,
    y_j>=0 for j!=mass.                                  (PC6)

The exact-mass coefficient may be signed. The checker verifies the
inequality at1,...,8 and over its entire affine or quadratic continuation
from9, using the leading coefficient and the neighboring integers of
each quadratic vertex. No finite load cutoff replaces this argument.
Integration gives U_f=sum_j y_j*B_j. All59 envelopes are no worse than
275's complete bounds;11 are strictly stronger. They use
164 nonzero coefficients and pass472 finite and59 full-tail checks.

For each target f, a fresh finite positive rational measure mu_f obeys
all26 updated constraints, with exact mass. The263 positive atoms pass
1534 exact moment checks. Thus every independent upper envelope
based only on(PC5) has bound at least L_f=<f,mu_f>. These measures
constrain the scalar moment problem; they need not be actual covering
families or compatible parts of one actual source.

## Complete signed comparison and method boundary

With the unchanged original weights w_i>0, signed mass coefficient cS,
outside-square coefficient cQ>0 and offset C0, the complete quantities are

    Nbar=cS*S+sum_(i=0..51) w_i*U_(cost-i)+cQ*U_square
        =33.314976564011674145499016972586558...,
    Tcount=(U_mean-S)/7986+S/87846
          =277/4392300,
    Ebar=S-U_H4/6-(sum_(e=0..3) U_(AP11-e)+Tcount)/7
        =94388175402220392465723949/1110484565190000000000000000
        =0.0849972870951798487335479334110563....                              (PC7)

Both Nbar and Ebar are positive; C0+Nbar/Ebar proves(PC1).
The denominator equals275's exact denominator. The403 numerator margin is

    (403-C0)*Ebar-Nbar=-0.896512203005152746459023255521423....     (PC8)

For the independent method lower bound, insert L_f in the same complete
formulas. This gives Nlo>0 and Ehi>0. Positive cost weights, fixed signed
mass and positive denominator deductions imply for every admissible
independent-envelope comparison

    N'>=Nlo,    0<E'<=Ehi,
    C0+N'/E'>=C0+Nlo/Ehi.                                (PC9)

This proves(PC2). Every witness is checked against the current four
stronger constraints;275's old method bracket is not transferred.
The lower bound rules out reaching403 through further optimization of these same26 independent scalar observations.
Additional joint information can change the available constraints.

## Exact artifacts and scope

The [consumer](../../frontier/j-source/j_face_joint_pair_factorial_complete_moment_cost_comparison.py)
and [certificate](../../certificates/source_norms/j-source/j_face_joint_pair_factorial_complete_moment_cost_comparison.json)
retain140 mathematical source pins, all26 current observations,52 original
costs and positive weights,59 whole-load exact envelopes,59 independently
feasible moment witnesses, every signed payment and complete survival
term. Canonical replay uses exact standard-library rational arithmetic.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j-source/j_face_joint_pair_factorial_complete_moment_cost_comparison.py --check
```

This is an ordinary complete comparison on both saturated actual J
faces. Off-face extension, the global join and unrestricted Erdos7 remain
open. Actual-family attainment and Lean verification are not asserted.
