# The old23 coordinate admits arbitrary heights with six further directions

The separately checked six-direction scalar gate at target19100 allows
the old23 exponent restriction to be removed. For every finite family
of pairwise distinct odd numerical moduli greater than1 dividing

    315*11*13*17*19*23^H * product_(i=1)^6 q_i^E_i,

with arbitrary nonnegative finite H,E_i and six distinct fresh primes
sorted at least29,31,37,41,43,47, the actual uncovered Haar density is at least

    13752395/20796214368384>1/1600000.                       (H23.1)

Every original phase is arbitrary and fixed globally. This statement
retains v3<=2 and v5,v7,v11,v13,v17,v19<=1 in EVERY original, including
fresh-bearing originals. It allows every actual finite23 height and every
actual finite fresh height. It is an ordinary source-transfer proof plus
exact finite certificates, not a new Lean verification or unrestricted
Erdős#7 resolution. Two distinct complete-domain exact enclosures of the
same fixed six-direction coefficients passed at target19100.

## 1. The same actual315 source, with simultaneous integer hinge bounds

Use the existing six-shape pruning and common normalization of the45
head, as in the [same-source quartic calculation](735-shape-specific-fourth-moments-on-the-unchanged-shallow-source.md). The canonical five originals are

    (3,0),(9,4),(5,0),(15,a15),(45,a45).

For root r=1 or2 and the three categories, choose

    a15 mod3=r, a15 mod5=1,
    (a45 mod9,a45 mod5)=(r,2),(3-r,1),(3-r,2).

The six resulting45 survivor sets S have sizes n=17,17,17,16,16,16.
First exclude one actual or auxiliary pure7 root. The actual seven-bearing
nonpure originals have old labels d in{3,5,9,15,45}; let b(x) be the
number of distinct other7 digits their fixed phases delete above x.
The SAME actual pruned315 survivor set has

    N=6n-sum_x b(x),
    N>=Nmin=(77,78,78,75,74,74).

Its uniform law is mu_i. Pruning produces a subset of the original
survivors; the one common coordinate normalization transports ALL
remaining originals and queries. It does not choose separate phases
for different queries or thresholds.

For every complete315 divisor query L, including its unit term,
1<=L<=12. The following bounds hold simultaneously on mu_i:

    E_(mu_i)(L-t)_+<=H_(i,t), t=0,...,11.                    (H23.2)

| shape | H0 | H1 | H2 | H3 | H4 | H5 |
|---|---:|---:|---:|---:|---:|---:|
|root1 same/other|271/86|185/86|100/81|61/81|16/39|7/26|
|root1 other/same|263/85|178/85|101/84|30/41|32/79|21/79|
|root1 other/other|263/85|178/85|101/84|30/41|32/79|21/79|
|root2 same/other|3|2|89/75|11/15|2/5|4/15|
|root2 other/same|234/77|157/77|91/76|14/19|2/5|4/15|
|root2 other/other|234/77|157/77|91/76|14/19|2/5|4/15|

| shape | H6 | H7 | H8 | H9 | H10 | H11 |
|---|---:|---:|---:|---:|---:|---:|
|root1 same/other|10/77|1/11|4/77|3/77|2/77|1/77|
|root1 other/same|5/39|7/78|2/39|1/26|1/39|1/78|
|root1 other/other|5/39|7/78|2/39|1/26|1/39|1/78|
|root2 same/other|2/15|7/75|4/75|1/25|2/75|1/75|
|root2 other/same|5/37|7/74|2/37|3/74|1/37|1/74|
|root2 other/other|5/37|7/74|2/37|3/74|1/37|1/74|

These are upper bounds, with no common maximizing query asserted.
The exact consumer verifies each entry by the existing deletion-sensitive
D2 criterion. For psi_t(a)=(a-t)_+, let A and B range over the complete45
queries on S, and put

    J_t(A)=max_B sum_j psi_t(A^up_j+B^up_j).

For each A, the checked sufficient inequality is

    5 sum_x psi_t(A_x)+J_t(A)
     +sum_(d in{3,5,9,15,45}) max_(a mod d)
          sum_(x in S, x=a mod d)(H_(i,t)-psi_t(A_x))_+
       <=6n H_(i,t).                                      (H23.3)

The D2 proof concentrates query increments at a live7 digit and subtracts
the energy actually deleted by b(x). Sorted pairing bounds convex sums
because the mixed second difference of psi_t is nonnegative. The
subtraction is then bounded by the displayed five actual-label cylinder
maxima. This proves the bound on every original seven-bearing phase
configuration, without having to choose a maximizing deletion pattern.

There are27720 complete45 layouts and141892 sorted-histogram pairs.
Each of the12 hinge tests consumes this finite dictionary. Upper bounds
at6 through11 retain the individual head shape; merging all shapes into
the older global comparator would lose the improvement used below.

## 2. Six reconstructed comparison laws on the same actual head sources

Set H_(i,12)=H_(i,13)=0. The consumer additionally verifies

    p_(i,y)=H_(i,y-1)-2H_(i,y)+H_(i,y+1)>=0, y=1,...,12,
    sum_y p_(i,y)=1.

Let Y_i have these probabilities at y. Exact reconstruction gives

    E(Y_i-t)_+=H_(i,t), t=0,...,13.

Thus the displayed table actually defines one comparison probability
law for each head shape. This compatibility is checked; it is not
inferred merely from the fact that the entries are separate upper bounds.
Piecewise interpolation then yields `L<=_icx Y_i` for every complete
315 query on the SAME actual law mu_i.

For increasing convex psi on[1,12], define

    R_i(psi)=psi(1)+(psi(2)-psi(1))H_(i,1)
       +sum_(t=2)^11 [psi(t+1)-2psi(t)+psi(t-1)] H_(i,t). (H23.4)

The discrete interpolation identity and nonnegative second differences
give, for every complete315 query,

    E_(mu_i)psi(L)<=R_i(psi).                            (H23.5)

The SAME mu_i is used for every query and psi. The reconstructed law
gives `R_i(psi)=E psi(Y_i)`. Therefore R_i is both linear and positive
on pointwise nonnegative functions. The query-dependent maximizers in
the construction of the hinge bounds have not been turned into a
jointly attained actual query; Y_i is an auxiliary dominating law.

This order of quantifiers matters. One cannot first optimize a query
for the integrated future penalty and then use that bound when the
query itself changes with an auxiliary exponent. Equation(H23.5) holds
separately for every convex test and every query; it can be applied
before averaging the auxiliary choices.

## 3. An actual full-height23 law with deterministic cylinder caps

At each of11,13,17,19 use uniform probability on the roots avoiding
the actual pure-prime original, or a fixed auxiliary root if it is absent.
Their original heights remain at most1.

At23, fix the actual pure23 root, using a fixed auxiliary root if absent.
Within each of the22 other first roots r, delete ALL actual pure23^e
originals at all their stated finite heights. Let S_r be the remaining
set and t_r its Haar mass. Since there is at most one original per depth,

    t_r>=1/23-sum_(e>=2)23^(-e)=21/(23*22)>0.

Define rho23 to assign mass1/22 to each such root, uniformly relative
to Haar on S_r. This is ONE actual pure-survivor law. Its joint density
is at most23/21, and each depth-e cylinder has probability at most

    u23(1)=1/22,
    u23(e)=23^(1-e)/21 for e>=2.                         (H23.6)

The cap includes every actual finite higher-pure hole. It is not a Haar
extension which silently fills the holes. Missing labels are allowed,
and a missing coordinate can be padded to height1 without adding an
original forbidden class.

Form the ONE product source

    sigma_i=mu_i * pure11 * pure13 * pure17 * pure19 * rho23.

On the full old carrier required by all originals, including their
fresh-bearing cofactors, it satisfies the Haar density bound

    sigma_i<=D_i Haar,
    D_i=(315/Nmin_i) product_(p=11,13,17,19)p/(p-1) *23/21. (H23.7)

The actual mass need not be uniform within the full old survivor. The
density domination in(H23.7) is retained explicitly for the final conversion.

## 4. Every actual mixed old original is paid on this source

Condition sigma_i once on avoiding all remaining actual old-only mixed
originals. Call this event E, its sigma_i probability s, and the normalized
law mu=sigma_i|E/s. All pure originals already have zero mass.

The nonunit315 mean bound is c_i=H_(i,1). For a singleton outside prime
support, the pure originals are already absent, so the old cofactor query
has mean at most c_i. For a support of size at least2 the unit old cofactor
is allowed, giving mean at most c_i+1. Sum the deterministic caps over
all heights:

    z_p=1/(p-1), p=11,13,17,19;
    z23=sum_(e>=1)u23(e)=1/21.

Every fixed outside exponent tuple still has at most one original for
each old cofactor. Union bounding these complete partial query groups
on the SAME product source gives

    s>=delta_i=c_i+2+sum_p z_p-(c_i+1)product_p(1+z_p)>0. (H23.8)

In shape order the exact lower bounds are

    2750479/31207680,
    3422543/30844800,3422543/30844800,
    17977/120960,4589/34496,4589/34496.

No original has been dropped because its23 exponent is large. The
infinite geometric sums only bound a stated finite family from above.
Mixed phases remain fixed; each group is bounded on the same sigma_i.

## 5. Legal transport of the convex interface through all query slots

Introduce comparison variables independent of mu_i and of each other:

    B_p~Bernoulli(1/(p-1)), p=11,13,17,19,
    Pr(N23>=1)=1/22,
    Pr(N23>=e)=23^(1-e)/21, e>=2,
    M=2^(sum_p B_p)*(1+N23).                            (H23.9)

For any increasing convex psi and any complete full old query L,

    E_(sigma_i)psi(L)<=E_M R_i(t |-> psi(Mt)).           (H23.10)

The needed concentration estimate has an elementary proof. If events E_j
have probabilities at most q_j with q_1>=...>=q_m, weights w_j are
nonnegative and P_j=A+sum_(l<=j)w_l, then pointwise convexity gives

    psi(A+sum_j w_j 1_(E_j))
      <=psi(A)+sum_j 1_(E_j)[psi(P_j)-psi(P_(j-1))].

Telescope only along active events: each actual starting partial sum is
at most P_(j-1), and a convex increment increases with its starting
point. Taking expectations and replacing event probabilities by q_j
is legitimate because all increments are nonnegative. The result is
exactly the expectation for nested events driven by one shared uniform.

Apply this at a fixed old point, ordering query indicators by increasing
23-height. Their cap probabilities decrease, and all slots at one
height have the same cap. It yields the auxiliary sum of the previous
coordinate queries whose exponent lies below N23, or one or two such
queries at a shallow outside prime. For n active layers, convexity gives

    psi(sum_(j=1)^n L_j)
       <=(1/n)sum_(j=1)^n psi(n L_j).

Each L_j is a legal complete old query with its own fixed phase tuple.
Use(H23.5) for EACH query and EACH auxiliary state before integrating.
This yields(H23.10), even though L_j can vary with its exponent and with
auxiliary choices. Iterating the four shallow and one full-height
coordinate gives exactly the product M in(H23.9).

At each value of the infinite comparison N23, pad missing query layers
beyond the actual finite height by the constant-one reading. This
increases the nonnegative comparison load BEFORE applying R_i. Jensen
still applies to its N23+1 terms, and a constant-one term is bounded
because psi(1)<=R_i(psi) for increasing convex psi. Thus(H23.10) uses
the SAME infinite auxiliary at every actual finite height, with each
query bounded separately. The functions used below grow linearly after
a fixed threshold, and M has a finite mean, so the resulting auxiliary
integrals are finite. This adds no infinite original family.

Positivity of R_i under pointwise changes follows here from the explicit
probability reconstruction in section2. It would not follow from the
mere definition of R_i using unrelated hinge upper bounds. The padding
argument also keeps the comparison on the actual source before invoking
R_i, so no unproved interchange of query maximization and auxiliary
averaging is used.

The auxiliary factors are independent only in this **comparison**.
After the actual restriction E, the old coordinates and all complete
query fields may be correlated. There is no claim of their independence.

## 6. Bound each field penalty, then combine on one restricted law

Keep the [fixed six-direction functions](738-full-convex-source-supports-six-fresh-prime-heights.md)
f_1,...,f_6 and g_inf with terminal slope640 from the
[unbounded-field certificate](739-an-aggregate-hinge-budget-removes-the-old-query-hard-cap.md). Its actual summed fee is

    F(C)=sum_i f_i(C_i)+sum_(|J|=2)g_inf(C_J)
       +(1/5000)sum_(|J|>=3)C_J product_(j outside J)m_j.

For a generic penalty phi among these six functions, g_inf and identity,
put a_phi=phi(8). For every padded actual full-height field C_J,
Jensen and(H23.10), followed by restriction to E, give

    E_mu phi(C_J)
       <=a_phi+(1/delta_i)R_i(h_phi),
    h_phi(t)=E_M(phi(Mt)-phi(8))_+.                     (H23.11)

For clarity, `s E_mu phi(C_J)<=s a_phi+E_sigma(phi(C_J)-a_phi)_+`.
The positive part is convex, so Jensen applies to the actual finite
geometric mixture defining C_J, including its constant-one padding.
Its full old query slots can all differ. Equation(H23.10) bounds each
slot before mixing. Finally R_i is linear, so its finite combination of
t-values commutes with the integrable auxiliary expectation.

Apply(H23.11) separately to all six unary fields, all15 pair fields and
all42 higher-support fields. This permits different queries to maximize
different terms; no common optimizer is imposed. Summing afterwards
uses only linearity of R_i. Define the one-variable aggregate function

    F0(t)=sum_i f_i(t)+15g_inf(t)+(934878/5000)t,
    h(t)=E_M(F0(Mt)-F0(8))_+.

All phi are nondecreasing, so the differences phi(v)-phi(8) have the
same sign (allowing zeros). Thus the weighted sum of their positive
parts equals the positive part of their weighted sum. Consequently

    E_mu F(C)<=F0(8)+R_i(h)/delta_i=:B_i.                (H23.12)

This equality of bounds is justified **after** the separate-field and
auxiliary-state estimates. It is not a single-query D2 bound for F0.

Exact arithmetic gives

| shape | B_i, rounded for display |
|---|---:|
|root1 same/other|19078.749269818807...|
|root1 other/same|15394.769886692875...|
|root1 other/other|15394.769886692875...|
|root2 same/other|12095.488147671409...|
|root2 other/same|13303.458727935504...|
|root2 other/other|13303.458727935504...|

The consumer checks the exact strict inequality B_i<19079 in every
shape. The rational values, not the displayed decimals, supply the bound.

To sum h exactly, first condition on the16 shallow Bernoulli patterns.
For a fixed resulting integer x=t*2^k, enumerate N23 until x(1+N23)
is at least256. Beyond that point F0 is affine. If the cutoff is K>=2,
the exact tail formulas are

    Pr(N23>=K)=23^(1-K)/21=:v,
    E[N23 1_(N23>=K)]=v*(K+1/22).                     (H23.13)

Thus every h(t), t=1,...,12, is a rational number computed with a finite
sum and an exact affine remainder. No geometric tail is discarded.

## 7. Carving, retained density and the original integer carrier

The separately verified scalar gate at target19100 yields

    (1/5000)E_mu W>=19100-E_mu F(C)>21.

From(H23.7)-(H23.8), the normalized restricted law has

    (delta_i/D_i)mu<=Haar.

Indeed `(s/D_i)mu=(sigma_i|E)/D_i<=Haar`, and s>=delta_i. The smallest
of the six paired factors is

    hmin=2750479/186876495,

attained by the first shape's conservative constants. Integrate the
same Haar-dominated six fresh-coordinate carving over this old law.
The actual total Haar density is at least

    hmin*21*5000/(28*30*36*40*42*46)
       =13752395/20796214368384>1/1600000,

as claimed. Larger fresh primes use the established normalized-response
monotonicity while retaining their actual field values. The finite CRT
carrier identifies this positive mass with at least one integer avoiding
every original congruence.

The actual source is explicitly constructed; the old23 height is not
replaced by an unspecified positive-source hypothesis. Old3/5/7/11/13/17/19
height restrictions and the six-fresh-direction limit remain. Extending
any of them needs another estimate. All deductions here remain ordinary
mathematics with exact finite checks, not new Lean verification.


## 8. Reproducible exact evidence and inherited proof inputs

The [scalar gate consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_old23_gate.py)
pins the six-direction coefficients and raises only the target from19000
to19100. Its [retained exact result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_old23_gate.json)
records173195 nodes and86598 leaves at spatial denominator256. An
independent implementation with denominator512, different supporting
lines and splits covers the same full real box with78011 nodes and39006
leaves, at maximum depth27. Both cover volume1971926775; the exterior
uses the unary bound. Their node counts differ because the enclosures
are independent, while both establish the same pointwise inequality.
The gate result contains no source-density claim.

The [actual-source consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_old23_full_height.py)
and its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_old23_full_height.json)
pin and replay the entire19100 gate, then check all332640
layout-threshold cases and1702704 histogram-pair-threshold cases,
reconstruct the six probability laws, and compute the complete geometric
tails, separate-field budgets and matched Haar factors exactly. It also
pins the unbounded-field result and checks that its hinge coefficients
are precisely those used here. With no output argument it rejects any
retained result differing from the recomputation.

An independently authored source checker uses histogram-count coupling,
direct cylinder sums, and direct comparison-law expectations for each
individual penalty. Its six exact budgets, stop-loss bounds and source
factors agree. The actual source-pruning reduction, concentration and
restriction proof above, and inherited normalized carving theorem are
ordinary mathematical inputs. Exact execution checks their stated finite
arithmetic consequences; it does not turn the whole proof into Lean.

Run from the repository root:

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_old23_full_height.py
```
