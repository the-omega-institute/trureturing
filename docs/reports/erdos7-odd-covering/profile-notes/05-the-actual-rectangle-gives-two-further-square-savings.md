[Index](../marked_head_profile.md) · [Previous](04-the-weighted-upper-quantile-lemma.md) · [Next](06-a-common-matrix-bound-for-all-actual-rectangles.md)

<a id="the-actual-rectangle-gives-two-further-square-savings"></a>
### The actual rectangle gives two further square savings

At an old point x, let m≤10 and n≤12 be the actual remaining row and
column counts after axis deletion, and let k≤12 be the number of distinct
remaining point holes. There are twelve possible original labels 143d,
d|315, which proves the hole cap. These are actual counts, not the
lower bounds for axis counts used in (VC2). Write T for the local
survivors and N_grid=mn−k for their number; N_grid is distinct from the
common old survivor count N.

When N_grid>0, the existing clipped density is f=min(40/31,120/N_grid)
on T, with old marginal h=f N_grid/120. Empty fibres have f=h=0. No
additional support restriction or change of probability measure is used.

For a selected row, column and surviving point, write r,c for their
surviving row/column sizes and u,v,w for the indicators that the row-column
intersection survives, the point is in the row, and the point is in the
column. The Gram matrix of the four indicators is

    [[N_grid,r,c,1], [r,r,u,v], [c,u,c,w], [1,v,w,1]].

Put d=n−r and e=m−c. Subtracting this matrix from
diag(N_grid+m+n+1,2(n+1),2(m+1),4) gives the weighted graph Laplacian
with edge weights r,c,1,u,v,w, plus diagonal slacks

    (d+e, 2+2d−u−v, 2+2e−u−w, 2−v−w).

All weights and slacks are nonnegative, so this is positive semidefinite
for every m,n≥1 and every point-hole pattern. An absent test row, column
or point has zero indicator and is handled by the corresponding
principal restriction. Convex concentration of the nonnegative
coefficients in each test block extends the bound to arbitrary row,
column and point assignments. Multiplying by f/120 gives the diagonal

    (h+f(m+n+1)/120, 2f(n+1)/120,
                         2f(m+1)/120, 4f/120).                (SC7)

The four block amplitudes A_i are complete old loads, each at least one
and with Eμ A_i²≤G_(S,N). They need not be independent of each other or
of the local geometry.

Write q for the four coefficients in (SC7) after removing h from the
first one, and set C=40/31. The following simultaneous bounds hold:

    q≤U:=(55/2,26C,22C,4C)/120,
    Σq=f(m+n+3)/40≤3/4,
    ΣU=391/496.                                               (SC8)

For completeness, if m+n≤20, then f(m+n+1)≤21C<55/2 and
Σq≤23/31<3/4. If m+n=21, the dimensions are (9,12) or (10,11),
so N_grid≥96 and f≤5/4; this gives both bounds. If m+n=22, the
dimensions are (10,12), N_grid≥108 and f≤10/9, which also suffices.
The other three coordinate bounds use f≤C directly. Both displayed
maxima occur at (m,n,k)=(9,12,12). Empty fibres have q=0.

Since A_i²≥1, the coordinatewise gaps in (SC8) give

    Σq_i A_i²≤ΣU_i A_i²−(ΣU_i−Σq_i)
              ≤ΣU_i A_i²−19/496.

After integration, the low-block square is at most

    G−1+Z+(391/496)G−19/496.

Here G=G_(S,N); the h term uses the same old-marginal saving as (VC8).
Every pair with at least one higher exponent retains the existing
reference estimate C(χ0−13/8)G. Thus the complete square bound gains
both a coefficient and a constant saving:

    Γ(ξ)≤G−1+Z+C(χ0−1)G−(9/496)G−19/496.                    (SC9)

Deleting the higher original classes and normalizing is unchanged.
The numerator below is positive in every common branch, so replacing
the remaining mass by its certified lower bound is valid:

    Γ(ν)≤1+[G−1+C(χ0−1)G−(9/496)G−19/496]/s_(S,N).        (SC10)

The maximum over the 144 branches is 2167128283/58962460, again at the
first shape with N=81. This proves (SC1). The first-moment and full
comparison bounds above apply to this same unchanged probability law.

The `shared_count_clipped_head` field is recomputed from the existing
old geometry by the adjacent standard-library verifier. It checks all
144 branches, the 1728 pointwise instances of the single existing
dual (VC6), and all 1372 nonempty actual rectangle count triples in
(SC8). The universal Gram inequality follows from the displayed
Laplacian identity. No optimizer output or new primal certificate is needed.
The former scalar optimality result still concerns its stated global
marginal information; (SC2)–(SC6) retain additional common geometry.
These are ordinary proofs with exact arithmetic, without a new tail
continuation or an end-to-end Lean theorem.

<a id="actual-obstruction-for-uniform-conditioning-and-its-signed-bound"></a>
## Actual obstruction for uniform conditioning and its signed bound

At first 11/13 height, fix the reference law τ=μ times the uniform
10×12 pure-survivor rectangle. For the four complete old test blocks
A,B,C,D, the fine test's reference square is at most

    E[A²+(2AB+B²)/10+(2AC+C²)/12
                       +(2BC+2AD+2BD+2CD+D²)/120].

Write `Rμ(A)=max_B Eμ AB`. Cauchy–Schwarz on the other old products
bounds this by `Eμ A²+(23/60)Rμ(A)+(29/120)G`.
Every deleted cell has full load at least A. For a candidate final
bound z, union-bound only the positive deletion contribution `(z−A²)_+`.
Each nonunit old label contributes row, column and point caps totaling
`1/10+1/12+1/120=23/120`; the unit cross label contributes `1/120`.
Thus the following condition for every A is sufficient for the normalized
uniform-survivor law to have Γ≤z:

    Eμ A²+(23/60)Rμ(A)+(29/120)G
      +(23/120) Σ_{d|315,d>1} max_a Eμ[(z−A²)_+ 1_{x=a mod d}]
      +(1/120)Eμ(z−A²)_+ ≤ z.                              (SC1)

The low surviving mass is positive: its union bound is at least
`1−(23/120)(M−1)−1/120=1993/3440`. The signed argument retains
the same μ and every distinct original label. The exact examples below
bound the scope of this sufficient criterion and of this particular
conditioned law; they do not rule out different supported laws.

<a id="same-old-law-and-exact-sufficient-criterion-barrier"></a>
### Same old law and exact sufficient-criterion barrier

The old original classes are

```
(3,0),(9,4),(5,0),(15,1),(45,37),(7,0),
(21,16),(35,24),(63,25),(105,19),(315,109).
```

Their complement Omega modulo 315 has size 86. With mu uniform on Omega
and the complete coherent layout `A(x)=sum_{d|315}1[x=8 mod d]`, its
histogram is

```
A:       1  2  3  4  6  8  12
count:   5 38 14 18  8  2   1.
```

Consequently `sum A=271` and `sum A^2=1131`. Direct maximization of every
individual divisor cylinder gives

```
max_B E_mu B = 271/86,
R_mu(A):=max_B E_mu AB = 1131/86 = G,
E_mu A^2 = G.
```

Here B ranges over all independent complete old layouts; the maximum
separates exactly into one finite residue maximization per divisor.

Put `h_z=(z−A^2)_+` and
`W(z)=sum_{d|315,d>1}max_a E_mu[h_z 1[x=a mod d]]`.
For the proposed sufficient criterion,

```
Phi(A;z)=E_mu A^2+(23/60)R_mu(A)+(29/120)G
         +(23/120)W(z)+(1/120)E_mu h_z.
```

For 25<=z<=35 the direct cylinder checks give

```
86 E_mu h_z=75z−571,
86 W(z)=164z−1197.
```

Each recorded cylinder witness maximizes at both endpoints and therefore
throughout the interval: every cylinder expression is affine there.
The verifier computes its own maximizers instead of trusting the oracle's
compressed witness table. Substitution gives

```
Phi(A;z)=(192443+3847z)/10320,
Phi(A;z)−z=(192443−6473z)/10320.
```

Globally the map Phi is Lipschitz with constant at most

```
(23/120)(271/86−1)+1/120=1447/3440<1.
```

Thus Phi(z)−z is strictly decreasing, and its unique zero is
`z*=192443/6473`. The sufficient criterion fails for every positive
z<z*, not just the portion in [25,35]. At 30 it succeeds on this example:
`Phi(30)=30−1747/10320`. This does not establish a universal bound of 30.

<a id="actual-conditioned-moment-and-its-narrower-scope"></a>
### Actual conditioned moment and its narrower scope

Add pure classes 0 mod 11 and 0 mod 13. For each old divisor d the table
below specifies additional row, column and point exclusions, respectively
by `(old residue,11-residue)`, `(old residue,13-residue)` and
`(old residue,11-residue,13-residue)`.

| d | Row | Column | Point |
|---|---|---|---|
|1|—|—|(0,9,8)|
|3|(2,6)|(1,11)|(2,10,11)|
|5|(2,2)|(4,2)|(2,10,5)|
|7|(5,5)|(6,3)|(6,10,6)|
|9|(2,3)|(5,4)|(2,9,6)|
|15|(2,7)|(11,2)|(2,9,10)|
|21|(2,4)|(20,12)|(2,10,6)|
|35|(17,5)|(34,9)|(34,2,7)|
|45|(2,8)|(41,5)|(11,2,9)|
|63|(47,4)|(34,12)|(23,8,3)|
|105|(17,4)|(34,10)|(26,8,7)|
|315|(52,7)|(244,4)|(97,10,7)|

The complete family contains exactly one congruence for every nonunit
divisor of 45045, hence 47 distinct odd nonunit moduli. The coherent fine
test center is 17018, which reduces to 8 modulo 315 and 1 modulo both
11 and 13. Its complete load is

```
F(x,i,j)=A(x)(1+1[i=1])(1+1[j=1]).
```

Among 10320 equally weighted reference cells, exactly 6872 survive every
original class. Their squared-load sum is 177110. Therefore, for the law
nu obtained by uniform conditioning on these actual survivors,

```
E_nu F^2=177110/6872=88555/3436>25,
retained reference mass=6872/10320=859/1290.
```

This proves `Gamma(nu)>=88555/3436`; it is not a claim that equality is
the maximum over all fine test layouts. The pre-deletion estimate is sharp
for this layout, since `E_tau F^2=(13/8)G` exactly. The additional loss in
the threshold 29.7301 therefore comes from the sufficient deletion bound.

These are obstructions for this prescribed uniform-conditioning method
and its sufficient criterion. They do not obstruct all supported laws,
do not apply automatically to higher 11/13 exponents, and do not exhibit
an odd covering system: this actual family has 6872 uncovered residues.

The actual family was supplied by Nyx. The adjacent verifier reconstructs
every CRT residue, checks the full period and the independent 86×10×12
grid, and verifies every weighted-cylinder maximum. Its fixed
`signed_conditioning_obstruction` certificate stores the original classes
and load histograms. This is exact arithmetic, not a Lean theorem.

<a id="what-the-rectangle-data-do-not-determine-about-a-hinge"></a>
## What the rectangle data do not determine about a hinge

Here the input is an actual head family together with a complete test
layout. Retaining the old shape, its survivor count, every actual rectangle
size and all four old block functions does not determine the test's
threshold-six hinge. This concerns exact evaluation: taking a supremum
over the omitted configurations can still give a sound upper bound.

For a concentrated four-block load on a nonempty surviving grid, let Ngrid
be its cell count, r and c the selected surviving row and column counts,
and u,v,t indicate, respectively, whether their intersection survives,
whether the selected surviving point lies in the row, and whether it lies
in the column. Put phi_tau(a)=(a-tau)_+. The exact unweighted cell sum is

    H_tau=(Ngrid-r-c+u) phi_tau(A)
          +(r-u) phi_tau(A+B)+(c-u) phi_tau(A+C)
          +u phi_tau(A+B+C)
          +phi_tau(A+vB+tC+D)-phi_tau(A+vB+tC).              (HO1)

The first four terms partition the grid by row/column membership; the
last difference adds the point block at its actual location. Its clipped
fibre integral is f H_tau/120. Empty fibres contribute zero. Thus the five
incidence values together with Ngrid and the amplitudes determine this
concentrated hinge. General labelled tests still need their actual
cylinder arrangement, or the justified convex-concentration upper bound;
(HO1) does not reconstruct that arrangement from four block totals.

For an actual counterexample use the 86-point old family specified in the
preceding subsection, with its forbidden old residue a_d for every
nonunit d|315. Add pure classes0 mod11 and0 mod13. For every d>1, add the
11d,13d and143d classes with old residue a_d and new digits1 where present.
All of these classes are inactive on the old survivors. The unit mixed
143class instead deletes the cell(10,12). This specifies exactly one
original class for every nonunit divisor of45045:47distinct moduli.

Every old survivor therefore has the same10×12rectangle with one point
hole, Ngrid=119, clipping density f=120/119 and old marginal h=1. The
constructed law is uniform on the10234actual survivors. In both complete
tests, all four old block functions are

    A(x)=sum_(d|315) 1[x=8 mod d].

For each d, the11d test chooses new digit1, and the13d test chooses digit1.
The first test's143d block chooses point(1,1); the second chooses point(2,2).
The old d block chooses8 mod d in both. CRT gives48actual divisor labels
for each complete test, with all four old block functions unchanged.
Their selected incidence data are (r,c,u)=(12,10,1) in both cases, but
(v,t)=(1,1) and(0,0), respectively. Direct evaluation gives

    sum_survivors (L_first-6)_+ =3998,
    sum_survivors (L_second-6)_+=3844,

hence

    E(L_first-6)_+=1999/5117,
    E(L_second-6)_+=1922/5117,
    difference=11/731>0.                                   (HO2)

For the observation q retaining the shared shape/count, actual scalar
rectangle data and four old block functions, (HO2) gives equal q-values
and unequal hinge values: ker(q) is not contained in ker(H_6). A derived
encoding of those same readings cannot restore the missing incidence.
Keeping the actual test cylinders together with CRT-closed intersection
counts I_U(d,a) does distinguish the inputs: compatible cylinder
intersections are again CRT cylinders, so their counts determine the
joint load histogram. This is a different issue from (P13.1), which uses
two original survivor states and one fixed next class to show that
residual mass alone does not determine the deletion update.

The verifier reconstructs all47original classes and both48-label tests,
checks the full period modulo45045 against an independent86×119CRT grid,
and checks(HO1)at every integer threshold0through48 for both tests above
every old survivor:8428exact identities. The new
`rectangle_hinge_observation_gap` certificate field retains these actual
inputs and load histograms. This is an ordinary exact-arithmetic result;
it asserts neither a new hinge upper bound nor a tail continuation.

<a id="actual-rectangle-hinge-bounds-on-the-same-law"></a>
## Actual rectangle hinge bounds on the same law

The actual law in (SC1), with the same fixed C=40/31, also satisfies the
following simultaneous full-height bounds. Write
Theta_nu(t)=sup_test E_nu(L-t)_+, with the supremum over complete divisor
test layouts. The full original 3/5/7 part must divide 315; both 11 and 13
may have arbitrary finite positive heights, and all axis and point
deletions are allowed.

| t | Certified upper bound for Theta_nu(t) | Approximation |
|---|---|---|
|4|1850731457651/1285518750000|1.439676752|
|5|285616505131/257103750000|1.110899803|
|6|321137/403528|0.795823339|
|7|205590443009/321379687500|0.639712002|
|8|242331326613/499400000000|0.485244948|
|9|129498094659/312125000000|0.414891774|
|10|881984754807/2497000000000|0.353217764|
|11|165110502807/565775000000|0.291830680|
|12|47555781251/205683000000|0.231209100|

The displayed decimals are rounded upward. These are pointwise hinge
bounds on the same supported probability as (SC1), rather than a new
probability comparator. In particular the first p=17 query in (AP2) at
t=6 has charge at most 321137/4035280. The entries include the
whole-cost refinement (JC1) below, which also uses (FD2). This does not establish a complete
tail continuation.

<a id="concentrating-the-test-and-retaining-the-actual-grid-size"></a>
### Concentrating the test and retaining the actual grid size

At an old survivor x, let a,b,c,d in {1,...,12} be the four complete old
test-block loads. After the actual axis deletions the carrier is an
m by n rectangle, where 0<=m<=10 and 0<=n<=12. Let k<=12 be the number
of distinct mixed point holes inside that carrier, and put Ngrid=mn-k.
For Ngrid>0 the actual clipping coefficient is

    f/120=1/max(93,Ngrid).                                  (HG1)

An empty fibre contributes zero. Put phi_t(v)=(v-t)_+. For a full
rectangle, the sum of the Ngrid largest hinge values bounds the sum on
its actual survivors. It is a convex function of every allocation of
the row, column and point blocks: it is the maximum of the sums over
all Ngrid-element subsets, each a sum of convex hinges. Enlarge the
possible allocations to the full simplices with totals b,c,d. Convexity
then permits concentration of each block on one row, one column and
one point. Components outside the carrier may first be moved into it,
which only increases the nonnegative cell loads. This is a pointwise
upper bound and does not assert that the concentrating choices arise
from one common arithmetic test layout.

The point mass can be placed at the row-column intersection. Indeed,
if two base loads satisfy u>=v, moving d from v to u cannot decrease
the sum of the Ngrid largest hinges. A selected subset taking neither
entry is unchanged. If it takes one, select the now larger entry; if
it takes both, convex increment monotonicity gives

    phi_t(u+d)+phi_t(v)>=phi_t(u)+phi_t(v+d).

The row-column intersection has the largest base load. Its point-loaded
cell is therefore retained when taking the Ngrid largest entries.
Consequently the exact concentrated upper envelope is

    K_t=[phi_t(a+b+c+d)+(n-1)phi_t(a+b)+(m-1)phi_t(a+c)
          +(m-1)(n-1)phi_t(a)-D_k]/max(93,mn-k),            (HG2)

where D_k is the sum of the k smallest nonintersection entries. These
are first the (m-1)(n-1) entries phi_t(a), then the row and column
entries ordered according to b<=c or c<=b. Formula (HG2) covers every
nonempty actual grid, including grids whose original selected
intersection or point was deleted; taking the largest surviving-count
subset was already an upper bound before concentration.

<a id="exact-duals-point-load-endpoints-and-empty-fibres"></a>
### Exact duals, point-load endpoints and empty fibres

The `actual_rectangle_hinge_profile` certificate retains one rational
dual at each t=4,...,12, of the form

    K_t <= c_t + sum_(i=0)^3 sum_(j=0)^11 w_(t,i,j) phi_j(A_i)
                 + sum_(j=0)^11 v_(t,j) phi_j(k),           (HG3)

with all w and v nonnegative. Every numerator, common denominator and
constant c_t is retained; no numerical optimizer or tolerance is part
of verification. At t=6 the particularly short dual is

    K_6 <= [psiA(a)+psiB(b)+psiC(c)+psiD(d)]/93
                     +(7/1984)phi_8(k),
    psiA=phi_1+2phi_2+16phi_3+74phi_6,
    psiB=phi_1+9phi_3+2phi_4,
    psiC=phi_2+7phi_3+2phi_4,
    psiD=phi_2.                                           (HG4)

There are 1372 nonempty triples (m,n,k). The checker uses all 12^3
values of a,b,c and the positive hinge knots of the point-load cost
in d. Before its first knot that cost is constant and the left side
increases, so the first knot bounds that entire interval. Between
successive knots, (HG2) minus the linear point cost is convex in d,
so its maximum occurs at an endpoint. Beyond the last knot, the
left-side slope is at most 1/max(93,Ngrid)<=1/93, while the checked
point-cost slope is at least 1/93. Thus the last knot bounds the
remaining d<=12. The endpoint sets, in threshold order, are

    {1}, {1,2}, {2}, {2}, {2}, {2,3}, {3}, {3}, {3}.

Multiplying by the positive common denominator and max(93,Ngrid)
reduces these checks to 26,078,976 integer inequalities. The endpoint
argument certifies all 256,048,128 original combinations. For empty
fibres the left side is zero. Nonnegative weights make the minimum
right side occur at a=b=c=d=1 and k=0; the checker verifies this
minimum is nonnegative. This check is essential because the retained
constants at t=4 and t=5 are negative.

<a id="one-arithmetic-branch-through-higher-digits-and-normalization"></a>
### One arithmetic branch through higher digits and normalization

Use only the existing (SC2)--(SC6) bounds on a fixed branch (S,N):

    theta_0=M_(S,N), theta_1=M_(S,N)-1,
    theta_2=theta_(S,N)(2), theta_3=the existing shape bound,
    theta_4=theta_(S,N)(4), theta_5=the existing shape bound,
    (theta_6,...,theta_12)=(10,7,4,3,2,1,0)/N.              (HG5)

The high-threshold numerators are already checked by the complete
old profile: the five additional copies of an old load contribute
zero at every threshold at least 6, so the numerator is independent of N. The
checker identifies these numerators in all six existing profiles.
Every complete test load has these bounds on the same uniform old
law. The number k of distinct surviving mixed holes is at most the
number of active mixed labels, which is another complete old load.
Hence E phi_j(k)<=theta_j as well; no independence between deletions
and the four test blocks is assumed.

Average (HG3) on that branch to obtain B_t(S,N). Restricting further
to actual survivors of higher classes only decreases the nonnegative
low-load hinge. Write L=L_low+L_high. The elementary inequality

    phi_t(L)<=phi_t(L_low)+L_high

and the existing higher-exponent reference calculation give
integral_xi L_high<=C(89/4800)M_(S,N). In fact 89/4800 is the difference
5809/4800-143/120 between the full-height and first-power auxiliary
means, agreeing with the coefficient in (VC7). The same branch has surviving mass at least

    s_(S,N)=1-[17theta_2+4theta_4]/93-C(89/4800)M_(S,N)>0.

Therefore the normalized actual law satisfies

    Theta_nu(t) <= [B_t(S,N)+C(89/4800)M_(S,N)]/s_(S,N).    (HG6)

The certificate evaluates (HG6) separately on all 144 existing
branches and then takes the maximum. It does not combine a numerator from
one branch with the mass of another. Before the fixed-count refinement below,
the t=6 maximum is the first shape with N=81 and equals 19427/24198;
all nine are retained in `actual_rectangle_hinge_profile`. The displayed
table includes the further whole-cost refinement (JC1).

Since the actual hinge function is convex, linear interpolation
between adjacent certified knots is also a pointwise upper bound.
Taking its minimum with another valid pointwise hinge bound remains
valid. These operations do not assert that the resulting upper curve
is convex or is the hinge transform of a probability measure; (AP2)
requires only the pointwise bounds. The certificate supplies numerical
premises for that existing continuation criterion, with no new Lean
declaration and no assertion that a full tail schedule succeeds.

<a id="fixed-count-labelled-deletion-refinement-at-threshold-six"></a>
## Fixed-count labelled deletion refinement at threshold six

The threshold-six dual can be sharpened on the three branches where the
coarse joint-cost bound was above four fifths. Consider the first canonical
old survivor shape, `root1_same_other_column`, which has 17 points. Its five
mixed-seven labels have old cofactors `3,5,9,15,45`. Group labels that use
the same nonzero seven digit. A group deletes the union of the selected old
cylinders for its labels; overlaps inside a group count once, while groups
with different seven digits delete different lifted points.

For a complete old-45 test load A on this 17-point set U, write
H_t(A)=sum_U(A-t)_+, and let M_t be its maximum over old test layouts.
For either nonnegative hinge combination psi=sum_t w_t phi_t in (HG4), put

    Jbar_psi(A)=sum_t w_t min_(0<=s<=t) [H_s(A)+M_(t-s)],
    Kbar_psi(A)=5 sum_U psi(A)+Jbar_psi(A).

For every complete old load B, the inequality
phi_t(A+B)<=phi_s(A)+phi_(t-s)(B) proves
sum_U psi(A+B)<=Jbar_psi(A). Across the six surviving seven digits,
the additional test loads are nonnegative and sum to at most a complete
old load B. Convexity at each x gives total undeleted cost at most
5 psi(A(x))+psi(A(x)+B(x)), hence at most Kbar_psi(A) after summation.
Every actual deletion above x removes cost at least psi(A(x)), because
psi is nondecreasing. Thus if delta_x digits above x are deleted and
D=sum_x delta_x=102-N,

    N E psi(L315) <= Kbar_psi(A)-sum_x delta_x psi(A(x)).

Ineffective test cylinders can be replaced by effective ones before this
upper bound, so the complete effective layouts enumerated below dominate
all tests. For fixed A, give each x cost psi(A(x)). For a label subset T,
let b_T(u) be the least cost of a union of cardinality u, with an empty
cylinder allowed. The anchored recurrence

    d_empty(0)=0,
    d_S(D)=min_{T subset S, min(S) in T, u}
           (b_T(u)+d_(S\T)(D-u))                         (FD1)

is a lower bound for the cost removed by any actual labelled deletion with
`D=102-N` deleted points. Enlarging the feasible set by allowing empty masks
is safe in this direction: it can only reduce the minimum deleted cost and
therefore can only increase the final upper bound. The five empty residue-zero
cylinders are available on this 17-point survivor set.

Every actual deletion is represented by grouping its five original labels
by their seven digit, so (FD1) bounds its removed cost from below. Conversely,
each partition has at most five blocks and can be assigned distinct nonzero
seven digits. Cardinalities add across blocks. Nonnegative cardinalities
make truncation at D=22 sufficient for D=20,21,22.

Two cheaper lower bounds permit exact screening. Since delta_x<=5, the
removed cost is at least the sum of the D smallest costs among five copies
of each psi(A(x)). Also, for any eta>=0,

    sum_x delta_x psi(A(x))
      >= eta D - sum_(labels d) max_(a mod d)
                       sum_(x in U, x=a mod d) (eta-psi(A(x)))_+.

This follows from delta_x<=sum_d 1_(x=a_d mod d) and nonnegative positive
parts. Taking eta in {0} union {psi(A(x)):x in U} gives the screening
lower bound used by the verifier; it need not attain the best lower bound.
A layout is screened only if Kbar minus this lower bound is already at most
the target. Every remaining layout is checked using (FD1).

There are 2,164 distinct union masks and 8,919 subset-union entries. The
4,760 complete old-45 test layouts have old hinge maxima
`(42,25,11,5,2,1,0)` at thresholds zero through six. A cheap lower bound
discharges 4,688 layouts for

    psiA=(x-1)+ + 2(x-2)+ + 16(x-3)+ + 74(x-6)+,

and 4,640 for

    psiB=(x-1)+ + 9(x-3)+ + 2(x-4)+.

The exact anchored DP checks the remaining 72 and 120 layouts respectively.
For `N=80,81,82`, the resulting numerator caps are

    N E psiA <= (1986,1986,1992),
    N E psiB <= ( 728, 728, 732).                         (FD2)

The two bounds in (FD2) apply to the a and b costs of (HG4). The other
two test costs and the hole-activation hinge retain their (HG5) bounds.
The verifier checks that these cost coefficients reproduce the exact
threshold-six dual, then uses the same branch mean and surviving mass in
(HG6). Replacing only these three branches in all 144 common shape/count
branches gives

    Theta_nu(6) <= 26114497/32685768
                 = 4/5 - 170587/163428840 < 4/5.           (FD3)

The unique maximizing branch is `root1_same_other_column` with `N=79`; the
refinement changes the `N=80,81,82` branches. The corresponding first
prime-17 query costs at most `26114497/326857680`. This is an ordinary
exact-arithmetic finite-head result. It does not formalize the DP in Lean,
extend the result to unbounded 3/5/7 powers, or provide the unrestricted
tail stopping certificate.


<a id="whole-convex-costs-on-one-old-layout-and-deletion-configuration"></a>
## Whole convex costs on one old layout and deletion configuration

The same derivation applies to every nonnegative hinge combination appearing
in the rectangle witnesses, including the cost of the hole activation. For
each of the six canonical old sets U_S, put n=|U_S| and D=6n-N. For a fixed
complete effective old-45 load A, form Kbar_psi(A) as above using that shape's
hinge maxima. Let L_psi,D(A) be the maximum of the two cheap deleted-cost
lower bounds established before (FD2). Then

    N E psi(L315) <= B_psi(S,N),
    B_psi(S,N)=max_A [Kbar_psi(A)-L_psi,D(A)].              (JC1)

Both terms use the same A. This retains the relation between its hinge
costs and the energy removed by the original labelled cylinders. In
particular it improves some sums of separately maximized hinge bounds,
even without evaluating the partition DP. The possible ineffective tests
are dominated by complete effective layouts exactly as in the preceding
argument. The union-bound estimate for L remains valid when several
original labels use the same seven digit.

There are 32 distinct costs after extracting their positive common integer
factors. The verifier calculates (JC1) for all 27,720 effective layouts and
all allowed survivor counts: 21,324,800 layout/cost/count bounds. It averages
each whole cost using the smaller of B_psi(S,N)/N and the earlier sum of
individual hinge bounds. For the three applicable threshold-six branches
it also takes the smaller bound from (FD2). The hole count is bounded by a
complete old activation load, and its cost is nondecreasing; the same
whole-cost estimate therefore applies to it. No relation between that
activation load and the four test loads is assumed beyond their common
actual old shape and survivor set.

Combining these five costs with the fixed rectangle constant, then adding
higher-exponent load and dividing by the same branch's surviving mass in
(HG6), gives the table above. All 144 branches are evaluated. The refined
threshold-six maximum is

    Theta_nu(6) <= 321137/403528 < 4/5,                    (JC2)

again uniquely at `root1_same_other_column`, N=79. Seven of the nine
threshold maxima improve on the rectangle profile with (FD3); thresholds
8 and 12 retain their preceding values. The `joint_cost_hinge_refinement`
certificate field stores the normalized cost coefficients, the integer
numerator bounds, every full-height branch, and the maxima. All arithmetic
in its canonical verifier uses Python integers and fractions. The result
has the same full original 357-part-dividing-315 scope and arbitrary finite
11/13 heights, and supplies no unrestricted-tail or new Lean conclusion.

<a id="actual-deletion-vectors-and-a-common-full-height-law"></a>
## Actual deletion vectors and a common full-height law

For every family whose original 3/5/7 part divides 315, the construction
with C=40/31 admits the following simultaneous bounds, allowing arbitrary
finite 11/13 heights and arbitrary axis and point deletions:

    Gamma <= 591122424341/16497075000 < 35.831954,
    sup_test E_nu L <= 1175795/219961 < 5.345471,
    Theta_nu(6) <= 306627/391318 < 0.783575.                 (DV1)

These are bounds for one supported probability nu for each original
family. The proof retains its actual old deletion vector throughout
the mass, moment and hinge estimates. It does not extend the original
3/5/7 exponents or establish a general tail continuation.

<a id="exact-optimized-costs-of-an-actual-deletion-vector"></a>
### Exact optimized costs of an actual deletion vector

Choose the canonical modulo-45 survivor set S by the preceding
support-shrinking reduction. All subsequent statements concern this
chosen carrier and its actual mixed-seven classes. Let b(x) count
the distinct deleted nonzero seven digits over x in S, and put
N=sum_x(6-b(x)). Five original mixed-seven labels use at most five
of the six nonzero digits. Consequently a single digit y_star survives
over every x in S, including when labels are absent, redundant or
assigned to the already excluded zero digit.

For a complete old-315 test, separate its zero-seven block A and project
its positive-seven block onto a complete old-45 load B. At each x,
concentrating the nonnegative positive-seven increments gives

    sum_(surviving y) psi(L(x,y))
      <= (5-b(x)) psi(A(x)) + psi(A(x)+B(x)).

This holds for every increasing convex psi. Conversely, choose any
actual old tests A,B, and place every positive-seven test class at
y_star. CRT realizes these residues for their original distinct test
moduli, and equality holds at every x. Thus, for the uniform law mu
on this actual old survivor set,

    N sup_test E_mu psi(L)
      = max_A [sum_x (5-b(x)) psi(A(x)) + J_psi(A)],
    J_psi(A) = max_B sum_x psi(A(x)+B(x)).                  (DV2)

Effective old test cylinders suffice: replacing an empty test cylinder
by a nonempty one only increases its load. The maximizing A can differ
between costs, but b and mu are fixed. In particular, b is sufficient
for these optimized convex costs; it need not determine an individual
test histogram or the effect or legality of a later original deletion.

The attainable b vectors also have an exact finite description. For
each labelled cofactor d in {3,5,9,15,45}, choose its cylinder on S,
allowing the empty mask. Partition the five labels by their nonzero
seven digit. A block deletes the union of its old cylinders at one
digit; summing these block indicators gives b. Conversely any such
partition uses at most five digits and is realized by CRT. Inactive
labels can be included with empty masks. This represents every original
mixed-seven assignment without an irredundancy assumption.

There are respectively 27679, 28939, 28735, 25813, 25238 and 24971
different b vectors on the six canonical shapes, totaling 161375.
The experimental verifier reconstructs these sets both by cylinder
choices and set partitions and by successive labelled digit-union
updates, then compares the complete resulting sets. It does not use
an independently optimized b for the mass denominator.
