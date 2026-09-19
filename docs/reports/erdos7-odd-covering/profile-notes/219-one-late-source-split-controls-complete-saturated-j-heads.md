[Index](../marked_head_profile.md) · [Whole J source](130-the-whole-j-face-forces-source-anti-alignment.md) · [Complete seven bridge](201-two-more-seven-labels-and-selected-intersections-control-both-heavy-costs.md)

# One late source split controls complete saturated J heads

There is a complete hinge interface on both actual saturated J faces.
It retains one actual raw source, its survivor, the mandatory late
source split, all independent original test labels and every infinite
exponent tail. The first three complete scans give

    integral(A-4)_+ <=29483/147000
                     =0.20056462585034013...,

    Cost0 <=772380280559124323560020499
             /127120057929096158286360000
           =6.075990627615473...,

    Cost16<=802051869914440232698722784579
             /165176625271619320673339025000
           =4.855722585417472... .

These are saturated-J bounds, with source mass1/4 and survivor
mass3/20. The source LP is exact for a containing relaxation, not
for the set of realizable covering families. No new52-cost numerator,
complete denominator, off-face transport, global K, Lean verification
or unrestricted Erdos7 resolution is claimed.

## 1. Absolute source caps retain the mandatory late mass

Use the first J face of130, with

    ROOT=(0,0,1,1,1), eta=(1/18,1/9,1/9,1/9,1/9).

Let L be the first-beta cell and M the distinct cell containing the
late source atom1/135. Root1 symmetry permits the canonical labels
(L,M,N)=(2,3,4). The complete late source mass with five-depth1 is
1/90; saturation puts it in slot B outside L. Therefore its two cell
masses are

    yM=theta, yN=1/90-theta, 1/135<=theta<=1/90.

The remaining deeper-five late mass is1/360. It and the optional
beta losses can be discarded when forming an upper cap envelope;
the mandatory B-column loss is retained.

In slot order(P,A,B,Q,H), the absolute raw cap rows are

    cell0: (0,1/90,1/90,1/120,1/90),
    cell1: (0,1/45,1/45,1/60,1/45),
    L:     (0,0,0,1/90,1/45),
    M:     (0,0,1/45-theta,1/90,1/45),
    N:     (0,0,1/90+theta,1/90,1/45).             (JH1)

The first two row sums equal their actual budgets1/24 and1/12.
The root1 caps sum to2/15, whereas the actual root1 budget is1/8.
The excess is precisely1/120. Each positive root1 cap is at least
1/90 throughout the theta interval.

For any nonnegative25-rectangle coefficient array z, define S as
the eight positive root1 entries in(JH1). The exact relaxed source
LP is therefore

    U_theta(z)=sum_(c,s) cap_theta(c,s)*z(c,s)
               -(1/120)*min_((c,s) in S) z(c,s).  (JH2)

Indeed, fill every cap and remove1/120 from a least-priced root1
entry. That entry has sufficient capacity. Conversely any feasible
full-budget vector removes the same total amount, at price at least
the minimum coefficient. Nonnegativity permits filling the budgets
also when the LP constraints are written with inequalities.

The minimizing coefficient is independent of theta. Thus

    U_theta(z)=constant+theta*(z(N,B)-z(M,B)).     (JH3)

This is an affine formula on the entire interval, not interpolation
of sampled LP optima. It remains an upper for every actual J source;
no realizability of the relaxed optimizer is needed.

## 2. The J survivor supplies two arbitrary-head corrections

The four shallow forbidden families give

    w(c,s)=1-[1_(c<2)+1_(c=1)+1_(s=H)
                            +1_(c>=2,s=H)]/5.    (JH4)

Its minimum is2/5. This is the J density, distinct from the K density.
For an arbitrary nonnegative head H(c,s), put

    q=(0,1/5,1/5,3/20,1/5),
    C3(H)=sum_s (q_s/90)*min(H(0,s),H(1,s)),
    C5(H)=sum_c eta_c*(1+1_(c>=2))/100
                                      *min_s H(c,s). (JH5)

The complete pure3deep forbidden deletion is supported in root0,
and130(J5) gives its exact slot marginal q/90. This proves the first
lower bound in(JH5) without forcing forbidden27 into either cell.
In particular the K forced27 rule is not used.

The distinct forbidden families5^b and3*5^b, b>=2, have combined
cell marginal eta_c*(1+1_(c>=2))/100. This follows from their complete
geometric sums and saturation of every original cofactor cap.
It proves the second lower bound. These two families are distinct
from each other and from the four shallow families. At saturation
the actual deleted measure equals the sum of virtual deletions, so
their contributions add on the same source even if their old
coordinate projections overlap. Consequently

    integral H dmu <= U_theta(w*H)-C3(H)-C5(H).   (JH6)

This arbitrary-head correction is available to subsequent square or
factorial consumers. Such consumers still need their own complete
head and tail decompositions; no new square bound is inferred here.

## 3. Selected operators use normalized coefficients

For deep-ternary cylinders, use the normalized source table pbar,
not the absolute caps in(JH1):

    pbar(0,.)=pbar(1,.)=(0,1/5,1/5,3/20,1/5),
    pbar(L,.)=(0,0,0,1/10,1/5),
    pbar(M,.)=pbar(N,.)=(0,0,1/5,1/10,1/5).

Here pbar is the130 table divided by eta_c, before optional deeper
losses. Dropping the mandatory late loss in these selected-cylinder
upper operators only enlarges the bound. Separately define

    E(c,s)=eta_c
           *1_(s!=P)*1_(not(c>=2,s=A))*1_(not(c=L,s=B)).

For nonnegative z, the valid raw-source operators are

    P_(a,0)(z)=3^-a*max_c sum_s pbar(c,s)*z(c,s),
    P_(0,b)(z)=5^-b*max_s sum_c E(c,s)*z(c,s),
    P_(1,b)(z)=5^-b*max_(r,s)
                             sum_(ROOT(c)=r) E(c,s)*z(c,s).

Apply these at the independent original labels25,27,75,81. Their
constant-function checks are respectively

    P25(1)=1/50, P27(1)=1/36,
    P75(1)=1/75, P81(1)=1/108.                   (JH7)

Using the absolute raw caps in the first operator would multiply by
eta twice and produce an invalid upper. The implementation keeps
these two tables separate and checks(JH7).

The same raw source is dominated by product Haar measure. Therefore
its actual mixed-cylinder intersections have caps

    Lambda(27 intersect25), Lambda(27 intersect75)<=1/675,
    Lambda(81 intersect25), Lambda(81 intersect75)<=1/2025.

The selected-increment telescoping and the one-/two-observation
bounds of201(EP7)--(EP13) consequently apply with these J operators.
Each label keeps its own original residue; no forbidden, source or
test residues are identified.

## 4. Both complete tail partitions remain explicit

Retain the original six-label head

    B=1+I3+I9+I5+I15+I45.

After removing those labels,130's complete zero-seven cap series is

    R0=11/360+13/600+1/60+1/180+1/72=53/600.

The1/180 is the9*5^b tail after removing45 from its complete1/36
category. Successively peel25,27,75,81, whose assigned caps are

    13/750, 11/540, 1/75, 11/1620.

The complete remainders are

    (R0,R1,R2,R3,R4)
      =(53/600,71/1000,1367/27000,1007/27000,2471/81000). (JH8)

For threshold t use kt=min(t-1,4). Each original zero-seven label
occurs in its selected prefix or exactly once in Rkt.

The complete nonunit positive-seven cap is1/10. The depth-one
labels21,35,63,105 have old-coordinate raw caps

    1/8,1/10,1/12,1/15,

and each assigned seven coefficient is6/35. Thus the two- and
four-projection omitted cap remainders are

    Z2=1/10-(6/35)*(1/8+1/10)=43/700,
    Z4=Z2-(6/35)*(1/12+1/15)=1/28.                (JH9)

These are exact remainders of a proved nonnegative cap series. They
are not obtained by subtracting an upper bound from unknown actual
mass. The checker reconstructs the complete old-cofactor cap sum1/2.

For the independent retained projections, let m be their count on a
rectangle, with0<=m<=2 or0<=m<=4. Keep every unit7^e label. The same
complete bridge as201 is

    g_(t,m)(v)=1/[5*7^max((t-v)_+-m,0)]
                  +(6/35)*max(m-(t-v)_+,0),
    f_t(v;c,s)=w(c,s)*(v-t)_++g_(t,m(c,s))(v).

Since w>=2/5>6/35, this is increasing and integer-convex, with exact
affine continuation. All finite transitions and their continuation
are checked before the layout scan.

## 5. One theta controls both complete bounds

For a nonzero nonnegative rational combination

    F(A)=sum_(t=1..8) a_t*(A-t)_+,

fix one original six-head layout and all four independent seven
projections. Define

    H(c,s)=sum_t a_t*(B(c,s)-t)_+,
    Phi_p(c,s)=sum_t a_t*f_(t,p)(B(c,s);c,s).

Let V_(i,p) be201's complete selected-increment upper with the J
operators in section3. For p=2,4, a bound on the same actual test is

    Fp(theta)=sum_t a_t*(Rkt+Zp)
              +U_theta(Phi_p)-C3(H)-C5(H)+sum_i V_(i,p). (JH10)

Only U_theta depends on theta, so both Fp are affine. The complete
uniform upper is

    max_(layout,projections) max_(theta in[1/135,1/90])
                                      min(F2(theta),F4(theta)). (JH11)

The minimum of two affine functions is generally concave piecewise
affine. Its maximum may lie at their intersection. The checker
therefore considers both endpoints and the exact rational crossing
when it lies in the interval. Parallel and identical lines need only
the endpoints. An independent check includes an interior maximizer;
no endpoint-only rule is used for the minimum.

The original12500 layouts and500 independent four-projection tuples
give6250000 containing branches per objective. A branch is skipped
only when its already-uniform max_theta F2(theta) is no larger than
the current attained maximum of the comparison function. All50
additional63/105 projections are then bounded. This pruning never
chooses theta separately for the two bounds being minimized.

Root1 permutations preserve the entire test inventory and act
transitively on the ordered distinct cells(L,M). The root0 cell
exchange transports the second J face together with the source,
density, corrections and projections. Hence no additional face or
source-label branches are omitted by the canonical choice.

## 6. Exact scans, consumer boundary and reproduction

The AP13, heavy0 and heavy16 scans expand22,12764 and12948 of the
125000 old two-projection branches, respectively. Including the
500-projection initial head, they evaluate1600,638700 and647900
four-projection branches. Every skipped branch has a stored uniform
upper no larger than the final maximum. The evaluated branches in
these three scans have no strict interior crossings; the crossing
rule remains part of the interface and is required for other inputs.

The AP13 comparison maximum uses

    layout=(1,4,2,1,2,4,2),
    (r21,s35,c63,r105,s105)=(1,4,4,1,4), theta=1/90.

Both heavy comparison maxima use

    layout=(1,4,4,1,4,4,4),
    (r21,s35,c63,r105,s105)=(1,4,4,1,4), theta=1/90.

These are maximizers of the containing comparison function. They
are not claimed to be attained by actual covering families.

For each original heavy cost f, the helper verifies the exact
identity f(v)=f(1)+sum_t a_t*(v-t)_+ at every finite transition and
on the entire eventual affine tail. The constant f(1)*3/20 is added
separately. The known complete J mean bound16/25 remains available;
its hinge1 consequence49/100 is another valid whole-domain bound.
The reported new numbers are not comparisons to K-face bounds or a
claim of improvement to an existing complete J/global52-cost ratio.

For each objective, eight independent fractional branch evaluations
and two maximizing-branch evaluations check the integer compiler.
The source LP is also checked by a separate feasible primal and
matching dual, with rational scaling valid even at an interior theta.
The exact certificate records all complete constants, source tables,
branch digests, pruning counts, the selected labels, and witnesses.

```sh
python3 docs/reports/erdos7-odd-covering/frontier/j_face_coupled_seven_heads.py --check
```

All infinite exponent tails remain in(JH8)--(JH10). Positive finite
prefix arguments pass to the full original test by monotone
convergence. The uniform geometric first-moment tails from130 justify
the same statements for actual finite families tending to either
saturated face. Extending this interface away from saturation and
assembling the remaining cost and survival terms are separate
mathematical obligations.
