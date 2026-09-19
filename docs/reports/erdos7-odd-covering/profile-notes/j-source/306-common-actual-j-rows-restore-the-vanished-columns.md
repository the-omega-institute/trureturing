[Index](../../marked_head_profile.md) · [Actual J neighborhood](../136-a-whole-j-source-neighborhood-has-a-complete-labelwise-bound.md) · [Whole saturated comparison](299-the-complete-saturated-j-comparison-crosses403.md) · [Original covering nodes](298-retaining375-certifies-the-complete-heavy-cost.md)

# Common actual J rows and quantitative restoration of vanished columns

On the actual source domain below, one common late coordinate makes
every original inequality residual and absolute equality residual at
most100t in the existing244/251/256/264/288/296 matrices. This also permits
quantitative restoration of all4634 columns that vanish on the saturated
face. The complete298 covering-node error is at most613395.009550r
when the original row errors are at most r. These are source-row and
finite-objective results; full prefix, assigned-tail and remaining-basis
transport is still needed for a numerical J neighborhood.

Use the actual-source definitions and domain of 136:

    delta >= 0, qJ >= 1-delta,
    rho = S-S0 >= 0, t = delta+rho <= 1/1000,
    R = E5+E15+E5d+E15d+E3+omega <= rho+7delta/36 <= t.

Here Lambda is the actual old-coordinate raw source, mu its actual
survivor projection, V the complete projected virtual deletion and
W=V-(Lambda-mu)>=0, with W(1)=omega. The six defects are those of 132
with 136's replacement E3=z/90-V3(1). More explicitly, V5 and V15 are
the cofactor5 and cofactor15 families over every positive seven depth,
Vp and Va are the cofactor5^b and cofactor3*5^b families with b>=2,
and V3 is the cofactor3^a family with a>=3, again at all positive seven
depths. Their nominal capacities are h/25, h1/25, h/100, h1/100 and
z/90 respectively. Absent labels contribute zero actual deletion.

Fix the orientation from 71. The actual source labels5,15,45,25 force
distinct first-five slots P,A,B,Q; H is the remaining slot. Original45
is in a root1 cell L. Use 136/220's actual quantities

    ell = h/5-Lambda(H) <= 5E5,
    p=z-3/4, a=1/4-alpha1,
    b=1/4-sum_root1 beta, Delta=p+a+b <= 3delta/4,
    lambda=1/72-sum_root1 late <= delta/72.

All these quantities are nonnegative. The last one is the sum of the
complete original late labels' unused raw capacities when their
additional root1 deletions are assigned disjointly. It includes absent
labels and assignments outside root1. No disjointness of raw cylinders
is asserted. The source widths obey 136(JT5), particularly

    h <= 5/9, h1/(h1-h0) <= 3,
    eta0-1/18 <= delta/18, eta_c <= 1/9 for c!=0,
    sum_c |eta_c-eta*_c| <= delta/9.

**One late coordinate for every cell.** The original source135 has raw
capacity1/135 and assigned root1 mass at least1/135-lambda. It is thus
present and in root1. Slots P,A and cell(L,B) are already removed by
the original first source labels. In slot Q the original source25
removes one fifth of its full raw rectangle, losing at least1/675
from its capacity. In slot H its assigned mass is at most ell. Both
possibilities are excluded because

    lambda <= 1/72000 < 1/675,
    ell+lambda <= 5/1000+1/72000 < 1/135.

Consequently original135 lies in (M,B), where M is one of the two
root1 cells other than L; call the remaining cell N. This names the
actual source cell, without changing any test135 residue or any other
original label. Canonical coordinates are L=2,M=3,N=4.

Let yM,yN be the actual additional root1 late mass with five depth
b=1 assigned in (M,B),(N,B). Their full raw budget is1/90. The first
135 gives

    yM >= 1/135-lambda, yN <= 1/270,
    yM+yN <= 1/90,
    rB := 1/90-yM-yN <= 5lambda+LH,

where LH is the b=1 assigned root1 late mass in H. The last bound is
136(JT8); the yN bound holds since first135 lies in M and every other
b=1 late label has combined raw capacity1/90-1/135=1/270. Set

    theta=max(1/135,yM),
    uM=theta-yM, uN=1/90-theta-yN.

Then theta belongs to [1/135,1/90], uM,uN>=0 and uM+uN=rB. For uN,
if yM>=1/135 this is rB; otherwise use yN<=1/270. Thus the same
theta supplies both original cellwise B caps in 244 rows17/22,
with total positive subtraction error at most rB. Its existing
normalized variable is x=270*(theta-1/135), which belongs to [0,1].

To control every raw cell, use the actual five-coordinate unions
from 220. Let D5 be the complete pure5 deletion, Dalpha the root1
alpha deletion assigned after D5, R5=D5\P, and
R=(D5 union Dalpha)\(P union A). Write

    HQ=h0*|R5 intersect H|+h1*|R intersect H|.

The missing Q width is at most Delta+|R5 intersect H| on root0 and
Delta+|R intersect H| on root1. This gives a nodewise comparison:
pre-late raw mass in each cell is at most eta_c times its saturated
normalized table coefficient plus its root's Q error. Other source
deletions only lower that mass. In B/M and B/N subtract the actual
yM,yN just assigned above. The three actual H deletion pieces
(root0 earlier, root1 earlier, root1 late) are disjoint, so

    HQ+LH <= ell.

For the saturated absolute table cap_theta from 219, therefore

    sum_(c,s) [Lambda(c,s)-cap_theta(c,s)]_+
       <= delta/24+h*Delta+ell+5lambda
       <= 19delta/36+ell <= 6t.                    (1)

The width term is delta/24, because only eta0 can increase and the
normalized row0 coefficients sum to3/4. The delta/90 in 220 bounds
one column, not this whole25-cell sum. Formula(1) uses the complete
Q and B residuals once; they do not receive separate copies of ell.

**Actual deletion references and their errors.** Let q be the actual
pure5 complement measure on the five coordinate (restricted Haar5),
with q(1)=z. In particular q is not the fixed face slot measure.
For each complete original (a>=3,e>=1) label use weight
u_e=6/(5*7^e). If the present label is in root0, put its actual
ternary Haar cylinder into nu3. For a wrong-root or absent label put
any root0 cylinder of that same ternary depth into nu3, as a reference
only. Then

    nu3(1)=sum_(a>=3,e>=1) u_e*3^-a=1/90,
    P3=nu3 tensor q, P3(1)=z/90.

Split V3=Vgood+Vwrong by its actual ternary root. P3-Vgood is positive,
has mass E3+Vwrong(1), and is supported in root0. A root1 label of
nominal weighted ternary width d has actual mass at most(z-alpha1)d,
while its capacity deficit is at least alpha1*d. Removed-root labels
have zero actual mass. Thus

    Vwrong(1) <= ((z-alpha1)/alpha1)*E3 <= 3E3,
    ||P3-V3||TV = E3+2Vwrong(1) <= 7E3.           (2)

The ratio uses z<=3/4+delta/4 and alpha1>=(1-delta)/4 on the stated
domain. The normalization1/90 introduces no unpaid error: it includes
every absent/wrong original label through its dummy reference and is
exactly the nominal total defining E3. The norm is full signed-measure
variation, without a factor1/2.

The product-reference proof of 227(MT3--MT5) applies with the actual
J widths, as follows. For Vp use each present label's actual five
cylinder and any same-depth cylinder for an absent reference, obtaining
nu_p(1)=1/100 and Pp=eta tensor nu_p>=Vp. For Va retain each good root1
label's actual five cylinder and use a same-depth reference for every
wrong/absent label, obtaining nu_a(1)=1/100 and
Pa=(eta restricted to root1) tensor nu_a>=Va_good. Wrong-root mass
is at most(h0/(h1-h0))*E15d. Therefore

    ||Vp+Va-(Pp+Pa)||TV
       <= E5d+(2h1/(h1-h0)-1)*E15d
       <= E5d+5E15d =: B5.                       (3)

This uses only product domination, the complete original label sums,
h1>h0 and the ratio bound in 136(JT5). No K forced27, K late-source
location, saturated total, or fixed-H equality enters it.

Finally the shallow3/9 discrepancy, wrong/missing cofactor5/15
replacement losses and W give one positive error measure Xi with

    mu+V3+Vp+Va <= w*Lambda+Xi,
    Xi(1) <= B := delta+10(E5+E15)+omega <= 11t,   (4)
    w=1-[1_root0+1_cell1+1_H+1_(root1,H)]/5.

Explicitly, take Xi=Xi39+Xi515+W on the same actual old-coordinate
source. Xi39 is the positive part of the ideal-minus-actual shallow3/9
deletion density. Xi515 is the sum of the ideal H and root1-H section
measures for wrong or missing cofactor5/15 labels, retaining every good
label. Favorable actual wrong-slot deletions may be discarded. These are
positive measures, with masses respectively at most delta,
10(E5+E15), and omega, by136 section3. Subtracting the remaining virtual families, all
positive and disjoint in original label from the four retained
families, only improves the inequality. Add W once. In particular
mu<=w*Lambda+Xi holds on every measurable event, including every
original mask state, retained membership refinement and complement.
The same Xi is used throughout; its copies cannot be independently
optimized before their row prices are added.

**Every actual row of the existing finite matrices.** Embed all raw
and surviving variables as masses of their stated actual events.
Embed each independent profile as the point mass of its own actual
parent; retain the published dummy profiles for absent/source-null
tests. Put e3(c,s)=V3(c,s), e5(c,s)=(Vp+Va)(c,s), and use the one
normalized theta above in every inherited row. The following bounds
are positive inequality residuals and absolute equality residuals.

| Existing row family | Error bound | Reason |
|---|---:|---|
|244 raw25-cell caps|19delta/36+ell<=6t|(1)|
|244 raw group caps (cell0,cell1,root1)|at most t|bounds below|
|All exact profile normalizations, actual partition inequalities, raw CRT intersections, unit rows|0|actual memberships and Haar domination|
|244 raw mass=1/4|delta/2|136 section5|
|244 survivor mass=3/20|rho+331delta/360<=t|D=s-C/5 and71|
|All raw-to-survivor cell/mask/state/complement rows|B<=11t|(4)|
|244 coarse e3+e5+mu<=w*Lambda rows|B<=11t|(4)|
|244 e3 root1 zero rows|3E3<=3t|(2)|
|244 e3 root0 slot total=q*_s/90|4E3+(5delta/4+4ell)/90<=5t|P3-Vgood positive and actual q slot comparison below|
|244 e5 cell totals=eta*_c(1+ROOT(c))/100|B5+delta/450<=6t|(3), actual width comparison|
|244 eight marked27/81 deletion lower rows|B+B5+delta/900<=17t|(3),(4), unthinned cells below|
|244 two marked25/75 deletion lower rows|B+7E3+(delta/4+2ell)/90<=19t|(2),(4), actual q cylinders below|
|25/75/125/225 descendant profiles|at most delta/450|actual eta exceeds eta* only in cell0; smallest five-depth denominator25|
|27/81/135 normalized pretable profiles|at most(Delta+4ell)/27<=t|136(JT9), interpreted before late removal below|
|244 survivor caps25,27,75,81 and251/264 cap125|100t|136's complete individual-label inequality; same original test residues|
|251/264 survivor caps135,225;288 cap375|0|mu<=Lambda<=product Haar|
|288 new375 descendant profiles|delta/2250|actual eta and five-depth denominator125|
|296 fresh parent25 global raw cap1/50|delta/450|h/25<=1/50+delta/450|
|296 fresh parent27 global raw cap1/36|delta/108|z/27<=1/36+delta/108|

Here all row coefficients and the right sides are the unchanged
published ones, including signed profile coefficients, w in[2/5,1],
the two opposite theta coefficients +/-1/270, and signed equalities.
Every coefficient lies in[-1,1], and every right side in[0,1]. In244
the587 inequalities partition into132 raw rows, one theta upper row,
400 atom density rows, four survivor caps,25 coarse deletion rows,
15 root1 e3 zero rows and10 marked lower rows. Its16 equalities are
four profile normalizations, two total masses and10 deletion totals.
The264 extension adds75 profiles,800 partition rows,2800 state
density rows,400 complement density rows, three survivor caps,
12 old/new CRT rows, three new/new CRT rows and6531 unit rows,
giving11211 inequalities and19 equalities. The288 extension adds
12800 four-per-atom rows,25 profiles, one survivor cap, seven CRT
rows and6410 unit rows, giving30454 inequalities and20 equalities.
The296 extension adds6400 partitions,50 profiles, two global caps,
16 old/new CRT rows, one new/new cap and19210 unit rows, giving56133
inequalities and22 equalities. The251/256 pair extension is obtained
by the same three-state partition/density/profile/CRT row types.
Nothing is normalized by a possibly small atom mass. Every variable
remains nonnegative and at most1. The following details discharge the
non-partition entries of the table.

The three raw group caps have errors at most delta/18+delta^2/72,
delta/36 and2delta/9, respectively. The first two use eta0*z and
eta1*z. For root1 use

    Lambda(root1)
       <= (1/3)*(1/2+delta/2)
           -(1/9-delta/18)*(1/4-delta/4)
           -(1-delta)/72
       =1/8+2delta/9-delta^2/72.

For the survivor total, the already established absolute bounds
|s-1/4|<=delta/2 and |C-1/2|<=83delta/72 give
|D-3/20|<=263delta/360. Add0<=S0-D<=17delta/90 and S-S0=rho.

Write p_s for actual pure5 deletion in slot s. Then
p_A<=a, p_B<=b, p_H<=2ell, and the actual q slot vector satisfies

    q_P=0, q_A=1/5-p_A, q_B=1/5-p_B,
    q_Q=3/20+p+p_A+p_B+p_H, q_H=1/5-p_H.

Hence ||q_slots-q*_slots||1<=5delta/4+4ell. Root0 slot totals of
P3-Vgood differ by at most its total mass E3+Vwrong(1)<=4E3,
which proves the e3 equality row estimate without replacing actual q
inside P3. For a depth2 five cylinder F in A,B or H, q(F)>=1/25-p_s.
Thus the reference lower1/2250 for a test25, or for a test75 in
root0, loses at most(delta/4+2ell)/90; use(2) and then(4). For a
test75 in root1 the relevant root0 profile coefficient is zero.

The27/81 marked lower rows deliberately omit thinned cell0. On each
other cell eta is Haar3 minus a positive measure; its total missing
Haar over cells1..4 is at most delta/18. In Pp+Pa the five total
weight is(1+ROOT(c))/100<=1/50. The individual marked reference
therefore loses at most delta/900 from its nominal coefficient;
then apply(3) and(4). If the original test is absent or source-null,
the published dummy parent is cell0, so these particular coefficients
and actual marked masses vanish. No Haar event at a false parent is
introduced.

For every normalized pretable profile, the source *before late
removal* has a five-section depending only on its parent cell. The
root-wide actual deletion sets in 116(S4)/136(JT9) bound that section
by K(c,s)+1_(s=Q)*(Delta+4ell). Restricting to an actual ternary
depth3 or depth4 test cylinder multiplies by its ternary mass,
bounded by1/27 or1/81. This proves the claimed profile bound for
the original tests27,81,135 and the independent fresh parent27 in296.
It does not infer a subcylinder bound from a coarse cell marginal.

The288 added375 rows have four entries per old atom: new raw mass
below old raw, new survivor below old survivor, and survivor density
rows for the375 membership and its complement. The first two are
exact and the latter two use(4) on those actual disjoint events.
Its profile, cap, seven CRT intersections and normalization are
exactly the corresponding table cases. They share the inherited
theta without any extra dependence on it.

The296 added states refine each actual old atom and375 bit by the
three nonempty memberships in the independent fresh parent25 and27
events. Their partition inequalities are exact, with the fourth
state as complement. The two sets of25 profiles and the two global
raw caps are bounded in the table. Its sixteen old-label CRT rows
and joint fresh-parent cap1/675 are exact. These fresh parents need
not match any original retained25/27 residue.

These estimates give one concrete actual embedding with *every* inequality residual <=100t and every absolute equality
residual <=100t in each of244,251/256,264,288 and296. The dimensions
include all12941 columns of288 and all32151 columns of296. This is
a rowwise uniform bound, not a claim that the sum of all residuals
is <=100t. All row prices must be combined on the common variables
delta,E5,E15,E5d,E15d,E3,omega (or safely bounded by100t times the
full sum of absolute prices).

**Restore the original vanished columns with their actual masses.**
Let r>=0 bound every original288 inequality residual and absolute
equality residual, and let x>=0 contain all12941 original coordinates.
The established298 induction consists of2645 oriented zero-right-side
rows. If such a row has positive coefficients a_j and negative coefficients
-a_i, every negative coordinate has already received a bound x_i<=b_i*r.
Discarding its other nonnegative terms gives, for each newly bounded j,

    x_j <= b_j*r,
    b_j = (1+sum_(negative i) a_i*b_i)/a_j.

An equality can use either orientation because its absolute residual is
bounded. An inequality retains its original orientation. Applying exactly
the original induction gives4634 bounds with

    max_j b_j=17, sum_j b_j=56866/5.

None of these actual coordinates is set to zero. For a covering dual with
nonnegative inequality prices y and free equality prices z, the perturbation
price of its zeroed objective is r*(sum y+sum|z|). The discarded positive
objective coefficients must then be restored as well.

For the complete heavy function H(v)=sum_(k=1..8) a_k*(v-k)_+, the full
slope is L=sum a_k=403/8. The original finite head satisfies1<=b<=6;
mask counts q are0..4; each of the two independent seven-depth counts m,e
is0..4. Let g(v,m,e) be the original weighted complete raw-seven increment.
Its coefficient is nonnegative, increasing in v, and at most

    L*(6*5/35+6*5/245+1/245)=241L/245<L.

The six original physical objective types are

    X: g(b+q),                 Y: H(b+q),
    OU:g(b+q+n)-g(b+q),       OV:H(b+q+n)-H(b+q),
    NU:g(b+q+n+1)-g(b+q+n),   NV:H(b+q+n+1)-H(b+q+n).

Here n is the original membership count, at most3, so every argument is
at most14. The141 remaining profile/control coefficients are zero.
For each type and q,n, maximize this exact coefficient over the containing
finite domain1<=b<=6 and0<=m,e<=4; call the result M_j for a column of
that type. This also dominates every coordinatewise maximum used in a
covering node. It need not be attained by one actual configuration.

The full restored price is

    Rzero=sum_(4634 columns j) b_j*M_j
         =1866086460287338944252337/3851791904442532050
         <484472.294087.

All981 distinct covering duals used by1177 nodes give

    Pcover=max(sum y+sum|z|)
      =375573528414630698967865160948169578054701/
       2913167994208453627395750000000000000.

Therefore every one of those original finite covering objectives, with
its fixed numerical face-tail constant added, is at most

    543/100 + Ccover*r,
    Ccover=Pcover+Rzero
      =1786922709626849452590071419103169578054701/
       2913167994208453627395750000000000000
      <613395.009550.

All50 full seed duals are also priced; their maximum is less than97428.136422
per r and requires no zero-column restoration. Substituting the actual
row result permits r=100t in these finite-objective inequalities.

The numerical face-tail constant in the preceding display has not been
asserted to bound the off-face actual omitted tail. It is retained only
to express the established finite-objective base value. Likewise these1177
nodes cover only their original residual leaves; original analytically
pruned branches and own-bound alternatives still require their separate
prices. A full neighborhood requires those prices, all assigned tail
increments, the remaining source observations and the signed consumer.

The [exact checker](../../frontier/j-source/j_actual_rows_zero_restoration.py) constructs
the unchanged original288 rows, propagates every original zero-row bound,
uses the existing dual codec, checks all original coefficient categories,
and evaluates the shared-defect arithmetic. Its
[certificate](../../certificates/source_norms/j-source/j_actual_rows_zero_restoration.json)
retains the full bound for each restored coordinate. The all-height
source-measure arguments above were independently audited; arithmetic
checks do not replace them. An independent reconstruction of all five
matrix sizes and an independent reconstruction of the zero-column and
dual prices also passed. No LP was solved or full prefix scan replayed.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j-source/j_actual_rows_zero_restoration.py --check
```

These are ordinary mathematical results and exact rational calculations.
No numerical J radius, global join, new Lean verification or unrestricted
Erdős7 result is asserted.
