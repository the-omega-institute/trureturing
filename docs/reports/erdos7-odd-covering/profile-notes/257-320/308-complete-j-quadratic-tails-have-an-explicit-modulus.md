[Index](../../marked_head_profile.md) · [Actual source rows](306-common-actual-j-rows-restore-the-vanished-columns.md) · [Analytic prefixes](307-original-j-prefixes-and-complete-tails-have-an-explicit-modulus.md)

# Complete mean and quadratic source moduli on the same actual J source

The complete mean and six second-order observations used by299 admit
the explicit moduli below, on the same actual source as306 and307.
The original independent test labels, complete tails, retained
matrix objectives and single common theta are preserved. These are
ordinary mathematical proofs with exact rational checks.

Use136's domain: delta>=0, qJ>=1-delta, rho=S-S0>=0,
t=delta+rho<=1/1000. Lambda is the actual raw old-coordinate source,
mu the actual survivor, and S=mu(1). Retain all original independent
test labels and the common theta in[1/135,1/90]. Let

    ell<=5t, Delta<=3delta/4, beta=Delta+4ell<=83t/4,
    sigma=delta/18,
    mu+V3+Vp+Va<=w Lambda+Xi, Xi(1)<=11t.

All inequalities include t=0. Every complete nonnegative series below
extends finite original families by monotone convergence; no common
null set across all test layouts is asserted.

## 1. Actual consumers and exact mass

Only18 of299's34 basis entries occur with nonzero coefficient in its59
fixed envelope proofs. The non-hinge entries needed here are:

| Observation | Controlling committed source | Number of consumer envelopes |
|---|---|---:|
|mass|actual S; face value3/20|38, including36 negative coefficients|
|mean|219/130, transported by136(JT2)|38|
|square|282|8|
|factorial5|294|1|
|cost48|282|1|
|cost49|282|7|
|factorial2|282|2|
|factorial3|282|2|

The other used entries are hinge4/cost0/AP11-0/AP11-1/AP11-2 and
hinge2/hinge3/hinge5/hinge6/hinge8. Their controlling sources are
296/298/292/266/249 and286/286/286/286/290 respectively.

The exact mass bound supplied by the actual-row lemma is

    |S-3/20| <= rho+331delta/360 <= t.                   (Q1)

A fixed whole-integer envelope with mass coefficient c0 transports as

    int F(A)dmu <= c0*S +sum_(i!=mass) c_i*(B_i+omega_i(t)).

Only c0 can be negative. Keep c0*S until all consumer coefficients have
been combined. If an isolated error bound is needed, pay |c0| times(Q1);
replacing S by an upper bound when c0<0 reverses the inequality.

## 2. The complete mean already has its modulus

136(JT2) proves, for each complete original own-load test A,

    int A dmu <= S+49/100+119delta/360+B1(100t),
    B1(e)=sum_(a,b>=0,a+b>0)min(e,3^-a*5^-b).

Combining(Q1) gives

    int A dmu <=16/25+rho+5delta/4+B1(100t)
               <=16/25+5t/4+B1(100t).                 (Q2)

The complete mean16/25 in219 comes from130's zero-seven nonunit
cap sum17/50, positive-seven cap3/20 and unit mass3/20. Thus(Q2)
does not require a new finite-head argument or omitted-tail estimate.

## 3. A complete second-order clipping function

Define

    B2(e)=sum_(a,b>=0)(2a+1)(2b+1)min(e,3^-a*5^-b),
    B2(0)=0.                                          (Q3)

For two ordered old labels, the number with ternary maximum exponent a
is2a+1, and analogously2b+1 for the five exponent. Consequently B2
dominates the sum of clipped LCM errors for every subcollection of
ordered label pairs, even when the unit and diagonal are included.
Its untruncated Haar sum is

    sum_(a,b)(2a+1)(2b+1)3^-a5^-b=3*(15/8)=45/8.

For e>0 there is an exact finite correction formula

    B2(e)=45/8-
      sum_(3^-a5^-b>=e)(2a+1)(2b+1)(3^-a5^-b-e).

For any integers A,B>=0 a convenient full-tail upper bound is

    B2(e)<=e(A+1)^2(B+1)^2
       +(15/8)(A+2)/3^A+3(4B+7)/(8*5^B).            (Q4)

Indeed the exact one-coordinate weighted tails are
(A+2)/3^A and(4B+7)/(8*5^B). A union bound on the two tails gives(Q4).
This proves B2(e)->0 as e->0 and gives a rational evaluation protocol.
No exponent cutoff is interpreted as removing the tail.

## 4. Raw complete cylinder caps have multiplicative drift

Let Cr(a,b) be258's original raw cap:

    Cr(0,0)=1/4, Cr(1,0)=1/8, Cr(2,0)=1/12,
    Cr(a,0)=(3/4)3^-a for a>=3,
    Cr(a,b)=(1/2,1/3,1/9)_a 5^-b for a<=2,b>=1,
    Cr(a,b)=3^-a5^-b for a>=3,b>=1.

For every independently chosen actual raw cylinder,

    Lambda(C_(a,b))<=Cr(a,b)+9delta*3^-a5^-b.          (Q5)

For the unit use|Lambda(1)-1/4|<=delta/2. For a root, root0 has
h0*z<=1/8+delta/12+delta^2/72, while the common-row proof gives
root1<=1/8+2delta/9. A cell has cap<=1/12+delta/36:
cell1 uses eta1*z; cell0 and the root1 cells remain strictly below
this bound on delta<=1/1000. For pure-three depth>=3 use
z<=3/4+delta/4. For pure-five cylinders use h<=1/2+delta/18.
Root-five and cell-five caps1/3 and1/9 remain valid because
h1<=1/3, h0<1/3 and max eta_c<=1/9. Mixed deep cylinders retain
their Haar cap. These inequalities imply the conservative factor9
uniformly. A cylinder and its original label are not identified with
any other independently chosen test.

## 5. Transport the original raw prime paths directly

For every nonnegative25-cell function g bounded by Z, the common-row
clipping argument gives

    int g dLambda <= raw_source_lp_face(g,theta)+7Zt.   (Q6)

The pre-late normalized ternary table changes positively only by
beta in slot Q in each parent cell. The absolute descendant-five
table changes positively by at most sigma, all in cell0. Hence265's
raw path coefficients, for its original head1<=B<=6, obey

    A3_actual<=A3_face+6beta, c3_actual<=c3_face+beta,
    A5_actual<=A5_face+6sigma, c5_actual<=c5_face+sigma.

These are bounds for every original deeper cylinder, derived from the
pre-late five sections and Haar domination, not from coarse marginals.
The unchanged discounted path proof applies to these upper coefficients.
Its exact closed expressions yield path drifts

    pair3:13beta/36, pair5:5sigma/16,
    square3:7beta/9, square5:27sigma/40.              (Q7)

The residual raw head/tail cross uses the five geometric coefficient
weights(1/18,1/20,1/20,1/20,1/72). For any0<=g<=Z its drift is at most

    Z*(beta/18+3sigma/20)<=2Zt.

In the pair expression, the finite head has coefficient at most15;
in the square expression it is at most36. The remaining raw LCM caps
use(Q5). Their complete series is bounded by45/8; for a square the
remaining twice-pairs plus diagonals are one subcollection of ordered
pairs. Therefore every original same-head bound from265 transports as

    P_actual(B,theta)<=P_face(B,theta)+200t,
    Q_actual(B,theta)<=Q_face(B,theta)+400t.           (Q8)

Explicit sufficient totals are

    P:105+12+13*(83/4)/36+5/(18*16)+405/8 <200,
    Q:252+24+7*(83/4)/9+27/(18*40)+405/8 <400.

The path terms replace precisely their original pure-prime pair,
cross and diagonal subseries. One does not subtract an old numerical
saving from a newly bounded whole moment. Taking the same finite
completion maxima and common-theta secants preserves(Q8).

In276's conditional PZZ construction, the complete weights sum to
sum u_e=1/5 and sum beta_e=1/30. Hence its full conditional expression,
including every depth>=3, has error at most

    200t/5+400t/30=(160/3)t.                        (Q9)

The first and second depth original projections remain separate.

## 6. The complete unselected factorial tail

Use282/294's original head B, h=(B-k+1)_+, 0<=h<=6, and the original
decomposition into unselected old O and positive-seven Z labels.
All selected retained terms remain in the finite actual matrix body.

For the remaining h*O term, the raw coefficient drift is at most12t.
For one omitted cylinder C of modulus d, the Xi error is at most
6Xi(1), and the actual weighted survivor integral is at most6/d.
Since the raw reference term is nonnegative, clipping these two
estimates before summing gives the further bound6B1(100t). Thus

    error(h*O)<=12t+6B1(100t).

For remaining h*Z, the entire raw six-mask family has coefficient
sum at most6/5; its finite head uses(Q6), and its complete old tail
has weight1/5. Its error is at most

    (6/5)*6*7t+(1/5)*6*2t=264t/5<=54t.

For remaining POO,136's original survivor cap at every LCM differs
by at most min(100t,1/lcm). Summing only the unselected unordered
pairs costs at most B2(100t)/2.

For remaining POZ, sum(Q5) over the complete original old/old
cofactor pairs and every positive-seven depth. Its error is at most

    (9delta/5)*(45/8)=81delta/8.

For PZZ use(Q9). The selected POO and POZ payments are omitted from
their respective sums exactly once; the remaining sums are positive
subseries. No actual intersection is charged to another label.
Together, per unit factorial coefficient, these give the conservative
complete-tail modulus

    T_quad(t)=150t+6B1(100t)+B2(100t)/2.             (Q10)

The unrounded linear sum is66+81/8+160/3<150. Source294 changes
the finite retained head and selected raw slope, while its unselected
cross/pair payments are exactly those of282. Thus(Q10) applies to
both sources without changing their exact retained formulas.

## 7. Analytical factorial prefixes and one common bound

For any nonnegative25-cell g bounded by Z, the actual-row inequality,
the P3/Pp/Pa total-variation comparisons and the actual q-slot vector give

    int g dmu <= raw_source_lp_face(wg,theta)
                 -deletion_correction_face(g)+31Zt.

The paid constants are7t for raw clipping,11t for Xi,7t for V3,
5t for Vp+Va, plus(5delta/4+4ell)/90+delta/450 for the reference
slot/width replacements. Their sum is at most31t. All signs agree
with subtraction of a valid actual lower deletion bound.

In the original analytical `QuadraticDepth.parts`,
g=Phi_k(B)<=15, so the factorial head costs at most465t. Together
with(Q10), each analytical factorial part costs at most

    615t+6B1(100t)+B2(100t)/2.

This is the actual formula used by the original two/four/six-projection
pruning and pure-factorial pruning. Retained-head strengthening changes
the LP objective; its old analytical fallback keeps the formula above.
The retained LP body instead uses the common100t row bound directly.

Write each original target as

    F(v)=a+sum_j a_j(v-j)_+ +f*Phi_k(v), A=sum_j a_j.

| Target |a|A|f|k|
|---|---:|---:|---:|---:|
|square|1|1|2|1|
|cost48|0|5|2|3|
|cost49|0|3|2|2|
|factorial2|0|0|1|2|
|factorial3|0|0|1|3|
|factorial5|0|0|1|5|

Let D_F be the maximum sum of absolute row prices of the *unscaled
complete original-objective* duals used by the fixed source cover,
including all retained fallback certificates. Prices of equality rows
are taken in absolute value; inequality prices are nonnegative.
Their full original columns must be preserved. A parameter-free bound
valid across the analytical and LP branches is

    int F(A_test)dmu <= B_F+omega_F(t),
    omega_F(t)=(100D_F+256A+615f+a)t
              +(A+6f)B1(100t)+(f/2)B2(100t).       (Q11)

The LP tail hinge error A[B1(100t)+37delta/180] is smaller than the
analytical hinge allowance used here. The signed common theta is a
single actual matrix variable; it receives no independent endpoint
choice. The constant term a*S uses(Q1).

For all six observations one convenient common bound is

    omega_quad(t)=(100D+2600)t+17B1(100t)+B2(100t),
    D=max_F D_F, omega_quad(0)=0.                   (Q12)

The largest coefficient256A+615f+a in the table is2510<2600. This is an
explicit vanishing modulus once the existing finite bank price norm D
has been read; it requires no optimization or scan replay. The original
fixed branch coverage remains valid because every original branch proof
has its own transported inequality with this common error.

The [neighborhood certificate](../../certificates/source_norms/j-geometry/j_explicit_actual_neighborhood.json)
binds the exact299 input and prices a containing superset of23 historical J banks with22850
duals, including282/284/294 and their inherited banks. Its exact maximum
is4331247056452228979446980667963962832663 /
97105599806948454246525000000000000, with ceiling D=44604. The two298
banks are excluded there; they are not needed for these six quadratic
observations. Thus a numerical common coefficient in(Q12) is

    omega_quad(t)=4463000t+17B1(100t)+B2(100t).        (Q13)

The price inventory is not a new dual-feasibility replay. It reads the
existing committed source certificates in original mathematical units.

## 8. The historical101-column matrix has the same row interface

The101-column source model has66 inequalities and19 equalities.
All66 inequalities and11 equalities are aggregated rows of244's
original model, so306 gives their100t residual bound. The eight
additional equality indices are0,1,2,14,15,16,17,18. The first three
fix the raw group totals1/24,1/12,1/8; each absolute error is at most
delta/2 by the complete coarse-table bound.

For the five H-slot equations, write

    ell_c=eta_c/5-Lambda(cell_c,H)>=0, sum_c ell_c=ell.

Each absolute error is at most

    ell_c+|eta_c-eta*_c|/5
      <=ell+delta/45 <=(226/45)t <=6t.

Consequently these historical branches also use the unchanged100t
row budget. Their duals are taken in original objective units, with
absolute equality prices, and are included in the complete inventory.

The [numerical neighborhood](309-an-explicit-actual-j-neighborhood-keeps-the-complete-comparison-below403.md)
combines these source bounds with all59 original consumer envelopes.
This source lemma alone does not assert a global comparison join,
later-prime continuation, Lean verification or an unrestricted Erdős7 result.
