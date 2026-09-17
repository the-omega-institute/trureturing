[Index](../marked_head_profile.md) · [Previous](31-one-original-zero-five-layout-across-both-actual-measures.md)

<a id="unequal-source-norms-sharpen-the-uniform357-input"></a>
### Unequal source norms sharpen the uniform357 input

For every finite original family with distinct nonunit moduli supported
on{3,5,7}, the same uniform probability on its complete actual survivor
set satisfies

    Gamma357<=4351/120=36.25833333333333...
                      <3849/106.                    (YC1)

The improvement is337/6360=0.0529874213836478.... The proof retains
all original prime-power heights and residue choices. It uses weighted
Young inequalities in the existing ZG2 expansion, the established
common zero5 source bounds, and the same SD3/SD5 signed deletion floor.
It is an ordinary proof with exact rational verification, not Lean or
a resolution of unrestricted Erdős #7.

<a id="the-information-omitted-by-the-symmetric-cross-estimate"></a>
#### The information omitted by the symmetric cross estimate

Use the actual raw complete35 survivor measure lambda35 and the raw
pure3 survivor measure eta. Their masses and cell parameters are the
existing n_l,w_l,d_l,s; eta_l=w_l/9, and the marginal density satisfies

    0<=d lambda35/d eta<=d_l on cell l.

Fix the original mod3 and mod9 choices(r,j) of the zero5 block B0
inside the original zero7 complete35 test A0. Write its baseline as
b_l=1+1_(root(l)=r)+1_(l=j). Retain the separate CRT factors of every
positive5 original label(a,e), where a>=0 and e>=1:

    A0=B0+sum_(a,e)A_(a,e)(u)J_(a,e)(v),
    B_e(u)=sum_a A_(a,e)(u).

Here A_(0,e)=1 when that label is present. Distinct a at the same e
need not have the same five-coordinate residue. Every added term is
nonnegative. Enlarge only the increment A0^2-B0^2 to the raw product
of the actual pure3 and pure5 survivor measures. At fixed u, expand
this increment into its single and pair indicators. Their coefficients
are nonnegative, their individual raw five masses are at most5^-e,
and their pair intersections are at most5^-max(e,f). Replacing these
indicators by auxiliary nested intervals [0,5^-e] therefore bounds the
integral above, term by term. Only in this upper comparison does the
positive load have the grouped form sum_e 1_[0,5^-e] B_e. No equality
or alignment of the original five residues is asserted.
Thus, for any fixed t>0, use

    2B0 B_e<=t*B0^2+B_e^2/t

in every zero-positive cross term, and the ordinary symmetric square
bound for positive-positive terms. The complete coefficients are

    sum_(e>=1)5^-e=1/4,
    2sum_(f>e>=1)5^-f=1/8.

If M bounds integral_eta B_e^2 for every complete ternary block, this
gives

    integral_lambda35 A0^2
      <=integral_lambda35 B0^2+(t/4)integral_eta B0^2
                                      +(3/8+1/(4t))*M. (YC2)

The coefficient3/8 includes the positive diagonal1/4 and
positive-positive1/8. All series include every original depth.

<a id="one-zero5-layout-under-its-two-actual-measures"></a>
#### One zero5 layout under its two actual measures

The existing ternary root/cell bound supplies

    M=max_b[sum_l eta_l*b_l^2+max_l(b_l+1)/9].

Apply the same arbitrary-root square bound to the combined positive
measure lambda35+(t/4)eta, whose cell mass is n_l+t*eta_l/4 and whose
depth-a cylinder cap is(d_l+t/4)*3^-a. Equivalently, the existing
common-layout depth estimate sums the exact tail

    sum_(k>=0)3^(-k-3)[2(b+k)+1]=(b+1)/9.

It follows from YC2 that the valid fixed-layout upper bound is

    U_t(r,j)=sum_l n_l*b_l^2+(t/4)sum_l eta_l*b_l^2
          +max_l[(d_l+t/4)*(b_l+1)/9]
          +(3/8+1/(4t))*M.                          (YC3)

The root/cell choice in both terms is the same original B0. No
compatibility or common maximizing choice is imposed on distinct
positive5 blocks. The arbitrary-root bound already covers nonnested
original ternary prefixes and empty labels at their original depths.

Set t=9/8 for the two-cell root r=0 and t=1 for the three-cell root
r=1. These weights are fixed on the whole continuous parameter domain.
Define U_(r,j)=U_t(r,j) and U=max_(r,j)U_(r,j). Both are upper bounds
on the same actual complete35 laws used by SD4.

<a id="the-previous-controlling-relaxation-cannot-attain-its-square-input"></a>
#### The previous controlling relaxation cannot attain its square input

At vertex398/layout(0,1), the zero5 block has pure-eta square bound2,
whereas M=5/2. Simultaneous saturation of those two upper bounds is
incompatible with equality in symmetric Young. If two actual blocks
instead coincide with norm at most2, they do not saturate the positive
block's5/2 upper comparison. This is a tradeoff between norm deficit
and cross-term slack, not a claimed positive distance between every
pair of actual blocks. For t=9/8, YC3 is

    U_(0,1)=61/18=163/48-1/144.

The same raw source and layouts are involved;1/144 is not subtracted
from an unrelated estimate. This gives an explicit obstruction to
simultaneously saturating the old163/48 comparison at this relaxed
point. No actual family attaining that parameter tuple is asserted.

<a id="same-actual-mixed7-deletion-and-every-missing-class-branch"></a>
#### Same actual mixed7 deletion and every missing-class branch

Retain SD3's weighted cofactor cap W_(r,j)(C) exactly. Its floor is
the same original b_l^2 and the actual complete test is still at least
that floor. The unchanged SD4/SD5 argument therefore gives

    s E_M[(L^2-C)1_(B^c)]
      <=(6/5)U_(r,j)+(7/15)U+W_(r,j)(C)/5-C*s,

where M is the product of the actual uniform35 law and actual pure7
law, and B is its actual mixed7 forbidden union. Conditioning on B^c
gives precisely the complete actual uniform357 law. Its mass remains
positive by the existing CM2 theorem.

For C=4351/120 all1296*10=12960 exact vertex/layout margins

    C*s-(6/5)U_(r,j)-(7/15)U-W_(r,j)(C)/5

are nonnegative. The minimum is zero. For fixed weights t each
quantity in YC3 is separately convex in the five parameter groups:
its initial terms are separately affine and its maxima have
nonnegative coefficients. W retains its established convexity.
The signed margin is therefore separately concave. Repeated vertex
interpolation proves its nonnegativity throughout the full continuous
parameter domain, not merely on a finite set of actual families.

The new controlling points are314,316,518,520, each with r=1 and
j=2,3,4. Representative314/(1,2) has

    s=7/24, D=1/6, U_(1,2)=U=191/48.

The former398/(0,1) has strictly positive final margin163/43200.
These are extrema of the comparison formulas; actual-family
sharpness is not asserted.

If modulus3 is absent, the established same-law inputs
Gamma35<=215/24 and R35<=17/12 give Gamma357<=5273/258.
If modulus3 is present but9 is absent or ineffective, use
Gamma35<=593/48 and R35<=47/24, giving Gamma357<=14543/438.
Both are strictly below4351/120. These include low ternary heights;
missing5/7 classes and arbitrary finite heights are already covered
by the full cap sums and the five-cell domain. No branch is omitted.

<a id="exact-limit-of-changing-only-these-young-weights"></a>
#### Exact limit of changing only these Young weights

At the new controlling point314 and original layout(1,2), the fixed
pure-zero5 square bound and the pure global bound both equal5/2,
while the actual-zero5 square contribution is43/24. The same cell
maximizes the complete deep term for every t>0. Hence YC3 becomes

    U_t=191/48+(5/8)*(t+1/t-2)>=191/48.

This follows from(t-1)^2/t>=0. The global U is at least U_t, and a
fixed available SD3 branch satisfies W_(1,2)(C)>=5C/8-53/18 for C>=9.
Since s=7/24, the signed SD5 margin is at most

    (7/24)C-(5/3)(191/48)-(5C/8-53/18)/5
      =(C-4351/120)/6.

Thus the retained SD3/SD5 comparison cannot give a smaller constant
by any positive Young weights, even weights depending on the parameter
point. The fixed weighting above attains this limit. This is a boundary
of the stated bounding formulas, not actual-family sharpness or a
barrier to retaining additional joint layout/deletion information.

The [source verifier](../verify_uniform_gamma_cofactor_coupling.py) checks
all12960 margins, the complete coefficients and both fallback fractions
against the [source certificate](../certificates/uniform_gamma_cofactor_certificate.json).
A separate implementation expands the weighted cofactor cap directly
from original cell weights and independently matches all12960 layout
records, source bounds, affine roots and target margins. The ordinary
source applicability and continuous interpolation arguments above supply
the bridge beyond those arithmetic checks.

<a id="complete-consumer-on-the-unchanged-ap13-law"></a>
#### Complete consumer on the unchanged AP13 law

Use YC1 only in the existing globally fixed uniform-cap slots and
complete auxiliary tails of U16 and U81. Keep the same all-original7
raw cost, all-originalAP weighted costs, original-label domain and
Delta. No actual probability is changed. Write g=4351/120-3849/106<0,
and let pn be the unchanged N11*N13 product probabilities. The exact
numerator changes are

    U16_new-U16_old=g*D*[E(N^2;N>=4)+9*p3],
    U81_new-U81_old=g*D*[E(N^2;N>=9)+49*p7+64*p8].       (YC4)

Thus Gamma13, T13(81) and the joint bound are recomputed together.
In particular the joint numerator changes by(2371/2880) times the
first line of YC4; the source improvement337/6360 is not subtracted
from the final joint bound. The result is

    Gamma13<=22083176977198383411/141008133466238896
           =156.60924256178234...,
    T13(81)<=16980540086875374377725858588657069/171483581894996419228554742368000
           =99.02137510326192...,
    F17^-(403;nu13)+F19^-(403;physical mu17)
      <=1081947977203541447444658369092299900073777/2408107143207565965787641353095374412800
       =449.2939528273653....                         (YC5)

The prescribed19 input is still the normalized physical mu17=nu13 K17.
It is not replaced by the killed input of BM/RC. Every original exponent,
residue, missing-class branch and full comparison tail remains included.

The joint, Gamma and T81 continuous-margin coefficients are respectively

    4620321152673881618746989997998445167871/11417612680765270081200009288990412800,
    58093929085555795259077/502552987673675425344,
    506744711227124988573279036192990409/5223653725416814001115975229056000,                              (YC6)

all strictly positive. The same separate-concavity argument therefore
extends the verified1296 vertex inequalities to the full continuous
domain. All eight additional branch inequalities are rechecked at the
new target values. Joint/Gamma and T81 maxima are computed separately.
The [joint verifier](../verify_joint_frontier.py) binds the new source
verifier and source certificate by two additional SHA-256 pins, while
retaining the eight predecessor input pins. These bind source identity;
they do not replace the ordinary mathematical proofs.

An independent algebraic reconstruction uses the published ABP rows and
YC4, with separately computed complete product moments and probabilities.
It checks the changed numerators, all1296 downstream values, their maxima
and continuous coefficients without recomputing the original raw-cost
implementation. The canonical full reconstruction also checks all eight
remaining branches and the complete polynomial tails.

The exact finite allowances are now

    unequal/current6: 52082243234769798513124592688404147/171483581894996419228554742368000,
    box20/current8: 6515903629657382326096259642454221443/21435447736874552403569342796000000.

Safe sufficient bounds are303.715 and303.977, respectively. The new
joint bound is still above both; its signed upper before finite-core
error is145.31532793062718...>0.
The uniform negative-Q criterion and arbitrary later-prime continuation
remain unproved. These results are ordinary proofs with exact rational
certificates, without new Lean declarations or an unrestricted resolution.

<a id="one-original-five-test-couples-square-loss-to-mixed-deletion"></a>
### One original five test couples square loss to mixed deletion

For every finite original family supported on{3,5,7}, the uniform law on
its complete actual survivor set satisfies the stronger bound

    Gamma357<=5761/159=36.23270440251572... .             (OS1)

The gain from YC1 is163/6360. The additional observation is the raw
pure5 mass of one original modulus5 test. That same event constrains
both the selected zero7 square and one mixed7 deletion term. Distinct
original mod15,45,... tests retain their own five-coordinate residues.
All exponent heights, missing-class branches and complete tails remain
included. This is an ordinary proof with exact rational certificates.

<a id="a-strip-loss-for-one-label-with-no-residue-identification"></a>
#### A strip loss for one label, with no residue identification

Keep lambda35, eta and the original zero5 block B0 from YC. Let P5 be
the actual pure5 survivor set, with raw Haar mass z. In the CRT expansion
of the selected zero7 test, write

    A0=B0+R,
    R(u,v)=sum_(a>=0,e>=1)A_(a,e)(u)J_(a,e)(v).

Each pair(a,e) is its original label. Set J=J_(0,1), the original
modulus5 test, and h=Haar(P5 intersect J), so0<=h<=1/5. At each fixed
ternary point u, the nonnegative polynomial2 B0 R+R^2 is bounded by
the auxiliary nested-interval comparison from YC. Give only label(0,1)
the improved cap h; every other label keeps cap5^-e. Individual masses
obey these caps, and each pair intersection is at most their minimum.
Thus the comparison follows term by term without coupling the actual
five residues.

Write R_h for this auxiliary sum and R_full for the old sum, where
also label(0,1) has cap1/5. Since A_(0,1)=1,

    R_h=R_full-1_(h,1/5].

On that strip R_full>=1, and in cell l the square-increment difference is

    (2 B0 R_full+R_full^2)-(2 B0 R_h+R_h^2)
       =2 B0+2 R_full-1>=2 b_l+1.

Retain the integral of B0^2 under lambda35. Enlarge only its nonnegative
increment to eta times raw Haar on P5, apply the interval comparison,
and then use YC3 to bound the full auxiliary expression. With
eta_l=w_l/9 this proves

    integral_lambda35 A0^2<=U_strip(r,j,h),
    U_strip=U_t(r,j)-(1/5-h)sum_l eta_l(2 b_l+1).       (OS2)

Only the selected zero7 test uses OS2. The independent positive7 tests
keep their old global bound U=max_(r,j)U_t(r,j). If a test inventory
is incomplete, completing its missing nonnegative labels gives an
upper bound with the same argument; no forbidden class is added.

<a id="the-same-event-also-lowers-the-pure3-cofactor-cap"></a>
#### The same event also lowers the pure3 cofactor cap

The raw cell masses remain n_l=eta_l(z-alpha_root(l)-beta_l)-late_l.
Here alpha and beta are the actual successive removed five masses;
late_l is the additional raw mass removed by deeper mixed classes.
For the same actual event J put

    q_l=lambda35(cell_l intersect J),
    L_l=eta_l(h-alpha_root(l)-beta_l)-late_l.

Before mixed deletion the intersection has mass eta_l h. The root
and cell exclusions remove at most eta_l(alpha_root(l)+beta_l), and
deeper exclusions remove at most late_l. Consequently q_l>=L_l,
including when L_l is negative. This is a lower bound for an actual
intersection, independent of the auxiliary comparison used in OS2.

For C>=16 set k_l=C-b_l^2 and c_l=2 b_l+1. The actual test has
A0>=b_l+1_J, and therefore

    (C-A0^2)_+<=k_l-c_l 1_J,
    k_l-c_l 1_J>=0.                                  (OS3)

For the three incident layouts r=1,j in{2,3,4}, let

    H_r=sum_(root(l)=r)k_l n_l.

In SD3 the pure3 cofactor term was max(H_0,H_1). For an original
root1 query, integrating OS3 gives at most H_1-sum_root1 c_l q_l,
hence at most H_1-sum_root1 c_l L_l. For a root0 query retain H_0.
The valid replacement is thus

    W'_3=max(H_0,H_1-sum_(root(l)=1)c_l L_l).           (OS4)

Let W' be SD3's full weighted cofactor cap with just this term
replaced. All other cofactor terms remain as before. For the other
seven layouts retain both the old W and the old selected square U_t.
The same actual SD5 deletion argument now gives, for incident layouts,

    s E_M[(L^2-C)1_(B^c)]
       <=(6/5)U_strip+(7/15)U+W'/5-C*s.               (OS5)

Here M and B are exactly SD5's product law and actual mixed7 forbidden
union. Conditioning on B^c is the actual complete uniform357 law;
the established positive-mass result supplies its denominator.

<a id="six-parameter-groups-and-complete-exact-verification"></a>
#### Six parameter groups and complete exact verification

The five old parameter groups and h in[0,1/5] form a product domain.
Actual families occupy a subset; the relaxation need not realize every
parameter tuple. OS2 is separately convex: its subtracted strip term
is separately affine. In OS4 each branch is separately affine, so
W' is separately convex. The other SD3 terms and U retain their
previous separate convexity. Hence

    C*s-(6/5)U_strip-(7/15)U-W'/5

is separately concave. It suffices to test each old product vertex
and the two endpoints h=0,1/5. The signed L_l must stay signed here;
replacing them by positive parts would require a different convexity
argument.

At C=5761/159, all7776 incident endpoint/layout margins are positive.
Their minimum is1/10800; the h=0 minimum is5377/10800. The9072
remaining old-layout margins are nonnegative, with six zero margins
at vertices398,410,422,616,628,640. Both missing-class bounds5273/258
and14543/438 are strictly below C. Repeated vertex interpolation
proves OS5's nonpositive upper throughout the full continuous domain.
This proves OS1, without claiming an actual family realizes any
relaxation vertex.

The [source verifier](../verify_uniform_gamma_cofactor_coupling.py) retains
the preceding bounds and reconstructs all16848 current endpoint/layout
records. The [source certificate](../certificates/uniform_gamma_cofactor_certificate.json)
stores their complete digest, counts, extrema and equality witnesses.
An independent implementation matches every selected square, global
square, weighted deletion cap and margin. These arithmetic checks
support the ordinary actual-label and interpolation proofs above;
they are not Lean verification.

<a id="propagation-through-the-complete-actual-ap13-consumer"></a>
#### Propagation through the complete actual AP13 consumer

Use g=5761/159-4351/120=-163/6360 in YC4, retaining every original
raw AP cost, Delta and test law. This recomputes both uniform-cap
slots and all complete tails. The resulting same-law bounds are

    Gamma13<=2759803303859498317/17626016683279862
           =156.57555268726503...,
    T13(81)<=40328059447468124566268231594828117/407273507000616495667817513124000
           =99.01959924785159...,
    F17^-(403;nu13)+F19^-(403;physical mu17)
      <=135235148346191272912644779662034152101019/301013392900945745723455169136921801600
       =449.266217170254... .                         (OS6)

The19 input remains normalized physical mu17=nu13 K17, distinct from
the killed input in BM/RC. The new joint gain is exactly
15753210252311875/567976817318556672; no independent source saving
is subtracted from an unrelated objective.

The joint, Gamma and T81 continuous-margin coefficients are respectively

    30608625189355598901951158054960421028721/75641684010069914287950061539561484800,
    384818684614381280186471/3329413543338099692904,
    63785933429005107702629491421514123461/657527412686841462390473381957424000,

all positive. The [joint verifier](../verify_joint_frontier.py) checks
all1296 vertices, all eight remaining branch records and the complete
tails against the [joint certificate](../certificates/joint_frontier_certificate.json).
Independent reconstruction matches the changed rows and coefficients.
The two uniform-source SHA-256 pins are updated; the eight predecessor
pins and historical gains are retained.

The exact finite allowances become

    unequal/current6: 123696050941439161049501590188192271/407273507000616495667817513124000,
    box20/current8: 30950723055587788444164903939965657323/101818376750154123916954378281000000.

Safe sufficient bounds are303.717 and303.979 respectively. OS6 remains
145.28648341810555... above the larger exact allowance, and the signed
upper before finite-core error is145.28581641810555...>0. The uniform
negative-Q criterion and arbitrary later-prime continuation remain open.
No new Lean declaration or unrestricted Erdős #7 resolution is claimed.
