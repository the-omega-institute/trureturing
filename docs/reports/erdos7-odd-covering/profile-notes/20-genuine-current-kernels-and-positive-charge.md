[Index](../marked_head_profile.md) · [Previous](19-1-same-law-inputs-and-definitions.md) · [Next](21-physical-and-killed-kernel-comparisons-at11-and13.md)

<a id="genuine-current-kernels-and-positive-charge"></a>
### Genuine current kernels and positive charge

The complete forbidden load factors as

`C(x)=(1+1_(x=1 mod3)+1_(x=1 mod9))`
`     *(1+1_(x=1 mod5))*(1+1_(x=1 mod7))`.

At `x=1 mod315` it equals12. At every other old row it is at most8: a missing depth-two ternary match gives at most `2*2*2`, and a missing5 or7 match gives at most `3*1*2`. Hence `alpha>delta=7/(p-2)` occurs precisely at row1. Elsewhere `C-1<=7`, and `7/(p-1)<7/(p-2)`.

Use the actual BBMST density relative to `m`:

`k_x(y)=1/(1-min(alpha(x),delta))` on the actual mixed good set,

`k_x(y)=(alpha(x)-delta)_+/(alpha(x)*(1-delta))` on the actual mixed bad set,

with zero bad density when `alpha=0`. Each row is normalized. Its assigned bad mass is `beta(x)=(alpha(x)-delta)_+/(1-delta)`. At row1 the actual bad roots are1 through11, so

| p | delta | beta(1) | b=E_nu beta |
|---|---|---|---|
|17|`7/15`|`53/128`|`53/18432`|
|19|`7/17`|`61/180`|`61/25920`|

Both charges are strictly positive. Actual mixed bad points exist in other rows too, but the kernel assigns them zero mass. The full physical probability is `P=nu k`; no conditioning or change of the old marginal occurs before this step.

<a id="one-complete-common-test-realizes-the-unit-floor"></a>
### One complete common test realizes the unit floor

At every original old test modulus `d|315`, choose residue2 modulo `d`. At every original current test modulus `dp`, including `d=1`, choose CRT residue `(2 mod d,p-1 mod p)`. This gives exactly24 test labels, the full exponent rectangle

`(a_3,a_5,a_7,a_p) in {0,1,2}*{0,1}*{0,1}*{0,1}`.

All choices are fixed before sampling the old row. The full test load is

`L(x,y)=A(x)*(1+1_(y=p-1))`.

Every bad point with positive physical mass lies at old row1 and current root in1 through11. At row1, every nonunit divisor test centered at2 fails, since every such divisor has a factor among3,5,7. Thus `A(1)=1`. Also `p-1` is outside1 through11. It follows that `L=1` on every bad point of positive physical mass. This proves

`integral_bad L^2 dP=b`, `integral_bad(L^2-1)dP=0`.

If `P^-` is the killed subprobability and `P^s=P^-/(1-b)` is its supported normalization, the exact identity is

`E_(P^s) L^2=1+(E_P L^2-1)/(1-b)`.

The final unit-floor conditioning formula is therefore exact for this full test as well.

<a id="the-same-geometry-has-nontrivial-joint-cap-information"></a>
### The same geometry has nontrivial joint cap information

The old square is `E_nu A^2=35/4`, and this is the exact complete old square maximum. Indeed, the one-prime ordered-pair cap sums are `10/3`, `7/4`, and `3/2`; multiplying gives `35/4`. Each pair of arbitrary original test cylinders has at most its corresponding product cap. The coherent surviving center2 attains all these caps simultaneously.

For the independent layout pair above, the three one-prime values of `E[A_p^2 C_p]` are4,2, and5/3. Hence

`E_nu[A^2 C]=40/3`, `E_nu[A^2(C-1)]=55/12`,

and the exact mixed-union cross energies are

`E_nu[A^2 alpha17]=55/192`, `E_nu[A^2 alpha19]=55/216`.

This old maximizing test can therefore be almost disjoint from the rows causing charge. It is not the diagonal `A=C` construction excluded by JL3.

For comparison with SH26, use precisely its cap envelope

`c_SH(x)=(p-1)/((p-2)*(1-min(alpha(x),delta)))`,

`c=(p-1)/(p-9)`, `D=E_nu[c-c_SH]`.

The extra testwise cap saving discarded by the SH26 unit-floor relaxation is

`Z=E_nu[(c-c_SH)(A^2-1)]`,

so `E_nu[c_SH A^2]=c*(35/4)-D-Z`. Exact computation gives

| p | `c*(35/4)-D` | `E[c_SH A^2]` | `Z` |
|---|---|---|---|
|17|`811780951/48648600`|`471459931/48648600`|`436309/62370`|
|19|`199838033/13224640`|`31651727/3306160`|`1331475/240448`|

These are values of the same SH26 cap envelope; they are not a new exact-current-maximum assertion. The strict positive covariance saving and zero excess killed loss coexist on the same source, mask, kernel and complete test. Any refinement must retain that joint geometry; a universally larger killed floor is false. No numerical bound for all generic17/19 layouts or unrestricted tails follows from this example.

The [killed-floor verifier](../verify_killed_unit_floor.py) reconstructs the
[exact certificate](../certificates/killed_unit_floor_certificate.json), including both finite
original families and all24 full test labels. It evaluates every physical
CRT point above the144 old survivors and recomputes the square moments,
charges, cross energy and cap covariance using exact fractions. Default mode
compares the entire saved certificate; `--write` regenerates it. These are two
separate one-step constructions from the actual357 law, not a17/19 chain
from the supported AP13 law. No Lean declaration is added.

```sh
python3 -I -O /absolute/path/to/verify_killed_unit_floor.py
```

<a id="shared-actual-cell-hinge-bounds-for-the-uniform357-law"></a>
## Shared actual-cell hinge bounds for the uniform357 law

For the same uniform complete actual357 survivor law used in CM8, SD1--SD6,
BS10 and PR, the following ordinary bounds hold for every complete original
test L, every original choice of residues and every finite exponent height:

|h|upper bound for E(L-h)+|decimal|
|--|--|--|
|3|1318076/584325|2.2557241261284386|
|4|94745926/61354125|1.5442470412543574|
|6|578163435166/676429228125|0.8547286414110404|

All three improve PR11. The same-law square bound remains3849/106. These
are maxima of a parameter relaxation, with no actual-family sharpness or
Lean verification claim. No forbidden or test label is deleted or merged.

<a id="the-actual-five-cell-input"></a>
### The actual five-cell input

First suppose the actual modulus3 and9 exclusions are effective. Reuse
exactly SD's five cells, with root map r(l)=(0,0,1,1,1), and parameters

    d_l=z-alpha_r(l)-beta_l,
    n_l=w_l d_l/9-t_l,   s=sum n_l,   x=sum w_l/9.

The parameter domain is

    w_l=1-D_l, D_l>=0, sum D_l<=1/2;
    alpha>=0, sum alpha<=1/4;
    beta>=0, sum beta<=1/4;
    t>=0, sum t<=1/72;   3/4<=z<=1.

Here n_l is the actual raw complete35 survivor mass of cell l. Its
remaining5 availability before deeper mixed deletions is d_l. For any
original pure3 test prefix at depth a>=3 lying in cell l, its raw
complete35 mass is at most d_l*3^-a. Under the raw actual pure3 survivor
measure eta, its mass is at most3^-a and cell masses are w_l/9. These are
the established SD2 input bounds. Inactive root3 or cell9 test choices may
be completed to a surviving root or cell, pointwise increasing the load.
This does not change any actual forbidden residue.

<a id="arbitrary-monotone-ternary-cost"></a>
### Arbitrary monotone ternary cost

For a fixed original root/cell test choice (r,j), set

    b_l=1+1_(r(l)=r)+1_(l=j),
    Delta_a(g,b)=max_(0<=i<=a-3)[g(b+i+1)-g(b+i)], a>=3,
    P_g(r,j;m,v)=sum_l m_l g(b_l)
                 +sum_(a>=3)3^-a max_l[v_l Delta_a(g,b_l)].

For every nondecreasing g used below, this bounds its raw ternary-test
integral with cell masses m and depth caps v_l*3^-a. Add the original
depth-a indicator after depths3,...,a-1. On that indicator the preceding
deep count is an integer between0 and a-3. Its cost increment is at most
Delta_a(g,b_l). That cylinder has one fixed cell l, so integrating the
increment gives the displayed maximum. Summing proves the bound without
assuming the original prefixes are nested or coherently centered.

Write

    P^A_g(r,j)=P_g(r,j;n,d),
    P^eta_g(r,j)=P_g(r,j;(w_l/9)_l,(1)_l),
    M_eta=max_(r,j)P^eta_id(r,j).

Constants are exact in this bound: adding a constant c to g adds c times
the measure's mass. This fact is used in the complete multiplier tails.

<a id="a-positive5-convex-increment-retaining-the-actual-zero5-integral"></a>
### A positive5 convex increment retaining the actual zero5 integral

Put f_t(v)=(v-t)+. A complete35 test consists of its original zero5
ternary block A0 and all its positive5 original blocks. The actual35
survivor set S35 is contained in the product P3*P5 of actual pure survivors.
Since every added label is nonnegative,

    integral_S35 f_t(A)
      <= integral_S35 f_t(A0)
           +integral_(P3*P5)[f_t(A)-f_t(A0)].            (HC1)

The first integral retains the actual35 cell masses. Only the nonnegative
increment is enlarged to the pure product. For each fixed3 coordinate,
comonotone comparison of the5-prefix indicators bounds the second
integral by a nested family with conditional probabilities5^-e/z. All
original3 roots in each5 block are unchanged. The resulting block count
N has raw positive-tail probabilities

    z Pr(N=n)=4/5^n, n>=2.

The zero-tail event makes no increment. On an outcome with N=n, convex
Jensen gives

    f_t(A0+...+A_(n-1))-f_t(A0)
      <= g_(t,n)(A0)+(1/n)sum_(e=1)^(n-1) f_t(n A_e),
    g_(t,n)(v)=f_t(nv)/n-f_t(v).                        (HC2)

The function g_(t,n) is nonnegative and nondecreasing: it is zero below
t/n, then v-t/n through t, then the constant t(1-1/n). It need not be
convex; the ternary bound above was explicitly proved for monotone costs.
Independently maximizing each positive5 block is a valid upper bound,
not a statement that different blocks have a common maximizing layout.

Consequently the raw actual35 cost has the valid bound

    F_t=max_(r,j){P^A_(f_t)(r,j)
       +sum_(n>=2) (4/5^n)
          [P^eta_(g_(t,n))(r,j)
             +(n-1)/n max_(r',j')P^eta_(f_t(n .))(r',j')]}.   (HC3)

The original zero5 root/cell stays outside its multiplier sum. This is
the convex-cost extension of the same decomposition that yields ZG2 and
SD2 for the square. No full-Haar old law is substituted.

For the raw old first moment, the same argument specializes to

    M=max_(r,j)P^A_id(r,j)+M_eta/4.                    (HC4)

<a id="complete-tails-with-no-cutoff-of-original-heights"></a>
### Complete tails, with no cutoff of original heights

Only thresholds t in {1,6/5,4/3,3/2,2,3,4,6} are needed. Let
N_t=max(2,ceil(t)). For n>=N_t and v>=1,

    f_t(nv)=nv-t,
    g_(t,n)(v)=min(v,t)-t/n.

Thus the entire n>=N_t contribution inside HC3 is exactly bounded by

    5^(1-N_t)[P^eta_(min(.,t))(r,j)-t*x
                       +(N_t-3/4) M_eta].             (HC5)

This uses the full geometric mass and first moment, not a renormalized
finite sample. For the ternary coefficient sums, all cost breakpoints
are at most6. Delta_a is therefore constant for a>=10 in every cost
appearing here. The program sums depths3 through10 and adds the exact
remaining coefficient1/(2*3^10). Every original depth remains covered.
When a finite physical height omits later labels, complete them with
arbitrary fixed test residues before these nonnegative comparisons;
the added indicators only increase the load and all displayed geometric
sums remain valid upper bounds for the original finite test.

<a id="pure7-comparison-and-actual-mixed7-deletion"></a>
### Pure7 comparison and actual mixed7 deletion

Under the actual pure7 survivor probability, every positive depth-e
test prefix has probability at most(6/5)7^-e. Comonotone comparison and
Jensen therefore use the complete auxiliary count

    Pr(N7=1)=29/35,
    Pr(N7=n)=36/(5*7^n), n>=2.

On the product of the actual uniform35 law and actual pure7 law, a
complete full test satisfies, for integer h in {3,4,6},

    s E f_h(L) <= B_h,
    B_h=(29/35) F_h
          +sum_(2<=n<h)36*n/(5*7^n) F_(h/n)
          +(6/5)7^(1-h)[(h+1/6)M-h*s].               (HC6)

The final term includes every N7>=h. Each coefficient F_(h/n) uses the
same actual five-cell parameters. Its independent maxima only enlarge
the expectation; they do not authorize adaptive original test residues.

The raw nonunit35 cylinder cap from SD3 with constant unit weight is

    T=max_r sum_(r(l)=r)n_l+max_l n_l+max_l d_l/18
       +sum_l w_l/36+max_r sum_(r(l)=r)w_l/36
       +max_l w_l/36+1/72.                            (HC7)

Let B be the actual mixed7 forbidden union. The same-family bound is
Pr(B)<=T/(5s), and the existing SD parameter domain guarantees s-T/5>0.
The signed conditioning identity gives

    s E[(f_h(L)-C)1_(B^c)]
      <= B_h-C*s+(C/5)T.                              (HC8)

Indeed L is at least the retained root/cell load b_l<=3. At the current
thresholds f_h(b_l)=0, so the safe deletion weight is exactly C. The
two-anchor signed rebate vanishes; no nonexistent hinge rebate is
claimed. The actual deletion union and the same s,T remain in the
denominator, and conditioning gives exactly the original uniform357 law.
Therefore C(s-T/5)>=B_h suffices.

<a id="continuous-parameter-domain-and-all-missing-class-branches"></a>
### Continuous parameter domain and all missing-class branches

For each fixed original root/cell and each selected branch of every
maximum in HC3--HC7, each expression is affine separately in the five
groups D,alpha,beta,t,z. Terms such as w_l d_l use different groups. All
maxima in F,M,T have nonnegative coefficients; the subtracted tail terms
are affine. Hence the target margin C(s-T/5)-B_h is concave separately
in each group. Repeated convex interpolation proves its nonnegativity
throughout the product domain if it is nonnegative at every product
vertex. There are6*3*6*6*2=1296 vertices. The exact verifier checks every
one for the three stated targets, with minimum margin zero in each case.
The scaled denominator(5/6)(s-T/5) has minimum53/432>0.

The five-cell domain covers all four effective9 branches, including
missing modulus5 or7 and arbitrary higher pure exclusions. For the eight
cases where modulus3 is absent or modulus9 absent/ineffective, reuse the
established corresponding PR profile. The verifier reads and checks all
twelve branches. Every fallback at3,4,6 lies below the stated respective
generic bounds; no branch is omitted.

<a id="reuse-and-verification-scope"></a>
### Reuse and verification scope

The source inputs are CM2, SD1--SD6, ZG2 and PR1--PR11. The repository
ArbitraryRootEventMoment module supplies the square-specialized root-tail
estimate; the present monotone-cost increment is proved directly above.
The repository ConditionalComparison/Supermodular supplies the finite
comonotone comparison, and pinned Mathlib Analysis/Convex/Jensen supplies
ConvexOn.map_sum_le. No exact current shared-cell hinge endpoint was found
in those searched declarations or the ordinary report. The BBMST source
arXiv1811.03547 was reachable (HTTP200); no literature-priority claim is
made. This argument and its exact coefficient checks are ordinary
mathematics, not an end-to-end Lean formalization.

<a id="consumer-on-the-same-actual-ap46-law-hc9"></a>
### Consumer on the same actual AP(4,6) law (HC9)

Pointwise translation of the new third hinge, and convexity in the
threshold, also give the same-law bounds

    h1<=2+h3=2486726/584325,
    h2<=1+h3=1902401/584325,
    h5<=(h4+h6)/2=811368634658/676429228125.

In particular E L<=1+h1=3071051/584325. These lower the complete-test
first moment, not the distinct sum of individually maximized cylinder
masses; that latter observation is left unchanged. Retain PR's original
AP kernels and physical square324599/3816. Substitution of this stronger
same-law profile into the established full-tail charge formula gives

    b11 <= 47372963/184062375,
    b13 <= 9492718910453/38266567762500,
    rho13 >= 18925009844347/38266567762500
           >0.4945572846,
    Gamma13 <= 6471426752685569/37850019688694
             <170.975518796,
    supported_Haar_density <=1039695426000000/18925009844347.

The raw physical Haar density remains1440/53. The supported Haar density
is consequently at most(1440/53)/rho13. These are improved observations
of the same full actual AP13 law. They do not themselves provide a17/19
joint certificate or a later-prime continuation. The preceding PR
certificate is kept intact and is a pinned input of this separate result.

The [shared-cell verifier](../verify_shared_cell_hinges.py) reconstructs the
[exact certificate](../certificates/shared_cell_hinges_certificate.json), including all1296
parameter vertices, all12 original-class branches and the same-law AP13 consumer.
Its preceding PR input is pinned by SHA-256; default mode compares every
certificate field, while `--write` regenerates the certificate.

<a id="complete-hinges-and-actual-continuation-from-supported-ap13"></a>
## Complete hinges and actual continuation from supported AP13

For the same actual AP(4,6) supported13 law, the shared-cell source
profile gives a complete-load mean bound

    M13<=2621130891614589/246025127976511
         =10.653915366989825... .                        (SP1)

Its complete hinge profile supplies two positive continuations:

    Gamma17<=71411032739803777721269/176909701938094610544
             =403.65809199538637...;
    Gamma19<=14309324828593686784688579/6107986643845861414296
             =2342.7236605062217... .                    (SP2)

The first applies actual pure-base AP17/T8 and then conditions. The
second starts from supported13, applies AP17/T8 and AP19/T8 physically,
and conditions only after19. It does not use the first construction's
conditioned17 output. Every original label, arbitrary residue and
finite height is retained. These are ordinary mathematical results,
not Lean declarations or an unrestricted Erdős7 solution.

<a id="same-actual-source-law-and-unbounded-initial-profile"></a>
### Same actual source law and unbounded initial profile

Let nu357 be uniform on the full actual357 survivor set. The unchanged
square bound is G=3849/106. HC1--HC8 strengthen its complete-test hinges
at3,4,6. The elementary inequalities

    H357(1)<=2+H357(3),
    H357(2)<=1+H357(3),
    H357(5)<=[H357(4)+H357(6)]/2

give the source complete-load mean M=1+H357(1)<=3071051/584325.
M bounds the complete-load mean; it does not rename the earlier
independently stated cylinder-sum bound. The shared-cell certificate
retains the stronger1--12 profile, including PR's other knots and all
original missing-class branches.

PR7--PR11 supply arbitrary further thresholds. For each of its twelve
branches let u3,u5,u7 be the reference pure masses and D the same-law
Haar density bound. Let V be the product of three independent prefix
counts with tails Pr(Kp>=e)=p^-e/u_p. Then

    E_nu357(L-t)_+<=D*u3*u5*u7*E(V-t)_+.

At an integer h, the exact identity

    E(V-h)_+=E V-h+sum_(n<h)(h-n)Pr(V=n)

uses the full geometric mean and finitely many lower product
probabilities. Take the maximum over twelve branches, and the minimum
with valid same-law moment bounds. Consecutive integer chords bound
the actual convex hinge between integers; for t<=1 use H357(t)<=M-t.
No distribution is truncated or renormalized.

For positive integer-valued L and integer h>=1, the unit-floor bound

    E(L-h)_+<=(G-1)h/(4h^2-1)                           (SP3)

also holds. For L<=h it is immediate. For L>h the pointwise difference
after clearing the denominator is `(L-2h)(h(L-2h)+1)>=0`, since L-2h
is an integer. The same formula applies below with the supported13
square bound. The numerical consumer only needs knots through17, so
the verifier extends1--12 through17 by these full-tail formulas. The
underlying profile construction applies at every real threshold.

<a id="full-physical1113-comparison-and-one-conditioning"></a>
### Full physical11/13 comparison and one conditioning

Apply actual pure-survivor AP11/T4 and AP13/T6 without intermediate
conditioning. Their physical law mu13, conditioned once on all actual
survivors after13, is precisely the same nu13 used in PR. The
shared-cell certificate strengthens its observations to

    rho13>=r=18925009844347/38266567762500>0,
    Gamma13<=g=6471426752685569/37850019688694.           (SP4)

AP1--AP5 compare full labelled tests to independent auxiliary factors
N11,N13 with caps c11=5/3,c13=2 and

    Pr(Np=1)=1-cp/p,
    Pr(Np=v)=cp(p-1)p^-v, v>=2,
    E Np=1+cp/(p-1).

Put N=N11*N13; its complete mean is49/36. The prefix caps hold on
every physical history, so for all t>=1,

    E_mu13(L-t)_+<=U(t):=E_N[N H357(t/N)].              (SP5)

These are comparison variables, not independent actual forbidden
events. No adaptive original test residues are chosen. Since
H357(t/n)=M-t/n for n>=t, the exact full-tail formula is

    U(t)=sum_(n<t)Pr(N=n)*n*H357(t/n)
             +M E[N;N>=t]-t Pr(N>=t).                  (SP6)

Subtract finite parts from the full probability1 and mean49/36 to
evaluate both tails. Every real t>=1 has a finite low-part evaluation
with the complete remaining tail retained.

For a>=t>=1, `(L-t)_+<=a-t+(L-a)_+`. Nonnegativity of the hinge and
the proved positive lower normalizer r give

    H13(t):=sup_L E_nu13(L-t)_+
       <=inf_(a>=t)[a-t+U(a)/r],
    sup_L E_nu13 L<=a+U(a)/r, a>=1.                    (SP7)

The second bound at a=6 gives SP1. Use a=6 for retained integer t<=6,
a=t for retained integers above6, and the minimum with SP3 at G=g.
The program checks the selected witnesses among1,...,17; it does not
claim a global minimum over every real a.

|t|H13(t) upper bound|
|---|---:|
|1|9.653915366989825...|
|2|8.653915366989825...|
|4|6.653915366989826...|
|6|4.653915366989826...|
|8|3.296496079559025...|
|12|1.845797624615341...|
|17|1.0561291774771513...|

In particular,

    H13(6)<=1144980123755523/246025127976511,
    H13(8)<=2583101470464529227/783590032605187535.       (SP8)

The certificate retains all17 consumer knots and every auxiliary tail
mass and mean. Chords give intermediate bounds; SP5--SP7 give a full
function beyond the table. These are simultaneous observations of one
actual law, without asserting that the upper envelope is itself a
comparator probability distribution.

<a id="single17-continuation"></a>
### Single17 continuation

From nu13 use actual pure-base AP17/T8, delta=7/15 and full-Haar cap2.
Its assigned charge is at most H13(8)/8<1; the unconditioned square
is at most(89/64)g. The ordinary AP bound gives

    Gamma17<=1+[(89/64)g-1]/[1-H13(8)/8]
             =403.70034396394783... .                   (SP9)

Keeping SH26's natural-cap deficit improves this to SP2. The exact
combined SH27 charge and energy cost is

    h17,W(z)=W(z-8)_+/8
               +(50/256)[16/(16-min(z,8))-2].

Above its convexity threshold it is increasing and convex. Its
integer values expand as a constant and nonnegative coefficients of
L-1 and (L-j)_+. Substitute SP1 and SP8, then solve the affine SH28
inequality in W. The verifier checks the coefficients and criterion
at the resulting W. Among integer thresholds1,...,15, threshold8 gives
the smallest bound from this functional. No other-kernel or
real-threshold optimality is claimed. The resulting actual17 law has
positive survival at arbitrary original17 heights and residues.

<a id="two-distinct1719-continuations"></a>
### Two distinct17/19 continuations

The consumer checks all255 pairs T17 in{1,...,15}, T19 in{1,...,17}
in each of two constructions:

* Restart: form nu13 as in SP4, then apply17 and19 physically and
  condition only after19. Source observations are g, SP1 and SP7.
* One final conditioning: start from uniform nu357, physically apply
  11/T4,13/T6,17/T17,19/T19, and condition only after19. Use the
  shared-cell357 profile with M,G; no supported13 observation or
  normalizer is inserted midway.

At p set d=p-1-T, cp=(p-1)/d, ap=(3p-1)/(p-1)^2, and let fp be the
product of later square-growth factors. The existing SH27 cost is

    hp,W(z)=W(z-T)_+/d
              +fp*ap[(p-1)/(p-1-min(z,T))-cp].

It is increasing and convex for W>=fp*ap*cp. Its complete integer
expansion has nonnegative mean and hinge coefficients. Earlier
auxiliary products use individual probabilities below T and the
full tail mass and mean for every remaining affine cost, as in SP6.

Write AW+B for the sum of certified costs. The SH28 residual is
I+(A-1)W, with

    I=G_source*product_p(1+ap*cp)-1+B.

Every tested schedule has I>0. If A>=1 the functional has no finite
solution. Otherwise set W=max(W_min,I/(1-A)) and check the full
criterion there; SH28 gives positive actual survival and supported
square at most1+W. The program separately verifies the complete
integer identity and residual at W=483 in all510 schedules.

There are72 finite sufficient bounds for the supported13 restart and
59 for four physical steps. The best in each uses T17=T19=8:

    Gamma19_restart<=14309324828593686784688579
                         /6107986643845861414296
                    =2342.7236605062217...,
    Gamma19_once<=81121527504111209187751525
                         /33163008211196445012696
                    =2446.1450236207183... .            (SP10)

Both yield actual positive survival for arbitrary finite original
families supported on3,5,7,11,13,17,19. No literature-priority claim
is made for this prime-support consequence. The first does not pass
through the conditioned single17 law from SP2.

|construction|minimum A among255|minimum residual at W=483|
|---|---:|---:|
|supported13 restart|0.8650551339908986...|242.74759569039884...|
|four physical steps, one conditioning|0.9354945670061158...|121.19490304202002...|

The least W483 defect in both is at T17=6,T19=8, distinct from the
best finite-bound schedule. All residuals are positive; no stated
integer schedule reaches484 through this upper functional. This does
not lower-bound actual charges or moments, exclude noninteger
schedules, refute the covering theorem, or exclude a certificate
using actual joint bad-set/test observations.

The implementation reuses generic `build_step` and `verify_at` from
the pinned `verify_pg1_scalar_schedule.py`. Its PG1 data loader and
13/T5 whole-N2 improvement are never called: the source is the
shared-cell strengthening of actual AP13 and all13 steps have
threshold6. A check rejects any different-law improvement in a row.
Source certificates and reused code are SHA-256 pinned. Default mode
validates the entire JSON; `--write` regenerates it. Duplicate keys
and changed fractions are rejected under `python3 -I -O`.

Published PR certificates remain unchanged. The finite computations
verify displayed constants and schedule outcomes; arbitrary-height
claims use the ordinary argument above.

The [supported13 profile verifier](../verify_supported13_hinges.py) checks the
[exact profile and continuation certificate](../certificates/supported13_hinges_certificate.json).
It uses the generic coefficient routines of the preceding pinned program,
without its PG1 law-specific data or threshold5 improvement.

<a id="finite-core-stability-for-the-actual-pure-base-ap-law"></a>
## Finite-core stability for the actual pure-base AP law

For every finite original family on3,5,7,11,13, use its actual uniform357
survivors, its actual pure-base AP11/4 and13/6 kernels, and one final
conditioning. Let nu_F be this supported law. Let F_b retain exactly its
original forbidden labels whose five exponents are at most b, with all
residues unchanged. Construct nu_b by the identical rule applied to F_b.
Both probabilities are lifted to one common finite physical period.

There is an explicit uniform bound E_b, proved below, such that

    |Gamma_full(nu_F)-Gamma_box_b(nu_b)| <= E_b.          (APC1)

The exact certificate gives

| b | E_b upper |
|---|---:|
|11|0.803401658|
|14|0.042600351|
|16|0.005840800|

Every omitted original forbidden class and every omitted test pair enters
a complete positive tail. This result concerns the pure-base AP(4,6)
probability, not the earlier AO full-Haar probability. The core law need
not avoid the omitted forbidden classes; the full nu_F does avoid them.
The finite core maximum is not computed by this error estimate.

The source constants are those of PR2 and the stronger shared-cell
hinge continuation (HC9):

    G0=3849/106, D0=432/53,
    r=18925009844347/38266567762500,
    G=6471426752685569/37850019688694,
    D=1039695426000000/18925009844347.

Every complete actual357 uniform law has square at most G0 and Haar
density at most D0. Both actual AP13 probabilities have square at most G,
Haar density at most D, and unconditioned final retained mass at least r.
These bounds hold for every original finite height, including missing
classes and uniform padding to a larger common physical period.

<a id="weighted-variation-before-the-current-prime-steps"></a>
### Weighted variation before the current-prime steps

For two finite positive measures on one old period, put

    Delta2(sigma,tau)=sup_A integral A^2 d|sigma-tau|,
    Delta0(sigma,tau)=integral d|sigma-tau|,

where A ranges over complete old divisor tests with independently chosen
residues at each original label. Delta0 is L1, twice the probability
convention for total variation when both measures are probabilities.

Use the previously proved localized two-test/one-query factor

    Phi_p(a)=(a+1)^2+2(a+1)/(p-1)+(p+1)/(p-1)^2,
    Sigma_p=p(p^2+4p+1)/(p-1)^3.

For a prime set S, define complete query-label tails

    T0(S,b)=product_(p in S)p/(p-1)
             -product_(p in S)sum_(a=0..b)p^-a,
    T2(S,b)=product_(p in S)Sigma_p
             -product_(p in S)sum_(a=0..b)p^-a Phi_p(a).

The second sum truncates only the queried forbidden label. Both test
axes remain complete, as in the cubic-tail result preceding PP1.

Let S_full subset S_core be the actual357 survivor sets for F and F_b,
with Haar masses s and s0. Put delta=s0-s. Their uniform laws mu,mu0
satisfy the exact identity

    integral A^2 d|mu-mu0|
      = (delta/s0) E_mu A^2
          +(1/s0) integral_(S_core\S_full) A^2 dHaar.

The removed set is contained in the union of omitted original357
cylinders. Their probability sum is bounded by T0, and their localized
square sum by T2. Since s0>=1/D0, this proves simultaneously

    Delta2(mu,mu0)<=e0w=D0[G0*T0(357,b)+T2(357,b)],
    Delta0(mu,mu0)=2delta/s0<=e0m=2D0*T0(357,b).        (APC2)

The square expectation in the first term is under the full actual
uniform law. The second term is an unnormalized Haar integral over the
removed set; no observation from a different supported law is inserted.
