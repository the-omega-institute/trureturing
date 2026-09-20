[Index](../../marked_head_profile.md) · [Previous](28-zero-local-losses-do-not-imply-a-common-maximizing-original-layout.md) · [Next](30-actual-threshold-deficits-and-sharp-row-caps.md)

<a id="a-common-old-block-budget-strengthens-the-actual-mask-certificate"></a>
### A common old-block budget strengthens the actual mask certificate

The positive-current blocks in MW4 all lie in the same complete original
old-test domain. Enforcing their common weighted-square budget gives a
stronger joint certificate, including an explicit coefficient improvement
when the original modulus19 class is present. An actual six-class family
also shows that the scalar version can improve the entire optimized family
min_r U_r. All conclusions below use the actual input
sigma=xi=nu13 K17^- and eta=xi K19^-; no physical17 input is substituted.
These are ordinary proofs with exact rational certificates, not Lean proofs.

<a id="complete-original-domain-and-a-priced-budget"></a>
#### Complete original domain and a priced budget

Keep every MW1 definition and original label. Let N be the number of
complete old divisor-test labels, including the single unit label. Every
old block A satisfies1<=A<=N. Write

    M=G(g), B_r=(b-kappa)G(c)+kappa G(w),
    g=q+S c²/v.                                          (BM1)

The last identity follows from r lambda=S rho and v+rho(c-q)=c.
For a single price t>=0, independent of the sampled point, put

    v_t=v+t g, z_t=c/v_t, f_t=q+S c²/v_t,
    F_t(x,n)=q n²+S max_(1<=j<=N)[2cjn-(v+t g)j²].        (BM2)

All weighted expressions are0 where c=0. Else v_t>0, f_t>=0. Completing
the square gives

    F_t(x,n)=f_t n²-S v_t dist(z_t n,{1,...,N})².

For fixed x the integer cost is convex and nondecreasing in n>=1. It need
not be nonnegative for arbitrary large t; none of the following arguments
requires that extra assertion. For every finite original current height,

    sup_L eta L² <= B_r+StG(g)+max_A integral F_t(x,A(x))d xi
                 <= B_r+StG(g)+G(f_t).                 (BM3)

In particular the infimum over prices never worsens its t=0 integer
version. The residual and the positive cost stay inside the same old-layout
maximum.

To prove BM3, MW4 first gives

    eta L² <= B_r+integral g A0²d xi
                   -sum_(e>=1)p^-e integral v(Ae-zA0)²d xi.

Each actual Ae belongs to the complete original domain, and so does the
comparison padding Ae=A0 beyond its finite current height H. Therefore
integral g Ae²d xi<=M for every e. Pointwise,

    v(Ae-zA0)²+t g Ae²
       >=min_(1<=j<=N)[v(j-zA0)²+t g j²].

Integrate, sum the full series sum p^-e=S, and pay exactly StM. BM1 and
completion of the square yield the first inequality. Dropping its
nonnegative distance yields the second. The comparison padding does not
create new original forbidden or test labels; MW3's complete tail is still
present. This uses the same legal domain for every positive block, rather
than allowing its integer value at each point to consume an unlimited norm.

For finite rational row data, the first right side is convex and piecewise
affine in t: each integer branch is affine in t, with a finite maximum at
each point and over all original A. Every nonnegative rational price is a
valid certificate without relying on an optimizer's convergence. These
corrections spend MW4's amplification residual; they are not additional
subtractions from the full OBE profile or from an unrelated KC envelope.

<a id="a-ratio-cap-gives-an-explicit-coefficient-and-an-actual-integral"></a>
#### A ratio cap gives an explicit coefficient and an actual integral

Suppose q/c<=u_*<=1 on c>0, for these same actual rows. Define

    d_*=lambda+rho u_*, e_*=u_* d_*+S,
    t_*=d_*(1-d_*)/e_*, gamma_*=S(1-d_*)²/e_*,
    a_*=1-S t_*/d_*, R_*=a_* g-f_(t_*).                 (BM4)

Then0<=a_*<=1 and R_*>=0, and

    sup_L eta L²
      <=(1-gamma_*)G(g)+(b-kappa)G(c)+kappa G(w)
            -integral R_*d xi.                         (BM5)

Indeed write u=q/c, d=lambda+rho u, e=ud+S. Direct division gives

    f_t/g=1-St/(d²+t e).

Both d and e increase with u. At t=t_* the denominator is at most
 d_*²+t_*e_*=d_*, so f_(t_*)<=a_*g. Positivity of a_* follows from
St_*/d_*=S(1-d_*)/e_*<=1. Finally A>=1 implies

    G(f_(t_*))<=a_*G(g)-integral R_*d xi,
    a_*+St_*=1-gamma_*.

Substitute in BM3. The ordinary integral is computed from the actual
weights and can vanish. A claimed saving gamma_*G(g) cannot be lower
bounded by inserting an upper bound for G(g); valid upper certificates
instead enter the nonnegative coefficients of BM5.

For the actual flat killed row R_x=c(x)1_(G_x)u19, q/c is its surviving
full-Haar fraction. If an original modulus19 class is present, its root
exclusion gives u_*=18/19, whatever that forbidden residue is. Additional
pure or mixed exclusions only shrink this fraction. At p=19,r=theta,

    d_*=6535/6859, e_*=2247661/2345778,
    t_*=38112120/811405621,
    gamma_*=104976/811405621
            =0.000129375490239548...,
    a_*=2241505/2247661.                               (BM6)

Consequently the signed actual bound is

    sup_L eta(L²-484)
      <=(811300645/811405621)G(g)
          +(37/361)G(w)+(865/58482)G(c)
          -xi(R_*)-484 eta1.                           (BM7)

All original heights remain arbitrary and finite. Without the original
modulus19 class, BM3 still applies; BM4 uses whatever ratio cap is proved
for that actual family. The universally safe choice u_*=1 gives
 t_*=gamma_*=R_*=0. No extra forbidden class is inserted into an already
fixed actual law.

<a id="strictness-at-a-positive-parameter"></a>
#### Strictness at a positive parameter

The scalar budget can also be compared to the optimized old MW family.
Fix r>0 and suppose integral g(z²-1)d xi>0. The finite old domain gives

    d/dt|_(0+) [B_r+StG(g)+G(f_t)]
       <=-S integral g(z²-1)d xi < 0.                  (BM8)

To see this, f'_0=-Sgz². At t=0 only maximizers of G(g) determine the
right derivative of the finite maximum. Every such A obeys

    integral gz²A²d xi
       =G(g)+integral g(z²-1)A²d xi
       >=G(g)+integral g(z²-1)d xi.

Thus some positive price strictly improves U_r. If a minimizing r for the
entire old interval0<=r<=theta is positive and satisfies this hypothesis,
BM3 strictly improves that entire minimum. This is an existence statement;
it supplies no uniform numerical saving where the displayed integral tends
to zero. At r=0, choosing j=n in BM2 proves the integer priced expression
is at least U0, so pricing alone there does not force an improvement.

<a id="an-actual-six-class-example-beats-the-entire-old-parameter-interval"></a>
#### An actual six-class example beats the entire old parameter interval

Take the six literal distinct odd classes

    3 mod9, 8 mod27, 0 mod19,
    20 mod57, 2 mod171, 326 mod513.                     (BM9)

The old period is27, with23 actual survivors. The absent5/7/11/13/17
steps are identities on their unused coordinates, so xi is exactly uniform
on those23 points. The three mixed19 exclusions have old cofactors3/9/27,
old residue2, and respective current residues1/2/3. Set

    k(x)=1_(x=2 mod3)+1_(x=2 mod9)+1_(x=2 mod27).

The pure base has18 roots. The actual mixed fraction k/18 is below7/17,
so the assigned charge is0 and every killed row has mass1. Its density
on its actual surviving roots is

    q(x)=1, c(x)=19/(18-k(x)).

The complete513-period survivor set has402 points; a point above x has
actual weight1/[23(18-k(x))]. The certificate reconstructs that actual
kernel from all six original classes. The full old test domain consists
of all729 independent residue choices at3,9,27, retaining its unit term.
It gives

    G(c)=54283/15640, G(w)=50701/15640,
    min_(0<=r<=theta) U_r
       =4903795219637565032713/1321543170681494545890
       =3.7106583639706385... .                        (BM10)

This minimum has a certificate for the whole parameter interval, not a
sampled grid. Write rho=r/(S+r), so0<=rho<=324/361. For a fixed layout A,

    integral [q+S c²/(c-rho(c-q))] A²d xi
                +bG(c)+(S rho/theta)[G(w)-G(c)]

is convex in rho. At its right endpoint the layout(1,1,1) is active in
G(g); its derivative, including the linear term, is exactly

    -124104315223942849669858982545049
       /9732274850802584322531169759311300 < 0.

The supporting tangent of this one active convex branch is at least its
endpoint value throughout the interval to its left. The whole maximum is
at least this branch, proving BM10. In this family G(c) and G(w) are attained
at(2,2,2), while G(g) is attained at(1,1,1); each claim is verified over all
729 layouts.

At t=1/18, the scalar budget BM3 is

    B_r+StG(g)+G(f_t)=3.710034179714640... <3.710035,

strictly below BM10. The exact fraction and maximizing-domain evaluation
are recorded in the certificate. The integer budget is424158493/114332310,
about3.709874251644177. Its t=0 integer version already has that same value
in this example; the example establishes the scalar improvement over
min_r U_r, not an extra integer improvement there. No full final-layout
maximum or positive mixed-charge claim is made for this family.

<a id="actual-sharpness-of-the-pure19-coefficient"></a>
#### Actual sharpness of the pure19 coefficient

Let Q0=3*5*7*11*13*17=255255. For any finite H>=1, forbid0 modulo every
nonunit divisor of Q0*19^H. All original forbidden moduli are distinct.
The uniform actual357 source and its actual11/13/17 steps yield exactly
uniform units modulo Q0; mixed exclusions are inactive on the preceding
units, and the sole13 conditioning has mass1. The actual killed19 kernel
is uniform on its units, with q=1,c=19/18. Both assigned mixed charges are0.

For any original test labels m,n, their intersection mass under the unit
law is at most1/phi(lcm(m,n)). A common unit centre1 attains every such cap
simultaneously. Thus maximizing over every independent original residue
gives

    Gamma_xi=product_(p|Q0)[1+3/(p-1)]=25935/2048,
    sup_L eta L²=Gamma_xi[1+c a_H],
    a_H=sum_(e=1..H)(2e+1)19^-e.                      (BM11)

All MW weights are constant here. With a=S+b, BM5's right side equals
Gamma_xi(1+ca), and R_*=0. Its exact remaining gap is

    c Gamma_xi 19^-H(2HS+a).                          (BM12)

This tends to0 as H grows through finite integers. Any universal
replacement gamma'>gamma_* in the same coefficient form therefore fails
for some finite member of this actual family. The conclusion concerns
this certificate form; the stronger full OBE profile is not ruled out.

Already H=3 gives255 original forbidden classes,256 complete tests and64
old labels, with

    sup_L eta L²=1165255/77824,
    eta maximum-[U_theta-2gamma_*G(g)]
       =18605587/24716980224 >0.                       (BM13)

The verifier checks all65536 ordered original-label pair caps and an
independent literal scan of the19^3 coordinate. It does not enumerate the
1,750,794,045-point full period.

There is also a strict integer improvement on this same actual family.
Convex concentration in each squarefree old prime coordinate maximizes
F_t: conditional on all other coordinates, all nonnegative test increments
can be put at one nonzero root. Convexity ensures that concentrating them
increases their uniform convex average. Fixing that root for every label
containing the prime works simultaneously for all other-coordinate values;
CRT preserves each original label. Iterating proves the centred maximum.
Its load distribution is A=product_(p|Q0)(1+I_p), with independent
Pr(I_p=1)=1/(p-1). Exact evaluation gives

    raw U_theta =92538380753/6179245056,
    integer t=0 =161413602929/10779402240,
    integer t=t_*=3725995/248832,
    strict integer gain=3499529/10779402240 >0.         (BM14)

Here v+t_*g=c, so the budgeted integer optimizer is j=n, and its value
also equals the r=0 split cap. BM14 proves a strict refinement of the
integer interface on this family; BM9--BM10 separately demonstrate an
improvement over the optimized MW parameter family. Neither witness is
an unrestricted numerical noncoverage theorem.

<a id="sharper-actual-row-caps-and-complete-test-only-tails"></a>
#### Sharper actual row caps and complete test-only tails

The actual killed row is a subprobability row, so q<=1 as well as
0<=q<=c<=9/5. For fixed q,

    partial_c g=S c(lambda c+2rho q)/v²>=0.

At c=9/5 it is convex in q. The endpoint values on0<=q<=1 are361/370
and2531/2170, respectively. Since w and v increase in both arguments,

    g<=2531/2170, w<=261/185, v<=1953/1805.              (BM15)

These are maxima on a necessary cap region; no finite arithmetic family
is claimed to attain its extreme point. Keep xi,c,q,all forbidden masks
and eta1 fixed, and truncate only original old test labels as in MW8.
The complete three-norm tail coefficient improves from2090/9 to

    110[g_max+kappa w_max+(b-kappa)c_max]
       =103734290/705033.                              (BM16)

For the budgeted integer cost one also has, with the same full ceiling N,

    0<=F_t(n)-F_t(m)<=F_0(n)-F_0(m)
       <=[g+Sv/12](n²-m²), 1<=m<n<=N.                 (BM17)

For the first inequality, a maximizing j_t(n) is a nearest integer to
c n/(v+tg), clamped to[1,N], hence is nondecreasing in n. Away from the
finitely many price breakpoints, the derivative in t of the cost difference
is -Sg[j_t(n)²-j_t(m)²]<=0. Continuity proves the price comparison.
At t=0, z>=1. If zm>N, both integer distances are upper-endpoint distances
and the distance at zn is larger. Otherwise the distance at zm is at most
1/2. Completing the square bounds the excess over g(n²-m²) bySv/4;
 n²-m²>=3 proves BM17.

Thus use C_F=g_max+Sv_max/12=11011381/9400440 and the complete pair tail
T_B already defined in MW8. The error in BM3's first right side is at most

    110[St g_max+C_F+kappa w_max+(b-kappa)c_max]T_B.    (BM18)

The StG(g) term is explicitly paid. The full original N inside F_t is
unchanged even when the baseline is restricted to a box; lowering that
ceiling would need another proof. The finite values are

    original MW, B16/B20: <0.000357927 /0.000005399757;
    BM7 pure19, B16/B20: <0.000357886 /0.000005399147;
    BM3 at t_*, B16/B20: <0.000360082 /0.000005432265.    (BM19)

The actual integral xi(R_*) and signed mass term remain exact under
this test-only truncation. Changes to the actual input probability or
forbidden masks require their separate common-carrier error estimates.

The [standard-library verifier](../../verify_budgeted_mask_square.py) reconstructs
its entire [certificate](../../certificates/budgeted_mask_square_certificate.json), including
both actual families, all original old layouts in BM9, the continuous
parameter tangent, the coefficient refutation, and complete geometric
pair tails. Run it with `python3 -I -O`. Independent rational derivations
confirm the constants and the budget identity. Repository MW/OBE/CRT
results are reused directly; the norm-price step is an ordinary Lagrange
upper certificate, with no literature-priority claim or new Lean wrapper.
The remaining299.661 joint frontier and later-prime continuation are still
unproved.

<a id="a-positive-actual-deficit-with-arbitrary-seven-heights"></a>
### A positive actual deficit with arbitrary seven heights

The DB support bridge extends from original357 parts dividing315 to
original357 parts dividing `45*7^H`, for every finite H. Thus the original
3-exponents are at most2 and5-exponents at most1; seven exponents, residues,
11/13/17/19 heights and their original mixed cofactors are arbitrary.
For the same actual AP11/T4, AP13/T6 source and killed17/T8,19/T8 kernels,
every complete final test has

    Delta_81 > 1.721417864,
    Delta_121 > 3.917246877.                              (D7.1)

These are the CT3 deficits, not independent rebates to subtract from a
different optimized envelope. All higher original labels and geometric
tails are retained. The result does not supply the unrestricted299.661
bound, arbitrary3/5 heights, or a later-prime continuation. The following
is an ordinary mathematical proof with exact rational checks, not Lean.

<a id="one-supported-extension-and-two-separate-tail-budgets"></a>
#### One supported extension and two separate tail budgets

Fix the full original family. Its13-stage core retains exactly the
original labels whose357 part divides315, with all11/13 heights retained.
The DV theorem and DB1 give one auxiliary core probability nu0 satisfying

    E_nu0 A <= M0=1175795/219961,
    E_nu0 (A-t)_+ <= H_t  (t=4,...,12),
    nu0 <= D0 m_core,  D0=38288250/4021271,               (D7.2)

for every complete core test. The H_t are the pinned DV6 values. Set
H_1=M0-1, use linear interpolation between knots1,4,5,...,12, and set
H(t)=M0-t for t<=1. Convexity of each actual hinge proves these upper
bounds. They are simultaneous bounds on the same nu0.

Pull the canonical support back to the original coordinates before any
comparison. Lift nu0 uniformly in all additional357 digits to a probability
lambda. Let F avoid every original13-stage forbidden class outside the
core, including all its11/13 factors. Write beta=lambda(F^c), q=1-beta.
For each complete full13-test A, split A=A0+U at the literal core-label
boundary. A0 is a complete core test and U retains all other test labels.

The following general argument distinguishes two bounds:

    beta <= D0 R_F,       E_lambda U <= D0 R_T,
    D0 R_F < 1.                                         (D7.3)

R_F pays every actual omitted forbidden label. R_T pays every omitted
complete divisor-test label, even when that modulus is absent from the
forbidden family. Missing intermediate forbidden powers never authorize
removing those test labels. Neither sum depends on test residues.

The supported probability sigma=lambda(.|F) is well defined. The hinge
map is1-Lipschitz and U>=0, while A>=1. Thus, for t>=1,

    E_sigma(A-t)_+ <= [H(t)+D0 R_T]/q,
    E_sigma A <= [M0+D0 R_T-beta]/q.                     (D7.4)

The mean subtracts only the unit floor on F^c. The hinge inequality
subtracts no unavailable deleted-energy term. For t<=1 the mean gives
E_sigma(A-t)_+ <= [M0+D0 R_T-beta]/q-t.

The actual nu13 still starts from uniform probability on the full actual
357 survivors and conditions only after the two physical AP steps. As
in DB1, its density relative to Haar is at least one at every true
13-stage survivor: the initial survivor-uniform density is at least one,
and each good AP step contributes
`1/[lambda_p(1-min(alpha_p,delta_p))]>=1`. The nonempty sigma support
also proves positive actual conditioning mass. Since lambda has Haar
density at most D0,

    sigma <= (D0/q) nu13,
    zeta=sigma R17 R19 <= (D0/q) eta,
    eta=nu13 R17 R19.                                   (D7.5)

Here R17,R19 are exactly the original full-family killed rows on both
sides, including actual pure bases and all original cofactors. Their
definition does not depend on the incoming measure. Domination is used
only for nonnegative functions; auxiliary upper moments are never
substituted as actual nu13 upper moments.

<a id="complete-hinge-charges-on-the-same-supported-probability"></a>
#### Complete hinge charges on the same supported probability

The existing AP2--AP4 comparison at threshold8 gives

    b17 <= H_sigma(8)/8,
    b19 <= E[N H_sigma(8/N)]/10,                         (D7.6)

where H_sigma is the upper function in D7.4. For the second term the
input is sigma K17 with the normalized physical kernel, whose Haar cap
is2. It dominates the actual killed input for the nonnegative second
loss. Its complete comparison factor is

    Pr(N=1)=15/17,
    Pr(N=n)=32/17^n  (n>=2),
    E N=9/8,   E(N-8)_+=1/(8*17^7).                     (D7.7)

AP3 subtracts precisely one missing unit cofactor. It does not subtract
one for every auxiliary block. All completions retain their separate
original labels and are fixed before sampling; the comparison sum runs
through every current depth.

Define the core upper charge using the unchanged H and M0:

    b0=H(8)/8+E[N H(8/N)]/10
      =261627396289452999368807449626177
        /1900544377402598245753456000000000
      <0.137659189.                                     (D7.8)

This expectation is finite arithmetic plus a complete geometric tail.
For N>=8 use NH(8/N)=M0 N-8, and

    Pr(N>=8)=2/17^7,
    E[N;N>=8]=(129/16)*(2/17^7).

Substituting D7.4 into D7.6, including this tail, gives a lost-mass upper
bound b for zeta relative to sigma:

    q b <= b0+(19/80)D0 R_T-beta/(80*17^7).              (D7.9)

The coefficient19/80 is1/8+(E N)/10. The negative beta term is the
entire `E(N-8)_+/10` contribution, not a discarded tail. No intermediate
conditioning or change of the actual kernels is used.

<a id="capped-hinge-minorants-preserve-more-of-the-actual-deficit"></a>
#### Capped hinge minorants preserve more of the actual deficit

For A>=1 define

    g81(A)=[65-13(A-4)_+]_+,
    g121(A)=[105-9(A-4)_+-2(A-5)_+-6(A-6)_+]_+.

Then

    0<=g81<=(81-A^2)_+,  g81<=65,
    0<=g121<=(121-A^2)_+, g121<=105.                    (D7.10)

For g81 the inner expression joins the values of81-A^2 at4 and9,
is constant below4, and is nonpositive above9. For g121 it joins the
values of121-A^2 at4,5,6,11, is constant below4 and nonpositive above11.
Concavity of the quadratic proves both minorants on the whole real
domain A>=1, hence on every actual integer load.

The cap controls how much can be lost under R17,R19. If g=[K-sum c_t
(A-t)_+]_+ is either displayed function, with c_t>=0, D7.4 and D7.9 give

    E_zeta g >= K-sum c_t[H(t)+D0 R_T]/q-K b.

Apply nonnegative domination D7.5 and CT3. Put

    C_g=[K-sum c_t H(t)-K b0]/D0,
    P_T=sum c_t+19K/80,
    P_F=K*(1-1/(80*17^7)).

Since P_F>0 and beta<=D0 R_F, the full actual bound is

    Delta_tau >= eta g
       >= max(0, C_g-P_T R_T-P_F R_F).                 (D7.11)

In particular (K,P_T,P_F) are

    tau81:  (65,455/16,65-13/(16*17^7)),
    tau121: (105,671/16,105-21/(16*17^7)).

The smaller caps65 and105, rather than80 and120, are legitimate because
we transported the displayed bounded minorants. The denominator q
cancels only after source expectation, lost mass and domination have
been combined on the same measure. This cancellation neither identifies
the two probabilities nor allows a signed integrand to cross domination.

<a id="all-seven-heights-fit-the-complete-budget"></a>
#### All seven heights fit the complete budget

For the announced family, the omitted region is a7>=2, a3<=2, a5<=1,
with arbitrary11/13 exponents. In canonical coordinates the auxiliary
support lies inside pure-exclusion sets of Haar fractions

    (rho3,rho5,rho7,rho11,rho13)=(5/9,4/5,6/7,10/11,12/13).

The effective disjoint pure3/pure9 exclusions are part of the auxiliary
support construction; they do not require both effective classes in
the original family. Virtual roots only shrink support. The canonical
coordinate permutations preserve modulus cylinders and extend to all
higher digits, so these bounds pull back to the original family.

A cylinder with exponent a at p contributes at most rho_p when a=0
and p^-a when a>=1 to its intersection with this product support. The
common complete bound for both forbidden labels and test labels is

    R_F=R_T=R
      =(5/9+1/3+1/9)(4/5+1/5)
         *sum_(e>=2)7^-e*(10/11+1/10)*(12/13+1/12)
      =5809/240240.                                    (D7.12)

For forbidden labels this uses original distinctness; for tests it
sums each complete divisor label exactly once. The sums over11/13
include every mixed high-seven cofactor. Infinite positive tails
enlarge the finite actual sums and pay all omitted heights.

The exact extension constants and hinge-charge bound are

    beta<=200175/869464,   q>=669289/869464>0,
    D0/q<=D7=306306000/24763693,
    b<=365547569281917276124431199626177
        /1462985754220309957976506000000000
      <0.249864067.                                    (D7.13)

For the charge upper bound the rational expression from D7.9 is
increasing in beta on the allowed interval; the verifier also recovers
it directly from the uniform hinge/mean upper functions at q0.
Substitution in D7.11 proves the exact versions of D7.1:

    Delta81 >=3546376647013190559753919296342943
                /2060148625836608295061920000000000,
    Delta121>=586481926980399541577236545508217779699
                /149717887422095550035593219104000000000. (D7.14)

These hold for the literal inherited13 block of every complete final
test, not just a chosen maximizing layout. The positive bound is uniform
in seven height and all later11/13/17/19 heights. The same formulas with
R_F=R_T=0 strengthen the earlier DB consumer on its original scope.

The [standard-library verifier](../../verify_high_seven_density_bridge.py) reuses
the source-hash and upstream-section checks of the existing DB verifier,
recomputes the full geometric sums and all rational charges, verifies
the minorant tail signs and reconstructs the entire
[certificate](../../certificates/high_seven_density_bridge_certificate.json). It supports
`python3 -I -O` from outside the checkout. The source DV geometry,
support construction, comparison theorem and universal measure argument
remain the explicitly stated mathematical inputs; these arithmetic
checks do not constitute a new Lean theorem or a solution of Erdős #7.
