# The square allocation and the reweighted source

This note continues `339b-the-actual-near-j-source-and-the-unit-refund.md`. The original note was split so that each file stays inside the per-file line budget; no text was changed.

## The direct square allocation cannot continue through the scalar recurrence

This is a numerical consumption of the existing source/operator and killed-unit interfaces, not a new generic transfer theorem. It concerns the same fixed(3,4)full-Haar head as339. All original powers and independent own-test residues remain.

Let phi(v)=v^2-1. In339(IR10)--(IR12), replace h_t by phi. The zero7 centered comparison is(6/5)phi, so the modified cell costs are kappa_l phi, kappa_l=6/5-zeta_l. For these costs42(A2) has q_(n,l)=n f_l, bar f_l=f_l/4, complete ternary-depth increment kappa_l(b_l+1)/9, and positive5 coefficients7/8 and5/8. Hence its exact modified zero7 contribution is

    P=max_b[sum_l eta_l*kappa_l*(b_l^2-1)+max_l kappa_l*(b_l+1)/9],
    F=max_b[sum_l kappa_l*(n_l+eta_l/4)*(b_l^2-1)
                +max_l kappa_l*(d_l+1/4)*(b_l+1)/9]
           +(7/8)sum_l eta_l*kappa_l+(5/8)P.

All sums converge as polynomial times geometric tails. Retain the unchanged explicit positive7 complement. On each of the nine containing source vertices the resulting centered-square cost is304687/57624, versus the old263/48. The same positive WF transport gives

    integral(L^2-1)dmu <= M2=1220880809/230496000.

The two head square factors are51/35 and67/48, with product J2=1139/560. Let z be the actual unnormalized through13 survivor mass and E(S)=eS-D as339. Before head killing the full square integral is at most J2(M2+S). Every complete test is at least1 on the actual head-deleted set of mass S-z. Subtract that unit square before the sole normalization, giving the allocated upper

    Gamma13<=1+[J2*M2+(J2-1)S]/z
            <=g(S):=1+[J2*M2+(J2-1)S]/(eS-D).

This is decreasing in S on E(S)>0. From339(IR2),(IR8) and s<=1/4+delta0/2,

    S<=1/4+delta0/2-a(1/8-delta0/12)-b(1/12-delta0/9)
      =123557689/576240000=:Smax,
    g(S)>=g(Smax)=334490138381673633/3923164203788188>85.

The lower bound here is on the allocated upper-bound formula g, NOT on actual Gamma13. Replacing g by a smaller valid bound would be a different method.

Combine the [unit refund in327](327-actual-two-prime-survival-needs-a-masked-moment.md)
with the [arbitrary-head transfer](../../problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md).
Without an additional masked deficit, this scalar procedure assigns

    R_p(F,d)=F[d(1+a_p-d)-b_p]/[d(1-d)-b_p F],
    a_p=(3p-1)/(p-1)^2, b_p=1/[4(p-1)^2], 0<d<1,

with strictly positive denominator. To derive it, start from a normalized
old-survivor law with Gamma<=F. The full kernel gives
`G=(1+a_p/(1-d))*F`; its actual deleted mass ell is at most
`q=b_p*F/[d(1-d)]`. Every complete test has unit at least1, so conditioning
on actual survivors gives at most `(G-ell)/(1-ell)`. Since G>=1, this
ratio increases with ell, and replacing ell by q in both places gives
R_p when q<1. The same actual deleted mass is thus used in numerator and
denominator before its bound is inserted. For fixed d this is increasing in F on its legal domain: writing v=d(1-d),u=v+a_p d-b_p, the difference at F2>=F1 is

    u*v*(F2-F1)/[(v-b_pF2)(v-b_pF1)]>=0.

Here u>0 because v>b_pF2>=b_p. If F2 is legal then every1<=F1<=F2 is legal, so the comparison also holds when thresholds are selected adaptively from previous scalar bounds.

For any proposed input f and output lower k>f, the inequality R_p(f,d)>k follows on every legal d if

    (k-f)d^2+(f-k+a_p f)d+b_p f(k-1)>0.

Three exact all-real quadratic certificates are:

| p | f | k | 4AC-B^2 |
|---|---:|---:|---:|
|17|85|171|625111/16384|
|19|171|480|8981/324|
|23|480|1000|4544192000/14641|

Each leading coefficient A=k-f and each displayed slack is positive, proving positivity without a numerical threshold grid. Thus every choice of legal later clipping parameters from this allocated seed has scalar bound above1000 after23, if it has not already lost its positive denominator. At29, legality requires F<(29-1)^2=784 since d(1-d)<=1/4. It therefore cannot continue.

This rejects the direct weighted square allocation followed by this scalar majorant, even with its unit refund and arbitrary later thresholds. It says nothing negative about actual surviving mass, improved nonlinear or masked estimates, another initial law, another head, or the unrestricted odd-covering problem. In particular it does not invalidate339's positive through37 hinge certificate, which carries a richer state.

The [sharpness and scalar-boundary producer](../../frontier/source-budgets/source_mean_sharpness.py)
replays the quadratic source operator, its unchanged complement, the
complete head multiplier and all three completed-square identities.
Their exact data share the [same canonical certificate](../../certificates/source_norms/source-budgets/source_mean_sharpness.json)
as the limiting-mean theorem above. The common report and one producer
retain the mathematical results and exact checks without a separate
search transcript.

## A fixed reweighted actual source survives through41

Under the same effective9, original noncontainment and original numerical
modulus7 hypotheses of(IR8), the stronger source guard

    qJ>=1-1/4000, rho>=3/50                              (RW1)

implies positive actual survival through41. Use cell weights
`r=(11/8,5/4,1,1,1)` in the ordered surviving mod9 cells(0,3,1,4,7),
with the same chart orientation as(IR8). Keep the full-Haar11/13
thresholds(3,4), then use thresholds(6,8,9,12,16,20,23) at
primes(17,19,23,29,31,37,41). Relative to the reweighted supported13
probability, the complete actual survivor mass through41 is greater
than1/125. In particular, a finite original family satisfying(RW1)
whose prime factors are all at most41 cannot cover the integers.
All original exponent heights and own-test residues are retained.

The rho condition3/50 is stronger than(IR7)'s7/125. The new F12 above
satisfies(RW1), establishing a nonempty source domain. It is a noncover.
No optimal weights, through43 or all-prime continuation is claimed.

### One new law, the same actual forbidden sets

Define the finite positive measure and its total mass by

    dmu_r=r(x mod9)dmu, T=mu_r(1).

Its normalized initial probability is mu_r/T. The full-Haar clipped
kernel at a prefix x uses only the actual forbidden fibre, its current
Haar fraction alpha_x and the fixed threshold. Changing the old point
weights does not change these kernels or their caps. On the common
raw physical chain, the new measure equals r times the old measure.
Since1<=r<=11/8, both have exactly the same actual survivor support.
The weights persist on the original3 coordinate at every later stage.

Normalize the new actual head survivors once, using their own mass z_r.
Positive survival under this probability proves an actual surviving
integer; its numerical masses are relative to this new supported13 law.

### A finite-delta lower bound for the weighted mass

Let mu0,muB be the post-seven masses in cells0 and3, and muR the sum
in the three root1 cells. Then S=mu0+muB+muR and exactly

    T=(11/8)S-(1/8)muB-(3/8)muR.                       (RW2)

The containing-chart inequalities of329 give
`z<=3/4+delta/4`, `alpha1>=(1-delta)/4`,
`betaR>=(1-delta)/4`, `lateR>=(1-delta)/72`.
Writing d_l=z-alpha_ROOT(l)-beta_l>=0, discard only the nonnegative
pure-deficit terms in the original raw35 formula to obtain

    nR<=sum_R d_l/9-lateR<=1/8+5delta/24,
    nB<=z/9<=1/12+delta/36.

Thus(IR8) gives the actual post-seven capacities

    muB<=CB(delta)=(1-zeta_B)(1/12+delta/36),
    muR<=CR(delta)=1/8+5delta/24.

Combining(RW2) with(WF4), with no assumption of attaining these
capacities simultaneously, proves

    T>=L_r(rho,delta)
      :=(11/8)[3/20+rho-(263/360)delta]-CB(delta)/8-3CR(delta)/8.
                                                               (RW3)

The coefficient ofdelta is-26257337/24202080<0. Hence the fixed error
budget delta0=1/4000 gives a uniform lower bound for everydelta<=delta0.
At rho=3/50 it is

    T>=22726567063/96808320000=0.234758407779414... .     (RW4)

This bounds the same actual weighted measure, without asserting a
realizable capacity optimizer. qJ,rho and S0 retain329's definitions.

### Every original source cost carries its cell weight

Keep p_n from(IR11), and for rational t>=1 and e>=0 define

    Q_(t,e)(v)=sum_(n>e)(p_n/n)[h_t(nv)-h_t(n)],
    s_r^Lambda=sum_l r_l*n_l.

The complete cell-dependent source bound is

    B_t^r(theta)=s_r^Lambda*E h_t(N7)
       +F_theta(r_l[Q_(t,0)-zeta_l*h_t])
       +sum_(e>=1)F_theta(r_l*Q_(t,e)).                 (RW5)

Here F_theta is exactly42(A2), with the original d,n,eta. This follows
by multiplying the same-original decomposition(IR10) by r_l before
comparison. The zero7 saving acts on its own original block; every
positive7 block and the constant term also receive r_l. The multiplier
is independent of the current5/7 coordinate and fixed before choosing
any original test, so the pointwise centered Jensen arguments apply.

All transformed costs are nonnegative, increasing, convex and vanish
at1. Multiplication by positive r_l preserves these facts and the
nonnegative deep increments in42(A3)--(A5). WF3 therefore still gives
`integral h_t(L)dmu_r <=lambda B_t^r(theta*)`, with the same
lambda=1+7delta0. The nine containing vertices control every fixed
nonnegative combination of these costs by separate convexity; the
maximum is taken after forming each complete payment.

All tails in(RW5) are complete. For an eventual affine cost av+b with
entrance k, the remaining7-block coefficient is
`a[E(N7;N7>=k)-(k-1)Pr(N7>=k)]` times F_theta(r_l*(v-1)).
The cell-dependent5 tails likewise retain both probability and first
moment, with slopes multiplied by r_l. No original exponent cutoff is
imposed. A sufficient same-measure mean bound is

    integral(L-1)dmu_r<=M_r:=lambda max_theta B_1^r(theta)
       =129284945411/193616640000.                     (RW6)

### The complete head and the unit refund use massT

Reuse(IR17)'s complete11 count atoms and tails, but replace every
source hinge by B_t^r and the source mean by M_r. Explicitly,

    C13^r(theta)=lambda sum_(n<4)u_n*n*B_(4/n)^r(theta)+T1*M_r,
    D_r=max_theta[lambda B_3^r(theta)/7+C13^r(theta)/8]
       =8070958205846453/90196311744000000,
    z_r>=E_r(T):=e*T-D_r, e=74535/74536.                (RW7)

At(RW4), the denominator is
`26206200489324719/180392623488000000>0`. Thus the sole normalization
on actual head survivors is legitimate for every source in(RW1).
Pure11/13 powers are included in the actual bad unions and paid by the
unit labels, as before.

For a later target p,t retain(IR19)'s full count product W, post13-only
product Z, their low atoms and complete tails. Put

    C_p^r=lambda max_theta sum_(n<t)u_n*n*B_(t/n)^r(theta)+T1*M_r,
    c_p'=T1-t*T0, f_p=E(Z-t)_+.

The complete physical integral is at most C_p^r+c_p'*T. Each original
through13 block still includes its unit, so the post13 comparison
functional is pointwise at least f_p on the mass removed at the head.
Subtracting f_p*(T-z_r) before normalizing gives

    H_(<p,t)<=f_p+[C_p^r+(c_p'-f_p)T]/(e*T-D_r).        (RW8)

Here c_p'>=f_p>=0. The floor uses Z only, and is not multiplied by a
maximum cell weight. All quantities refer to the same reweighted law.
Later assigned charges are evaluated under their full incoming physical
laws; domination of earlier killed sets gives the same union bound.

Define Fq,Kq as in(IR21), Cq^r=sum k_p*C_p^r, and

    Aq=(1-Fq)e-Kq, Bq^r=(1-Fq)D_r+Cq^r.

Then the actual normalized surviving mass obeys

    eta_(<=q)^r(1)>=(Aq*T-Bq^r)/(e*T-D_r).              (RW9)

The exact coefficients have Aq>0 and
`e*Bq^r-Aq*D_r=e*Cq^r+Kq*D_r>0` at each of the seven rows.
Consequently(RW3) can be substituted in the increasing lower bound.
At rho=3/50 and q=41, exact rational arithmetic gives

    eta_(<=41)^r(1)>=0.008224657647256354...>1/125.      (RW10)

The strict source threshold from the same fixed formula is
rho>0.05912956428530256...; (RW1) is a simpler sufficient condition.
At rho=9/140 the lower bound is0.0468207220070943...>1/25.
All displayed comparisons use exact fractions.

The new actual F12 has204 distinct original labels with private integers,
delta=0.00003388634450980418... and rho=0.0642857815054542... . Its
post-seven cell masses are the earlier exact w_l*n_l, so directly

    T=sum_l r_l*w_l*n_l
     =240369043020445468666057/997697958915599121093750.

It satisfies(RW1)--(RW4). This family has the residues of the sharpness
construction, including pure49 residue8; it is distinct from the earlier
N12 benchmark. Its private witnesses establish original noncontainment.

The existing[source consumer](../../frontier/source-budgets/source_own_test_consumer.py)
and[canonical certificate](../../certificates/source_norms/source-budgets/source_own_test_consumer.json)
retain `reweighted_full_haar_chain`: all new hinges and complete tails,
the mass bound, exact guard and actual F12. The generalized operator
reproduces every inherited hinge at r=1 and reuses the finite construction
code without consuming its dependent certificate. Replay the existing
`source_own_test_consumer.py --check` command. These are ordinary proofs
and exact arithmetic, not new Lean declarations.

### Fixed cell weights cannot close the present square/scalar route

There is also a uniform limitation for **every** fixed nonnegative
five-cell weight r, including unequal root1 weights. It concerns the
current WF/A2 assigned square numerator, the fixed(3,4)head and the
unit-refund scalar recurrence above; it is not a lower bound on actual
Gamma and does not invalidate the complete-hinge survival result(RW10).

Put phi(v)=v^2-1. The square form of42(A2), already used above, is

    P_k=max_b[sum eta_l*k_l*(b_l^2-1)+max_l k_l*(b_l+1)/9],
    F(k phi)=max_b[sum k_l*(n_l+eta_l/4)*(b_l^2-1)
                 +max_l k_l*(d_l+1/4)*(b_l+1)/9]
             +(7/8)sum eta_l*k_l+(5/8)P_k.

For each cell, the average of b_l^2-1 over the ten baselines is23/10.
Replace both maxima by these averages and discard nonnegative deep terms.
Since n_l<=3eta_l/4 on the containing face, every k_l>=0 satisfies

    F(k phi)>=sum k_l[(23/10)n_l+(231/80)eta_l]
             >=(123/20)sum k_l*n_l.                   (RW11)

The seven comparison square has E N7=6/5 and E N7^2=5/3. Thus its
assigned centered numerator at each containing vertex is

    B_r=(2/3)sum r_l*n_l+(7/15)F(r phi)+F((6/5-zeta)r phi)
       >=(131/12)sum r_l*w_l*n_l
                    +(143/30)sum r_l*zeta_l*n_l.

Let W_r=sum r_l*w_l*n_l. Pointwise domination gives
`max B_r >=(131/12)max W_r`; no common maximizing vertex is required.
IR8 and WF3 give T<=lambda max W_r, while the prescribed assigned
square upper is M2_r=lambda max B_r. Therefore M2_r/T>=131/12 whenever
T>0. ZeroT cannot define a normalized law. With J2=1139/560 and the
nonnegative head payment D_r, any positive head denominator gives

    g_r=1+[J2*M2_r+(J2-1)T]/(eT-D_r)
       >=1+[J2*(131/12)+J2-1]/e=216789167/8944200>24.   (RW12)

For the scalar recurrence already defined above, use the exact positive
quadratic Q from its three-row obstruction. The certificate now supplies
25 fixed(p,f,k) rows, covering every prime17 through127. They start
(17,24,34), end(127,12354,58341), and satisfy A=k-f>0 and4AC-B^2>0.
The producer verifies every intervening prime, linked input/output floor,
and exact completed-square identity. No numerical minimization enters
this finite certificate. Monotonicity in the input makes each row valid
for every legal threshold, including adaptive choices.

At131 a positive scalar denominator requires F<(131-1)^2=16900,
but the carried floor exceeds58341. The prescribed route therefore fails
by131 for every such r and clipping schedule, or earlier if a denominator
fails. A better source numerator, different head, or richer joint state
is outside this obstruction. It identifies a limitation of changing only
these cell weights within that allocated square/scalar procedure.
