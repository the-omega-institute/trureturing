[Index](../marked_head_profile.md) · [Previous](30-actual-threshold-deficits-and-sharp-row-caps.md) · [Next](32-unequal-source-norms-sharpen-the-uniform357-input.md)

<a id="one-original-zero-five-layout-across-both-actual-measures"></a>
### One original zero-five layout across both actual measures

Using exactly the actual HC/DP source and kernels, the bounding formulas
give

    Gamma13 <=5522463803581385359/35094633753560524
             =157.359208885350...,
    T13(81) <=80490856468458306483061934903046859
              /809780928515534112801584606185500
             =99.39831086910345...,
    F17^-(403;nu13)+F19^-(403;physical nu13 K17)
      <=12962561422729019748540463097645271562217
         /28539940401461137428522682187907859200
       =454.1902064401433... .                          (ZC1)

These improve the DP comparison475.52710009238956 on the same law.
The new all-family upper still exceeds the required finite frontier;
later primes and unrestricted #7 remain open. This is ordinary
mathematics plus exact rational arithmetic, not a Lean proof.

<a id="1-the-pointwise-bridge-between-hcs-two-actual-measures"></a>
#### 1. The pointwise bridge between HC's two actual measures

Keep HC's raw pure3 survivor measure eta and five surviving mod9 cells.
Let lambda35 be the3-coordinate marginal of the raw complete35 survivor
measure; it has total mass s. It has density a(x) with respect to eta,
where a(x) is the surviving5-coordinate Haar fraction at that same x.
This raw measure is distinct from the normalized probability used elsewhere.

The original CM2 definitions are stronger than mere cylinder caps:
alpha_r is the removed5 mass from the original3*5^b labels in root r;
beta_l is the **additional** mass removed from9*5^b in cell l after that
root union. Therefore, before deeper mixed exclusions the available
5-fraction in cell l is exactly d_l=z-alpha_r(l)-beta_l. Further mixed
classes can only remove points. Consequently

    d lambda35 / d eta =a(x),  0<=a(x)<=d_l on cell l.        (ZC2)

This follows directly from the original union definitions in P12,
specialized in CM2 and SD2 of
[the problem dossier](../../../../Problems/erdos-7-odd-covering-systems.md). It does not infer
a density bound from a cylinder-mass bound. The old masses remain

    lambda35(cell l)=n_l=w_l*d_l/9-t_l,
    eta(cell l)=w_l/9.

Both measures see the same original ternary test A0 and the same
original prefix at each depth. No auxiliary probability is substituted.

<a id="2-center-jensen-before-summing-the-full5-mixture"></a>
#### 2. Center Jensen before summing the full5 mixture

Let f be any increasing convex cost used by DP (a hinge, a nonnegative
weighted hinge sum, or a square hinge). Write

    p_n=4/5^n, n>=2,   sum p_n=1/5,
    q_n(v)=[f(nv)-f(n)]/n,
    Gbar_f(v)=sum_(n>=2)p_n q_n(v)-f(v)/5,
    J_f=sum_(n>=2)p_n f(n).

The function q_n is nonnegative and convex on v>=1. Gbar_f is
nondecreasing: it differs by a constant from sum p_n g_n, where
g_n(v)=f(nv)/n-f(v) is nondecreasing by convexity. Gbar itself may have a
negative constant; only its nonnegative increments enter the depth bound.

For the same original A0,A1,..., Jensen's HC2 inequality is equivalently

    f(A0+...+A_(n-1))-f(A0)
      <=q_n(A0)-f(A0)+f(n)+sum_(e=1)^(n-1)q_n(A_e).

After HC1 and summing **all** n, the raw35 cost is bounded by

    integral_lambda35 f(A0)+integral_eta Gbar_f(A0)
       +x J_f+sum_(e>=1)integral_eta Q_e(A_e),
    Q_e(v)=sum_(n>e)p_n q_n(v), x=eta(1).              (ZC3)

Thus each positive5 original block A_e is unchanged throughout its
mixture terms. Centering at f(n) makes every remaining infinite tail
rational. There is no uncanceled sum p_n/n and no original-depth cutoff.

A valid retained-block upper term is sum_e max_A P_eta(Q_e). We retain the valid larger comparison

    Pos_f=sum_(n>=2)p_n(n-1) max_A P_eta(q_n).           (ZC4)

Section5 proves the retained and former comparisons coincide at all
six pure3 mass vertices. The numerical improvement in ZC1 comes from the original zero5 block.

<a id="3-merge-its-actual-and-pure-costs-at-each-original-depth"></a>
#### 3. Merge its actual and pure costs at each original depth

Fix the original root/cell choice and b_l=1+1_(r(l)=r)+1_(l=j). For each
cell put

    h_l(v)=d_l f(v)+Gbar_f(v),
    R_l(k)=max_(0<=i<=k)[h_l(b_l+i+1)-h_l(b_l+i)].

Every R_l is nonnegative and nondecreasing. When an original depth-a
prefix in cell l is added, its f increment under lambda35 plus its Gbar
increment under eta is at most its eta integral of the corresponding
h_l increment: this is exactly ZC2 and the nonnegative f increment.
The prior active deep count is bounded by the number of preceding
original depths allocated to that same cell. Its pure eta cylinder
mass is at most3^-a.

Apply DP2 to these common rewards, retaining each original depth's
cell and its actual prior counter. The resulting bound is

    Z_f(r,j)=sum_l n_l f(b_l)+sum_l(w_l/9)Gbar_f(b_l)
       +max_l sum_(k>=0)3^(-k-3) R_l(k),
    F_f^new=max_(r,j) Z_f(r,j)+x J_f+Pos_f.             (ZC5)

This replaces a sum of independently maximized deep costs by the
maximum of their common running increments. It retains both the same
zero5 layout across the entire5 mixture and the relation between its
two actual measures. Neither original prefixes nor forbidden masks are
assumed nested. Completion of absent depths adds nonnegative increments.

Running maxima satisfy

    R_l(k)<=d_l max_i Delta f(b_l+i)
                   +sum_n p_n max_i Delta g_n(b_l+i).

Then the maximum over cells is at most the separate maxima. Constants
and initial values in ZC3 cancel exactly. Therefore ZC5 is never larger
than the preceding DP raw35 expression; the strict gain is a legitimate
restriction of its upper comparison.

<a id="4-exact-complete5-and-ternary-tails"></a>
#### 4. Exact complete5 and ternary tails

The implemented costs have f(v)=A*v^j+B for all v>=K, with j=1 or2 and
K>=2. Put T_i(K)=sum_(n>=K)p_n*n^i=4*geom_i(5,K). Then

    Gbar_f(v)=sum_(2<=n<K)p_n[f(nv)-f(n)]/n
                +A*T_(j-1)(K)*(v^j-1)-f(v)/5,
    J_f=sum_(2<=n<K)p_n f(n)+A*T_j(K)+B*T_0(K).

The positive-block term ZC4 has finite part2<=n<K, and complete tail

    A*[T_j(K)-T_(j-1)(K)]*[max_A P_eta(v^j)-x].         (ZC6)

For j=1, Gbar_f is eventually constant, so every h_l has eventually
constant increments and its running maximum stabilizes. For j=2,
sum_(n>=2)p_n*n=9/20 gives the eventual quadratic coefficient

    h_l(v)=A*(d_l+1/4)*v^2+constant.

Once the present increasing increment dominates all preceding ones,
the running maximum equals that increment forever. The implementation
checks this entrance condition and uses the full geometric zeroth and
first moments to sum the remainder. This handles every ternary depth.

Adding a constant c to f changes F_f^new by exactly c*s. This follows
from the centered formula: q_n is unchanged, Gbar decreases by c/5,
J_f increases by c/5, and those pure-mass terms cancel. Thus the later
complete7/11/13 affine and quadratic tails preserve the same exact
constant terms as DP.

<a id="5-positive5-block-retention-gives-no-gain-in-this-comparison-at-its-vertices"></a>
#### 5. Positive5 block retention gives no gain in this comparison at its vertices

At the six pure3 mass vertices, every w_l is1 except possibly one value
1/2. The three-cell root has total width at least5/2, while the two-cell
root has total width at most2. At least one cell j in the three-cell
root still has w_j=1.

For any increasing convex cost c, let Delta1=c(2)-c(1),
Delta2=c(3)-c(2); then Delta2>=Delta1>=0. If the root/cell are incident,
their initial pure increment is W_r*Delta1+w_j*Delta2, apart from the
common constant. If they are nonincident it is(W_r+w_j)*Delta1.
The fixed choice of the three-cell root and an undecreased incident
cell simultaneously maximizes both expressions for **every** c.
Its largest b is3, also simultaneously maximizing the convex deep
increment at every depth because all pure caps are1.

For this same choice DP's pure operator is linear in any nonnegative
sum of increasing convex costs. Thus, at every such vertex,

    sum_e max_A P_eta(sum_(n>e)p_n q_n)
      =sum_n p_n(n-1)max_A P_eta(q_n).

The proof includes the infinite limits by their convergent positive
series. The other four HC parameter groups do not change this pure
observation. Hence retaining the positive original blocks alone gives
exactly zero gain at all1296 parameter vertices for the current source.
This is a statement about the comparison formulas, not the actual
maximizing original residue families.

<a id="6-same-full-source-continuous-parameter-domain-and-numerical-consumer"></a>
#### 6. Same full source, continuous parameter domain and numerical consumer

Use ZC5 for the raw35 hinge, weighted hinge and square-hinge functions. All complete7/11/13 multipliers, physical source choices,
actual sole conditioning, DP row potentials and later kernel inputs
remain exactly as in DP4--DP11.

Each combined increment is affine in d_l before a running maximum. The
complete discounted sum and maximum over cells are therefore convex
in that parameter group. Initial n_l and w_l contributions remain
separately affine; positive pure comparison terms are maxima of affine
functions. Exact constants remain exact by section4. Consequently the
same separate-convexity and vertex interpolation proof applies.

All1296 product vertices were reconstructed with exact fractions. The
three maxima in ZC1 still occur at vertex398. All three vertex margins
are nonnegative and attain zero. The unchanged coefficient K_Z and
the new target C satisfy

    (C-C0)*131/132-K_Z
      =5547333519740397212762826906723421600619
         /13546741505436061975028474427478348800 >0.

The analogous Gamma and tau81 coefficients are positive. In detail,
write rho=131/132, Delta=rho*D-H, and Z=K_Z*D+Q. Here D is separately
concave and H,Q are separately convex. The target margin is

    (C-C0)Delta-Z=[(C-C0)rho-K_Z]D-(C-C0)H-Q.

Its positive coefficient and C>C0 make it separately concave, so the
vertex inequalities extend to the entire product domain. The same
argument applies to both square margins. Delta is separately concave
and its vertex minimum is strictly positive, making every division
valid throughout. All eight other missing-class branches remain below
the new targets using their existing complete-tail formulas.
Therefore this covers the full continuous effective9 domain and all
twelve original-family branches, with arbitrary finite heights.

The [standalone verifier](../verify_joint_frontier.py) evaluates ZC5 and
reconstructs every exact record in the
[single certificate](../certificates/joint_frontier_certificate.json). Eight earlier
mathematical source files remain pinned by SHA-256. The current certificate
sharpens DP1; its conclusions also imply all three earlier DP1 bounds.
A separately written implementation evaluates the uncentered HC/SQ
expressions with the same common-depth constraint. The programs verify
the finite arithmetic and exact tails of these ordinary proofs; they
do not enumerate all actual families or supply Lean verification.

<a id="7-the-remaining-finite-criterion-on-the-same-actual-law"></a>
#### 7. The remaining finite criterion on the same actual law

Using ZC1 in KC's complete finite-core comparison gives allowances

    403-T13(81)-0.000667 >303.6010221308 [box20/current8],
    403-T13(81)-0.263    >303.3386891308 [unequal/current6]. (ZC7)

Thus303.601 and303.338 are safe sufficient finite upper thresholds.
The454.190207 joint bound remains above both. Before adding finite-core
error, the signed upper estimate is

    (T13(81))_upper-403+(F17^-+F19^-)_upper
      =150.5885173092467... >0.

This is a gap in a sufficient estimate, not a positive lower bound for
the actual functional, nor an actual covering family. Both a uniform
negative KC criterion and continuation through arbitrary later primes
remain unproved. The physical19 input, all original labels and the
complete tails are unchanged; no independent BM, RC or OBE saving is
added to this estimate.

<a id="retaining-the-original-zero-seven-block-across-its-complete-mixture"></a>
### Retaining the original zero-seven block across its complete mixture

On the unchanged actual HC/DP source and physical kernel input, the new
ordinary comparison gives

    F17^-(403;nu13) + F19^-(403;physical nu13 K17)
      <= 5323534511332833048109272786522049864207
         /11791742854906074667157193240441043200
       = 451.46290729346447...,

    Gamma13 <= 5522642653862251759/35214095188281724
             = 156.83045735901896...,

    T13(81) <= 80660556065861952082417951246296859
              /814143916251213275694277434123000
             = 99.07407579395733... .                       (Z7.1)

These follow from the new common zero-five operator, the existing HC6
pure-seven comparison, and retaining one additional original layout.
The joint gain over the zero-five bound is2.727299146678829.... The finite
frontier is still unmet and unrestricted Erdős #7 remains open.

<a id="one-original-block-one-actual-source-law"></a>
#### One original block, one actual source law

Let lambda35 be the raw actual complete35 survivor measure, with total mass s,
and the actual pure7 survivor probability. A complete original357 test
has original complete35 blocks A_0,A_1,..., each including its unit term.
HC6's comonotone comparison preserves those original blocks and uses
the complete auxiliary probabilities

    p_1 = 29/35,
    p_n = 36/(5*7^n), n>=2.                          (Z7.2)

For every increasing convex cost f on v>=1, Jensen gives

    integral_(lambda35 tensor pure7) f(L)
      <= sum_(n>=1) (p_n/n) sum_(e=0..n-1) integral_lambda35 f(n A_e).

Both sides use the same raw mass s; no normalized expectation is inserted.

The existing comparison applies the zero-five source bound F35 to each
f(n .) separately, yielding sum_n p_n F35(f(n .)). In that expression,
the original A_0 was allowed a different comparison maximizer for each
n. It is valid but avoidable: A_0 is one fixed original block.

Define the centered common cost

    q_f(v) = sum_(n>=1) (p_n/n) [f(nv)-f(n)].

This cost is nonnegative, increasing and convex for v>=1. Applying the
same F35 operator once to q_f preserves the same A_0 through the whole
seven mixture. Each positive original block is still bounded separately,
exactly as before. The resulting valid bound is

    q_n(v) = [f(nv)-f(n)]/n,   J = sum_n p_n f(n),
    B_new(f) = F35(q_f) + s J + sum_n p_n(n-1) F35(q_n). (Z7.3)

or, using exact constant shifts and positive homogeneity,

    B_new(f) = F35(q_f)
      + sum_(n>=1) p_n [(n-1)/n F35(f(n .)) + s f(n)/n]. (Z7.4)

No original residues, auxiliary probabilities, incoming source, or later
conditioning are changed. In particular this is a bound on the product
of the same actual complete35 law and actual pure7 law; the existing
actual mixed7 deletion and its retained denominator D apply afterward.

<a id="the-gain-and-complete-analytic-seven-tail"></a>
#### The gain and complete analytic seven tail

The common zero-five source operator is positively homogeneous,
subadditive, and exact on additive constants: F35(f+c)=F35(f)+c*s.
This follows from its linear initial contributions, running maxima of
linear increments, nonnegative complete sums, and final maxima. Thus

    B_old(f)-B_new(f)
      = sum_n (p_n/n)[F35(f(n .))-s f(n)] - F35(q_f) >=0.

For n beyond the polynomial cutoff, every centered q_n is the same
monomial-minus-one direction multiplied by a nonnegative scalar. Its
complete geometric tail therefore merges exactly before applying
subadditivity, leaving only finitely many summands.

For f(v)=A v^j+B above an integer K, with j=1 or2 and K>=2, put
`T_i = sum_(n>=K) p_n n^i = (36/5) geom_i(7,K)`. Since v>=1, the
complete tail of the centered cost is exactly

    q_f(v) = sum_(1<=n<K) (p_n/n)[f(nv)-f(n)]
             + A T_(j-1)(v^j-1).

The other part of B_new has finite sum1<=n<K and complete tail

    A [T_j-T_(j-1)] F35(v^j)
      + s [A T_(j-1)+B T_0].                           (Z7.5)

All coefficients of source-cost bounds are nonnegative. Constant terms
are exact. There is no logarithmic1/n tail, truncation of original
heights, or renormalized finite distribution. The common cost is itself
eventually affine or quadratic, so the complete zero-five and ternary
tail proofs remain applicable without modification.

<a id="continuous-parameters-and-the-numerical-consumers"></a>
#### Continuous parameters and the numerical consumers

The displayed direct expression for B_new is a positive sum of F35
costs plus separately affine terms in s. Therefore B_new remains
separately convex in the same five HC parameter groups. The existing
seven-deletion denominator D, later eleven/thirteen source, unit-floor
subtraction, row potentials, and physical seventeen input are unchanged.

Write rho=131/132, Delta=rho D-H, and the weighted numerator as
Z=K_Z D+Q. The new H and Q remain separately convex and D is separately
concave. The joint target margin is

    (C-C0)Delta-Z
      = [(C-C0)rho-K_Z]D-(C-C0)H-Q.

At the new target its coefficient of D is

    2276822305629044790887711236465769668549
      /5597057671003656854022099457909324800 >0.

The Gamma and threshold81 coefficients are respectively

    85570893162301542772813/739073429811656823312 >0,
    552829796486351122976435256824925733537
      /5695750838093488076757164929124508000 >0.

All three margins are therefore separately concave. Exact nonnegative
vertex margins and the positive minimum of Delta extend the bounds to
the full continuous parameter domain. All1296 vertices and all eight
other missing-class branches pass. A joint/Gamma maximizing representative
is vertex398; all tied indices are398,410,422,616,628,640. A threshold81
maximizing representative is vertex386; its ties are386,388,590,592.
These targets are maximized separately; the threshold81 value at398
is only98.95720643555728.

The [standalone verifier](../verify_joint_frontier.py) evaluates the direct
positive formula and reconstructs all records in the
[complete certificate](../certificates/joint_frontier_certificate.json). It extends the
centered zero-five cost operator to scaled costs and q_f, with analytic
polynomial tails. A separate implementation starts from uncentered
zero-five costs and subtracts the rigorously nonnegative common-layout
gain. Every vertex field and fallback record agrees exactly.

The sufficient finite-frontier allowances are

    403-(T13(81))_upper-0.263
      =303.66292420604265... [unequal/current6],
    403-(T13(81))_upper-0.000667
      =303.92525720604266... [box20/current8].          (Z7.6)

Thus303.662 and303.925 are safe sufficient thresholds. The signed upper
estimate before finite-core error is147.5369830874218 and remains
positive. These are ordinary proof and exact arithmetic results, not
Lean verification or a full covering-system resolution. The required
uniform negative KC estimate and arbitrary later-prime continuation
remain unproved.

<a id="every-original-seven-block-and-a-common-ap-zero-block"></a>
### Every original seven block and a common AP zero block

On the same actual AP11/T4--AP13/T6 law and prescribed physical17
input, the complete original-label bounds give

    F17^-(403;nu13)+F19^-(403;physical nu13 K17)
      <=20841391090341979866125382429441856802801
        /46309752753991653188223872174911046400
       =450.04323821499054...,
    Gamma13<=5523249664714699759/35252033366559724
            =156.67889586063097...,
    T13(81)<=80660556065861952082417951246296859
             /814547014001232991335635026248000
           =99.02504665708572....                      (CB1)

The common AP cost is evaluated on the strengthened full-original7
source operator itself. The actual source law, original labels and
residues, full tails, sole final normalization and physical17 input
are unchanged.

The general principle of retaining one original label through all auxiliary outcomes is already in the repository's FL1--FL4 (marked_head_profile.md, section "Retaining an original exponent label across the full auxiliary law"), and in its earlier "An original zero label across every auxiliary outcome" application. The present numerical result reuses that principle with the current all-family source and its same-law deletion floor; it is not a new general comparison theorem.

<a id="source-operator-used-everywhere"></a>
#### Source operator used everywhere

Let F35 be the current common-zero5 raw operator with raw mass s. For a nonnegative increasing convex f on v>=1 and the unchanged pure7 comparator p7(n), define

    c_e(v)=sum_(n>e) p7(n)[f(nv)-f(n)]/n,
    B(f)=s*E f(N7)+sum_(e>=0)F35(c_e).                  (CB2)

For each fixed original block A_e, Jensen supplies c_e(A_e).
Nonnegative summation and the F35 bound prove CB2. It keeps every
original7 exponent block together across all outcomes in which it occurs. The operator handles every such eventually affine or quadratic f, not only a finite list of primitive hinge names. Positive homogeneity, subadditivity and exact constant shifts follow from those of F35. Each fixed-cost B is separately convex in the five HC parameter groups.

For f(v)=a v^j+b once v>=K, the finite blocks e=0,...,K-2 are evaluated as their whole costs. The complete remaining block tail is

    a*[T_j-(K-1)T_(j-1)]*[F35(v^j)-s],
    T_i=sum_(n>=K)p7(n)n^i.                            (CB3)

Each n>=K contributes to exactly n-K+1 tail blocks, proving CB3.
The implementation passes every compound AP cost through CB2,
including both its primitive and composite source costs.

<a id="ap1113-original-label-bridge-and-common-cost"></a>
#### AP11/13 original-label bridge and common cost

For each fixed actual357 point x, write A_(e,f)(x) for the globally fixed original complete357 test in exponent tuple (e,f) of11 and13. Apply the existing conditional original-label comparison first to13, whose cylinder cap c13*13^-f holds conditional on the full physical history, and then to11 with cap c11*11^-e. The intermediate set functional stays increasing and supermodular. Since c11=5/3 and c13=2 are constants across histories, the auxiliary depth runs can be sampled independently of each other and of x.

Thus the compared load is

    sum_(0<=e<N11,0<=f<N13) A_(e,f)(x),

where N=N11*N13 is the number of original blocks. This independence belongs to the comparison counts, not to the actual kernels. One original A_(0,0) occurs in every rectangle. Finite original heights can be completed in advance; the added terms are nonnegative and the full count moments are finite.

For increasing convex f put

    q_f(v)=E[(f(Nv)-f(N))/N],  e_f=E f(N).

Use Jensen on each original rectangle, and apply the one common B to its same original zero block before maximizing. Other blocks retain the existing separate comparison. The valid raw expression is

    S(f)=B(q_f)+sum_n p_n[(n-1)B(f(n .))/n+s f(n)/n].    (CB4)

Equivalently,

    S(f)=s e_f+B(q_f)
           +sum_n p_n(n-1)[B(f(n .))-s f(n)]/n.

All centered costs here are nonnegative. The old expression sum_n p_n B(f(n .)) dominates S by subadditivity. Both sides use the new all_blocks B, so the actual gain is recomputed rather than imported from the weaker zero7 source.

<a id="unchanged-actual-deletion-floor-and-conditioning"></a>
#### Unchanged actual deletion floor and conditioning

Let u>=D be the actual retained357 raw mass after mixed7 deletion. The Jensen contributions are at least their total floor e_f on the same deleted set, and S(f)>=s e_f. Therefore

    [S(f)-e_f(s-u)]/u <= [S(f)-e_f(s-D)]/D.

This is an upper bound under the actual uniform357 survivor law, followed by the proved actual physical11/13 comparison. Nonnegative f and the same final survival lower bound Delta/D give

    sup_A E_nu13 f(A) <= R(f)/Delta,
    R(f)=S(f)-e_f(s-D).                                 (CB5)

No auxiliary upper moment is substituted for an actual-law upper bound without this comparison. The floor e_f(s-D) is not omitted or charged twice.

<a id="complete-ap-tail-and-continuous-domain"></a>
#### Complete AP tail and continuous domain

The full N product moments are1,49/36,253/108. For f(v)=a v^j+b above K, put T_i=E[N^i;N>=K]. Then

    q_f(v)=sum_(n<K)(p_n/n)[f(nv)-f(n)]
                          +a T_(j-1)(v^j-1).

The remaining part of S has complete tail

    a(T_j-T_(j-1))B(v^j)+s[a T_(j-1)+b T_0].             (CB6)

All source-bound coefficients are nonnegative and constants are exact. Every infinite tail is a full geometric moment calculation; there is no original-height cutoff or renormalization.

For fixed f, S is a positive sum of B costs plus separately affine multiples of s, so it stays separately convex. R=e_f D+[S-e_f s] leaves the collected denominator coefficient K_Z unchanged. The joint bound uses the new R(phi17), R(phi19), R((v-5)+), while U16/U81 and Delta are precisely those obtained from the stronger positive7 source. Its signed margin is separately concave if

    (C-C0)*131/132-K_Z>0.

The exact coefficient is

    347521291319402151520483236052982555338213
      /857272418780792361930100697448363494400 >0.

The [complete certificate](../certificates/joint_frontier_certificate.json) checks all1296
vertices and this coefficient; all eight non-effective9 branch bounds
are below CB1, with margins evaluated at the current targets. The
Gamma and T81 coefficients are positive by the same separately concave
margin argument. Thus the three bounds hold throughout the continuous
parameter domain and cover all twelve original-family branches.

The [canonical verifier](../verify_joint_frontier.py) uses centered source
costs and the direct positive formulas CB2 and CB4. A separate
implementation uses uncentered source costs and evaluates the AP
common-layout gain. All1296 records and8 fallback records agree exactly.
Polynomial tail formulas include every original height and multiplier.
The source inputs and their eight SHA-256 pins are unchanged.

The sufficient finite allowances become303.7119533429143 for the
unequal/current6 core and303.9742863429143 for box20/current8. Safe
sufficient bounds are303.711 and303.974 respectively. The signed
upper before finite-core error is146.06828487207625, still positive.
The uniform negative-Q criterion, arbitrary subsequent-prime
continuation and unrestricted Erdős #7 remain unproved. These are
ordinary mathematical estimates and exact arithmetic certificates,
without an actual-family sharpness assertion or new Lean declaration.

<a id="every-original-ap1113-exponent-block"></a>
### Every original AP11/13 exponent block

Retaining each original AP exponent tuple across all auxiliary outcomes
strengthens CB1 on the same actual law to

    F17^-(403;nu13)+F19^-(403;physical nu13 K17)
      <=270521516350366644094844875118567294436413
        /602026785801891491446910338273843603200
       =449.35129587304937....                         (ABP1)

The source bounds remain Gamma13<=156.67889586063097... and
T13(81)<=99.02504665708572..., with their exact values in CB1.
The gain over CB1 is

    476847867448244109695443125/689143933742337091835542297
      =0.6919423419412003... .

This is an application of the existing FL1--FL4 original-label grouping
principle to CB2's all-original7 operator. It keeps the prescribed
physical AP11/T4 and AP13/T6 kernels, every original residue and label,
the same mixed7 deletion floor, one final conditioning, and the physical
mu17 input of the19 functional.

<a id="group-before-taking-each-source-maximum"></a>
#### Group before taking each source maximum

Use the original-label reverse conditional comparison in CB4: conditional
on the actual357 point x, the compared full test has load

    sum_(0<=e<N11,0<=f<N13) A_(e,f)(x).

Each A_(e,f) is its globally fixed original complete357 block. The
auxiliary counts N11,N13 are independent of each other and x because
their full-history caps are the constants5/3 and2. This does not assert
independence of the actual physical coordinates. Their distributions are

    Pr(Np=1)=1-cp/p,
    Pr(Np=n)=cp*(p-1)*p^-n, n>=2.

Put N=N11*N13. For an original exponent tuple a=(e,f), define

    Q_a(v)=E[1_(e<N11,f<N13)*(h(Nv)-h(N))/N],
    S_all(h)=s*E h(N)+sum_a B(Q_a),                    (ABP2)

where B is exactly the CB2 source operator on the same raw mass s.
On each auxiliary rectangle, centered Jensen assigns one summand to
each of its N original blocks. Collecting the summands with the same
original tuple yields Q_a(A_a). Each Q_a is nonnegative, increasing and
convex; bounding its source integral by B(Q_a) proves ABP2. All completions
are fixed before sampling. Nonnegative summation and the finite complete
count moments justify the infinite extension of physical heights.

CB4 keeps only Q_(0,0) together and bounds the other tuples separately
within each outcome. Positive homogeneity and subadditivity of B show
S_all<=S from CB4. No equality of actual maximizing layouts is assumed.

<a id="exact-finite-exceptions-and-the-complete-tuple-complement"></a>
#### Exact finite exceptions and the complete tuple complement

Suppose h(v)=A*v^j+B0 for v>=K, where j is1 or2 and K>=2. The finite
set of tuples that can be active for some N<K is exactly

    I={(e,f):(e+1)*(f+1)<K}.

For a=(e,f) in I, set

    p_a(n)=sum_(uv=n,e<u,f<v) Pr(N11=u)Pr(N13=v), n<K,
    M_a=E[1_(e<N11,f<N13)*N^(j-1)],
    t_a=M_a-sum_(n<K)p_a(n)*n^(j-1)>=0.

Auxiliary independence computes M_a as the product of the two complete
one-coordinate active moments. For exponent e and order r in{0,1},
these moments are

    E[1_(Np>e) Np^r]
      =1                         if e=0,r=0,
      =1+cp/(p-1)                if e=0,r=1,
      =cp*p^-e                   if e>=1,r=0,
      =cp*p^-e*(e+1+1/(p-1))     if e>=1,r=1.

Thus each whole original-block cost is exactly

    Q_a(v)=sum_(n<K)(p_a(n)/n)[h(nv)-h(n)]
                           +A*t_a*(v^j-1).           (ABP3)

It is eventually a polynomial of degree j, with leading coefficient
A*M_a and constant sum_(n<K)(p_a(n)/n)[B0-h(n)]-A*t_a. The existing
generic zero5/all-original7 source formulas therefore apply, including
their full five, seven and ternary tails.

For every tuple outside I, Q_a=A*M_a*(v^j-1). There are exactly N
active original tuples in each rectangle, so

    sum_a M_a=E N^j,
    sum_(a outside I) B(Q_a)
      =A*[E N^j-sum_(a in I)M_a]*[B(v^j)-s].          (ABP4)

The coefficient is nonnegative. The complete product moments are
E N^0=1, E N=49/36 and E N^2=253/108. Equations ABP3--ABP4 account for
every original exponent height with no truncation, renormalization, or
uncanceled inverse-N series.

<a id="same-floor-continuous-domain-and-checked-consumer"></a>
#### Same floor, continuous domain and checked consumer

The comparison integrand equals E h(N) plus nonnegative centered costs
on the same raw pre-deletion source. Let u>=D be the actual357 mass
after mixed7 deletion and e_h=E h(N). Then S_all>=s*e_h and

    [S_all-e_h(s-u)]/u <= [S_all-e_h(s-D)]/D,
    R_all(h)=S_all(h)-e_h(s-D),
    sup_A E_nu13 h(A)<=R_all(h)/Delta.                 (ABP5)

The last step uses the unchanged final survival lower bound Delta/D.
The floor is charged once on the same actual removed set. The physical
AP11/13 comparison is not replaced by a product law on the actual source.

ABP2--ABP4 express S_all as a positive sum of fixed-cost B bounds plus
separately affine multiples of s. Hence it is separately convex in the
five original HC parameter groups and exact on constant shifts.
Writing R_all=e_h*D+[S_all-s*e_h] leaves K_Z unchanged. For the joint
target C in ABP1 the separately concave target margin has D coefficient

    (C-C0)*131/132-K_Z
      =20407800120324728147819485087313651255189
        /50427789340046609525300041026374323200 >0.    (ABP6)

The current consumer improves the three weighted costs R17,R19,R5.
Delta,U16,U81 and the complete Gamma/T81 source bounds remain exactly
the CB2 all-original7 quantities; no common-AP square gain is claimed.
Positive vertex Delta and nonnegative target margins extend by repeated
vertex interpolation to the full continuous domain. All1296 product
vertices and all eight other original-family branches pass. Joint and
Gamma maximizing representatives include398; a T81 representative
is386. The certificate records all tied maximizing indices, without
claiming that actual families attain the comparison extrema.

The [canonical verifier](../verify_joint_frontier.py) uses centered source
costs, divisor-probability convolution, and the closed active moments
above. A separate implementation uses uncentered source costs, direct
factor-pair convolution, and geometric active moments. Every common
certificate field, all1296 rows and all eight current-target fallback
records are checked against that independent implementation. The
[certificate](../certificates/joint_frontier_certificate.json) also retains the earlier
bounds and separates this gain from the previous improvements.

The finite allowances remain303.7119533429143 and303.9742863429143;
safe sufficient bounds are303.711 and303.974. The joint upper remains
145.63934253013505 or145.37700953013507 above those allowances. The
signed upper before finite-core error is145.37634253013505, still
positive. These local gaps are not a percentage of the unrestricted
proof. The uniform negative-Q criterion and the later-prime continuation
remain open; no new Lean declaration or unrestricted resolution is claimed.
