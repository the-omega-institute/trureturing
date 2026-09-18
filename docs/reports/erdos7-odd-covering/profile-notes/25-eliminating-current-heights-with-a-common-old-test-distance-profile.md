[Index](../marked_head_profile.md) · [Previous](24-actual-radial-families-retain-a-strict-common-test-loss.md) · [Next](26-conditional-head-deletion-with-a-priced-arbitrary-cofactor-tail.md)

<a id="eliminating-current-heights-with-a-common-old-test-distance-profile"></a>
### Eliminating current heights with a common old-test distance profile

Fix a finite actual old carrier, a finite nonnegative measure sigma and its complete old-test domain D. Each original divisor remains an independently chosen label. Let R_x be the actual killed current-prime kernel, q(x)=R_x(1), and choose a full-Haar density cap c(x): every depth-e current prefix has mass at most c(x)p^-e. Assume0<=q<=c and finite integrals. The literal actual cap g/lambda and the larger generic AP cap are both allowed. The following upper bound uses these quantities on their one actual source; it requires no normalization of sigma.

Define

    <A,B>_c=integral c A B d sigma,
    ||A||_c^2=<A,A>_c,
    Gamma=max_(A in D)||A||_c^2,
    d(A)=Gamma-||A||_c^2,
    M={A in D:d(A)=0}.

The domain D and M are finite and nonempty. For a fixed literal zero-current block A0, keep the joint profile

    psi_t(A0)=min_(A in D){t d(A)+||A-A0||_c^2},
    t>0.                                          (OBE1)

This minimum couples norm deficit and distance to the same old test. It cannot in general be recovered from marginal moments or independently maximized Gram entries.

<a id="finite-original-heights-and-the-retained-deficits"></a>
#### Finite original heights and the retained deficits

For original current height H, put s_e=p^-e and

    S_H=sum_(e=1..H)s_e,
    a_H=sum_(e=1..H)(2e+1)s_e,
    t_(e,H)=e+1+sum_(f=e+1..H)s_f/s_e,
    B_H(A0)=integral q A0^2 d sigma+S_H||A0||_c^2,
    Psi_H(A0)=sum_(e=1..H)s_e psi_(t_(e,H))(A0).

For independent old blocks A0,...,AH, the current-prefix pair caps give

    integral L^2 d(sigma R)<=Phi_H,
    Phi_H=integral q A0^2 d sigma
       +sum_((e,f)!=(0,0),0<=e,f<=H)
                             s_max(e,f)<Ae,Af>_c.

The following is an exact identity for this cap functional:

    Phi_H=B_H(A0)+(a_H-S_H)Gamma-Psi_H(A0)
      -sum_(e=1..H)s_e[
          t_(e,H)d(Ae)+||Ae-A0||_c^2
                           -psi_(t_(e,H))(A0)]
      -sum_(1<=e<f<=H)s_f||Ae-Af||_c^2.             (OBE2)

To prove it, expand each pair by2<A,B>_c=||A||_c^2+||B||_c^2-||A-B||_c^2. The coefficient of||Ae||_c^2 is(e+1)s_e+sum_(f>e)s_f=s_e t_(e,H), and these coefficients sum to a_H-S_H. Substitute||Ae||_c^2=Gamma-d(Ae), then add and subtract the minimum OBE1. Every displayed bracket and distance is nonnegative. Thus

    sup_L integral L^2 d(sigma R)
      <=(a_H-S_H)Gamma
         +max_(A0 in D){B_H(A0)-Psi_H(A0)}.         (OBE3)

No equality between positive blocks is imposed. If one common current root and all its relevant prefixes avoid every pure and mixed exclusion, c=g/lambda is simultaneously attained by assigning all positive labels to that root. At H1, OBE3 is then exact: there are no positive-to-positive distances and the sole positive block can attain OBE1. At higher H, OBE3 remains an upper bound; it discards those distances and possible incompatibility of the separate minima.

<a id="complete-tails-and-finite-affine-intervals"></a>
#### Complete tails and finite affine intervals

Set S=1/(p-1), a=(3p-1)/(p-1)^2 and

    B(A0)=integral q A0^2 d sigma+S||A0||_c^2,
    Psi(A0)=sum_(e>=1)p^-e psi_(e+1+S)(A0).

For every finite original current height with these same q,c and D,

    sup_L integral L^2 d(sigma R)
      <=(a-S)Gamma+max_(A0 in D){B(A0)-Psi(A0)}.    (OBE4)

Indeed extend the finite block tuple by arbitrary complete old tests in the cap functional. All added pair terms are nonnegative, and the full series converges absolutely since every inner product is at most Gamma and the coefficient sum is a. Apply the expansion used for OBE2 to this series. The resulting norm coefficient is p^-e(e+1+S). This adds comparison terms, not original forbidden classes, and does not identify the finite coefficients with the infinite ones.

The complete tail of Psi has a finite description. Let

    D_*(A0)=min_(A in M)||A-A0||_c^2,
    T_*(A0)=max_(A not in M)
       (D_*(A0)-||A-A0||_c^2)_+/d(A),

with maximum0 when there are no nonmaximal tests. Then

    psi_t(A0)=D_*(A0) for every t>=T_*(A0).         (OBE5)

Every nonmaximal test contributes at least D_* after this threshold, while a nearest member of M attains D_*. Zero seminorm differences cause no difficulty: tests equal c-sigma almost everywhere have the same norm, and q<=c makes their baseline terms agree too. Original labels are not removed from the admissible domain.

Before the threshold, psi_t is the lower envelope of the finitely many affine functions t d(A)+||A-A0||_c^2. Its breakpoints partition the integer depths e into at most|D| active intervals. On each interval the sum defining Psi is a combination of sum p^-e and sum e p^-e; the last interval is exactly geometric by OBE5. With rational actual data, crossings, integer interval endpoints and sums admit exact rational computation. No iteration through every depth up to T_* is necessary.

The old domain can still be very large, and its nonzero norm gaps can be arbitrarily small. This finite interface supplies no uniform complexity bound on the original family search. It eliminates the independent current-height layout choices from this particular valid upper estimate, using the actual old norm/Gram profile and q-weighted baseline.

<a id="when-the-complete-bound-improves-strictly"></a>
#### When the complete bound improves strictly

Relative to U0=max_D B+(a-S)Gamma, the gain in OBE4 is

    delta_profile=min_(A0 in D){max_D B-B(A0)+Psi(A0)}.

For t>0, psi_t(A0)=0 exactly when A0 itself maximizes the c-weighted norm, allowing the same null-space identification. Finiteness therefore gives

    delta_profile>0 iff argmax_D B and M are disjoint. (OBE6)

This is a condition on two observations under the same actual source and kernel. Its numerical size must be supplied by that source's profile.

The strict case occurs in an actual family at every finite current height. Use uniform units modulo3^8 as source, forbid0 modulo3, and take prime p>=17, threshold8, pure0 modulo p, and the eight classes3^j p with old residue1 and current root j. Include the redundant pure classes0 modulo p^e to retain any desired higher current height. The original3^8 height is retained by its mixed class; every original test remains present. All5/7/11/13 factors are absent, so their source steps are identities.

Write R for the nested old depth count, P8=1/4374, and u_j=g_j/(p-1). The same actual row calculation as RS gives

    q_j=1 (j<=7),  q8=(p-2)/(p-1),
    u7=1/(p-8),  u8=(p-2)/[(p-1)(p-9)],
    c_j=p u_j.

The strictly increasing c_j make the spine prefix the unique maximal c-weighted cylinder at every old depth. Expanding the complete square gives the unique norm-maximizing load A_*=1+R. For the full-height baseline weight w_j=q_j+[p/(p-1)]u_j, move just the last old cylinder to another child of the depth7 spine. The resulting complete spur test A' satisfies

    B(A')-B(A_*)=17 P8(w7-w8)>0,
    w7-w8=[1-p(u8-u7)]/(p-1),
    u8-u7=7/[(p-1)(p-9)(p-8)].                    (OBE7)

Positivity follows from(p-1)(p-9)(p-8)>7p for p>=17. Thus the norm maximum does not maximize B, proving OBE6 is nonvacuous for actual kernels, without assuming repeated positive blocks. This example establishes a strict comparison gain; it is not a new numerical bound for arbitrary AP13 families.

For the final KC objective one can apply OBE3 or OBE4 directly at19 with sigma=nu13 K17^- and R=K19^-; the output is exactly eta and the old domain contains every original17 label. Subtract the test-independent484 integral q d sigma from the bound. This is the actual killed input, with its mass retained; no normalized physical or separately conditioned source is substituted. Uniform numerical control of its norm/Gram profile over the full original family remains open. The identities, envelope computation and strict-gain argument here are ordinary mathematics, not Lean verification.

<a id="incompatible-actual-current-prefixes-give-a-uniform-test-correction"></a>
### Incompatible actual current prefixes give a uniform test correction

Let R be one actual unnormalized killed row on Z/p^H Z, let q=R1, and let M_e be its largest depth-e prefix mass. All original current heights and prefixes remain literal. Define

    Omega_H(R)=min_(v_e at depth e,1<=e<=H) [
      sum_e(2e+1)(M_e-R(v_e))
        +2 sum_(e<f)R(v_f)1_(v_f not subset v_e)].  (CPI1)

The minimum is over independent prefixes, including nonnested choices. Omega is nonnegative and equals0 precisely when one nested chain attains all the M_e. For a nonempty row every M_e is positive, so zero cost forces maximality and pairwise compatibility. For an empty row every term is0 and any chain works. Set Omega_0=0.

At a fixed old history, let a0,...,aH be the literal complete-test block amplitudes, and put m=min_e a_e. Each a_e>=1 because its old-cofactor-one label is retained. With

    c_e(a)=2a0*a_e+a_e^2+2a_e sum_(1<=d<e)a_d,
    U_M(a)=q a0^2+sum_e c_e(a)M_e,

the actual square obeys

    integral L^2 dR<=U_M(a)-m^2 Omega_H(R)
                  <=U_M(a)-Omega_H(R).             (CPI2)

To prove this, fix all depths except e. The square integral is convex in the nonnegative vector assigning its a_e active labels to depth-e prefixes. A simplex vertex concentrates all of them on one prefix and does not decrease the maximum. Repeat for each depth. This is an upper relaxation within the row; globally consistent choices across different old histories are not assumed.

For concentrated prefixes, direct expansion gives the exact deficit

    U_M(a)-integral(a0+sum_e a_e 1_(v_e))^2 dR
      =sum_e c_e(a)(M_e-R(v_e))
        +2 sum_(e<f)a_e a_f R(v_f)
                                    1_(v_f not subset v_e).

Here c_e(a)>=(2e+1)m^2 and a_e a_f>=m^2, proving CPI2. The list of separate maxima alone does not give the incompatibility terms.

A smaller certificate uses any1<=r<s<t<=H:

    Omega_H(R)>=min_(u at depth r,v at depth s) [
      (2r+1)(M_r-R(u))+(2s+1)(M_s-R(v))
       +1_(v not subset u)(2R(v)+2M_t)].            (CPI3)

If u,v are disjoint, a depth-t prefix z can lie below at most one. Its two incompatibility terms cost at least2R(z), and its own mass deficit adds(2t+1)(M_t-R(z)). Their sum is at least2M_t. If u,v are compatible, simply discard the nonnegative depth-t terms. Retain the r,s terms and minimize to obtain CPI3.

<a id="integration-together-with-the-old-block-profile"></a>
#### Integration together with the old-block profile

For a fixed actual old measure sigma and its actual rows R_x, write omega_H=integral Omega_H(R_x)d sigma. This quantity is independent of the original complete test. It can be subtracted from the supremum of the same C1 envelope U_M, and hence from C5 with these actual prefix masses:

    sup_L integral L^2 d(sigma R)
      <=Gamma(q sigma)+sum_e(2e+1)Gamma(M_e sigma)
                                                    -omega_H.

It also combines with OBE without counting a loss twice. If M_e<=c p^-e, the explicit chain is

    integral L^2 d(sigma R)
       <=integral U_M(A)d sigma-omega_H
       <=Phi_H(A)-omega_H
       <=U_OBE-omega_H.                            (CPI4)

The first loss concerns current-prefix geometry; OBE2 is an exact identity inside the subsequent cap functional. U_OBE can be either OBE3 or the complete-tail OBE4. In the latter case only the comparison cap is extended; the actual row, height and Omega_H are not padded. At19 take sigma=nu13 K17^- and R=K19^-, then subtract484 integral q d sigma to bound the original signed objective. A CPI3 certificate may replace Omega in the same chain.

CPI4 does not authorize appending a subtraction to CT3 while leaving its exact transported increments unchanged. Nor can the loss of one chosen family be subtracted from a supremum over all families. The corrected envelope and its actual source/mask data must remain together. Clean nested rows from SPF have Omega=0.

<a id="a-literal-arithmetic-witness-and-an-equal-readout-comparison"></a>
#### A literal arithmetic witness and an equal-readout comparison

Take Q=3^4*5^2*7*11*13=2027025 and forbid0 modulo every nonunit divisor of Q. There are120 old test labels and777600 old units. The prescribed actual source construction gives the uniform unit law; all mixed11/13 exclusions are inactive. At17 retain current height3 by the pure classes0 modulo17,17^2,17^3, the latter two redundant. Add the following current residues, assigning them at each depth to distinct nonunit d|Q with old residue1 modulo d:

| depth | current residues | count |
|---|---|---:|
| 1 | 3,...,16 | 14 |
| 2 | 1+17j for6<=j<=16; 2+17j for1<=j<=16 | 27 |
| 3 | 1+17j+289k for0<=j<=5,1<=k<=16; 2+289k for3<=k<=16 | 110 |

There are119 available nonunit cofactors, so each assignment is possible. Reusing a cofactor at different depths retains distinct original moduli. The actual CRT residue for current y and cofactor d is1+d((y-1)d^-1 mod17^e), modulo d17^e. In total the family has273 distinct forbidden moduli and480 complete test labels.

At old point x0=1 the surviving current leaves are

    S={1,2,18,35,52,69,86,291,580}.

There are4624 pure-surviving leaves before mixed deletion. The AP/T8 killed mass of each retained leaf is w=15/36992, and

    (q,M1,M2,M3)=(9,6,3,1)w,
    Omega_3(R_x0)=8w.                              (CPI5)

Root1 has six leaves in six distinct depth2 children; root2 has three leaves in one child. For compatible depth1/depth2 choices, their prefix deficits alone are at least9w. For incompatible choices, their deficits plus pair loss are at least6w, and depth3 contributes at least2w by CPI3. Choosing root1, the depth2 prefix2 and any retained leaf attains total loss8w. Equivalently the unit-amplitude envelope is49w and the actual maximum is41w. All126 nonempty-prefix triples reproduce this maximum, with nine maximizing triples. Zero-mass choices cannot improve the maximum of the nonnegative square.

Consequently omega_3>=8w/777600=1/239708160 for this entire family, uniformly over every complete test. Adding pure0 modulo19 and no mixed19 exclusions gives an actual two-stage continuation. Polarization of its two19 blocks gives weights19/18 and1/9, so applying the same bound to each yields a correction7/1438248960 to the corresponding composed envelope. The full signed mass term remains unchanged.

The alternative retained set

    S'={1,290,579,18,35,52,2,19,36}

has exactly the same(q,M1,M2,M3) but Omega_3=0: root1, its child1 and leaf1 simultaneously attain all three maxima. It has the same two occupied roots, seven occupied depth2 children and nine leaves. Delete the other14 roots,27 children and110 leaves using distinct old cofactors at each depth as above. This realizes S' in another actual family with the same source and original label inventory. At x0 its pure mass, assigned charge and all separate prefix maxima agree with those for S. Its unit-amplitude maximum is49w instead of41w. Unit amplitudes are legitimate at this row: center every nonunit old test at2 so only the old unit term is active at x0=1.

Thus the new observation is the ancestry relation between actual maximizing prefixes, which is not determined by their separate masses. This is a row-level distinction, not a claim that the two entire families have identical laws on every old row. The ordinary proof and exact CRT/prefix counts verify the mechanism without a uniform positive Omega bound over unrestricted families or a Lean endpoint.

<a id="a-uniform-four-block-loss-in-one-actual-charged17-to19-family"></a>
### A uniform four-block loss in one actual charged17-to19 family

Take the actual uniform144-unit source nu modulo315, from exclusions0 modulo3,5,7. Its ternary height2 is retained by the later original moduli. At each p=17,19 add pure0 and eight mixed classes with old residue1 modulo

    (d_i)=(3,9,15,21,45,63,105,315)

and current root i,1<=i<=8. This is one family of21 distinct odd forbidden moduli, period101745, and48 complete test labels. There are no11/13 exclusions. In particular the19 masks have no17 factor.

Write I_d=1_(x=1 mod d). The number of bad roots is

    k=I3(1+I9)(1+I5)(1+I7) in{0,1,2,4,8}.

For each p put alpha_p=k/(p-1), delta_p=7/(p-2), beta_p=(alpha_p-delta_p)_+/(1-delta_p), g_p=1/(1-min(alpha_p,delta_p)), t_p=g_p/(p-1) and q_p=1-beta_p. Only x=1 has k8, giving beta17=1/16 and beta19=1/18 there. Thus the actual charges are b17=1/2304 and b19=1/2592. The second charge is under the normalized physical17 input, whose old marginal is nu.

The final killed row is the product of the two actual killed rows, because the19 masks depend only on x. Define q=q17*q19, u=t17*q19, v=t19*q17, w=t17*t19. Their exact values are

| k | q | u | v | w |
|---|---|---|---|---|
| 0 | 1 | 1/16 | 1/18 | 1/288 |
| 1 | 1 | 1/15 | 1/17 | 1/255 |
| 2 | 1 | 1/14 | 1/16 | 1/224 |
| 4 | 1 | 1/12 | 1/14 | 1/168 |
| 8 | 85/96 | 85/768 | 17/192 | 17/1536 |

Separate a complete test into independent old blocks A,B,C,D for current exponent pairs(0,0),(1,0),(0,1),(1,1). Pairwise current-cylinder bounds give

    integral L^2 d eta<=E_nu F(A,B,C,D),
    F=q A^2+u(2AB+B^2)+v(2AC+C^2)
                      +w(2AD+2BC+2BD+2CD+D^2).    (BQC1)

For each fixed four old layouts this bound is attained by setting their positive current roots to16 and18, respectively. These roots are globally clean. Thus the current-residue optimization is exact, and all four old layouts remain independently variable.

<a id="centered-cylinder-coefficients-retain-the-actual-atom-energy"></a>
#### Centered-cylinder coefficients retain the actual atom energy

Let Gamma(f)=max_A E_nu[f A^2], and C=sum_(d|315) I_d. Every intersection of a centered I_e and two arbitrary original test cylinders is empty or a residue class modulo their LCM. Under the uniform unit law its mass is at most that of the class centered at1. Expanding the square therefore gives

    E_nu[I_e A^2]<=E_nu[I_e C^2] for every e|315.

For f=u,v,w the table gives the expansion

    f=f0+(f1-f0)I3
       +(f2-f1)(I9+I15+I21)
       +(f4-2f2+f1)(I45+I63+I105)+c_f I315,
    c_f=f8-3f4+3f2-f1,
    (c_u,c_v,c_w)=(223/26880,67/22848,817/304640).  (BQC2)

All coefficients are nonnegative. Hence C simultaneously maximizes u,v,w and all their nonnegative linear combinations. Its value at the actual atom x=1 is12.

The baseline is q=1-epsilon I315 with epsilon=11/96. If G=E_nu C^2, the complete test centered at2 has unweighted square G and value1 at x=1. All tests have A(1)>=1 and unweighted square at most G, so

    Gamma(q)=G-epsilon/144,
    Gamma(q)-E_nu[q A^2]
                          >=epsilon(A(1)^2-1)/144. (BQC3)

<a id="one-positive-rational-matrix-controls-all-four-old-layouts"></a>
#### One positive rational matrix controls all four old layouts

Set A0=A,A1=B,A2=C,A3=D and use the symmetric table

    H=[[0,u,v,w],[u,u,w,w],[v,w,v,w],[w,w,w,w]].

Its row sums R_i are u+v+w,2u+2w,2v+2w,4w. Define

    S=Gamma(q)+sum_i Gamma(R_i)
     =Gamma(q)+3Gamma(u)+3Gamma(v)+9Gamma(w).

Polarization is an exact identity on these same four tests:

    S-E_nu F=Gamma(q)-E_nu[q A0^2]
       +sum_i[Gamma(R_i)-E_nu[R_i Ai^2]]
       +sum_(i<j)E_nu[H_ij(Ai-Aj)^2].              (BQC4)

The atom coefficients of R_i in BQC2 are

    lambda=(12713/913920,10033/456960,733/65280,817/76160).

Every other centered-cylinder deficit is nonnegative, so with a_i=Ai(1),

    Gamma(R_i)-E_nu[R_i Ai^2]>=lambda_i(144-a_i^2)/144.

Retain the same actual atom in the nonnegative squared differences of BQC4 and apply BQC3. This yields

    144(S-E_nu F)>=144 sum_i lambda_i-epsilon+a^T M a,

    M=[[8881/28560, -85/768, -17/192, -17/1536],
       [-85/768, 50657/456960, -17/1536, -17/1536],
       [-17/192, -17/1536, 541/5440, -17/1536],
       [-17/1536, -17/1536, -17/1536, 6847/304640]].

There is an exact rational positivity certificate:

    r=(1,4/3,5/4,9/5),
    Mr=(17981/548352,7403/2193408,427/391680,
                                           43703/54835200)>0.

For e_ij=-M_ij>=0 and every real a, direct expansion gives

    a^T M a=sum_(i<j)e_ij r_i r_j(a_i/r_i-a_j/r_j)^2
                 +sum_i ((Mr)_i/r_i)a_i^2.

Every original old block contains its unit indicator, so a_i>=1. Substitution gives the uniform full-test loss

    Gamma(q)+3Gamma(u)+3Gamma(v)+9Gamma(w)
       -max_L integral L^2 d eta
       >=16283037949/284265676800
        =0.05728105528707995...>0.057281.           (BQC5)

All maxima retain the48 original test labels. There is no assumption that A,B,C,D coincide or that their extrema have a prescribed form. The factors q19 in u, q17 in v and both in q preserve the actual two-stage killing. Subtracting484 eta1 on both sides gives the same loss for the signed objective, but this benchmark is not the separate KC sum of the17 and19 frontiers.

The literal21-class construction,144 source rows, both physical/killed kernels, every cylinder coefficient and the matrix certificate have been recomputed with exact rational arithmetic. The arbitrary-layout conclusion follows from BQC1--BQC4 and the displayed matrix identity. This proves a same-family strict loss with positive charge at both stages; it does not supply a uniform0.057281 subtraction over other original families, the299.398 target, later-prime continuation or Lean verification.

<a id="prefix-tree-optimization-and-branch-price-certificates"></a>
### Prefix-tree optimization and branch-price certificates

This is ordinary mathematics with exact rational computation, not Lean
verification. All masses belong to one actual unnormalized killed row. No
probability replacement, original-modulus deletion, or repeated-block hypothesis
is used. The method evaluates CPI's row relaxation; it does not make the original
complete test independently selectable at different old histories.

<a id="1-tree-score"></a>
#### 1. Tree score

Let R be a finite nonnegative measure on Z/p^H Z. Its prefix tree has one
node v=(e,a) for each current residue a modulo p^e, with mass m(v)=R(v).
Let M_e=max_(depth v=e)m(v), q=R1, and

    C_H = sum_(e=1)^H (2e+1) M_e.

Select one node v_e at each depth. Let anc_S(v) be the number of selected
strict ancestors of a selected node v. Laminarity of residue cylinders gives

    J(S) = integral[(sum_(v in S)1_v)^2 + 2 sum_(v in S)1_v] dR
         = sum_(v in S) [3+2 anc_S(v)] m(v),

because distinct incomparable nodes are disjoint and the intersection of an
ancestor with v has mass m(v). Rewriting CPI1 gives exactly

    Omega_H(R) = C_H - max_(one node per depth) J(S).                 (PT1)

Thus the quantity to optimize is a positive tree score. Nodes of zero mass can
be omitted for this maximum when q>0. Any selected zero-mass node has no
positive-mass descendant; replacing it by any positive-mass node at the same
depth cannot decrease the original pointwise nonnegative square. Repeating
leaves a tuple of positive nodes. For q=0, Omega_H=0 separately.

If s full-height leaves carry positive mass, the positive tree has at most
1+Hs nodes. Constructing all its masses costs O(Hs) additions, when the leaf list
is already available. This does not give a bound on the size or discovery cost
of that actual row representation.

<a id="2-exact-subset-of-depths-dynamic-program"></a>
#### 2. Exact subset-of-depths dynamic program

For a node v of depth d, an integer a in [0,d-1], and a subset D of
{d,...,H}, let F_v(a,D) maximize the score of choosing exactly one node at each
depth in D, all inside v's subtree, with a already selected strict ancestors.
These are the only external effects on the subtree score.

Put epsilon=1_(d in D), D'=D\{d}, a'=a+epsilon. Then

    F_v(a,D) = epsilon(3+2a)m(v)
        + max_(disjoint union_c D_c = D') sum_c F_c(a',D_c).        (PT2)

Here c runs over the positive children of v. An empty subtree allocation gives
zero. An allocation requesting a depth unavailable below a leaf is infeasible.
At the virtual depth-zero root, epsilon=0 and a=0; D={1,...,H} gives max J.

Proof: v is the only depth-d node of its subtree, so its inclusion is forced by
D. Every other chosen node lies in exactly one child subtree; its depth is
allocated to that child, with no duplicated depth. Selections from different
children have zero interaction. Selected ancestors contribute only through a'.
This proves both inequalities in PT2 and gives reconstruction of a maximizing
tuple. It does not impose that all selected nodes form a chain.

Combine children by max-plus subset convolution. For a fixed state a, the total
number of disjoint-pair trials on a future-depth set of size k is 3^k. A simple
uniform upper bound is O(H N 3^H) arithmetic operations and O(H N 2^H) stored
score entries for a tree of N positive nodes; the depth-dependent bound can be much
smaller. This is exponential in H, but has no product of level widths. Literal
tuple enumeration has product_e n_e candidates, where n_e is the positive
width at depth e. The implementation caches one whole table per (node, ancestor
count), sharing each convolution across all requested masks. It does not rerun
the convolution separately for each final mask. The subset program is not
claimed faster on every small row; its advantage is dependence on H versus the
product of widths. The reference implementation retains witness tuples of length
at most H beside each score entry; tuple-copy operations and witness storage
therefore carry an additional factor at most H. Arithmetic bit complexity and
actual old-state enumeration are additional costs.

<a id="3-depth-prices-give-small-checkable-lower-certificates"></a>
#### 3. Depth prices give small checkable lower certificates

Fix real prices lambda_1,...,lambda_H. Drop the one-node-per-depth restriction
inside an auxiliary maximization, allowing any subset S of positive nodes. Put

    B_v(a) = max over selections in v's subtree
               [subtree score with a selected ancestors - sum selected prices].

It obeys the binary tree recurrence

    B_v(a) = max {
        sum_c B_c(a),
        (3+2a)m(v) - lambda_d + sum_c B_c(a+1)
      }.                                                         (PT3)

At the virtual root use B_root(0)=sum_(depth1 v)B_v(0). Every feasible PT1 tuple
has total price sum_e lambda_e, so

    max J <= sum_e lambda_e + B_root(0),
    Omega_H >= C_H - sum_e lambda_e - B_root(0).                   (PT4)

The maximum of the latter expression with zero is also a valid lower bound.
Prices of either sign are valid. Computing PT3 uses O(HN) arithmetic operations
and O(HN) states, since at depth d only a=0,...,d-1 can arise. Root and edge
traversals are included in this bound. A rational upper table need only satisfy
both inequalities corresponding to PT3; exact equality is unnecessary. Such a
table is a short certificate checked with additions, comparisons, and the actual
prefix masses. Floating-point optimization may propose prices but cannot certify
the bound without this exact evaluation.

PT4 is a Lagrangian upper relaxation of max J, not an assertion of strong
duality for the integral one-node-per-depth problem.

<a id="4-branching-enforces-a-few-actual-depth-constraints"></a>
#### 4. Branching enforces a few actual depth constraints

Choose some depths to fix. A branch specifies one positive node at every fixed
depth, with no nesting restriction between the specified nodes. In PT3, force
the inclusion action for that node and force the exclusion action for all its
peers. Set its depth price to zero and price only the remaining free depths.
The resulting recurrence exactly maximizes the priced unrestricted score within
that branch. For any such branch b and any branch-specific price vector,

    J_b <= sum_(free e) lambda_(b,e) + B_(b,root)(0) = U_b.

All positive-node tuples are covered by the branches. These suffice for the
original maximum by PT1's zero-node replacement argument, hence

    max J <= max_b U_b,
    Omega_H >= C_H - max_b U_b.                                  (PT5)

Each branch takes O(HN) arithmetic. Exhausting r fixed depths costs at most the
product of their positive widths times that per-branch work. Branch selection
and price discovery are separate from certificate validity. Fixing more depths
can only improve the best possible upper certificate, because existing prices
restrict to the finer branch; it does not guarantee a particular chosen price
vector improves. Fixing every depth reduces to the literal exact problem.

<a id="5-exact-tests-on-the-actual-s--s-fixtures"></a>
#### 5. Exact tests on the actual S / S' fixtures

Use unit leaf masses first, multiplying the conclusions by the actual common
weight w=15/36992 afterwards. For

    S = {1,2,18,35,52,69,86,291,580}

the positive widths are (2,7,9), masses (M1,M2,M3)=(6,3,1), and C3=40.
The subset program gives max J=32, so Omega3=8, reproducing the independent
literal-square maximum 41 after adding q=9. There are 126 complete positive
tuples. For S' from CPI5, the program gives max J=40 and Omega3=0.

The unbranched price vector (18,6,6) gives B_root(0)=3 and upper score 33,
therefore Omega3>=7. This is the best possible scalar-depth-price certificate,
not a failure to search prices long enough. Consider three unrestricted subsets:

    A = {root1, root2, child2, leaf2, leaf291, leaf580},
    B = {child2},
    C = {root1, child2}.

Their depth-count vectors and scores are

    A: (2,1,3), score63;
    B: (0,1,0), score9;
    C: (1,1,0), score27.

The equally weighted mixture has mean count (1,1,1) and mean score33. For every
price vector lambda, the unrestricted maximum priced score is at least its
average over this mixture, namely 33-sum lambda. Thus no scalar-price bound is
below33. It leaves an exact integrality gap of1 in this fixture.

Two root branches remove that gap with explicit integer prices:

    selected root1: lambda2=9,  lambda3=5; upper J=32;
    selected root2: lambda2=15, lambda3=7; upper J=31.

Both bounds follow directly from PT3 with lambda1=0 and the depth-one actions
fixed. Hence max J<=32 and Omega3>=8. A feasible original tuple attains J=32,
so this lower certificate is exact. This uses two tree recurrences, not an
assumption that the maximizing prefixes form a chain. In particular the winning
root1 branch uses the incompatible depth-two child2.

The actual arithmetic realization, original 480 test labels, actual row factor
w, and full old measure remain those of CPI5. Integrating a row certificate uses
its actual weight and does not give a positive uniform correction for families
whose rows have a common nested sequence of maxima.

<a id="exact-verification-1"></a>
#### Exact verification

verify_prefix_correction.py uses exact integers/Fractions and does not rely on Python assertions.
It checks both fixtures against direct literal leaf squares; compares PT2 with
all 256 binary depth-three support sets; compares another 80 rational weighted
rows at binary depth4 and ternary depth3; and checks PT3 against exhaustive
arbitrary-node-subset maximization on 20 small rational rows. Root-branch upper
bounds are independently checked on the 80 weighted rows. The exact dual-gap
mixture and branch-price constants are separately checked.

The script also reconstructs both literal odd-modulus families from scratch:
it generates all old divisors, all 273 distinct forbidden moduli and their CRT
residues, the 480 complete original labels, and checks every current leaf at
old x=1 against the actual congruences. It reconstructs the uniform old-unit
count 777600 and the AP/T8 killed leaf weight 15/36992. Its adjacent
prefix_correction_certificate.json pins the exact counts, masses, all observed
survivors, and a digest of each original arithmetic family. Normal verification
recomputes these fields and rejects any mismatch or duplicate JSON key.

These checks establish reproducible computational evidence for the new mechanism
and its examples. The general mathematical justification is PT1--PT5 above;
no Lean validation or unrestricted #7 numerical improvement is claimed.

The [prefix certificate](../certificates/prefix_correction_certificate.json) also reconstructs both273-modulus arithmetic realizations from their literal CRT classes, all480 complete test labels, the pure current base, and the actual killed leaf mass. Altered numerical values and duplicate JSON keys are rejected.

<a id="prefix-corrections-survive-height-extension-and-controlled-law-changes"></a>
### Prefix corrections survive height extension and controlled law changes

Let R be a finite nonnegative measure on the leaves of a p-ary prefix tree of actual height H. Me=max_(depth e nodes v) R(v), q=R1. For a selection v1,...,vh of one node at every depth, set N_v(y)=sum_e1_(y in ve). CPI gives exactly

  Omega_h(R)=U_h(R)-J_h(R),
  U_h=sum_e=1..h(2e+1)Me,
  J_h=max_v integral(N_v^2+2N_v)dR.                 (PCS1)

All quantities at h use the projection of the same actual row; J_h removes the common unit q from the square. Direct expansion proves PCS1, with no nested-selection restriction. Both U_h and J_h are nonnegative, positively homogeneous, monotone under adding positive measure, and bounded by C_h R1, where C_h=h(h+2). Omega_h is nonnegative and homogeneous but is NOT asserted monotone in R.

For h<=H,

  0<=Omega_H(R)-Omega_h(R)
    <=2 sum_e=h+1..H (e-1)Me
    <=2c p^(-h) [h/(p-1)+1/(p-1)^2]               (PCS2)

whenever Me<=c p^-e. The first inequality follows because every summand in the original CPI1 cost is nonnegative and restricting a full selection gives a legal h-selection. For the upper bound, extend a minimizing h-selection by choosing a maximal-mass node at each later depth. All new individual deficits vanish. For depth e there are e-1 earlier choices, each causing incompatibility cost at most2Me. This proves the finite sum; summing the entire geometric tail proves the final formula. It also covers h=0. At actual height0 both corrections are0.

For two nonnegative measures R,S on the SAME finite height-h tree, with epsilon=||R-S||_1 (full L1, not half),

  |Omega_h(R)-Omega_h(S)|<=C_h epsilon.            (PCS3)

Write R-S=delta_plus-delta_minus with masses a,b. A maximizing cylinder in R gives Me(R)-Me(S)<=a, and swapping gives >=-b. Thus -C_h b<=U_h(R)-U_h(S)<=C_h a. Every function N_v^2+2N_v takes values in[0,C_h], so the same bounds hold for J_h(R)-J_h(S). Subtracting gives [-C_h(a+b),C_h(a+b)]. This proves PCS3, including different total row masses and empty rows. No normalized conditional probability or division by a row mass is used.

For a joint nonnegative measure zeta on a finite old carrier X times current prefixes, let zeta_x be its unnormalized current row, and

  omega_h(zeta)=sum_x Omega_h(zeta_x).

By positive homogeneity this equals integral Omega_h(R_x) dsigma when zeta=sigma R, even on zero-mass rows. Therefore, on the SAME old carrier and prefix tree,

  |omega_h(zeta)-omega_h(zeta')|<=C_h||zeta-zeta'||_1. (PCS4)

In particular for actual height H>=h, any certified lower value B_h<=omega_h(zeta') gives

  omega_H(zeta)>=max(0,B_h-C_h epsilon).           (PCS5)

Only the one full joint L1 discrepancy is charged: incoming-law change and kernel change must not be counted separately after already included in epsilon. The larger actual current height costs NOTHING in this lower certificate because PCS2 is monotone. A two-sided approximation additionally pays the geometric upper tail of PCS2; with c(x) caps its integrated coefficient is integral c dsigma.

At p19,T8, sigma=nu13 K17^-, R=K19^-, zeta=eta. The generic full-Haar cap is c<=18/10=9/5 and sigma1<=1. Thus for h=6,

  0<=omega_H-omega_6<=2*(9/5)*19^-6*(6/18+1/18^2)
       =109/(90*19^6).

The joint-law sensitivity is48 epsilon. At p17 the cap2 similarly gives tail97/(64*17^6) and sensitivity48 epsilon. If H<6 use h=H: extra original test depths cannot be fabricated just to claim a larger correction.

For the KC lifted finite reference on the common original carrier, existing positive-kernel contractions give

  ||eta-eta_core||_1<=epsilon17,0+epsilon19,0+eNm.    (PCS6)

Consequently its depth-h correction can be transported by PCS5 with this error. This only transports a supplied certificate, not its unknown uniform minimum over original residue families. The core must be lifted to the common carrier; simply averaging or forgetting old rows is not covered by PCS4.

There are two distinct legitimate uses. To correct an independently established ACTUAL envelope U, combine CPI4 and PCS5: Q_eta<=U-484 eta1-max(0,B_h-C_h epsilon). Alternatively evaluate the full REFERENCE corrected objective using its own row data, then apply KC8's already-paid full-objective comparison. In the latter use no second PCS5 error is required. Neither route appends a new subtraction to the exact CT identity or changes299.398 without the missing uniform optimization.

The common-old-carrier condition is necessary. Split CPI5's S row into its six leaves below root1 and three below root2. Each separate row has Omega3=0, while their sum has Omega3=8 at unit leaf mass. Forgetting which old row occurred can therefore invent a positive correction. Positive homogeneity does not authorize averaging old histories. The ordinary proof above was independently checked, with exact tests on256 support sets,80 rational row pairs and all32,640 pairs of those support sets; this is not Lean verification.
