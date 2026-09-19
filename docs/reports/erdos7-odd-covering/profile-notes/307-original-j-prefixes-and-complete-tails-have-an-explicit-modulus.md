[Index](../marked_head_profile.md) · [Actual source rows](306-common-actual-j-rows-restore-the-vanished-columns.md) · [Complete original heavy bound](298-retaining375-certifies-the-complete-heavy-cost.md)

# A quantitative modulus for the original J analytic prefixes and tails

On the actual-source domain of136 and the
[common-theta row interface](306-common-actual-j-rows-restore-the-vanished-columns.md),

    delta>=0, qJ>=1-delta, rho=S-S0>=0,
    t=delta+rho<=1/1000,
    R=E5+E15+E5d+E15d+E3+omega<=rho+7delta/36<=t,

let F(v)=sum_(j=1..8) a_j*(v-j)_+, where a_j>=0 and
A=sum_j a_j>0. Define

    B1(e)=sum_(a,b>=0,a+b>0) min(e,3^-a*5^-b),
    E_A(t)=A*(256t+B1(100t)), E_A(0)=0.          (P1)

Every analytic two/four/six/seven/eight-projection prefix formula
actually used by298 and296 has the following uniform transport:

    actual complete original F objective
       <= its original face formula at the common theta + E_A(t).
                                                            (P2)

This includes each old threshold-dependent selected prefix and the
strengthened four-step telescopes retaining25,27,75,81 for *every*
hinge, including H1 in298 and H4 in296. The same error works for all
original head layouts and independent positive-seven projections.
It also supplies the omitted-tail increase for the retained LP
objectives. It does not price their duals or restore strong-zero
columns. The proof is ordinary mathematics with independent verification. The
original branch partition is retained; no new LP or prefix scan is needed.

The exact source sites are `j_face_coupled_seven_heads.py`:
`source_tables`, `raw_source_lp`, `deletion_correction`, `prepare`,
`objective`; `j_face_second_depth_retained_heads.py`: `prepare_six`;
and the four-step `prepared`/`rational` bodies in
`j_face_retained375_heavy_heads.py` and
`j_face_retained375_survival_heads.py`. The latter's complete
prefix ledger is inherited by296. The clipping and signed-credit arguments below use these actual J
quantities throughout.

**1. Keep the complete kernels and account for the one density error.**
The old head B=1+I3+I9+I5+I15+I45 has1<=B<=6. A selected old prefix
has at most four additional indicators, so its load is at most10.
Keep the existing ideal density w(c,s) in[2/5,1]; it is independent
of theta. For first/second-depth extra counts0<=m,e<=4, the complete
conditional-cap kernel is

    g_j(v,m,e)
      =(6/35)*(1+m-(j-v)_+)_+
       +(6/245)*(1+e-((j-v)_+-(1+m))_+)_+
       +1/[5*7^(2+((j-v)_+-(1+m)-(1+e))_+)].

The one-depth kernel is the special case e=0; the formula retains
the entire unit-seven tail. It is the sum remaining after deleting
the first(j-v)_+ entries from a nonincreasing list of complete
seven caps. Hence

    0<=g_j<=241/245<1,
    phi_j(v)=w*(v-j)_++g_j(v,m,e)

is nonnegative, increasing and integer convex, with every forward
increment at most w<=1. Before v reaches j its next cap is at most
6/35; afterwards its increment is w. These properties hold at every
integer v, not only a finite table. Consequently

    Phi(B):=sum_j a_j*phi_j(B)<=6A,
    0<=Phi(v+1)-Phi(v)<=A,
    H_selected:=sum_j a_j*(selected_load-j)_+<=9A. (P3)

For the old threshold-dependent compiler, the increment at each
selected step sums only the active thresholds. The same bounds
hold since these are a subset of the positive coefficients. For
the strengthened compiler every threshold is active in all four
steps. No inference about activation is made from j-1 here.

Use the actual positive measure Xi from the row interface:

    mu+V3+Vp+Va<=w*Lambda+Xi,
    Xi(1)<=Berr:=delta+10(E5+E15)+omega<=11t.    (P4)

It is the sum of the positive shallow3/9 density discrepancy, the
wrong/missing5/15 ideal-section loss measure, and W. It is one
measure for all marked events. Apply(P4) to H_selected. Since every
selected hinge dominates its base-head hinge H(B), the actual
deep-family deletion credit can be kept at H(B), while the Xi
error is at most9A*Berr<=99At. The raw seven increment receives no
additional density error: it is integrated against Lambda, as in
the original conditional-cap inequality. Thus phi and all its
finite difference coefficients stay unchanged off the face.

**2. The raw25-node LP loses at most42At.** The common-theta
construction provides an actual theta in[1/135,1/90] such that

    sum_i[Lambda_i-cap_theta,i]_+
      <=19delta/36+ell<=6t, ell<=5E5.

The three disjoint group budgets(cells0,1,root1) have total positive
excess at most

    delta/18+delta^2/72+delta/36+2delta/9
      =11delta/36+delta^2/72<=t.                 (P5)

Clip the actual25 masses to the face cell caps, removing at most6t.
Then trim each group to its original face budget, removing at most
the group excess in(P5), hence at most another t. The resulting
nonnegative vector is feasible for the face cap/group LP at the
*same* theta. With coefficients Phi(B)<=6A, the original actual
raw head is bounded by that LP value plus42At.

The existing closed formula

    sum_i cap_theta,i*Phi_i
      -(1/120)*min_(i in SUPPORT)Phi_i

is exactly this face LP optimum, as checked by the existing
independent LP API in `rational_objective`. Thus the negative
minimum term is retained with its original value. It is not
discarded and is not falsely declared valid directly on an
off-face source. Clipping is the justification for using it.

**3. All selected operators and their CRT alternatives cost at
most4At together.** A descendant25 or75 profile has positive
coefficient mass change at most delta/450: only eta0 can exceed
its face width, by delta/18, and its denominator is25. A27 or81
profile has positive coefficient mass change at most

    (Delta+4ell)/27
      <=(3delta/4+20E5)/27<=t.                  (P6)

For(P6), before late removal the actual source's five-section in
each parent cell is bounded by K(c,s)+1_(s=Q)*(Delta+4ell), using
the actual root-wide deletion sets of116/136. Restricting the
ternary coordinate to the original test cylinder multiplies by at
most1/27 or1/81. This is a section bound, not an inference from a
coarse cell total. It is uniform over every original parent.

Every nonnegative finite-difference array used in a selected
operator is at most A by(P3), even for the strengthened H1/H4
four-step construction. Therefore each selected operator gains
at most At. The raw mixed intersections remain bounded exactly
by1/675 or1/2025. In particular the fourth-step alternatives keep
the arrays l=D_4^1, u=D_4^2, h=D_4^3 and their original corrections

    max_i max(2*(u_i-l_i),h_i-l_i)/2025,
    max_i(h_i-u_i)/2025.

All these coefficient arrays are unchanged; their CRT caps have
zero error. Each option therefore gains at most At through its
one selected operator. Taking the minimum of the valid options
preserves this upper. Summing at most four steps costs at most4At.
Their pointwise inequalities are201(EP8--EP13), so independent
original residues and both compatible/incompatible intersections
are preserved.

**4. The complete base-head deletion credit loses at most26At.**
Set m_s=min(H(B_0s),H(B_1s)), and h_c=min_s H(B_cs); both are at
most5A. The original J credit is exactly

    Dface=sum_s m_s*q*_s/90
             +sum_c h_c*eta*_c*(1+ROOT(c))/100.

Unlike the K credit there is no compulsory cell1 deep3 term. With
the actual product references of the row interface,

    P3=nu3 tensor q, nu3(root0)=1/90,
    P3-Vgood>=0, (P3-Vgood)(1)<=4E3,
    ||q_slots-q*_slots||1<=5delta/4+4ell,
    ||Vp+Va-(Pp+Pa)||TV<=B5:=E5d+5E15d,

and the product-five cell totals differ from the face totals by
at most delta/450 in total variation. Nonnegativity then gives

    Dface-integral H(B) d(V3+Vp+Va)
      <=5A*[4E3+B5+(5delta/4+4ell)/90+delta/450]
      <=5A*[5R+29delta/1800]<=26At.             (P7)

The penultimate step combines prices on the same six defects:
4E3+B5+4ell/90<=4E3+E5d+5E15d+(2/9)E5<=5R.
The actual q, including its source perturbation, is retained in P3.

Adding(P4)--(P7), every finite analytic candidate gains at most

    (99+42+4+26)At=171At.                      (P8)

This already includes actual density error, original cap LP,
all selected-mask telescopes and the full deletion credit.

**5. Complete assigned old and positive-seven tails.** For each
nonunit zero-seven original label d=3^a5^b, 136 gives

    mu(C_d)<=c_d^face+100t,
    mu(C_d)<=3^-a*5^-b.

The positive excess above its assigned face cap is consequently
at most min(100t,3^-a*5^-b). For *any* omitted-label subset its
entire infinite sum is at most B1(100t). Apply this separately to
the actual per-threshold omitted support and then sum a_j: its
total price is at most A*B1(100t). This covers both the original
remainders R_min(j-1,4) and the strengthened common R4, as well as
the punctured old tails after retaining135,125,225,375.

For positive-seven tails use the actual complete raw-cofactor
series, not survivor caps. Put N3=max_root Lambda(root),
N9=max_cell Lambda(cell), dmax=max_c(z-alpha_ROOT(c)-beta_c).
Its seven disjoint cofactor categories are

| Cofactor | Actual assigned raw cap | Face assigned raw cap |
|---|---:|---:|
|3|N3|1/8|
|9|N9|1/12|
|3^a, a>=3|dmax*3^-a|(3/4)*3^-a|
|5^b, b>=1|h*5^-b|(1/2)*5^-b|
|3*5^b, b>=1|h1*5^-b|(1/3)*5^-b|
|9*5^b, b>=1|max(eta)*5^-b|(1/9)*5^-b|
|3^a*5^b, a>=3,b>=1|3^-a*5^-b|same|

The J source guards give h1>h0, so h1 is the correct largest-root
width in this table. Projection onto the same J face gives
||n-n*||1<=delta/2. Its two root totals are both1/8 and maximum
cell total1/12. Hence the positive cap changes obey

    (N3-1/8)_+<=(delta/2),
    (N9-1/12)_+<=(delta/2),
    (dmax-3/4)_+<=delta/4,
    (h-1/2)_+<=delta/18,
    (h1-1/3)_+=(max(eta)-1/9)_+=0.

Since sum_(a>=3)3^-a=1/18 and sum_(b>=1)5^-b=1/4,
the total *positive* difference of the complete raw-cofactor cap
series is at most

    delta/2+delta/2+delta/72+delta/72=37delta/36.

Multiply each original depth-e label by u_e=6/(5*7^e), whose
complete sum is1/5. The total positive difference of the full
nonunit positive-seven series is at most37delta/180. Every
punctured subset has the same valid upper. This includes the
original Z2,Z4,Z6,Z7,Z8=13/490, and the further deletion of the
fresh175/189 assigned payments3/875 and1/210 in296.

Each remainder is constructed by retaining the designated summands
of its cap series and summing its complement. Thus no estimate is
subtracted from unknown actual mass. The unit-seven series is
already wholly in g_j and is not paid again here. Combining both
complete tails gives the separate LP-tail modulus

    T_A(delta,t)=A*[B1(100t)+37delta/180].        (P9)

Equations(P8),(P9) imply(P2), with room in the rational constant256.
The old remainder itself, its missing-label convention and each
newly retained original test stay unchanged.

**6. The modulus is explicit and tends to zero.** For every integer
L>=1 and e>=0, split the complete cofactor sum into the box
0<=a,b<L and its two geometric outer strips. This gives

    B1(e)<=(L^2-1)*e+(15/8)*(3^-L+5^-L).        (P10)

No original label is discarded: the right side pays each complete
outer strip. For0<t<=1/1000 choose the least L>=1 with3^-L<=t.
It is computable using integer comparisons when t is rational.
Then5^-L<=t, and the convenient purely rational upper is

    E_A(t)<=A*t*[256+100L^2+15/4].              (P11)

It tends to zero because tL^2 tends to zero. Thus(P1) does not
assert a false uniform Lipschitz bound on infinitely many labels;
it gives an explicit logarithm-squared modulus. At t=0 every
error is zero directly, without invoking the positive-t choice L.

**7. Use the same theta before minimizing and retain nonanalytic
certificate obligations.** Every actual source has the one theta
constructed from its original source135 and total late allocation.
If L_i(theta) are any of the old/strengthened analytic face lines,
then(P2) gives

    actual F <= min_i L_i(theta)+E_A(t)
       <=max_(theta in[LO,HI]) min_i L_i(theta)+E_A(t).

This is precisely the endpoint/crossing envelope used for the
recorded pruning classes. A prefix bound applies to all its later
independent projection descendants as before. The uniform error
does not require knowing which alternative or crossing attained
the recorded minimum, replaying the prefix partition, or assuming
convexity of a new off-face optimum. Here A=1 for296's H4/AP13 and
A=403/8 for298's original heavy function.

LP-certified pruning is a distinct basis. In298, the
`six_known_dual_bounded` class may use264,256 or251 duals; its50
seed prefixes use their own checked complete objective duals.
In296's inherited ledger the corresponding existing bank is256.
Own-leaf upper minima can also select inherited complete bounds
rather than an analytic line. Those actual adopted bounds must
receive their own complete row price, plus(P9); a stored face
constant does not inherit(P2) merely by being listed in a prefix
record. The uniform100t row theorem supplies the mathematical
interface, and each original dual norm must be included when applying the result.

The [306 restoration theorem](306-common-actual-j-rows-restore-the-vanished-columns.md)
pays the original objective coefficients of298's4634 vanished columns.
Complete299 also uses non-hinge observations and signed mass, so this
prefix result alone does not assert a numerical neighborhood, global
join, arbitrary later-prime continuation or a Lean result.
