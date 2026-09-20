[Index](../../marked_head_profile.md) · [Shared survival](46-one-forbidden-carrier-mixture-strengthens-survival.md) · [Original linear refinement](39-source-deficits-through-one-actual-survivor-mass.md)

# Six linear tests share the survival carrier

This result conditions only the six R17/R19 directions at original
tuples(0,0),(0,1),(1,0). Their barriers are the unchanged entries of
shared_linear_refinement.UNCHANGED_BARRIERS. The other35 directions
keep their globally defined three-event unconditional margins; those
may be evaluated by inherited certified lower bounds at unrefined
vertices. No broad common-carrier quadratic theorem is used.

The statement is an ordinary mathematical consequence of the actual
measure, source payment and cap hypotheses in profiles31,39 and46.
It does not identify original test residues, replace the actual
probability law, truncate exponent tails, or establish Lean verification.

## 1. Fixed costs and the three-event threshold

Let i be any of the41 linear-cost directions in the complete AP45
inventory. Its old one-event barrier is C_i^old and its cost f_i is
a nonnegative mixture of scaled linear hinges, up to a constant.
It is increasing and discretely convex with an eventual affine tail.
The inventory guarantees C_i^old>=f_i(4). Define the fixed new barrier

    C_i=max(C_i^old,max_(b=1,2,3)[f_i(b)+3*Delta f_i(b)]),
    epsilon_i=C_i-C_i^old>=0.

These barriers are independent of theta and every forbidden carrier.
For the six directions under consideration epsilon_i=0; among all41
there are seven zero increases and34 positive increases. R5(0,0) is
the seventh unchanged direction and stays among the other35 here.

For independent zero5/first-positive5 layouts b,c5 in BASES set

    v_l=Delta f_i(b_l), k_l=C_i-f_i(b_l), t_l=c5_l*v_l.

Then0<=v_l<=t_l<=k_l. For the three original test events5,15,45,
with their own mod5 residues and active count N, the same actual
complete test obeys

    (C_i-f_i(A_i))_+<=k_l-v_l*N, k_l-v_l*N>=0.       (L1)

The complete zero7 source cost is

    psi_i(v)=sum_n(p7_n/n)*[f_i(n*v)-f_i(n)],
    sum_n p7_n=1.

For a scaled hinge g(v)=(a*v-t)_+ with a,t>=0 and n>=1,
[g(n(v+1))-g(nv)]/n>=g(v+1)-g(v). Nonnegative summation gives

    Delta psi_i(v)>=Delta f_i(v)                    (L2)

at every integer v>=1. The eventually affine cost representation
makes all these source sums finite-valued with exact geometric tails.

## 2. The L=1 payment holds before choosing a shallow carrier

Use exactly the actual measures and cap mixture pi of profile46.
For one of the three selected original5 events with ternary support
Dtest, full event Itest and actual pure5 mass h<=1/5, let

    K(E)=integral_eta v*1_(Dtest intersect E),
    R(E)=h*K(E)-integral_Lambda v*1_(Itest intersect E)>=0.

By(L2), the selected zero7 source comparison pays

    (1/5-h)*K(Omega)+R(Omega)

once, with outside coefficient L=1. This is exactly the payment
used in profile39's three-event linear refinement.

The five selected deleted pure3 cofactors3,9,27,81,243, over every
positive7 depth, have total cap multiplicity5*sum_e u_e=1. Apply
their cap enlargement to the nonnegative floor in(L1). If
B=sum_alpha u_alpha*K(E_alpha), then B<=K(Omega) and
sum_alpha u_alpha*R(E_alpha)<=R(Omega). Hence

    -h*B+sum_alpha u_alpha*R(E_alpha)
       -[(1/5-h)*K(Omega)+R(Omega)]<=-B/5.           (L3)

There is one such calculation for each selected test event. The
payments are not shared between tests. Adding independently valid
test inequalities with their nonnegative inventory weights does not
spend any one test's source loss a second time.

After(L3), the selected deletion coefficient on a ternary cylinder E
is the signed expression

    integral_E k d lambda-integral_E(t/5) d eta.

Put a_l=k_l*n_l-t_l*eta_l/5, z_l=k_l*d_l-t_l/5>=k_l/20>=0,
w_l=9*eta_l*k_l. For c=(r,j) in the18-carrier set let

    A_c(a)=1_(r!=empty)*sum_(ROOT(l)=r)a_l
                                +1_(j!=empty)*a_j,
    T_i(k,t)=(13/243)*max(z)+(1/486)*max(k*d)
             +(sum(w)+R(w)+max(w))/36+max(k)/72.

Depths1 and2 retain A_c(a), including its sign and zero empty-carrier
entries. Depths3,4,5 and the remaining pure3 tail give13/243 and1/486.
The positive5 cofactor terms use product domination without consuming
the source payment. All terms still have the outer7 multiplier1/5.

Let U_i(theta;b,c5) be profile39's complete retained source envelope:
its independent positive7 complement, its zero5 baseline and complete
deep source term, and the retained first-positive5 layout through the
whole positive5 tail. Define

    m_i(theta;c)=C_i*s-max_(b,c5)[U_i(theta;b,c5)
                                      +(A_c(a)+T_i(k,t))/5]. (L4)

For the actual deficit d_i=C_i*S-s*E_M[f_i(A_i)*1_V],(L3) gives
the fixed-layout bound before its shallow maximization. Expressing
sum_e u_e*A_(c_e) by the same pi as in profile46 and only then
maximizing each test's own layouts proves

    d_i>=sum_c pi_c*m_i(theta;c).                   (L5)

In particular(L5) holds simultaneously for the selected six costs
and the three survival hinges, with one actual S and one pi. The
source layouts inside each m_i remain independent. It also defines
a valid conditioned expression for the other35 costs, although their
carrier tables need not be evaluated for the application below.

## 3. Uniform domination of the old one-event margins

Let o_i(theta;b) be the old fixed-layout one-event margin from
shared_source_deficits.aggregate, using C_i^old and correction v_l.
Write o_i(theta)=min_b o_i(theta;b). Let cap0=5*(s-D).

First, its omitted empty alternatives are harmless on the complete
domain. Convexity and C_i^old>=f_i(4) imply

    min_l(C_i^old-f_i(b_l))>=Delta f_i(3)>=max_l v_l.

Since s>=1/4 and sum eta_l<=5/9, the old signed coefficient vector
a^old obeys

    sum_l a_l^old
      >=max(v)*(s-sum(eta)/5)>=max(v)*5/36>=0.

At least one root sum and one individual cell entry are therefore
nonnegative. Adding explicit zero branches leaves the old root and
cell maxima unchanged. This supplies the domain-level justification
for the guard sum(signed)>=0 in fixed_cost._cofactor_cap.

With those zero branches included, the complete cofactor expression
W(k,t) is a sum of maxima of linear functions, with nonnegative
coefficients. It decreases when t increases. Also

    W(k+epsilon*1,v)<=W(k,v)+epsilon*W(1,0),
    W(1,0)=cap0=5*(s-D).                            (L6)

The selected and unselected deep coefficients sum to1/18. Thus
the same cap0 is used before and after the three-event refinement.
Because t>=v and a fixed carrier is bounded by the full maximum,

    A_c(a_new)+T_i(k_new,t)
       <=W(k_new,t)
       <=W(k_old,v)+epsilon_i*cap0                 (L7)

for every b,c5,c, including partial and empty c.

Second, retaining the same first-positive5 layout cannot increase
the old source bound. If R_n(c5) is the complete pure3 envelope for
psi_i(n*B1), R_n=max_c5 R_n(c5), and x=sum eta_l, its positive5
contribution is

    P_i(c5)=sum_(n>=2)(p5_n/n)*[
                  R_n(c5)-psi_i(n)*x
                  +(n-2)*(R_n-psi_i(n)*x)]
               +x*sum_(n>=2)p5_n*psi_i(n).

Replacing R_n(c5) by R_n recovers the old positive5 term exactly;
all replacement coefficients are nonnegative. The affine tail is
retained using its complete zeroth and first geometric moments,
so this inequality is not a finite-height comparison. Thus

    U_i(theta;b,c5)<=U_i^old(theta;b).              (L8)

Combining(L7)--(L8), for every b,c5,c,

    C_i*s-U_i(theta;b,c5)-(A_c(a_new)+T_i)/5
       >=o_i(theta;b)+epsilon_i*D.

Taking the independent layout minima proves the stronger uniform
carrier statement

    m_i(theta;c)>=o_i(theta)+epsilon_i*D
    for every c.                                  (L9)

Define u_i(theta)=min_c m_i(theta;c). The minima over carriers and
layouts commute because they are all minima of the same expression.
Equivalently, the corresponding source maxima commute. Hence u_i
is exactly the globally defined three-event unconditional margin
of shared_linear_refinement, and

    u_i(theta)>=o_i(theta)+epsilon_i*D.             (L10)

No assertion that the finite patched table is concave enters here.

## 4. The global six-direction joint function

Let I be the six selected R17/R19 directions and w_i the complete
positive inventory weights:1 for R17,15/17 for R19,13299/1360 for
R5, and the complete positive complementary-tuple coefficient for
the41st monomial direction. Define, on the whole parameter domain,

    G(theta;c)=sum_(i in I)w_i*m_i(theta;c)
                     +sum_(i not in I)w_i*u_i(theta).        (L11)

For the remaining tests d_i>=u_i; distribute these unconditional
bounds over the same pi using sum pi=1. Together with(L5), this gives

    sum_i w_i*d_i>=sum_c pi_c*G(theta;c).           (L12)

For each fixed c, G is separately concave. In(L4), the signed shallow
term is separately affine, its deep maxima have nonnegative
coefficients, and the retained positive5 source is a positive sum
of convex envelopes plus affine centering. The independent positive7
complement is convex by its original positive representation, not
merely because software writes it as a difference of two source
values. Finite layout maxima preserve convexity of the upper source
expression; negation gives concavity of m_i. Finite carrier minima
preserve concavity of u_i. The positive weighted sum in(L11) then
preserves separate concavity.

Add G to the common-carrier fixed-target expression from profile46,
with the appropriate nonnegative numerator coefficient. Keep the
full already charged H41 increase in the coefficient of S. The
other numerator terms may stay at their existing independent bounds.
For a nonnegative coefficient of S use D_c inside the carrier
minimum; for a negative coefficient use s, exactly as in profile46.
Every resulting true fixed-target expression is separately concave.
Its vertex lower bounds suffice for the1296-product-vertex extension.

## 5. Exactly what to subtract from the existing M41 vertex table

Let E={398,410,422,616,628,640}. The existing stored M41 is

    M41(v)=sum_i w_i*u_i(v),                       v in E,
    M41(v)=sum_i w_i*[o_i(v)+epsilon_i*D(v)],       v not in E.

For the six selected directions epsilon_i=0. Therefore define

    b_i(v)=u_i(v), if v in E,
    b_i(v)=o_i(v), if v not in E,

and replace exactly their six stored contributions:

    G_lower(v;c)=M41(v)-sum_(i in I)w_i*b_i(v)
                              +sum_(i in I)w_i*m_i(v;c).    (L13)

At a refined vertex(L13) equals the true G(v;c). At each other
vertex it is at most G(v;c) by(L10) for the remaining35 directions.
This proves the desired efficient evaluation interface. Only the
six new conditional margins require evaluation at all vertices.

Subtracting the old one-event value at a refined vertex would instead
add the unwanted positive quantity

    sum_(i in I)w_i*[u_i(v)-o_i(v)]

to(L13). That would count the selected directions' existing
three-event improvement twice. For example the published R17(0,0)
values at vertex398 are o=0 and
u=596939244969749806/259995953549870913375>0, so the error is already
strict in that one direction. This is a concrete failure of the
uniform-old-subtraction formula, independent of the new scan.

The formula(L13) is a vertex lower-bound table for the true function
(L11). Its entries may come from different valid lower bounds at
different vertices. The table itself is not asserted to be concave.
The all-height source/deletion proof, separate concavity of(L11),
and final fixed-target checks provide the continuous conclusion.

## 6. Same-source numerator and signed actual-mass endpoints

Keep profile46's actual mass S, common cap mixture pi, raw mass
lower bounds D_c and credited survival margin M_c^+. They satisfy

    S>=sum_c pi_c*D_c, S<=s,
    rho_actual*S>=q*S+sum_c pi_c*M_c^+, q=23/42.

Write Mquad and mg for the preceding independent quadratic and
square margins, R81 for the complete finite-below7 square contribution,
and H=AC*H16+H41. The six-direction refinement changes only the
linear numerator deficit. The four numerator comparisons can be
written

    N_k<=H_k*S-C_k(theta)-e_k*sum_c pi_c*G(theta;c),

where

    target       offset       H_k         C_k                    e_k
    J            WHOLE_CONST  H           AC*Mquad                1
    Gamma13      16           H16         Mquad                   0
    T81          0            A81         cG*mg-R81               0
    K            WHOLE_CONST  H+A81       AC*Mquad+cG*mg-R81       1.

All H41 barrier increases already charged in profile39 remain in H.
No extra barrier cost is omitted or subtracted in this refinement.
For a proposed target t, set k=t-offset>=0 and a=q*k-H_k. A sufficient
fixed-target condition, for every carrier c, is

    a*D_c+k*M_c^++C_k+e_k*G(theta;c)>=0, if a>=0,
    a*s  +k*M_c^++C_k+e_k*G(theta;c)>=0, if a<0.    (L14)

Indeed the actual target margin is at least

    a*S+sum_c pi_c*[k*M_c^++C_k+e_k*G(theta;c)].

For a>=0 use the shared lower mass bound; for a<0 use the actual
upper bound S<=s. This retains the same S throughout the numerator
and denominator calculation, rather than replacing it in only one
of them. The positive survival bound justifies the final division.

Every expression in(L14) is separately concave by section4 and the
unchanged quadratic/square interfaces. The1296 product vertices
therefore suffice for the complete continuous domain. At the
vertices replace G only by its lower bound(L13). Both endpoints
D_c and s are checked exactly, and the sign-selected endpoint is
also recorded. The other eight source branches and both finite-core
interfaces are recomputed with the resulting targets.

There are two distinct gains. First replace the selected six margins
by their true independent minima u_i at every vertex, keeping all
carriers independent of those tests. This fills inherited slack at
unrefined vertices and gives the independent-six target. Next use
m_i(theta;c) in(L13) with the actual common survival carrier; this
gives the additional common-carrier target improvement. Neither step
credits again the six margins already refined at the six vertices E.

## 7. Exact resulting targets and remaining boundary

The exact combined target is

    K=939255932492828564979463271311817433032375077
      /1841033926460824769898218824685297153712000.

The comparisons, rounded only for display, are

    comparison                          J                   K
    preceding shared survival           418.634807694316    510.760863276862
    six true independent margins        418.483168563845    510.609224146390
    six common-carrier margins          418.052447373367    510.178502955912.

The K gain decomposes exactly into

    independent gain
      =127700651802281448924012000
       /842135215398244244066236933
      =0.15163913047133654...,

    additional common-carrier gain
      =31744446554666426945307835524420041
       /73700684471639672473610621235047850
      =0.43072119047797747....

Their sum is0.582360320949314.... The same decomposition holds
for the J improvement. This is an improvement in a sufficient
comparison, not an attained extremum of actual forbidden families.

The constant-barrier stopping bound of profile44 assumed its fixed
independent numerator comparison. Conditioning six numerator tests
changes that family, so the preceding stopping bound is preserved
within its stated scope and does not constrain this new comparison.

The other three target values remain exactly

    Gamma13=85384373808161620601/581553711777853386,
    T81=2873884370396495734788444926897322493
         /30972486365132609061662761799310375,
    rho=40511716507/80223412500.

For the two complete cores, K+core_error-403 is respectively
107.1790791240706... and107.3994747568066.... Both remain positive.
Thus the strict negative-Q sufficient condition is still unproved;
these improvements do not establish unrestricted Erdős #7 or the
later-prime continuation.

The exact evaluator is
[joint_linear_carriers.py](../../frontier/source-budgets/joint_linear_carriers.py), with
[verify_joint_linear_carriers.py](../../frontier/source-budgets/verify_joint_linear_carriers.py)
reconstructing the source rows, profile46 conditional survival values,
the six new tests and the final consumers. The certificate stores
aggregated conditional linear margins, exact control values and
gain components. Original-layout computations and complete geometric
tails are recomputed; no temporary cache is a canonical input.
The original47-cost saturation helper is reused only for its already
pinned cost inventory and exact positive-source formulas.

At398 the true six independent margins match their already refined
profile39 values. At402 the independent weighted linear gain is
0.01148635031890990..., while the survival-worst carrier(0,1)
adds another0.03262623880940250... above those independent minima.
This separates the two mechanisms at a common control point.

The finite arithmetic verifies the numerical premises of the ordinary
universal argument. It is not a Lean proof. The six linear conditional
payment established here does not by itself establish a conditional
payment theorem for all five quadratic tests or for the square term.

The [logical certificate](../../certificates/source_norms/source-budgets/joint_linear_carriers.json)
has SHA256 `4015bb61396aa4369c4960c2728f20abe345d290f63f6c7b7dbdb4c43382c0c1`.
Its verifier checks139968 conditional linear values, both cost modes,
233280 target endpoint inequalities per mode, eight fallbacks and two
complete cores. Independent control arithmetic checks all conditional
values at398 and402; the complete prototype and canonical reconstruction
also agree exactly, with conditional-value digest
`774516bff04f72c26ec791f56d60190cc2db5420b9dbcbb86f8a81ecefe1a5e6`.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/source-budgets/verify_joint_linear_carriers.py --check
```

The read-only reconstruction exits zero. `--output PATH` writes a
standalone exact result, and `--write` uses the existing certificate writer.
These commands validate this ordinary numerical comparison; they do not
claim Lean or required repository-CI completion.
