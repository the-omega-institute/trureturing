# Five joint blocks admit ten mixed-square labels on ten primes

Let P={3,5,7,11,13,17,19} and V={7,11,13,17,19}. In the
nine-prime family of
[Report591](591-two-centre-star-boundary-closes-complete-height-three-tails.md),
allow all ten additional numerical labels

    3q^2 and 5q^2, q in V.

Every original residue is arbitrary and globally fixed. All pure powers,
all squarefree mixed originals, all mixed originals having an exponent
at least 3, and these ten extra labels are permitted on P. Every original
touching 23 or 29 is unrestricted. For every finite family of pairwise
distinct such numerical moduli, the complete survivor satisfies

    H(U)>=76451847872258007/36466956697600000000>1/500. (MB1)

Allowing every original touching 31 as well gives the ten-prime bound

    H(U)>=312371125918407363039/1034509982105600000000000
         >1/3400.                                    (MB1a)

Both statements transport to arbitrary ordered odd primes, preserving
the exponent vectors and which coordinates are unrestricted. In the
ten-prime statement the first seven coordinates retain the displayed
mixed-exponent restriction plus the ten added square labels; every
original touching any of the last three coordinates is unrestricted.

There is no cutoff on original or query heights. The construction combines
the five squarefree originals 15q with the ten added originals in one
actual boundary. It extends
[Report593](593-a-joint-triple-block-admits-two-mixed-square-labels.md)'s
two added labels to all ten, with a stronger nine-prime density bound.
This is an ordinary proof with an exhaustive integer certificate, not a
new Lean result or a resolution of unrestricted Erdős #7.

## 1. An actual supported submeasure with simpler boundary factors

Use Report591's single product source rho. At prime 3 the two retained
first-root masses are t and 1-t, with 1/3<=t<=2/3. At p>=5 each of
the p-1 retained first roots has mass 1/(p-1), and a height-e cylinder
has mass at most 1/[(p-2)p^(e-1)] for e>=2. Each coordinate is supported
on the complete actual pure-power survivor. The density bound is

    rho<=D H_P, D=3458/405.

Normalize the auxiliary central 15 deletion to cell (0,0) in the
two-by-four grid of retained 3/5 roots. For each q in V, take the actual
joint block with labels

    3q, 5q, 15q, 3q^2, 5q^2.

Every source-active original keeps its actual residue. Missing or
source-null slots can be filled with fixed auxiliary cylinders in the
retained roots; these additional deletions only shrink the eventual
survivor. No query selects a new source or original phase.

Write r_q=1/(q-1) and a_q=1/[q(q-2)]. Conditional on a central cell
c=(i,j), let chi_q be the indicator of avoiding this actual q-block,
and f_q(c)=integral chi_q d rho_q. The 3q and 5q originals are enabled
on a row R_q and a column C_q, the 15q original on a point K_q, and
the two square originals on a row R'_q and a column C'_q. Their q-parts
have masses at most r_q,r_q,r_q,a_q,a_q, respectively. The union bound
on this one actual coordinate law gives

    f_q(i,j)>=b_q(i,j)
      =1-r_q[1_(i=R_q)+1_(j=C_q)+1_((i,j)=K_q)]
         -a_q[1_(i=R'_q)+1_(j=C'_q)].               (MB2)

Overlapping cylinders and their actual parent/child equalities are allowed.
For every cell, b_q>=1-3r_q-2a_q>=31/70>0, and b_q<=1.
Consequently theta_q(c)=b_q(c)/f_q(c) is well-defined and lies in [0,1].
Define the fixed submeasures

    d zeta=1_(c!=(0,0)) product_(q in V)[chi_q theta_q(c)] d rho,
    eta=1_(U_P) zeta.                               (MB3)

Here U_P is the complete actual P-survivor. The source is chosen once
for the original family, before any future query. Given c, the original
product coordinates are independent, so integrating every local thinned
block gives exactly

    integral chi_q theta_q(c) d rho_q=b_q(c).

Thus zeta has the advertised product boundary and eta is supported on
the entire actual survivor, with eta<=zeta<=rho<=D H_P. It need not
preserve the old first-root marginal. This thinning construction avoids
assuming that a smaller boundary survival vector always improves a
mass-minus-query estimate: no such monotonicity is used.

## 2. Original losses and all future queries use the same boundary

For a query or remaining original with outside-prime support T subset V,
drop both chi_q and theta_q for q in T. They are bounded by one, so
this is a valid upper estimate on the same measure. Apply the original
rho_q cylinder cap at those coordinates. For q outside T, integrate the
entire local factor to b_q. The central table is therefore

    g_T(i,j)=1_((i,j)!=(0,0)) product_(q notin T)b_q(i,j). (MB4)

Put t_0=t,t_1=1-t and h_i=(1/4)sum_j g_T(i,j). The six screens are

    A_T=sum_i t_i h_i,
    B_T=max_j sum_i t_i g_T(i,j),
    C_T=max_i t_i h_i,            D_T=(1/3)max_i h_i,
    E_T=max_(i,j)t_i g_T(i,j),   F_T=(1/3)max_(i,j)g_T(i,j). (MB5)

These keep first-layer and deeper ternary queries separate. The complete
height sums and all 192 support/mode coefficients of Report591 apply
without truncation. Let L be the remaining original-loss envelope, Qbar
the complete nonunit-query envelope, and a=A_empty. Then

    s=eta(1)>=s_0=a-L,
    R_P(eta)<=Qbar,
    Gs-R_P(eta)>=G(a-L)-Qbar, G=566/49.              (MB6)

The five squarefree labels 15q now belong to the retained block. Remove
their old loss charges exactly once. In the six-mode by 32-support
coefficient array this means

    L[mode=4, mask={q}] -= 1/[4(q-1)],
    (G L+Qbar)[128+2^index(q)] -= G/[4(q-1)].        (MB7)

No query coefficient is removed: all numerical labels, including 15q,
3q^2 and 5q^2, remain available as future queries at every height.
The new square originals were absent from the old squarefree/height-three
loss inventory and are now handled by MB3, so they receive no second
loss charge. Every adjusted coefficient is nonnegative.

## 3. Convex decomposition reduces each local boundary to 64 templates

Fix q and its point K_q. Put d_q=r_q+a_q and beta_q=r_q/d_q.
Choose a row I equal to R_q or R'_q with probabilities beta_q and
1-beta_q, and independently choose a column J equal to C_q or C'_q
with the same probabilities. Then MB2 is the exact convex combination

    b_q(i,j)=E[1-d_q(1_(i=I)+1_(j=J))-r_q1_((i,j)=K_q)]. (MB8)

There are only 2*4*8=64 aligned templates on the right. They are a
conservative comparison family; the proof does not claim that every
template or endpoint geometry is jointly attainable by actual originals.
Nor does it rephase an original in the actual measure MB3.

Fix all other q-vectors and t. The block mass is linear in the remaining
q-vector. Each of the six screens is linear or a maximum of finitely many
linear forms, and its subtracted coefficient is nonnegative. The gate
in MB6 is therefore concave in each q-vector separately. By MB8 and
Jensen's inequality, one aligned template has gate no larger than the
convex combination. Replacing the five q-vectors successively proves
that their 64^5 templates suffice for a uniform lower bound.
The gate is also concave in t, so its two endpoints suffice.

Permuting the three nonzero columns preserves the central deletion,
all coordinate masses and all screens. Across the ten column fields
(J_q,K_column,q), Burnside's count of orbits is

    (4^10+3*2^10+2)/6=175275.

The generator assigns each new nonzero column its first unused name.
This enumerates each orbit once, including words using fewer than three
nonzero names. The ten independent row bits and the two t endpoints
leave exactly

    175275*2^10*2=358963200                            (MB9)

cases. No permutation of the differently weighted primes is used.

## 4. An outward-rounded complete certificate

Use factor scale F=2^20 and coefficient scale C=10^9. Enclose every
rational template cell between floor(F b)/F and ceil(F b)/F. During
each coordinate multiplication round the lower product down and the
upper product up. Keep cell (0,0) exactly zero. Every product is thereby
enclosed in [0,1] without a floating-point comparison.

At t=1/3 or 2/3 the six screens have common denominator 12F. Use
the lower table for the positive mass term, the upper tables for every
subtracted screen, round G down and every nonnegative coefficient up.
The resulting signed integer expression divided by 12FC is a lower
bound for the exact gate. The complete scan gives

    delta=2831549921194741/12582912000000000>0.       (MB10)

For clarity about approximation, five local-factor roundings and the
four subsequent product roundings give a uniform cell error at most
9/F on each side. Each screen is Lipschitz with constant at most one
for the cell sup norm. This bounds the difference between the rounded
and exact envelopes; positivity itself follows directly from the
outward directions at every operation.

Encode an aligned template by

    code=((row*4+column)*2+point_row)*4+point_column.

The minimizing first-moment witness has codes (9,18,27,27,27), in
the order q=7,11,13,17,19, and t=2/3. A separate exact Fraction
sum over all 127 nonempty core supports gives

    s_0=56739218190535207/285614821411920000,
    Qbar=157630977697265911/76163952376512000,
    Gs_0-Qbar=12598821375881264063/55980504996736320000.

The exact value exceeds MB10. The theorem uses the minimum from the
complete scan, not the value of this single witness. Report591's raw
23/29 continuation on MB3 gives

    H(U)>=49 delta/(616D),

which is exactly MB1.

## 5. A joint second-moment certificate on the same head

For each finite core period Q resolving all original head exponents,
let Gamma_Q be the maximum second moment of a complete query layout,
including the unit query. Reuse
[Report592, Section2](592-joint-second-moment-extends-cubic-tails-to-ten-primes.md)'s
ordered-pair bound on the same eta:

    Gamma_Q(eta)<=s+Wbar,
    Wbar=sum_(f>1, P-supported) product_(p|f)(2v_p(f)+1) qhat_f,
    q_f(eta)<=qhat_f from MB5.                       (MB11)

Here qhat_f is the MB5 upper bound before the complete height series
is summed. The coordinate weights for p>=5 are

    omega_p=3/(p-1)+[2p/(p-1)^2+3/(p-1)]/(p-2).

The ternary first-layer screens C_T,E_T receive multiplier 3, and the
deep screens D_T,F_T receive multiplier 6. These are the exact complete
weighted geometric series. No original or query height is discarded.

In addition to the first-moment gate, scan the two profiles

    s_0=a-L,              179s_0-Wbar.

Their subtracted screen coefficients are nonnegative, so the separate
concavity, 64-template reduction and column symmetry from Section3 apply
to both. The same full scan gives the uniform lower bounds

    s_0>=a_*=2495445733291199/12582912000000000>1/6,
    179s_0-Wbar>=m_*=112240173285157/62914560000000>0. (MB12)

The mass profile uses coefficient scale 10^9; the moment profile uses
10^8. Both use the same 2^20 factor intervals. The three signed-integer
accumulation bounds, in first-moment, mass, moment order, are

    318313534008066048,
     21488369619959808,
    500119239043055616,

all below 2^63-1. The mass minimum has codes (9,18,27,27,18), t=2/3;
its exact unrounded value is

    226575078019560373/1142459285647680000.

The moment minimum has codes (9,18,27,27,27), t=2/3; its exact
unrounded value is

    93938888752450539169/52644523882645094400.

These are independent witness reconstructions, not substitutes for the
358963200 cases certified for each profile. The two inequalities MB12
hold simultaneously for every one actual eta. Their different minimizing
comparison templates do not select different probability laws.

Normalize only this head: mu=eta/s. By MB11--MB12,

    Gamma_Q(mu)<=1+Wbar/s<=180-m_*/s<180.            (MB13)

This head is constructed before either the nine-prime or ten-prime
continuation. The two conclusions are alternative continuations of MB3;
neither spends the survivor budget of the other.

## 6. Retaining the common moment margin through 23,29,31

Apply Report592's physical-law capped-deletion recurrence at new primes
23,29,31 with controls delta=2/5,9/20,1/2. Every new original is assigned
to its largest new prime, retaining its full old numerical cofactor,
phase and height. The conditional kernels preserve the preceding joint
law; all forbidden sets are charged on this same law.

For seed joint moment g and survivor lower bound v, the update is

    v'=v-g/[4delta(1-delta)(q-1)^2],
    g'=g[1+(3q-1)/((1-delta)(q-1)^2)].               (MB14)

Starting with g=180 and v=1 gives

| New prime | Survivor lower bound | Joint moment upper bound |
| ---: | ---: | ---: |
|23|593/968|26880/121|
|29|72983/223608|2482560/9317|
|31|33907/1118040|14950528/46585|

The density multipliers have product 200/33. For these fixed controls,
the final survivor expression for any seed B is exactly 1-c B, where

    c=1084133/201247200,
    1-180c=33907/1118040>0.                          (MB15)

Use the stronger same-law seed MB13, rather than discarding its margin
at normalization. Multiplying the final survivor bound by the original
head mass s gives

    s[1-c Gamma_Q(mu)]
      >=(1-180c)s+c m_*
      >=(1-180c)a_*+c m_*
      =1978350464149913299247/126613790392320000000000.
                                                               (MB16)

Both coefficients used in the last lower estimate are positive. The
head density is at most D/s, followed by the factor 200/33. Hence

    H(U)>=33/(200D)[(1-180c)a_*+c m_*],              (MB17)

which equals MB1a. This retains a correlation already certified on one
source, without choosing separately optimal sources for mass and moment.

For comparison, the first-moment witness still has

    169s_0-Wbar=-53214191081719771867/263222619413225472000<0.

This prevents inheriting the particular seed-170 envelope of Report592.
It does not prevent continuation: the fixed controls allow every seed
below 1/c=201247200/1084133, which is greater than 180. MB12 provides
the required replacement bound. No claim about every possible survivor
law follows from a negative value of the old sufficient envelope.

## 7. Scope and retained arithmetic

The [producer](../../frontier/cover-geometry/multi_joint_square_profile.py),
[integer engine](../../frontier/cover-geometry/multi_joint_square_scan.cpp),
and [data](../../frontier/cover-geometry/multi_joint_square_profile.json)
generate every template and coefficient from the definitions, record
the full orbit count, and reconstruct extremal witnesses independently
using exact fractions. The engine checks its signed-64-bit accumulation
bound before scanning. Heights are accounted for by the complete
geometric series, rather than sampled finite exponent boxes.
All 41 producer checks pass. An independent 127-support reconstruction
also agrees with each of the three extremal interval and rational values.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/multi_joint_square_profile.py

The nine-prime statement also holds on any nine ordered odd primes:
replace each prime by the corresponding ordered prime and retain the
same exponent vectors. The digit-injection averaging in
[Report592, Section5](592-joint-second-moment-extends-cubic-tails-to-ten-primes.md)
preserves the density lower bound and original numerical distinctness.
The same transport applies to the ten-prime statement, with its full
last-three-coordinate inventory.

The result still excludes arbitrary remaining core mixed squares such
as 9q and 25q, and does not give unrestricted additional prime support.
The substantive boundary change is to keep all five overlapping
squarefree/square blocks on one actual source, while retaining every
future numerical query and its complete height series.
