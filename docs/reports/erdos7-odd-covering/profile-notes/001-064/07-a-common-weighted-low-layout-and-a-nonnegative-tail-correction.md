[Index](../../marked_head_profile.md) · [Previous](06-a-common-matrix-bound-for-all-actual-rectangles.md) · [Next](08-all-integer-schedules-through23-for-the-fixed-scalar-feature-map.md)

<a id="a-common-weighted-low-layout-and-a-nonnegative-tail-correction"></a>
### A common weighted low layout and a nonnegative tail correction

The independent cylinder caps in (SH8) can lose the joint geometry.
There is a stronger finite observation that keeps a single complete
weighted low layout in each auxiliary outcome. Let Z_3,Z_5,Z_7 be
independent nonnegative integers with

    Pr(Z_p>=k)=p^-k,   Pr(Z_p=k)=(p-1)/p^(k+1).

For d dividing315 set

    w_d(Z)=product_(p:v_p(d)=h_p)(1+Z_p),
    F_mu(Z)=max_(a_d mod d)
      E_mu [sum_(d dividing315)w_d(Z)1_(x=a_d mod d)]^2.

Then every full test at arbitrary finite 3/5/7 heights satisfies

    E_lambda L^2 <= E_Z F_mu(Z).                         (SH10)

To see this, first center the additional test prefixes as above,
keeping every low residue fixed. For fixed matching depths Z, the
number of active original labels projecting to d is
product_(p saturated in d)(1+min(Z_p,n_p)), where n_p is the physical
extra height. Average their low cylinder indicators. This average
belongs to the convex hull of the cylinder indicators for that d,
with coefficients independent of x. The squared norm of the sum
is convex on the product of these finite convex hulls. Applying
Jensen, one cofactor at a time, bounds it by a vertex value: one
actual low cylinder for each d, chosen jointly for the entire cost.
Finally increasing min(Z_p,n_p) to Z_p adds nonnegative weights.
This proves (SH10), and also shows why choosing a different residue
at each point x is not allowed. The vertex choice may depend on Z;
the bound does not assert a single optimizer for all Z. The convex
hull step directly reuses Mathlib's `ConvexOn.le_sup_of_mem_convexHull`.

For the marked heads of (SH6) the same globally unused seven digit
evaluates F_mu(Z) by only two weighted old45 layouts. In each such
layout give cofactor c dividing45 weight

    v_c(Z)=(1+Z_3)^(1_(9 divides c))
             (1+Z_5)^(1_(5 divides c)),
    A_Z(x)=sum_(c dividing45)v_c(Z)1_(x=a_c mod c),

and define B_Z with independently chosen old45 residues. For low
weights u_x common to the surviving seven digits, normalized by
R=sum_x(6-b(x))u_x, the exact identity is

    R F_mu(Z)=max_(A_Z,B_Z) sum_x u_x [
      (5-b(x))A_Z(x)^2
        +(A_Z(x)+(1+Z_7)B_Z(x))^2].                     (SH11)

In particular F_mu(0)=G is the exact unweighted low square.
All high original labels are still accounted for by their matching
depths; this expression does not identify them as the same modulus.

An exact polynomial upper bound controls the unbounded auxiliary
depths without discarding their contribution. Write

    P_mu(Z)=sum_(d,e dividing315)w_d(Z)w_e(Z)m_lcm(d,e),
    c0=P_mu(0)-G>=0.

For every fixed complete low layout, each ordered pair satisfies
mu(C_d intersect C_e)<=m_lcm(d,e). Thus its weighted deficit from
P_mu(Z) is a sum of nonnegative terms. Every coefficient w_d w_e
is at least one, so this deficit is at least the same layout's
unweighted deficit, hence at least c0. Minimizing over the layouts
proves P_mu(Z)-F_mu(Z)>=c0 for every Z. Also (SH8) gives
E_Z P_mu(Z)=P_mu(0)+Delta_square, using only the geometric first
and second moments of each 1+Z_p.

Consequently for any finite set B of auxiliary depth triples,

    E_lambda L^2 <= G+Delta_square
      -sum_(z in B) Pr(Z=z)[P_mu(z)-F_mu(z)-c0].         (SH12)

Every correction is nonnegative. The omitted depths retain the
entire baseline saving c0, so a small evaluated set already gives
a valid improvement whenever one of its corrections is positive.
Larger sets preserve the previous bound monotonically. The same
formula remains valid if F_mu(z) is replaced by a certified upper
bound B_z and its correction by max(0,P_mu(z)-B_z-c0).
Divide the resulting square-minus-one by the appropriate same-law
denominator in (SH5). This finite calculation controls arbitrary
physical heights; it does not move the actual deletion event or
reuse a uniform-density denominator for nonuniform weights.

The corrected upper bound has a convex form useful for joint weight
optimization. Put beta=Pr(Z in B) and

    eta_out(d)=E_Z[1_(Z not in B)
      sum_(lcm(e,f)=d)(w_e(Z)w_f(Z)-1)]>=0.

Rearranging (SH12) gives the identical expression

    U_B(mu)=(1-beta)G(mu)+sum_d eta_out(d)m_d(mu)
                +sum_(z in B)Pr(Z=z)F_mu(z).            (SH13)

Every coefficient is nonnegative and independent of mu. Each of G,
m_d and F_mu(z) is the maximum of finitely many linear functions of
the low probability. Thus U_B has a finite epigraph representation,
and `1+(U_B(mu)-1)/(1-R_high(mu))` admits the same linear fractional
transformation as (SH9). The coefficients eta_out are exact: subtract
the finite-box terms from the infinite geometric coefficients in
(SH8). Nonnegativity follows from their displayed expectation, rather
than from a numerical tolerance. All expectations are finite since
each Z_p has a finite second moment.

<a id="an-exact-obstruction-to-optimizing-the-independent-cylinder-formula"></a>
### An exact obstruction to optimizing the independent cylinder formula

There is an actual low family for which changing fibre weights alone
cannot make the particular formula (SH9) improve 3849/106. This is
a limitation of that upper-bound formula, not a lower bound for
the actual worst test moment or for arbitrary supported probabilities.

Take the eleven original classes (modulus,residue)

    (3,0),(9,4),(5,0),(15,11),(45,1),(7,0),
    (21,1),(35,9),(63,10),(105,74),(315,82).

The five old45 classes leave

    S=(2,7,8,14,16,17,19,23,28,29,32,34,37,38,43,44).

The five mixed-seven classes delete digits 1,2,3,4,5 respectively,
giving the actual deletion vector and fibre sizes

    b=(0,1,0,2,1,0,3,0,2,2,0,2,3,0,1,2),  r=6-b.

There are 77 survivors modulo315, with digit6 surviving over every
point of S. Consider every nonnegative weight vector w with
sum_x r_x w_x=1, assigning probability w_x to each surviving seven
digit over x. This allows unequal fibre totals but requires equal
point weights within each fibre.

Let G(w)=F_mu(0) be the exact low square from (SH11), and let
R(w)=R_high and Delta(w)=Delta_square from (SH8). On the nonempty
domain R(w)<1 the independent-cylinder formula satisfies

    1+[G(w)-1+Delta(w)]/[1-R(w)]
      >=101816531/2603049 >3849/106.                     (SH14)

The excess is exactly 773416685/275923194. Uniform point weights
w_x=1/77 have R=1825/3696<1, so this is not a vacuous assertion.
It does not exclude (SH12), which retains joint layouts, nor
probabilities with unequal weights inside a seven-digit fibre.

Here is a finite rational proof of the universal quantifier over w.
Use the nonnegative linear fractional variables

    v_x=w_x/(1-R),  t=1/(1-R),
    zG=G/(1-R),     z_d=m_d/(1-R).

Writing eta_d=sum_(lcm(e,f)=d)gamma_ef, these variables satisfy

    sum_x r_x v_x-t=0,
    t-sum_d gamma_d z_d=1,
    z_1-t=0.

Every actual low cylinder gives its mass constraint with upper
variable z_d. Every actual pair of old45 layouts gives its square
constraint with upper variable zG. Thus each chosen constraint
has the form A_i x<=0, with x=(v,t,zG,(z_d)). The objective in
(SH14) is 1+c x, where c x=zG-t+sum_d eta_d z_d.

The adjacent certificate specifies 21 actual cylinder constraints
and five actual pairs of old45 residue assignments, together with
rational multipliers y_i<=0 and three free equality multipliers z.
For the equality matrix E and right side b0=(0,1,0), it verifies

    A^T y+E^T z<=c  in all 30 coordinates,
    1+z dot b0=101816531/2603049.

Hence c x>=y^T A x+z^T E x>=z dot b0, proving (SH14).
Only valid explicit layout constraints are needed for this lower
bound; no exhaustive maximization or LP solver is part of its replay.

`verify_fiber_uniform_saturated_envelope_obstruction.py` uses the
adjacent `fiber_uniform_saturated_envelope_obstruction_certificate.json`.
It reconstructs the original family and all 315 residues, the actual
deletion vector, all saturated coefficients, all 26 constraints,
and the rational dual inequality. Run it with `python3 -I -O`.
The standalone certificate proves (SH14); it makes no claim about
attainment, the optimal joint-layout formula, or unrestricted #7.

<a id="grouping-deletions-by-their-single-extra-prime-coordinate"></a>
### Grouping deletions by their single extra prime coordinate

The union bound for the survival denominator can also preserve
joint geometry. For p in {3,5,7}, choose E_p contained in D_{p}
with |E_p|<=p-1, and let A_p range over complete low test loads
with exactly one cylinder for each d in E_p. Put alpha_p=1/(p-1).
Define

    U_E(mu)=max_(A_3,A_5,A_7)
       E_mu[1-product_p(1-alpha_p A_p)],
    rho_d=gamma_d-sum_(p:d in E_p)alpha_p>=0,
    R_E(mu)=sum_d rho_d m_d(mu)+U_E(mu).

For the actual higher deletion event F from (SH5),

    lambda(F)>=1-R_E(mu).                               (SH15)

In particular this bound applies to a changed low probability;
it uses no ambient uniform-density assumption.

To prove it, group precisely the original labels (J,e,d) with
J={p} and d in E_p. Conditional on the low point x, the three
groups' hit events depend on disjoint additional prime coordinates
and are independent. Writing their probabilities as u_p(x), the
probability that at least one group hits equals
1-product_p(1-u_p(x)). Within a group the union
bound gives

    u_p(x)<=sum_(e>=1)p^-e A_(p,e)(x),

where each A_(p,e) is one complete E_p layout. Complete absent
labels arbitrarily. Dividing the coefficients by alpha_p writes
this upper bound as alpha_p times a convex combination of complete
layouts. At finite heights the remaining coefficient can likewise
be filled by any layout, only increasing the bound. Its value is
between zero and alpha_p |E_p|<=1.

The function 1-product_p(1-u_p) is nondecreasing in each coordinate
on this cube. After substituting the upper bounds, it is affine in
each of the three layout averages with the other two fixed.
Successively maximizing over their convex hulls therefore gives
the finite vertex maximum U_E. This operation chooses complete
layouts independent of x. The remaining original labels are
bounded by their separate cylinder masses. Removing exactly the
chosen singleton-J contributions from gamma_d gives rho_d>=0
by the subset expansion in (SH2), and proves (SH15).

Every integrand defining U_E is nonnegative and fixed before mu
is chosen. Thus R_E is a nonnegative sum of maxima of linear
functions of mu. It is no larger than the preceding R_high:
the pointwise union polynomial is at most sum_p alpha_p A_p,
whose separate maxima sum to the removed cylinder terms.
Consequently any square bound U_B from (SH13) gives, when R_E<1,

    Gamma_nu<=1+(U_B(mu)-1)/(1-R_E(mu)),                 (SH16)

on the same actual conditioned law. This is another finite convex
epigraph and linear fractional optimization, with a stronger
denominator as well as the joint numerator.

For marked heads there is a compact evaluator with

    E_3 contained in {9,45},
    E_5 contained in {5,15,45},
    E_7={7c:c dividing45}.

These choices meet the required size bounds. Write a=A_3/2 and
b=A_5/4; both are functions only of the old45 point. For normalized
per-digit weights w_x and fibre sizes r_x, the globally surviving
seven digit gives

    U_E=max_(A_3,A_5) [sum_x r_x w_x(a_x+b_x-a_x b_x)
      +(1/6)sum_(c dividing45) max_(t mod c)
          sum_(x=t mod c)w_x(1-a_x)(1-b_x)].             (SH17)

The last factors are nonnegative. For every cofactor c, assigning
its seven part to the globally surviving digit dominates any
other digit pointwise for that weighted mass. The six choices
then maximize independently. This centering concerns the low
test calculation defining U_E; it does not center the original
higher forbidden classes. Choosing only E_3={9}, E_5={5} already
retains the full seven group. Using both larger sets preserves
the same proof and cannot worsen the bound: the increase of the
union polynomial is at most the sum of the added alpha-weighted
loads, whose cylinder maxima were removed from the separate sum.

<a id="a-certified-common-law-improvement-at-unrestricted-357-heights"></a>
### A certified common-law improvement at unrestricted 3/5/7 heights

Let Omega be the 77-point survivor set of the eleven classes in
(SH14). For every finite distinct odd family using only 3,5,7,
whose complete low315 survivors contain Omega, all higher original
exponents and residues may be arbitrary. There is one probability
nu supported on its actual full survivors with

    Gamma(nu)<=2512626164927510733601/70505216618162484375
              <35.637451<3849/106.                      (SH18)

Here Gamma is the supremum of the second moment over complete
tests with one class for each original-period divisor, including
one. Padding low coordinates to 315 and completing test labels
only adds nonnegative contributions. The low geometry remains
a hypothesis; (SH18) is not a new bound for every three-prime
family or for unrestricted odd prime support.

Give each surviving seven digit over the ordered old45 points in
(SH14) the following integer weight, divided by 99999992:

    (1120062,1267867,1115811,1440615,
     1305700,1120062,1802478,1115811,
     1668294,1440615,1120062,1449636,
     1818198,1115811,1253063,1440615).

The r-weighted sum is exactly 99999992. Extend this low law
uniformly in the additional prime coordinates and condition
on all actual higher forbidden classes. Use (SH17) with
E_3={9,45}, E_5={5,15,45}, and the complete six-label E_7.
Exact maximization gives

    U_E=1777961435/4799999616,
    sum_d rho_d m_d=74007725/799999936,
    lambda(F)>=2577991831/4799999616>0.

For the same low law, take the auxiliary box
0<=Z_3<=8, 0<=Z_5<=5, 0<=Z_7<=4. The common-layout formula
(SH12), independently evaluated in the positive form (SH13), gives

    E_lambda L^2<=1286697806403687124613/65637332249013000000.

Substitution in (SH16) proves (SH18). Its exact saving over
3849/106 is 5036205280991264597669/7473552961525223343750.
No original high class is centered, and the numerator and
denominator belong to the same lifted and conditioned probability.

`verify_saturated_joint_head.py` replays the adjacent
`saturated_joint_head_certificate.json` using NumPy and exact
integer arithmetic. It reconstructs the actual315 survivors
and all 4480 active old45 layouts directly from the original
classes. Empty old cylinders are dominated by nonempty ones
for the nondecreasing costs used here. The 270 depth maxima
therefore examine all 5,419,008,000 ordered square-layout pairs;
the grouped deletion calculation examines all 35,840 pairs
of the two low layout families. Every maximizing value is
also checked with Python integers. The largest certified
integer range is 5,074,124,123,068, below 2^63. Geometric tails,
conditioning and the strict comparison use exact fractions.

Run `python3 -I -O docs/reports/erdos7-odd-covering/verify_saturated_joint_head.py`.
This requires no solver, saved layout cache, or scratch experiment
files. An independent standard-library calculation also checks
the complete grouped denominator. The all-height theorem uses
the ordinary arguments (SH10)--(SH17); this is not an end-to-end
Lean result or an optimality claim for the selected weights.

<a id="convex-costs-on-the-same-arbitrary-height-probability"></a>
### Convex costs on the same arbitrary-height probability

The common-layout argument also supplies the observations needed by
subsequent prime steps. Keep the actual low law mu, its independent
higher-digit lift lambda, and its actual conditioned law nu from (SH18).
For a nonnegative increasing convex function h, define

    F_h(z)=max_(one low cylinder per d)
      E_mu h(sum_(d dividing315)w_d(z)1_(x=a_d mod d)).

The prefix centering and convex-hull argument of (SH10) give

    E_lambda h(L)<=E_Z F_h(Z).                          (SH19)

Center only the test prefixes before conditioning. Conditional on the
low point and other prime coordinates, their nested coupling maximizes
each convex cost, as in the earlier survivor-weighted comparison (C1).
For fixed depths, Jensen then replaces each cofactor's average indicator
by one cylinder, with mixing coefficients independent of the low point.
These two steps hold for h as well as for the square. The auxiliary
expectation may be infinite for unrestricted h; the hinge bounds below
are finite. Under fibre-constant weights w_x with sum_x r_x w_x=1,
the common surviving seven digit gives the exact formula

    F_h(z)=max_(A,B) sum_x w_x[
      (r_x-1)h(A_x)+h(A_x+(1+z_7)B_x)].

Let F_2 denote the square cost, and let U_B and beta be the square
upper bound and depth-box mass in (SH13). Put

    V_out=U_B-sum_(z in B)Pr(Z=z)F_2(z)-(1-beta)>=0.

For any integer threshold t>=1,

    H_lambda(t)<=sum_(z in B)Pr(Z=z)F_((.-t)_+)(z)
                      +t V_out/(4t^2-1),
    H_nu(t)<=H_lambda(t)/q_*.                           (SH20)

Indeed every complete load is an integer k>=1 and
(k-t)_+<=t(k^2-1)/(4t^2-1). On the positive branch the cleared
majorant difference is (k-2t)(t(k-2t)+1)>=0, by integrality;
equality at k=2t shows the coefficient is exact. Apply this inequality
outside the box, then use its complete square-minus-one budget V_out.
The box complement is never discarded. Conditioning only divides the
nonnegative hinge integral by its same-law lower denominator q_*.

There is an exact elimination of the two modulus45 choices. It makes
these convex observations substantially cheaper without approximating
the maximizing layout. Fix base old45 layouts A0,B0 omitting45, and put
v=(1+z_3)(1+z_5), u=1+z_7, X=A0+uB0. Their baseline cost is

    C=sum_x w_x[(r_x-1)h(A0_x)+h(X_x)].

For each old45 point i, define the increments

    a_i=w_i[(r_i-1)(h(A0_i+v)-h(A0_i))+h(X_i+v)-h(X_i)],
    b_i=w_i[h(X_i+uv)-h(X_i)],
    j_i=w_i[(r_i-1)(h(A0_i+v)-h(A0_i))
                      +h(X_i+(1+u)v)-h(X_i)].

The exact best cost after restoring both singleton45 labels is

    C+max(max_i a_i+max_j b_j, max_i j_i).               (SH21)

Different-point choices give a_i+b_j; coincident choices give j_i.
Convexity implies j_i>=a_i+b_i. If the independent maxima use
different points they are attained; if they coincide their value is
dominated by the attainable same-point choice. This proves both
inequalities in (SH21). Nonempty45 cylinders are precisely singleton
points, and empty choices are dominated by nonempty choices for these
costs. On the (SH18) carrier there are only 280 base layouts, compared
with 4480 after restoring45, so each convex query uses 78,400 base
pairs instead of 20,070,400 full pairs. The proof also applies to other
finite carriers with the stated singleton structure.

<a id="a-direct-threshold-two-correction-and-simultaneous-bounds"></a>
### A direct threshold-two correction and simultaneous bounds

Threshold two has an additional exact linear decomposition. For a
complete old45 layout A with weights v_c(z_3,z_5) from (SH11), put

    m_A(z)=max_A sum_x r_x w_x A_x,
    m_B(z)=max_B sum_x w_x B_x,
    bonus(A)=sum_x(r_x-1)w_x 1_(A_x=1),
    g(z_3,z_5)=max_A[bonus(A)-(m_A(z)-sum_x r_x w_x A_x)].

All cofactor weights are positive, so A_x=1 means that none of its
five nonunit old45 cylinders hits x; this observation is independent
of the depths. Since A>=1 and A+(1+z_7)B>=2, direct expansion gives

    F_((.-2)_+)(z)=m_A(z)+(1+z_7)m_B(z)-2+g(z_3,z_5).
                                                               (SH22)

The mean deficit of each layout is a sum of nonnegative individual
cylinder deficits multiplied by v_c. Each v_c is nondecreasing in
z_3,z_5. Thus g is nonincreasing in each coordinate. Also g>=0:
choose each cylinder to attain its independent mean maximum, leaving
zero deficit and a nonnegative bonus. The expected linear part in
(SH22), before subtracting two, is exactly

    M_lambda=sum_(d dividing315)(1+gamma_d)m_d.

For a finite box 0<=z_3<=n_3, 0<=z_5<=n_5, write
pi_p(k)=(p-1)/p^(k+1) and t_p=p^(-(n_p+1)). Monotonicity yields

    E g <= sum_(inside)pi_3(z_3)pi_5(z_5)g(z_3,z_5)
      +t_3 sum_(z_5<=n_5)pi_5(z_5)g(n_3+1,z_5)
      +t_5 sum_(z_3<=n_3)pi_3(z_3)g(z_3,n_5+1)
      +t_3 t_5 g(n_3+1,n_5+1).                         (SH23)

The three complement regions are disjoint and exhaust both infinite
tails. This gives H_nu(2)<=(M_lambda-2+E g upper)/q_* without
charging the omitted higher depths to a square bound.

On exactly the probability and low geometry in (SH18), use its
270-point box in (SH20), and n_3=12,n_5=8 in (SH23). The same
probability nu simultaneously satisfies

    E_nu L<=19618622895502373704/3964266656997890625
            <4.948866,
    E_nu L^2<=2512626164927510733601/70505216618162484375,
    E_nu(L-t)_+<=H_t,                                   (SH24)

where the displayed decimal bounds are rounded upward:

| t | H_t upper |
|---|---|
| 2 | 2.948865602 |
| 3 | 2.058624315 |
| 4 | 1.420795591 |
| 5 | 1.089549227 |
| 6 | 0.808227449 |
| 8 | 0.504434647 |
| 10 | 0.338457518 |
| 12 | 0.217859420 |

Every entry has an exact fraction in the adjacent certificate.
In particular H_2=11690089581506592454/3964266656997890625 and
H_6=171123706666048609715948/211727165504341940578125.
The mean follows from L<=2+(L-2)_+. Between listed thresholds,
the chord of the two hinge upper bounds is valid by convexity in t;
below two, H_2+2-t is valid. These are bounds for every complete
test on one fixed law. Taking a different law for each cost is not
part of the construction. All original3/5/7 heights remain arbitrary;
the specified low geometry remains a hypothesis.

<a id="a-same-law-two-prime-consumer"></a>
### A same-law two-prime consumer

The pure-power charge bound (AP2), its convex comparison (AP3)--(AP4),
square bound (AP5) and final conditioning (AP6) consume (SH24) directly. Let G be
its square bound and use thresholds T_11=4, T_13=5. The first charge
is at most H_4/6. Its comparison multiplier N has

    E N=7/6, Pr(N=1)=28/33, Pr(N=2)=50/363.

At the next prime, use H_5 at N=1, the chord
H(5/2)<=(H_2+H_3)/2 at N=2, and H(t)<=2+H_2-t at N>=3.
The complete remaining multiplier tail is handled by E N. Thus

    b_11<=H_4/6,
    b_13<=[131 H_2/726+50 H_3/363+28 H_5/33+2/121]/7,
    J_13<=(1403/630)G,
    q_13>=1-b_11-b_13,
    Gamma_13<=1+(J_13-1)/q_13.                          (SH25)

Here the charges are those of the physical probability chain in
(AP2), and q_13 is measured relative to its normalized starting
law nu. This is not an assertion that the conditional low marginal
remains mu. The old period Q is the full3/5/7 part of the entire
original family's period, including exponents occurring in later-prime
moduli. Uniformly pad the (SH18) lift to these physical heights before
conditioning. Likewise extend11/13 to their full physical heights.
The distortion parameters are delta_11=1/3, c_11=5/3<=11 and
delta_13=4/11, c_13=12/7<=13, as required by (AP5).
With the exact (SH24) inputs,

    q_13>=1769882874608640689865554/3455108140373052546796875,
    Gamma_13<=3815365447008599276017720573/24778360244520969658117756
               <153.979740.

This allows arbitrary finite11/13 heights and residues in addition
to the arbitrary3/5/7 heights already present in (SH18). It supplies
a supported probability for further prime steps under that same low
geometry, not a general tail continuation or a solution of #7.

`verify_saturated_convex_profile.py` reconstructs its adjacent
`saturated_convex_profile_certificate.json`. The (SH18) certificate
is a hash-bound prerequisite checked by `verify_saturated_joint_head.py`.
The new replay checks all2160 hinge observations, compares the reduced
square evaluator with every one of the270 independently enumerated
square maxima, and checks the direct threshold-two identity against
all270 hinge observations. It reconstructs140 two-coordinate correction
values, including the23 boundary values for the omitted regions.
The largest certified vector-arithmetic range is85,377,593,169,792,
below2^63. Geometric sums, conditioning and the two-prime consumer use
exact fractions. Run the new replay with `python3 -I -O`.
The arbitrary-height conclusions use the ordinary proofs above;
no new Lean theorem or unrestricted noncoverage endpoint is asserted.

<a id="combining-actual-prefix-cap-savings-with-their-own-coverage-charge"></a>
### Combining actual prefix-cap savings with their own coverage charge

The preceding continuation admits a refinement that leaves every
physical prime kernel unchanged. Start with one fixed supported head
law mu, and a finite deterministic admissible schedule from (AP1)--(AP6).
At each prime p write

    d_p=p-1-T_p, delta_p=(T_p-1)/(p-2),
    c_p=(p-1)/d_p<=p,
    a_p=(3p-1)/(p-1)^2, k_p=1+a_p c_p.

Let alpha_p(x) be the actual mixed forbidden density in row x relative
to its uniform pure-power survivor law. The existing distortion kernel
has its natural density multiplier bounded by
1/(1-min(alpha_p(x),delta_p)). Consequently its actual depth-e prefix
cap is c_actual(x)p^(-e), where

    c_actual(x)=(p-1)/[(p-2)(1-min(alpha_p(x),delta_p))]<=c_p.

These are the natural caps already retained by
`FiniteLaw.distort_prob_le_natural` and
`CappedGain.distorted_prefix_le`. Define D_p=E(c_p-c_actual)>=0
under the actual previous-history law. If J bounds every old complete
test square, two such tests A_e,A_f satisfy

    E[c_actual A_e A_f]<=c_p J-D_p,
    Gamma_new<=k_p J-a_p D_p.                           (SH26)

For the first inequality use Cauchy--Schwarz to bound E A_e A_f by J,
and A_e A_f>=1 to retain at least D_p from the density deficit.
For the second, expand an arbitrary new test over every ordered pair
of p-exponents. The zero-zero pair contributes at most J; every other
pair has intersection cap c_actual p^(-max(e,f)). Individual residues
may vary with the old modulus: expansion into old labelled indicators
still gives the complete loads A_e A_f after applying the cap.
Their finite coefficient is bounded by sum_(j>=1)(2j+1)p^-j=a_p.
This enlargement is valid because c_p J-D_p>=E c_actual>0.

Write f_p=product_(later r)k_r and P=product_p k_p. Let beta_p be
the actual assigned mixed-union probability at step p, and B=sum beta_p.
All these expectations are preserved by later normalized kernels.
Iterating (SH26) bounds every final complete test by

    E L^2<=G P-sum_p f_p a_p D_p.

For W>0 satisfying W>=f_p a_p(p-1)/d_p at each prime, define on z>=1

    h_p(z)=W(z-T_p)_+/d_p
       +f_p a_p[(p-1)/(p-1-min(z,T_p))-c_p].

This function is increasing and convex: below T_p its derivative is
f_p a_p(p-1)/(p-1-z)^2, above T_p it is W/d_p, and the stated condition
is exactly the nondecreasing slope condition at the join. Using the
original weighted mixed load R_p from (AP3), alpha_p<=R_p/(p-2) gives

    W beta_p-f_p a_p D_p
      <=E h_p(1+R_p)
      <=E_(N_p) max_L E_mu h_p(N_p L).                  (SH27)

The last comparison preserves the original labels and the single missing
unit in (AP3), then applies Jensen exactly as in (AP4). Its N_p is the
same auxiliary multiplier as in the original schedule. When h_p(1)<0,
apply the nonnegative convex comparison to h_p(1+R)-h_p(1), and restore
the constant once. No density deficit is estimated independently from
the negative intercept of this combined cost.

Suppose C_p(W) bounds the right side of (SH27). The finite criterion

    G P-1+sum_p C_p(W)<=W                               (SH28)

alone implies a positive final survivor law with Gamma<=1+W. No
separate scalar charge bound below one is needed. To see this, combine
(SH26)--(SH28): for every final complete test L,

    E L^2-1+W B<=W.

The normalized physical kernels exist on the entire earlier history;
none conditions on previous good events. Their union bound for final
bad mass therefore applies even before positivity is known. If3 divides
the full physical period, some mod3 cylinder has probability at least1/3.
Complete a test containing that cylinder and the unit class. Its load
is at least1+I, so its square expectation is at least2. Applying the
last inequality to this test gives B<=1-1/W<1. More generally any
nonunit divisor d gives B<=1-3/(dW)<1 by the same argument.
Thus final survivor mass rho>=1-B is positive. For every test,
E L^2-1<=W(1-B)<=W rho; discarding the complement saves at least
its mass, and one final conditioning proves Gamma<=1+W. The test
chosen to establish positivity does not change the physical law.

The costs in (SH27) have an exact finite observation formula for integer
head loads. For fixed n, put v_j=h_p(nj) and K=ceil(T_p/n). Then

    E_mu h_p(nL)=v_1+(v_2-v_1)(E_mu L-1)
       +sum_(j=2..K)(v_(j+1)-2v_j+v_(j-1))E_mu(L-j)_+.

All feature coefficients are nonnegative under the final W condition.
For n>=T_p the entire cost equals W(nL-T_p)/d_p, so the infinite
auxiliary tail is computed from its remaining probability and first
moment. For a fixed set of mean and hinge upper bounds, the resulting
certificate is affine in W. Algebraic evaluation at zero and one may
extract its coefficients, but only the final W satisfying convexity
gives a probability bound.

Using the exact same-law observations (SH24) and the unchanged schedule
11/T4,13/T5, the certificate (SH28) gives

    Gamma_13<=20165592223021484810434066670921
                 /131127082414004971430759164752
                <153.786631.                           (SH29)

The saving over (SH25) is exactly
25321722548022558251710601395/131127082414004971430759164752.
All physical heights and the low-geometry hypothesis remain as in
(SH25). The adjacent convex-profile verifier checks every active
integer cost coefficient, the full multiplier tail, convexity at the
final W, and exact equality in (SH28). This is an ordinary refinement
of the existing normalized distortion construction, not a new Lean
declaration or a complete unrestricted-prime continuation.

Repository searches covered (AP1)--(AP6), the scalar fibre boundary,
the actual clipped rectangle estimates, `PrimeRectangleTransfer`,
`ConditionalComparison/Distortion`, `CappedGainDistortion`, and
`ThreePrime/DistortionChain`. The existing natural-cap and full-history
union-bound results are reused directly. Public sources checked on
16 September2026 include BBMST [1811.03547](https://arxiv.org/abs/1811.03547),
its scalar potential in Section6, the geometry optimization in Section5.3
of [1901.11465](https://arxiv.org/abs/1901.11465), and Hough--Nielsen
[1703.02133](https://arxiv.org/abs/1703.02133), Lemmas5--6. No directly
applicable arbitrary-height11/13 endpoint was found in those statements;
no literature-priority claim is made for the refinement.
