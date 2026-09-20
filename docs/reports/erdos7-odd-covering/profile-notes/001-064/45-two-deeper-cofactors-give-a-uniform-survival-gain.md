[Index](../../marked_head_profile.md) · [Whole-hinge source theorem](42-whole-hinge-absorption-sharpens-actual-survival.md) · [Complete cell costs](43-complete-cell-costs-strengthen-whole-hinge-survival.md)

# Two deeper cofactors give a uniform survival gain

Retaining the mixed7 forbidden cofactors27 and81 improves the complete
two-cofactor source margins of profile43 by the uniform constants

    delta4=4/253125,
    delta5=4/1265625,
    delta4/6+(4/33)*delta5=14/4640625.                 (DC1)

Precisely, write m_(2,t) for profile42's true absorbed margin, evaluated
with the full cell-dependent source operator as in profile43. For every
original test, with its own independent residues and the same actual
surviving raw mass S,

    E_nu357 h_t(A)<=1-[m_(2,t)(theta)+delta_t]/S,
    delta_t=4/(405*5^t), t=4,5.                     (DC2)

This improves the complete margin, not only its earlier epsilon lower
bound. It covers arbitrary finite original exponent heights, missing
or empty deletion carriers, and the complete geometric tails. The
result is an ordinary mathematical theorem; it does not assert Lean
verification, a negative-Q conclusion, or unrestricted Erdős #7.

A conservative consequence on the same actual law is

    J<=418.6484652424881...,
    Gamma13<=146.8256312175257...,
    T13(81)<=92.95113075956209...,
    K=J+T13(81)<=510.93214848743776...,
    rho_actual>=0.5049715215298277... .

The complete box20/current8 error is0.000576185014054454..., leaving
a sufficient-criterion gap of107.93272467245183.... The final section
derives these bounds directly from profile43 and(DC1), without claiming
an optimum of the refined four-cofactor envelope.

## Actual measures and the mod81 refinement

Fix any finite original forbidden family in the effective9 branch.
Let eta be its raw pure3 survivor measure, Lambda its raw actual35
survivor measure, and lambda the3-coordinate marginal of Lambda.
The actual survivor restriction gives

    dLambda=W(x,y)*deta(x)*dm5(y), 0<=W<=1,
    0<=dlambda/deta<=d_l on surviving mod9 cell l,
    d_l>=1/4, eta(C_a)<=3^-a for every depth-a cylinder C_a.

These are the actual domination hypotheses of profile31, not merely
bounds on parent cell totals. Complete35 loads depend on both3 and5
and are integrated against Lambda; pure3 blocks use lambda or eta.

Partition the actual ternary carrier into mod81 children c of the
five surviving mod9 cells. Set

    eta_c=eta(c), n_c=lambda(c), d_c=d_(parent(c)).

The pointwise density and cylinder bounds persist. Zero-mass cells
may be retained; no argument divides by n_c or eta_c. If an actual
height is below4, adjoining unused uniform ternary coordinates defines
this partition without changing any original event.

For each original pure3 test block retain its first four test labels.
Its fine baseline is

    b_c=1+I1(c)+I2(c)+I3(c)+I4(c), 1<=b_c<=5,        (DC3)

where Ia is that test's original depth-a cylinder indicator. Let B4
be the finite set of all such baseline vectors. The four test residues
remain independently chosen; they are not identified with deletion
labels. Every positive5 block also retains its own independent choices.

## The complete source operator on the refined cells

For fixed nonnegative increasing convex costs f_c with f_c(1)=0, put

    p5_n=4/5^n, n>=2,
    q_(n,c)(v)=[f_c(n*v)-f_c(n)]/n,
    bar f_c(v)=sum_(n>=2)p5_n*q_(n,c)(v)-f_c(v)/5,
    u_c=d_c*f_c+bar f_c.

Define

    P4_eta(q)=max_(b in B4)[sum_c eta_c*q_c(b_c)
                    +max_c sum_(a>=5)3^-a*Delta q_c(b_c+a-5)],

    F4(f)=max_(b in B4)[sum_c(n_c*f_c(b_c)+eta_c*bar f_c(b_c))
                    +max_c sum_(a>=5)3^-a*Delta u_c(b_c+a-5)]
        +sum_(n>=2)p5_n*[sum_c eta_c*f_c(n)+(n-1)*P4_eta(q_n)]. (DC4)

The costs used below have finite complete series. Since

    u_c=(d_c-1/5)*f_c+sum_(n>=2)p5_n*q_(n,c),

its increments are nonnegative and increasing. The same actual
positive5 comparison, signed centering, density substitution and
prefix-allocation argument as in profile42 prove that F4 bounds the
raw Lambda expectation of every complete35 test. The cell label of
f_c depends only on old3, so it is fixed during the pointwise5
comparison. The only change in the prefix argument is that the
remaining depth labels begin at5.

## A source perturbation inequality with the signed baseline retained

Let chi=chi_t=min(1,h_t), t=4 or5. Suppose f_c and
g_c=f_c-delta_c*chi are both admissible costs for(DC4), with delta_c>=0.
The following inequality holds whenever n_c<=d_c*eta_c and d_c>=1/5:

    F4(g)+sum_c n_c*delta_c
      <=F4(f)+sum_c(d_c-a_t)*eta_c*delta_c,
    a_t=sum_(n>=2)p5_n*chi(n)=5^-t.                 (DC5)

To prove it, define the nonnegative increasing function

    kappa_t(v)=sum_(n>=2)(p5_n/n)*[chi(n*v)-chi(n)].

At a fixed baseline v=b_c, the old initial source term minus the new
one is exactly

    delta_c*[(n_c-eta_c/5)*chi(v)+eta_c*kappa_t(v)].  (DC6)

This may be negative. The old combined deep cost minus the new one is

    delta_c*[(d_c-1/5)*chi(v)+kappa_t(v)],

which is increasing. Hence every old deep increment dominates the
new one. Its difference need not be convex; the individual old and
new costs already have the convexity required for their envelopes.

For each positive5 strip, the centered-cost difference is

    (delta_c/n)*[chi(n*v)-chi(n)],

also nonnegative and increasing. Its initial pure term and every deep
increment are nonnegative, so the corresponding P4 envelope decreases.
The positive5 constant difference is exactly
a_t*sum_c eta_c*delta_c, including the complete n-tail.

The remaining baseline inequality follows from the identity

    (n_c-eta_c/5)*chi(v)+eta_c*kappa_t(v)-n_c+d_c*eta_c
      =(1-chi(v))*(d_c*eta_c-n_c)
         +chi(v)*(d_c-1/5)*eta_c+eta_c*kappa_t(v)>=0. (DC7)

Every term on the right is nonnegative. In particular, for t=4 and
baseline v=5, chi(v)=1 and the second term handles the potentially
negative centered coefficient. No shallow-baseline assumption v<=t
is used. Combining(DC6)--(DC7) with the deep and positive5 comparisons
proves(DC5) before taking each common baseline maximum; its correction
is independent of that baseline, so the maxima preserve the inequality.

## Refinement is dominated by the parent source relaxation

Let F2 be the parent mod9 operator of profile42. If f_c=f_(parent(c))
is constant on each parent, then

    F4(f)<=F2(f).                                    (DC8)

Fix a fine baseline in(DC3) and write b_l=1+I1(l)+I2(l). For the
zero5 term, telescope its explicitly retained I3 and I4 increments
from that parent baseline. The pointwise density bound and
Delta f_l>=0 bound the combined lambda and eta increment by the
eta integral of the corresponding increment of u_l=d_l*f_l+bar f_l.

Put r_l(k)=Delta u_l(b_l+k). If the two test cylinders belong to
parents l3,l4, their contributions are at most

    3^-3*r_(l3)(0)
      +3^-4*r_(l4)(1_(l3=l4)).                     (DC9)

No actual nesting or intersection is assumed. Missing or empty
test cylinders have zero contribution and may be assigned an
arbitrary parent in this nonnegative upper comparison.

For any fine cell c chosen by the remaining deep maximum, its parent
l satisfies

    b_c<=b_l+1_(l3=l)+1_(l4=l).

Thus its entire a>=5 continuation is bounded by the parent allocation
schedule which first chooses l3, then l4, and then chooses l forever.
The parent DP2 lemma bounds(DC9) plus that continuation by

    max_l sum_(a>=3)3^-a*r_l(a-3).

The initial terms before those two increments sum exactly to the
parent initial terms, because fine masses sum to parent masses.
This proves the zero5 comparison in(DC8). The same argument applies
to every positive5 pure cost q_n, whose increments are nonnegative
and increasing. Its constant terms are unchanged by disaggregation.
Taking independent layout maxima and complete positive sums proves
(DC8). Only the unperturbed cost f must be parent-constant; the fine
cost g below is handled by(DC5), not by parent averaging.

## Absorb four actual deletion cofactors

Retain forbidden ternary carriers C3,C9,C27,C81 and define

    omega2=(1_C3+1_C9)/5,
    delta=(1_C27+1_C81)/5,
    omega4=omega2+delta,
    f=psi_t-omega2*chi, g=psi_t-omega4*chi.

Here psi_t is the complete original zero7 source cost of profile42.
Both costs are admissible: the native h_t coefficient in g is

    29/35-omega4>=29/35-4/5=1/35>0,

and its remaining hinge components have nonnegative coefficients.
The four deletion carriers may overlap, have unrelated ancestry, or
be empty on the actual support. They remain independent of the test
labels defining B4.

Applying(DC5) and then(DC8) gives

    F4(g)+integral_lambda delta
      <=F2(f)+integral_eta(d-a_t)*delta
      <=F2(f)+(d_*-a_t)/5*(1/27+1/81),              (DC10)
    d_*=max_l d_l.

The last step uses d_l-a_t>=0 and the actual cylinder mass caps.
The complete pure3 deletion tail changes exactly as follows:

    sum_(a>=3)3^-a=1/18,
    sum_(a>=5)3^-a=1/162,
    1/18-1/162=1/27+1/81.

With w_l=9*eta_l and
U=(sum(w)+R(w)+max(w))/36+1/72, the remaining deletion caps are

    T2=(d_*/18+U)/5,
    T4=(d_*/162+U)/5
       =T2-d_*/5*(1/27+1/81).                       (DC11)

All positive5 cofactor terms U remain unchanged. The factor1/5 is
the complete sum of the normalized actual pure7 cap coefficients
6/(5*7^e), e>=1.

Let Z0 be the original complete35 zero7 block of the tested load A.
At every7 exponent, apply the caps to the nonnegative integrand
(1-h_t(Z0))_+=1-chi(Z0), sum over all exponents, and then maximize
over the four ternary carrier choices. This allows the actual labels
and7 residues to vary independently with the exponent. The same
signed actual source/deletion identity as in profile42 gives

    m_(4,t)=s-P_t-T4
      -max_(C3,C9,C27,C81)[integral_lambda omega4+F4(g)],
    E_nu357 h_t(A)<=1-m_(4,t)/S.

The positive original7 complement P_t and the actual S are unchanged.
Use(DC10) before maximizing the four labels, and substitute(DC11).
This proves

    m_(4,t)>=m_(2,t)+a_t/5*(1/27+1/81),              (DC12)

which is(DC1)--(DC2). The gain is paid once in this survival inequality;
it is not also subtracted from a numerator source cost.

## Empty carriers, complete tails and the resulting denominator

A missing cofactor can be represented by the empty carrier or padded
in the nonnegative upper comparison. If it is empty, its delta
component and actual integrals vanish, while(DC10) still holds.
The old T2 charged its full d_*3^-a/5 cap even when no point was
deleted there. Removing that cap in T4 saves at least the claimed
a_t3^-a/5; emptiness increases the slack. No positive lower bound on
eta(C27) or eta(C81) is required. The same reasoning applies separately
at any7 exponents where the original labels are absent.

For all costs above, f_c(v) and g_c(v) are affine of slope1 once
v>=t+1. Thus q_(n,c)(v)=v-1 for n>=t+1, and the complete positive5
tail uses exactly

    sum_(n>=N)4/5^n=5^(1-N),
    sum_(n>=N)4*n/5^n=5^(1-N)*(N+1/4).

The combined deep increment is eventually d_c and its remaining
ternary tail is a geometric sum. The retained original7 complement
P_t keeps its complete tail. There is no original-height cutoff.

Retain profile41's fractional-hinge margin m25 and the profile43
complete source margins m_(2,4),m_(2,5). On the same actual AP45 law,

    rho_actual*S>=q*S+m25/22+m_(2,4)/6+(4/33)*m_(2,5)
                                      +14/4640625,
    q=23/42.                                        (DC13)

The refined actual cell masses have disappeared from this result
through inequalities valid for every such refinement. Consequently
no new parameter scan is needed to establish the additive constant.
The functions m_(2,t)+delta_t remain separately concave, so the
existing same-S and continuous-parameter arguments apply. Any newly
evaluated vertex targets require their endpoint and interpolation
justification. The actual-law rescaling below instead reuses the
already proved profile43 target inequalities.

The theorem retains exactly two additional pure3 cofactors at the
fixed barriers C4=C5=1. It does not license unrestricted further
absorption: four overlapping carriers leave only1/35 of the native
hinge coefficient. No actual-family attainment of an auxiliary source
maximum is asserted, and unrestricted Erdős #7 remains open.

## Conservative cost improvement on the actual law

Write Delta for profile43's raw survival lower mass at an actual family
and its actual S. The new bound is Delta'=Delta+delta, where
delta=14/4640625. Five surviving mod9 cells imply

    0<S<=s=sum_l n_l<=sum_l eta_l<=5/9.

Since rho_actual is a probability, (DC13) and the inherited survival
inequality give

    0<rho43*S<=Delta<Delta'<=rho_actual*S<=S<=5/9.

These inequalities are used on actual families; no new inequality
Delta'<=S is asserted at unrealized relaxed parameter endpoints. Put

    epsilon=delta/(5/9)=14/2578125,
    alpha=1-epsilon=2578111/2578125.

For each profile43 cost target T43 with constant part c, its proof
provides a nonnegative raw numerator N satisfying

    0<=N<=(T43-c)*Delta,
    actual cost<=c+N/(rho_actual*S).

Retaining that numerator inequality, rather than only its numerical
consequence, yields

    actual cost<=c+N/Delta'
      <=c+(T43-c)*(1-delta/Delta')
      <=c+alpha*(T43-c).                            (DC14)

Use c=C0 for J and K, c=16 for Gamma13, and c=0 for T13(81), with
C0=185694867601/8599322160. Each numerator retains its own original
test labels. The same actual source law supports all the inequalities.
Similarly,

    rho_actual>=Delta'/S>=rho43+epsilon.             (DC15)

Equations(DC14)--(DC15) specify the exact rational constants displayed
above from profile43's exact targets. In particular,

    K<=7557242320543468465242707644102427392964030762135303/
       14791087902602937395342934572776638914165625000000,
    rho_actual>=1012763466811/2005585312500.

The eight other source branches use their previous complete comparisons,
checked against these new targets; no5/9 premise is imposed on them.
Both complete-core errors are then recomputed. The identity

    J_new+T81_new-K_new=alpha*(J43+T81_43-K43)>=0

preserves the common-target error accounting. The two complete gaps
are107.93272467245183... and108.1531268121857....

The reproducible arithmetic is
[`frontier/cover-geometry/deeper_absorption_credit.py`](../../frontier/cover-geometry/deeper_absorption_credit.py):

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/deeper_absorption_credit.py
```

It reads pinned logical certificates and source modules, writes only
stdout by default, and supports `--output PATH` for exact JSON data.
It evaluates eight fallback branches and both complete cores, with
zero new source-vertex evaluations. An independent rational computation
matches all five targets, fallback values and complete-core outputs.
This is arithmetic verification of the ordinary argument, not Lean
verification or a new exhaustive optimization of the four-cofactor model.
