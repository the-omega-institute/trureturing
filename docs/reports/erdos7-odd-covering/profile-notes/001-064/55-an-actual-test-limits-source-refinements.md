[Index](../../marked_head_profile.md) · [Actual source family](50-sharp-source-survival-endpoints.md) · [Actual tensor35 test](51-sharp-off-diagonal-source-costs.md) · [Allocated thresholds](53-allocated-seven-thresholds-sharpen-actual-survival.md)

# An actual test limits source refinements

The comparison of profiles49 and53 cannot reach its target403 by
optimizing the h4/h5 threshold allocations alone. Every upper target
certifiable within the specified fixed comparison family satisfies

    K_certificate >=
      85359535508429362403462912894296348843645007
      /168825936155207478969705582638937789792000
      =505.6067654791821... .                         (B1)

This leaves a gap of102.60676547918213... above403 before adding a
positive core error. Relative to profile49, the improvement available
in this family is at most4.219947504887497.... After profile53's
published bound509.4606885156834..., the remaining improvement is at
most3.8539230365012465....

This is a lower bound on the upper target obtainable from a fixed
sufficient comparison. It is not a lower bound on actual K, an
impossibility result for other comparisons, or a resolution of
unrestricted Erdos #7. The proof uses one actual finite-family limit,
not a search over source vertices or threshold choices. The same
obstruction also applies to more general source bounds under the
explicit endpoint condition in section5.

## 1. What is fixed

The comparison family retains the following data:

* The profile49 conditional numerator inputs, including the41 linear
  and five quadratic costs, independent source-square margin, raw81
  contribution, slopes and offsets.
* The profile46 h25 margin and the common forbidden-carrier mixture.
* The original actual-mass bounds D_c, the complete mixed7 deletion
  remainder Trest and shallow carrier payment h_c.
* The uniform conditional27/81 credits
  delta4=4/253125 and delta5=4/1265625.
* The same fixed-target comparison combining these quantities.

Only the source upper bounds used to obtain the h4 and h5 margins are
improved. Threshold allocations may be arbitrary admissible arrays;
the positive original blocks need not share a threshold. Taking the
best of several allocations is included. No optimality of profile53's
particular allocation table is claimed or needed.

The statement concerns a proof through this sufficient comparison.
A negative required target margin does not imply failure of the
original covering conjecture or of a different proof.

## 2. One actual source and original tensor357 test

Use the off-diagonal forbidden family of profile50, with finite
height N, and its limit theta404. Its five surviving mod9 cells are

    C0=[0]9, C1=[3]9, C2=[1]9, C3=[4]9, C4=[7]9,
    ROOT=(0,0,1,1,1).

At the limit the raw source data are

    d=(3/4,3/4,1/4,1/2,1/2),
    n=(1/24,1/12,1/36,1/24,1/18),
    eta=(1/18,1/9,1/9,1/9,1/9),
    s=1/4, D=3/20.

The actual surviving masses satisfy S_N->D. The finite shallow
mixture is pi_A=1-7^-N and pi_empty=7^-N, with A=(0,1). Thus its
limit is concentrated at A; no finite exact point mass is assumed.

Choose the same original35 test in every original seven block:

    Z=B3*B5,
    B3=1+sum_(a>=1)1_[7]_(3^a),
    B5=1+sum_(b>=1)1_[4]_(5^b).

These are the finite truncations and limit used in profile51. Their
shallow ternary baseline is b=(1,1,2,2,3). The deeper test cylinders
form a nested chain in C4, where the raw source marginal equals
(1/2)eta. All nested five cylinders lie in the source-free cylinder
[4]5. These facts concern this explicit witness, not arbitrary tests.

For each positive original seven exponent e choose [4]_(7^e).
The finite pure7 forbidden cylinders are
[6*7^(e-1)]_(7^e),1<=e<=N. Their complements have raw mass

    z_N=(5+7^-N)/6.

Every [4]_(7^e) is entirely free of this pure7 deletion. Under the
normalized actual pure7 law, the nested test count B7 therefore has

    Pr(B7>=e+1)=7^-e/z_N, 1<=e<=N.

The limiting count has exactly

    p1=29/35, pn=36/(5*7^n) for n>=2,
    E N=6/5.                                         (B2)

The actual pre-deletion tensor357 load is Z*B7. This identity uses
valid original residues at every modulus3^a5^b7^e. Equal choices
between its original blocks specify a witness; no equality is
imposed on other tests in the universal source theorem.

The product B3*B5*B7 is Haar-integrable. The normalized finite pure7
densities are bounded by6/5, and the raw source indicators converge
pointwise. Dominated convergence therefore passes all linear-growth
hinge integrals below to the limit. The finite constructions establish
that the endpoint is approached by actual families.

## 3. Direct source integrals with complete tails

Let omega=(1/5,2/5,0,0,0), chi_t=min(1,h_t), and define

    C_t(v)=E_N h_t(N*v),
    I_t=integral_Lambda[C_t(Z)-omega*chi_t(Z)], t=4,5. (B3)

These are raw pre-mixed7-deletion source integrals. In particular
the subtraction in(B3) is the shallow clipped payment used by the
comparison; it is not the integral of the full actual deleted set.

For v>=1 the entire seven expectation is

    C_t(v)=sum_(n=1..t-1)pn*h_t(n*v)+T1*v-t*T0,
    Tj=sum_(n>=t)pn*n^j, j=0,1.                      (B4)

The Tj are exact geometric moments. For v>=t,
C_t(v)=(6/5)*v-t. Hence
f_l(v)=C_t(v)-omega_l*chi_t(v) has affine slope6/5 from t+1 onward.
The factor6/5 is required in both the ternary and five tails; these
are not the unit-slope costs of the earlier source-attainment table.

For a cell cost f and a shallow baseline value u put

    T_l(f;u)=sum_(k>=0)3^(-k-3)*[f_l(u+k+1)-f_l(u+k)].

Direct integration of the actual tensor test gives

    integral_Lambda f(Z)
      =sum_l n_l*f_l(b_l)+d4*T_4(f;3)
       +sum_(j>=1)5^-j*[
          sum_l eta_l*(f_l((j+1)*b_l)-f_l(j*b_l))
          +T_4(f((j+1)*.);3)-T_4(f(j*.);3)].         (B5)

To verify(B5), telescope f(B3*B5) along the nested five cylinders.
The initial term is integrated against lambda. Each positive-five
increment lies in a source-free test cylinder and is integrated
against eta with its exact factor5^-j. Telescoping B3 along its
nested C4 chain gives the displayed ternary terms. This argument
does not use a source-envelope maximum or choose auxiliary layouts.
It also retains the nonzero constant f_l(1).

Each sum in(B5) has a finite affine entrance followed by a complete
geometric tail. The resulting exact values are

| t | integral C_t(Z) | integral omega*chi_t(Z) | I_t |
| --- | --- | --- | --- |
| 4 | 3321163/15435000 | 1/11250 | 1106597/5145000 |
| 5 | 269853023/1620675000 | 1/56250 | 269824211/1620675000 |

## 4. Every threshold allocation obeys the same obstruction

For any admissible threshold array, the allocated nonnegative hinge
sum at equal original loads Z satisfies

    sum_(e<n)h_(a_(n,e))(Z)>=h_t(n*Z),
    sum_(e<n)a_(n,e)=t.                              (B6)

Every valid source envelope is at least the corresponding actual
test integral. Using the full source constant and all positive
blocks of profile53, equation(B6) therefore implies

    P_t^tau+F_theta404(psi_0^tau-omega*chi_t)>=I_t.    (B7)

The same lower bound applies to every admissible array, so it is
preserved when taking their infimum. No convexity in the allocation
parameters or finite optimization certificate is required.

The unchanged full-carrier credited margin has the form

    m_t^tau=s-Trest-h_A
              -[P_t^tau+F_theta404(psi_0^tau-omega*chi_t)]+delta_t.

At404/A, h_A=1/24 and Trest=7/120, so s-Trest-h_A=D. Thus

    m_t^tau<=D-I_t+delta_t=:m_t^upper.               (B8)

The conditional credits are included exactly once. The explicit
margin ceilings are

    m4^upper=-45193369/694575000,
    m5^upper=-400767583/24310125000.

These signed quantities must not be clipped at zero. Relative to
the old margins at this same control, their available increases
are at most611/205800 and9841/7203000, respectively.

## 5. A broader conditional statement for source bounds

The preceding obstruction is not specific to threshold allocation.
Suppose a source-and-shallow upper bound B_t(theta;c) satisfies, for
every finite actual source and original test,

    U_t(A)+R_c(A0)<=B_t(theta;c),
    R_c(A0)=integral_Lambda omega_c*(1-h_t(A0))_+.    (B9)

Assume either that(B9) also covers the limiting source in section2,
or that the bound admits that endpoint limit, for example by the
upper-semicontinuity condition along the explicit finite family

    B_t(theta404;A)>=limsup_N B_t(theta_N;A).         (B10)

Continuity at this endpoint is sufficient. The existing finite
source-envelope formulas, including fixed threshold allocations,
satisfy this condition. It is an explicit premise; a discontinuous
assignment at a non-realized finite endpoint is not silently included.

The actual finite tensor test in section2 has

    U_t(A_N)+R_A(A0_N)->h_A+I_t.

Apply(B9), take the limit and use(B10). This gives

    B_t(theta404;A)>=h_A+I_t.                        (B11)

Consequently any improved comparison still using

    m_t=s-Trest-B_t+delta_t

obeys the same margin ceilings(B8), even if its entire source and
outer-Jensen upper bound has been optimized. The actual family
supplies a universal obstruction to lowering that source payment.
The other frozen terms in section1 are essential to the conclusion.

## 6. The fixed numerator forces a target above505

The inherited h25 value at404/A is68963/441000. Combining it with
(B8) gives

    M_upper=m25/22+m4^upper/6+4*m5^upper/33
           =-766735967/133705687500,
    q=23/42,
    q*D+M_upper=20432462441/267411375000>0.          (B12)

Retain the profile49 conditional numerator at this same control.
With its notation its combined slope is H+A81 and correction is

    Corr=AC*Mquad_A+M41_A+cG*mg-Raw81.

All these quantities are unchanged in profile53. In particular
mg=5701/3888. The positive fixed comparison numerator and offset are

    N_fixed=(H+A81)*D-Corr
      =16632177193488738812476720877032433019439
        /449729701159543356783713630148000000000,
    C0=185694867601/8599322160.                     (B13)

For a valid finite upper target K, its D-endpoint certificate must
satisfy

    (K-C0)*(q*D+M_actual_comparison)>=N_fixed.       (B14)

A nonpositive comparison denominator cannot yield a valid finite
upper target from this positive numerator. For a positive one,
M_actual_comparison<=M_upper implies

    K>=C0+N_fixed/(q*D+M_upper),

which is exactly(B1). If the actual-mass coefficient is negative,
the sign-selected s-endpoint inequality is stronger than its
D-endpoint inequality; hence(B14) remains necessary. The finite
actual family also approaches S=D and pi_A=1, so the control is
not excluded by the source-feasibility results.

No actual numerator extremizer is asserted. N_fixed is the numerator
of the frozen comparison, and need not be attained by the tensor
test used to constrain its denominator. This is why(B1) is a bound
on this comparison's capability rather than on actual K.

## 7. Exact checker and the remaining route

The [checker](../../frontier/source-budgets/source_refinement_ceiling.py) and
[result](../../certificates/source_norms/source-budgets/source_refinement_ceiling.json)
pin the profile49 and53 certificates and the actual-family helpers.
They evaluate only theta404. The independent square margin is
recovered from the pinned49 aggregate by subtracting its five
quadratic contributions and dividing by the pinned complete
quadratic-tail weight1600217/12882870; no source39 vertex scan or
temporary cache is used.

The program directly checks four finite tensor357 source integrals
at heights3 and4 against the original-source histograms and their
closed formulas. The limiting source costs are evaluated both by
combining the complete seven expectation first and by integrating
its individual finite terms and exact affine tail. Both orders agree.
It retains the clipped payment, raw constants, slope6/5, both full
credits and the existing physical AP square-tail coefficient.

The ordinary proof supplies the quantifiers over arbitrary allocations
and, under(B9)-(B10), more general source bounds. Finite arithmetic
checks these proof inputs; it does not infer the universal statement
from a finite collection of threshold samples. No Lean verification
is claimed.

Further progress toward403 must change at least one fixed part of
section1: improve the numerator comparison, improve h25, retain more
actual mixed7 deletion payment than the current remainder and credits,
or introduce a joint inequality that changes their present separate
combination. Adding observations that only tighten the same source
upper bound, while leaving these other terms fixed, remains subject
to(B1). The result provides a stopping criterion for that restricted
refinement route.
