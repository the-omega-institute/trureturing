[Index](../../marked_head_profile.md) · [Raw aligned comparison](328-complete-raw-costs-cover-the-high-surplus-aligned-face.md) · [Actual source](302-a-positive-actual-source-neighborhood-keeps-j-below403.md)

# A finite actual neighborhood of the whole J face covers high surplus

Let an actual finite source lie in the effective9 chart, with the same
original independent test domain and actual normalized mixed7 survivors
as302. Write rho=S-S0 using its actual carrier-averaged lower mass. Then

    qJ>=1-1/4000 and rho>=1/40
        imply E>0.0994684 and J<402.459<403.           (WF1)

There is no45/135 alignment condition. Both whole-J-face orientations
are covered. The source domain is nonempty, as the explicit finite family
below verifies. This extends the raw-cost method used in328 to a finite
actual domain, without using its135 mean improvement, any survivor LP
bound, or any small-rho assumption.

## A containing point on the whole face

Let qJ>=1-delta with0<=delta<=1/4000. The concentration argument in71,
used without a rho premise in311, permits the orientation

    deficit0>=(1-delta)/2, alpha1>=(1-delta)/4,
    sum_root1 beta>=(1-delta)/4,
    sum_root1 late>=(1-delta)/72,
    3/4<=z<=3/4+delta/4.

The original parameter simplex budgets are respectively1/2,1/4,1/4,
1/72. Define a starred containing point with

    deficit*=(1/2,0,0,0,0), alpha*=(0,1/4), z*=3/4.

Delete the root0 beta coordinates and add the missing root1 beta budget
to any fixed root1 cell. Do the same for late. Thus

    beta*=beta_root1+r_beta e_L, 0<=r_beta<=delta/4,
    late*=late_root1+r_late e_L, 0<=r_late<=delta/72.

The chosen cell L is arbitrary; it is not identified with source45 or
source135. Therefore(beta*,late*) belongs to the product of the full
root1 simplexes of masses1/4 and1/72. Its nine vertices are

    beta*=(1/4)e_i, late*=(1/72)e_j, i,j in root1.   (WF2)

These are containing parameter points. No actual finite source is claimed
to attain qJ=1 or any vertex, and no independent test is assigned a source
residue.

Write w=1-deficit, a_j=z-alpha_ROOT(j)-beta_j,
eta_j=w_j/9 and n_j=eta_j a_j-late_j. The source formulas give

    eta<= (1+delta)eta*, a<= (1+3delta)a*,
    n<= (1+7delta)n*                              (WF3)

entrywise. Here a*>=1/4, every root1 n*>=1/72, and root0 masses are
(1/24,1/12). On root1, eta<=eta* and

    0<=a-a*<=3delta/4,
    n-n*<=delta/12+delta/72=7delta/72.

On the distinguished root0 cell,

    n0-n0*<=delta/18+delta^2/72;

on its other cell the increase is at mostdelta/36. These are less than
7delta n_j* on the stated range. For pure masses only eta0 can increase,
by at mostdelta/18=delta eta0*. These are pointwise domination bounds,
not assertions of a common source density or a realizable starred source.

The projection retains71's total errors

    ||n-n*||_1<=delta/2, ||w-w*||_1<=delta,
    ||a-a*||_infinity<=3delta/4.

For the original complete cofactor cap sum

    C=rootmax(n)+max(n)+max(a)/18
        +[sum(w)+rootmax(w)+max(w)]/36+1/72,

its starred value is1/2 and

    |C-1/2|<=delta+delta/24+delta/12
                 =9delta/8<=83delta/72.

Also |s-1/4|<=delta/2. Since S0>=D=s-C/5,

    S=S0+rho>=3/20+rho-(263/360)delta.             (WF4)

No lower bound on rho is inserted into a negative mass coefficient.

## Centered raw operators preserve this domination

For an original increasing convex cost g set f(v)=g(v)-g(1), v>=1.
Let B5 and B7 denote the SAME complete raw source operators in31/42,
implemented by zero5_raw and zero7_raw. They preserve additive constants:

    Bp(g-c)=Bp(g)-c*s, p=5,7.

The stored zero-five correction includes a negative term. Its centered
form must therefore be checked before claiming monotonicity. For f(1)=0,

    C_f(v)=sum_(r>=2)(4/5^r)[f(rv)-f(r)]/r-f(v)/5.

Convexity gives[f(rv)-f(r)]/r>=f(v) and
[f(r(v+1))-f(rv)]/r>=f(v+1)-f(v). As
sum_(r>=2)4/5^r=1/5, both C_f(v) and its integer increments are
nonnegative. Also f and its increments are nonnegative.

Thus the shallow zero-five expression is a positive combination of
n_j f(b_j) and eta_j C_f(b_j). Its complete deep term is a positive
sum of running maxima of a_j Delta f+Delta C_f. Under(WF3), with
lambda=1+7delta, the variable terms increase by at mostlambda and
the fixed nonnegative Delta C_f can be enlarged by the same factor.

Every positive-five block similarly consists of nonnegative centered
differences[f(rb)-f(r)]/r, with nonnegative pure-mass coefficients,
nonnegative complete ternary tails, and a nonnegative constant multiple
of sum eta. Consequently

    B5(f;actual)<=lambda B5(f;star).

For the original seven operator, each transformed block cost
sum_(r>e)p_r[f(rv)-f(r)]/r is increasing, convex and zero at1. The
remaining exact tail is a nonnegative multiple of B5(v^k-1), for
k=1 or2, rather than an unpriced difference of two unrelated uppers.
The mass term is s E f(N)>=0. Since s<=lambda s*, all terms give

    B7(g;actual)-g(1)s
         <=lambda[B7(g;star)-g(1)s*].              (WF5)

Complete geometric tails are retained in every step. The affine/quadratic
tail entries in the existing operator are exact summations, not cutoffs
of the original labels. Every one of the52 original costs, square, H4,
and the four AP11 functions keeps its own independently chosen test.

The generic complete raw mean requires no source135 gain. The cofactor
cap argument gives M<=(6/5)(s+C), hence

    M-s<=s/5+(6/5)C
         <=13/20+(89/60)delta
         <=13/20+(91/60)delta.                    (WF6)

The starred value is9/10-1/4=13/20. This uses the full original cap sum
at every positive seven depth, whose normalized cap weights sum to1/5.

## Nine complete accounts and the finite guard

Use the original offset C0, signed source coefficient cS, square price cQ,
positive52 weights, and the exact count tail a=1/7986,b=1/87846. Put

    k=403-C0, e0=1-b/7=614921/614922,
    n0=cS+cQ+sum_i w_i g_i(1)
       =742754686136309887178461/5393494724947082158204800,
    L=k e0-n0
       =10102918572711673951243633060687
          /26498239583665014643260182400>0.

Evaluate the same complete raw59 targets on(WF2), with generic raw
mean9/10. Convexity in the source mass and availability blocks implies
that the product-simplex interpolation is controlled by the nine vertex
accounts. All nine have the same numerical P and D bounds:

    P*=13892689289759908173789898167640162501
          /367593071513567360916667212000000000,
    D*=88501078819/1176610050000.

Here P is the weighted centered52-cost plus centered square sum; D is
H4/6 plus the four AP11 terms and a(M-s), divided by7 as appropriate.
The seven and five block maxima are evaluated separately for each target;
equality of these vertex upper numbers does not assert a common optimizer.

Equations(WF5)--(WF6) imply, for every actual source in the stated domain,

    P_actual<=(1+7delta)P*,
    D_actual<=(1+7delta)D*+(a/7)(91/60)delta,
    N<=n0*S+P_actual, E>=e0*S-D_actual.             (WF7)

At rho>=1/40 and delta<=1/4000, use

    Smin=7/40-(263/360)/4000=251737/1440000,
    lambda=4007/4000.

The exact rational account gives E>0.0994684, positive403 margin
greater than0.0539, and J<402.459. The ratio
(n0*S+lambda P*)/[e0*S-lambda D*-(a/7)(91/60)delta]
decreases in S wherever the denominator is positive, since all displayed
constants are positive. Both error allowances increase with delta.
Thus this check applies to every larger rho and every smaller delta;
it establishes(WF1), not just one corner measurement.

The corresponding exact-face containing threshold is

    rho>=26396104279640385787243578412401116813889149
      /1083110170950420907768636916953101981408750000
      =0.024370654978226273... .

That face arithmetic supplies the reference bounds only. The actual finite
conclusion is the positive-width guard(WF1).

## An actual finite source belongs to this domain

Take311's literal raw35 family at height N=12, with its dispersed beta and
aligned45/135 labels. Retain its pure7 classes at each depth. Among mixed7
labels retain ONLY cofactor3 on root0 with seven class1 and cofactor9 on
cell1 with seven class2, at every1<=e<=N; all other mixed7 labels are absent.
This leaves204 distinct original odd moduli. No source test labels are
removed from the complete test domain.

Put t=(1-3^(2-N))/18, q=(1-5^-N)/4 and v=7^-N. The raw parameters remain

    deficit=(9t,0,0,0,0), alpha=(0,q), z=1-q,
    beta=(0,0,1/5,q-1/5,0),
    late=(0,0,1/135,0,t*q-1/135).

The two surviving carrier families are disjoint across depths, each other,
and the pure7 classes, by311's literal cylinder rules. If n is the actual
raw cell vector, their total old mass is A=n0+2n1. Direct normalization
therefore gives

    S=s-(1-v)A/(5+v),
    S0=s-T2-(1-v)A/5,
    T2=(1/5)[max(a)/18+(h+h1+max(eta))/4+1/72].

Its complete qJ product is unchanged:

    qJ=(1-3^(2-N))^2(1-5^-N)^4(1-v).

Exact arithmetic at N=12 gives

    1-qJ=0.00003388634450980418...<1/4000,
    rho=0.05833338038722376...>1/40,
    S=0.2083341340165365...>0.

This is an actual finite source witness for nonemptiness. It does not
assert realization of any containing vertex or maximizing cost, nor does
it classify every finite source in the new domain.

The companion recomputes the finite-guard rational account from the nine
complete raw accounts and checks the displayed witness formulas. It uses
canonical artifact reads/writes, no optimizer and no new source scan.
The result concerns the original J comparison. Other source sectors, a
global source join and arbitrary later-prime continuation remain separate
proof obligations; no Lean result or unrestricted Erdős7 conclusion is
asserted.

The [exact certificate](../../certificates/source_norms/j-source/j_whole_face_high_rho_finite_guard.json) is regenerated by the [standard-library checker](../../frontier/j-source/j_whole_face_high_rho_finite_guard.py):

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/j-source/j_whole_face_high_rho_finite_guard.py --check
```
