[Index](../../marked_head_profile.md) · [Complete aligned comparison](317-the-complete-actual-aligned-j-comparison-crosses403.md) · [Finite-source neighborhood](318-a-finite-aligned-source-neighborhood-keeps-j-below403.md)

# An explicit total-variation neighborhood of the actual aligned endpoint set

Let Z* be318's set of actual countable aligned source configurations:
qJ=1, source45 and135 in the same surviving mod9 cell, and rho=2/675.
Use the COMPLETE normalized357 survivor measures, not only their old35
projections. If an actual finite or countable source f in318's aligned
effective9 chart and some z in Z* satisfy

    ||mu_f-mu_z||var <= 1/100000000,

then the original complete comparison has a positive denominator and

    J_env(f) <401051/1000=401.051<803/2<403.       (TV1)

The norm is full signed-measure variation, with no factor1/2. Every
original target keeps its independently chosen own label residues.
There are no test cutoffs, common optimizers, relaxed endpoint measures,
or unpriced count tails in this conclusion.

This is an explicit radius in ACTUAL MEASURE DISTANCE. It is not a
numerical epsilon in318's qJ/rho source-parameter condition. A quantitative
inverse from those defects to distance from Z* remains unproved here.

## Complete CRT moments give a uniform modulus

Reuse18, “The Haar fourth moment and the original-label transfer”, which
already proves the complete ordered-tuple CRT bound and records
F4(3)=30, F4(5)=285/32, F4(7)=140/27 and H4_357=16625/12.
The complete second-moment sum is62/302's35/4 before the6/5 density
factor. No new source instance or moment enumeration is needed.

For any independent original357 test t, write A_t=1+B_t for its complete
load. B_t is the sum of its nonunit cylinder indicators. For each ordered
k-tuple of labels, its CRT intersection is empty or has Haar mass at most
the reciprocal of the LCM. The maximal mass is attained simultaneously
for all such tuples by placing all test residues at zero. Thus every
polynomial in B_t with nonnegative coefficients has Haar integral at most
its value for that common-zero TEST configuration. This comparison places
no constraint on the actual test residues being bounded.

The existing k=2,4 complete geometric sums of ordered exponent maxima are

    S2=product_(p=3,5,7) sum_(a>=0)(2a+1)/p^a=35/4,
    S4=product_(p=3,5,7) sum_(a>=0)((a+1)^4-a^4)/p^a
       =30*(285/32)*(140/27)=16625/12.

Since (A_t^2-1)^2=4B_t^2+4B_t^3+B_t^4 has nonnegative coefficients,

    integral (A_t^2-1)^2 dHaar <= S4-2S2+1=16427/12.   (TV2)

This uses the nonnegative expansion; it does not subtract an upper bound
for S2 from an unrelated upper bound for S4. Monotone convergence includes
all original labels and all exponent tails. The first-moment bound makes
A_t finite Haar-almost everywhere for each fixed test.

Both actual source densities lie in[0,6/5] by302. Their difference has
absolute density at most6/5, not12/5. Put t=||mu_f-mu_z||var. By
Cauchy--Schwarz and(TV2),

    integral (A_t^2-1) d|mu_f-mu_z|
       <=sqrt((16427/10)*t).                          (TV3)

Each of302's59 original target functions has an explicit quadratic
increment constant L_g satisfying

    |g(n+1)-g(n)|<=L_g*((n+1)^2-n^2), n>=1.

Hence, writing v_g=g(1)>=0, for every independent own test,

    |integral g(A_t)dmu_f-integral g(A_t)dmu_z|
       <=v_g*t+L_g*sqrt((16427/10)*t).                 (TV4)

The same uniform bound holds for the difference of their separate
suprema over all own tests. Different targets may have different
optimizers throughout.

## The original signed comparison gives a rational radius

Let N*, E*, C0 be317's exact numerator upper, positive denominator lower,
and original offset. For its original weights w_i, signed mass price cS,
external square price cQ, and count coefficients a=1/7986,b=1/87846,
define

    N0=|cS|+sum_i w_i*v_cost-i+cQ*v_square,
    N1=sum_i w_i*L_cost-i+cQ*L_square,
    E0=1+v_H4/6
          +(sum_j v_AP11-j+a*v_mean+|b-a|)/7,
    E1=L_H4/6+(sum_j L_AP11-j+a*L_mean)/7.

These constants are reconstructed from the original59 functions in302
and the unchanged317 comparison. The exact values are

    N0=1556107055932111300021081/5393494724947082158204800,
    N1=2070782892374236779637510453/148113662831239102344547200,
    E0=29283/29282,
    E1=1357579/38740086.

Put m(t)=sqrt((16427/10)*t). Keeping the exact same source mass in all
signed terms and the entire count law gives

    N_env(f)<=N*+N0*t+N1*m(t),
    E_env(f)>=E*-E0*t-E1*m(t).                         (TV5)

For t<=10^-8, m(t)<41/10000 since16427/10<41^2. Substitution with
that rational upper into(TV5) gives a positive denominator and

    C0+[N*+N0*10^-8+N1*(41/10000)]
           /[E*-E0*10^-8-E1*(41/10000)]
       =401.0505138262098...<401051/1000.              (TV6)

All inequalities and the displayed decimal enclosure are checked by
the [portable helper](../../frontier/j-source/j_aligned_full_source_tv_neighborhood.py) and its [canonical certificate](../../certificates/source_norms/j-source/j_aligned_full_source_tv_neighborhood.json), with canonical source reading
and rational arithmetic only. The comparator is the original J envelope;
it is not identified with Gamma19.

## A uniform finite-label sufficient condition

There is a direct coupling when f and z have the SAME original forbidden
label at every nonunit modulus3^a5^b7^e with0<=a,b,e<=N. Absences, if
present in a label coordinate, must agree as well. Define the complete
tail bounds

    T_N=(35/16)*[1-(1-3^(-N-1))*(1-5^(-N-1))*(1-7^(-N-1))],
    T7_N=7^-N/6.

The two forbidden unions differ in Haar measure by at most2T_N. Their
pure-seven normalizers differ by at most2T7_N. Each full survivor lies
inside its pure-seven survivor. Dividing by the common5/6 normalization
floor, the two terms from the indicator and normalizer differences give

    ||mu_f-mu_z||var <=(12/5)*(T_N+T7_N).              (TV7)

At N=18 this rational upper is less than10^-8. Thus ANY actual source
whose original labels through this box agree with SOME actual z in Z*
satisfies(TV1). The source labels are compared; no own-test labels are
fixed or identified with them.

The missing step for a qJ/rho radius is now precise: construct an actual
endpoint completion of a sufficiently accurate source prefix, or prove
a quantitative source-measure repair without exact prefix agreement.
Small LP row residuals or the identity mu=Lambda-V+Omega alone do not
provide such an endpoint. The endpoint's beta/late freedoms remain
available, so no comparison to one fixed endpoint is required or claimed.

The exact numerical companion is checked with:

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/j-source/j_aligned_full_source_tv_neighborhood.py --check
```

The complete measure proof is ordinary mathematics; no new Lean verification
or frozen-truth claim is made.
