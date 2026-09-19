[Index](../marked_head_profile.md) · [Common source operator](31-one-original-zero-five-layout-across-both-actual-measures.md) · [Actual source endpoints](50-sharp-source-survival-endpoints.md) · [Sharp endpoint costs](51-sharp-off-diagonal-source-costs.md)

# Every high-threshold scalar source envelope is jointly sharp

Fix theta404 and the actual off-diagonal source/test construction of
profile51. For every real T>=5, let

    h_T(v)=(v-T)_+,
    psi_T(v)=sum_(n>=1)(p7_n/n)*[h_T(nv)-h_T(n)],
    p7_1=29/35, p7_n=36/(5*7^n) for n>=2.

Then the same tensor35 test against the same actual source family
attains the inherited complete source upper envelope in the limit:

    lim_N integral_(Lambda_N) psi_T(Z_N)=F_(theta404)(psi_T).   (1)

Consequently F_(theta404)(psi_T) is the sharp supremum of limiting
source-cost values among finite source families approaching theta404,
for every real T>=5. One source/test sequence works for all these
thresholds. It also has the actual mass and carrier limits from
profile50: S_N tends to3/20 and pi_N tends to the point mass at(0,1).

This concerns scalar35 source costs. It does not assert sharpness of
absorbed costs at every threshold, complete357 tests, deletion clips,
or a final K comparison. The proof is ordinary mathematics with exact
finite rational premises, not Lean verification.

## 1. The only obstruction is a fifty-branch zero5 comparison

At theta404 the data are

    d=(3/4,3/4,1/4,1/2,1/2),
    n=(1/24,1/12,1/36,1/24,1/18),
    eta=(1/18,1/9,1/9,1/9,1/9).

The root map is r=(0,0,1,1,1). The ten baselines are exactly

    b_l=1+1_(r_l=R)+1_(l=J), R in{0,1}, J in{0,...,4},

ordered by increasing R, then increasing J; their indices start at0.
Write b*=(1,1,2,2,3) for baseline9 and j*=4. For any nonnegative scalar
increasing convex f on[1,infinity) with an affine tail, define

    Q_f(v)=sum_(n>=2)(4/5^n)*[f(nv)-f(n)]/n,
    D_f(a)=sum_(k>=0)3^(-k-3)*[f(a+k+1)-f(a+k)].

The fixed zero5 branch for one of the ten baselines b and deep cell j is

    Z_(b,j)(f)=sum_l[(n_l-eta_l/5)*f(b_l)+eta_l*Q_f(b_l)]
                +(d_j-1/5)*D_f(b_j)+D_(Q_f)(b_j).      (2)

This is exactly the existing complete common-source operator before
its zero5 maximization, with bar_f=Q_f-f/5. Every operation in(2) is
linear in f. Differences between two branches annihilate constants.

For the pure3 measure eta, the three-cell root has mass1/3, the
two-cell root has mass1/6, and cell4 has the largest cell mass1/9.
Thus b* maximizes the initial pure expectation of every increasing
convex cost. Its deep cell has baseline3, so it also maximizes each
complete convex deep increment sum. This is the common maximizer
criterion of profile31, and here it holds for every positive5 cost
[f(nv)-f(n)]/n and the full affine tail simultaneously.

The actual tensor construction uses that same baseline and nested
deep cell for every positive5 block. The five-coordinate test
cylinders are source-free and the source density on cell4 is exactly
d4. The direct integral formula of profile51 therefore gives

    I(f)=Z_(b*,4)(f)+Pos_f,
    F(f)=max_(b,j)Z_(b,j)(f)+Pos_f.                    (3)

Precisely, with q_n(v)=[f(nv)-f(n)]/n and x=sum_l eta_l, the
unchanged complete positive5 part, including its constant, is

    Pos_f=sum_(n>=2)(4/5^n)*[
        x*f(n)+(n-1)*(sum_l eta_l*q_n(b*_l)+D_(q_n)(3))].

It is attained by this one test. Geometric tails and at most linear
cost growth justify the complete sums. Hence F(f)=I(f) exactly when all fifty branch differences
Z_(b*,4)(f)-Z_(b,j)(f) are nonnegative.

## 2. Every primitive hinge of threshold u>=3 favors the witness

Put delta_(b,j)(u)=Z_(b*,4)(h_u)-Z_(b,j)(h_u). We first prove

    delta_(b,j)(u)>=0 for every u>=3 and every(b,j).    (4)

For u>=3, h_u vanishes at every shallow baseline value1,2,3. The
initial part of(2) is therefore only sum eta_l*Q_(h_u)(b_l), which is
maximized at b*. Since Q_(h_u) is convex, its deep sum is also largest
at baseline3. The remaining primitive-hinge deep coefficients are

    d4-1/5=3/10, max_j(d_j-1/5)=11/20.

For u>=3 the exact geometric relation is

    D_(h_u)(3)=3*D_(h_u)(2)=9*D_(h_u)(1).           (5)

Thus any competitor with b_j<=2 has no advantage even in its
primitive-hinge deep term. If b_j=3 and j is in the three-cell root,
its coefficient is at most3/10, so again every part is dominated.

The only remaining case has baseline3 at a cell in the two-cell
root. The worse of its two possibilities is baseline1/deep cell1;
the depleted cell0 has a smaller initial pure expectation. Relative
to that branch, the initial Q gain is Q_(h_u)(2)/6, the Q deep terms
cancel, and the primitive deep disadvantage is D_(h_u)(3)/4. It is
therefore enough to prove

    Q_(h_u)(2)>=(3/2)*D_(h_u)(3), u>=3.             (6)

The exact base values are

| u | Q_(h_u)(2) | D_(h_u)(3) |
| --- | --- | --- |
| 3 | 3/25 | 1/18 |
| 4 | 11/375 | 1/54 |
| 5 | 32/1875 | 1/162 |

Both sides are affine in u on each unit interval, so these three
checks establish(6) on[3,5]. For the unbounded extension,

    D_(h_(u+2))(3)=D_(h_u)(3)/9,
    Q_(h_(u+2))(2)>=(2/15)*Q_(h_u)(2).              (7)

For the second inequality, retain only n>=3 in the new sum and write
n=m+1. Then

    [h_(u+2)(2m+2)-h_(u+2)(m+1)]/(m+1)
      >=[m/(m+1)]*[h_u(2m)-h_u(m)]/m,

and m/(m+1)>=2/3 for m>=2, while the five-coordinate probability
falls by a factor1/5. The displayed numerator comparison follows from
h_(u+2)(2m+2)=h_u(2m) and h_(u+2)(m+1)<=h_u(m).
The ratio between the two sides of(6) therefore
improves by at least6/5 under u -> u+2. Every u>=3 is reached from
[3,5] by such shifts. This proves(6), hence(4), without a threshold
cutoff.

## 3. Exact low-threshold branch information

Each delta_(b,j)(u) is affine on each unit interval. Indeed every
cost evaluation in(2) is at an integer argument, where h_u is affine
between consecutive integer thresholds; the complete convergent
geometric sums preserve this property.

Evaluate all fifty branches at u=0,1,2,3. Exactly fourteen can be
negative below3:

    (1,0),(1,1),(1,2),(1,3),(1,4),
    (4,0),(4,1),
    (6,0),(6,1),(6,2),(6,3),(6,4),
    (9,0),(9,1).                                   (8)

Call this set B. All other branches are nonnegative for every u>=0,
by unit-interval affinity below3 and(4) above3. The exact minima
over the branches in B at the necessary endpoints are

| u | min_(b,j in B) delta_(b,j)(u) |
| --- | --- |
| 0 | -1/24 |
| 1 | -1/24 |
| 2 | -1/120 |
| 3 | 11/1800 |
| 4 | 7/27000 |
| 5 | 527/405000 |

Consequently all branches obey the global lower bound -1/24, and
every branch in B satisfies

    delta_(b,j)(u)>=7/27000 for3<=u<=5.             (9)

These finite rational comparisons use the complete tails in(2), not
finite exponent approximations. They are reconstructed in
[source_stoploss_spectrum.py](../frontier/source_stoploss_spectrum.py).

## 4. One positive seven-mixture term controls every possible negative tail

Since branch differences annihilate constants and are linear in the
cost, the centered seven mixture satisfies exactly

    Z_(b*,4)(psi_T)-Z_(b,j)(psi_T)
      =sum_(n>=1)p7_n*delta_(b,j)(T/n).             (10)

The sums converge absolutely: the primitive cost is bounded by its
argument, and every branch has finite complete geometric moments.

For branches outside B, every summand is already nonnegative. For
a branch in B and T>=21, put

    M=floor(T/3), m=M-2.

Then M>=7,m>=5 and

    3<=T/m<3*(M+1)/(M-2)<=24/5<5.

The n=m term in(10) is at least p7_m*7/27000 by(9). All n<=M terms are nonnegative by(4). The only
possible negative terms have n>M, and their total is at least

    -(1/24)*sum_(n>M)p7_n=-p7_m/7056,

because

    sum_(n>M)p7_n=(6/5)*7^-M=p7_(M-2)/294.

Thus the whole difference is at least

    p7_m*(7/27000-1/7056)
      =p7_m*311/2646000>0.                         (11)

This proves the required fifty-branch criterion for every real
T>=21, rather than extrapolating from a numerical scan.

## 5. The finite initial interval and actual attainment

For every integer k=5,...,21, exact evaluation of all fifty
psi_k branches gives

    Z_(b*,4)(psi_k)>=Z_(b,j)(psi_k).

Each fixed difference is affine in T on[k,k+1]: every argument nv
and n in the definition of psi_T is an integer, and all the complete
sums in(2) are linear. The endpoint comparisons therefore prove the
criterion for every real T in[5,21]. Combined with(11), this proves
it for all real T>=5. By(3), the limiting actual tensor integral equals
the inherited envelope at every such threshold.

The original finite source and test families are exactly those of
profile51. For each fixed T,0<=psi_T(v)<=v, and the common dominating
tensor B3*B5 has raw Haar mean15/8. Dominated convergence supplies
the actual finite-family limit in(1). The inherited envelope is
continuous at theta404 for each fixed T, so it is also a universal
upper bound on limsup along every approaching source/test sequence.
The one explicit sequence reaches all these bounds.

As a consequence, any fixed finite nonnegative linear combination
of these T>=5 marginal source bounds is also attained by that same
sequence. Merely lowering their old source-envelope values at this
endpoint is impossible. This conclusion places no numerical bound
on routes that add genuinely new relations with positive7 test
blocks, mixed7 deletion, or other parts of the final comparison.

## Verification scope

The standard-library checker
[source_stoploss_spectrum.py](../frontier/source_stoploss_spectrum.py)
reconstructs300 primitive endpoint branches and850 integer
psi-threshold branches from the pinned common source operator. It
also reconstructs the recurrence base and the exact strict tail buffer.
At T=5,12,21 it cross-checks the actual tensor integral from profile51
against two implementations of the source envelope. The checks use
complete affine and geometric tails. They do not enumerate or truncate
the infinitely many original source labels.

The proof of(4), unit-interval affinity, and(10)-(11) supplies the
unbounded quantifier. Hash checks establish dependency identity;
the ordinary proofs establish the mathematical meaning of those
helpers. No finite scan is used as a substitute for an infinite
statement, and no Lean verification is claimed.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/source_stoploss_spectrum.py
```

The program is read-only by default and accepts `--output PATH` for
exact rational JSON. `--base REPORT_ROOT` explicitly selects the report
root when the checker is run from a staging location. It uses only
pinned canonical dependencies, with no scratch imports.
