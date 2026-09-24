# Fixed-cardinality resampling beyond the uniform leakage bound

The uniform independent replacement parameter in [report530](530-one-supported-law-controls-unused-and-deep-occupied-labels.md)
cannot improve its JL6 query certificate in the entire range where the
elementary uniform-survivor law does not already prove R_P<565/51.
This includes the stated shallow-block version with its reciprocal-tail
payment. The conclusion concerns that numerical certificate, not the
query cost of every supported probability.

One can change the joint replacement rule while preserving a common-law
Gibbs conclusion: select exactly k of n occupied labels uniformly,
rather than selecting them independently. Its exterior leakage uses
hypergeometric inclusion probabilities, while its inside-survivor
exponential bound follows from the classical Maclaurin inequality.
Two actual irredundant classes distinguish the new construction from
independent replacement at the same marginal probabilities. Neither
result proves the seven-prime query target or unrestricted Erdős#7;
the proofs and fixed arithmetic below are ordinary mathematics, not
new Lean verification.

## Uniform independent replacement has no additional low-mass range

Throughout let

    P={3,5,7,11,13,17,19},
    A=product_(p in P)p/(p-1)-1=212731/110592,
    T=565/51,        alpha=7235955529/6075000000000.

Fix an actual finite family M of distinct nonunit P-smooth numerical
moduli with one globally fixed phase per label. Let U be its complete
survivor, h=H(U), and N(x) its original covering multiplicity. Then

    a=1-h=H(N>=1),
    lambda=integral N dH=sum_(d in M)1/d<=A,
    f_0=A-lambda=sum_(d unused)1/d>=0.

For the uniform law rho=H|U/h, every query cylinder has probability at
most1/(h*d). Thus h>A/T already gives R_P(rho)<=A/h<T, with every
query depth included. Consider the remaining regime h<=A/T.

An additional constraint on these actual-family data is essential.
Report530's unused-label theorem and q_d>=1/d imply

    log(h/alpha)>=f_0.                               (UR1)

The scalar relaxation h>=alpha alone is too weak; h=alpha with lambda<A
violates(UR1) and cannot represent an actual family under that theorem.

For independent replacement with the same0<s<=1 at every occupied
label, the exact phase-free leakage is

    L(s)=integral_(N>=1)s^N dH.

It has a sharp lower envelope based on integer multiplicity. Set
mu=lambda/a, k=floor(mu), theta=mu-k, where a>0. Discrete convexity gives

    L(s)>=a*((1-theta)*s^k+theta*s^(k+1)).             (UR2)

The affine line through the two adjacent integer values lies below
s^N at every positive integer N; integrate using a and lambda.
For0<s<1 this is sharp among integer multiplicity laws with the same
mass and mean, attained on those adjacent integers. No assertion that
every such law has an arithmetic realization is made.

If beta=alpha-L(s)>0, the numerical JL6 certificate is

    Q(s)=[log(h/beta)-(1-s)*f_0]/s.                   (UR3)

It is an upper bound for a selected Gibbs law. The following lower
bounds on Q show that this upper certificate cannot cross T.

### Small h: private mass forces a positive cost

If h<=1/32, integer multiplicity gives

    H(N=1)>=2a-lambda,       L(s)>=s*(2a-lambda).

Use(UR1) and -log(1-z)>=z to obtain

    Q(s)>=f_0+L(s)/(alpha*s)
         >=[2(1-h)-A]/alpha+f_0*(1+1/alpha)
         >=(31/16-A)/alpha
          >38525/3456=T+4045/58752>T.                (UR4)

The last step uses31/16-A=1541/110592>0 and alpha<1/800.

### The rest of the nontrivial Haar regime

For1/32<=h<=A/T, the rational inequalities A/T<7/40 and A<39/20 give

    H(1<=N<=2)>=(3a-lambda)/2>21/80>1/4.

Therefore L(s)>s^2/4. Positivity of beta and alpha<1/800 require
s^2<1/200, hence s<1/14. Also h/alpha>25, so log(h/alpha)>2;
lambda>=1-h implies f_0<=A-1+h<9/8. Consequently

    Q(s)> (7/8)/s >49/4>T.                          (UR5)

The elementary estimate exp(1)<3 suffices for the logarithm comparison.
This includes the endpoint h=A/T, where uniform Haar gives only R<=T.

### The same obstruction includes the paid shallow block

Let C be any occupied block, D=M minus C, and suppose the reciprocal
payment satisfies sum_(d in D)1/d<=gamma<1/80. Replace only C uniformly
with probability s. Its exact block leakage is
L_C(s)=sum_(nonempty S subset C)H(E_S)*s^|S|, where E_S is the set of
points covered by exactly the original labels in S and no others.
Thus points covered by D contribute zero to L_C(s). Off the
union of D this equals the all-label integrand; on that union the
removed integrand is at most s. Hence

    L_C(s)>=L(s)-s*gamma.                            (UR6)

The JL6 upper certificate, using that same density-based tail payment,
is

    Q_C(s)=[log(h/beta_C)-(1-s)*f_0]/s+gamma/beta_C,
    beta_C=alpha-L_C(s)>0.

For small h, the possible subtraction gamma/alpha in(UR4) is canceled
by gamma/beta_C>=gamma/alpha. Thus Q_C(s)>T still follows. In the
larger-h branch, remove the D-union from{1<=N<=2}. It leaves mass
greater than21/80-gamma>1/4, where the block multiplicity still equals N.
Thus L_C(s)>s^2/4 and(UR5) still applies after dropping the nonnegative
tail payment from the lower bound.

The retained tau_P(10^9) is below1/80, so this covers report530's
shallow cutoff. Using an upper bound ell(s)>=L_C(s) only worsens Q_C.
It does not cover nonuniform probabilities, a sharper phase-dependent
leakage bound, different payments based on actual cylinder geometry,
or the dependent sampling construction below.

## Select a fixed number of labels before sampling their phases

Let n=|M|>=1 and fix an integer0<=k<=n. Choose a uniformly random
k-element subset K of the actual occupied labels. This choice is
independent of the query phases and of the arithmetic point x.
For a finite query inventory J, draw one potential replacement phase
for each queried original label and one phase for each unused query
label, independently of each other and of K, using theta_d. Install
only the replacements in K intersect J, and add the unused query
classes. Unqueried original labels and queried originals outside K
stay fixed. Each realized family still has one globally fixed class
per numerical label.

Put r=k/n and write E_S for the exact full-family covering cells. Define

    p_k(j)=binomial(n-j,k-j)/binomial(n,k),   0<=j<=k,
           0,                             j>k,
    L_k=sum_(nonempty S subset M)H(E_S)*p_k(|S|).      (FR1)

Here p_k(0)=1; for positive j<=k the ratio is the falling-factorial
ratio(k)_j/(n)_j. A point in E_S outside U cannot survive unless every
label in S is both queried and selected. Its exterior survival
probability is therefore at most p_k(|S|), giving the uniform upper
bound L_k. No selection is made separately for different points.

### The same linear query weights remain valid

On U, set w_d(x)=0 for unqueried occupied labels. Conditional on K,
the occupied contribution to the survival probability is
product_(d in K)(1-w_d(x)). Its average is

    e_k(1-w_1,...,1-w_n)/binomial(n,k)
       <=[1-(sum_d w_d)/n]^k
       <=exp(-r*sum_d w_d).                          (FR2)

The first inequality is the classical Maclaurin elementary-symmetric
mean inequality for nonnegative arguments; the k=0 case is interpreted
as1 throughout. One way to see the inequality is to fix the sum of the
arguments and average pairs: the terms using one member depend only
on their sum, while terms using both increase with their product.
Repeated averaging gives the all-equal maximum. This is a use of that
classical inequality, not a claim of new symmetric-polynomial content.

The unused-label factors are at most exp(-sum_unused w_d), just as
before. Every realized legal family has survivor mass at least alpha,
so subtracting(FR1)'s exterior contribution and using(FR2) gives

    beta_k=alpha-L_k>0
       ==> integral_U exp(-sum_unused w_d-r*sum_occupied w_d)dH
                         >=beta_k.                  (FR3)

The finite Gibbs minimization and all-query compactness proof of
report530 GD1--GD2 now applies without change. One probability nu on
the same complete U has

    nu<=H|U/beta_k,
    R_unused(nu)+r*R_occupied(nu)+KL(nu||H(.|U))
       <=log(H(U)/beta_k).                           (FR4)

Both the weight r and the entire sampling rule are fixed before query
inventories vary. Thus this is one all-depth law, not a different law
for each test.

For every j, p_k(j)<=r^j; hence L_k is no larger than the independent
leakage at the same marginal probability. If n>=2,

    L_independent(r)-L_k
       >=r*(1-r)/(n-1)*H(N=2).                      (FR5)

This follows from the exact difference of the two inclusion
probabilities when j=2; all other differences are nonnegative. It
requires no independence among original covering events.

### Fixed-cardinality choices in separate blocks

More generally partition M into fixed nonempty blocks M_b, and choose
exactly k_b of their n_b labels uniformly, independently across blocks.
Then r_d=k_b/n_b for d in M_b, and replace(FR1) by

    L_blocks=sum_(nonempty S subset M) H(E_S)
                   *product_b p_(n_b,k_b)(|S intersect M_b|).     (FR6)

Apply(FR2) in each block and multiply. With beta=alpha-L_blocks>0,
the same Gibbs law has weighted query sum
R_unused+sum_d r_d*q_d, relative-entropy budget log(H(U)/beta), and
density at most1/beta. A cell containing more than k_b covering labels
from any block contributes zero exterior leakage. The partition and
block quotas must belong to one fixed construction; selecting a new
partition for each query or point would not establish this conclusion.

## Two actual irredundant labels distinguish the sampling rules

Take the originals0 mod525 and0 mod875. They have gcd175 and lcm2625.
Neither contains the other; the integers525 and875 are private witnesses
for the corresponding original classes. Their exclusive masses are

    H(E_{525})=4/2625,
    H(E_{875})=2/2625,
    H(E_{525,875})=1/2625,
    H(U)=2618/2625.

Select exactly one of these two labels, with equal probabilities.
Compared with independent half-probability replacements, the costs are

    L_fixed=1/875 < alpha < 13/10500=L_independent.   (FR7)

Thus(FR4) has a positive certified denominator for the fixed-cardinality
rule, while the independent rule at those same marginal weights does
not. Query phase1 at both labels makes these exterior bounds exact:
both replacement cylinders are1 mod175 and miss the entire old union.
The example establishes strict extension of this resampling interface;
it does not improve a noncoverage range or show a small total query
cost unavailable by other means. Here uniform Haar on U already gives
an elementary bound far below T.

Arbitrary correlation cannot be substituted for(FR2). With these same
originals and query phases, instead select both labels or neither,
each with probability1/2. The marginal replacement probabilities are
still1/2. At the actual survivor x=1 both w values are1, but the
averaged inside survival is1/2>exp(-1). Thus the exponential domination
used by the Gibbs argument fails. Preserving marginal probabilities
alone does not preserve the required joint response.

The [fixed arithmetic consumer](../../frontier/cover-geometry/fixed_cardinality_resampling.py)
and [result](../../frontier/cover-geometry/fixed_cardinality_resampling.json)
check the uniform-obstruction constants, consume the retained tail,
and verify the actual two-label geometry and both sampling costs.
No old producer, parameter grid or Lean proof is rerun. Finding a
fixed block selection whose joint budget proves the general query
target remains open.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fixed_cardinality_resampling.py
```
