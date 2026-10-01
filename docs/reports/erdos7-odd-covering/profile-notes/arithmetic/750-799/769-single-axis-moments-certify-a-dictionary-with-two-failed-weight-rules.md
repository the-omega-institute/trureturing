# Single-axis moments certify a dictionary with two failed weight rules

The [common row-mass envelope](758-one-row-mass-law-handles-all-outside-colours.md)
has372 joint query slots. A scaled AM-GM comparison gives a stronger
sufficient condition using300 single-axis moment slots, with ONE common
row law throughout. A literal74-row dictionary below defeats both uniform
row weights and product lower-fibre weights in the original envelope.
Weights in {0,1,2} pass even the new stronger condition.

This is a new sufficient interface and one exact certificate. It does not
establish feasibility for every old-phase dictionary, admit higher outside
powers, or resolve unrestricted Erdős #7. All proofs and computations here
are ordinary mathematics and exact rational arithmetic, not Lean verification.

## The fixed source and complete debit

Use D={d:d|315}, outside lower primes P=(11,13,17,19,23), and the full
eleven core and five eleven-slot singleton old-phase dictionaries of758.
Each phase belongs to one original numerical modulus and stays fixed
across every query. Let X be the actual core survivors. Put

    h_j(x)=sum_(e|315,e>1) 1_(x=b_(j,e) mod e),
    ell_j(x)=P_j-1-h_j(x),
    X+={x in X:ell_j(x)>0 for every j}.

Every row law u is nonnegative, nonzero and supported on X+. Actual
singleton root sets A_j(x) satisfy |A_j(x)|>=ell_j(x). As in758, the law
with old marginal u is uniform on the actual product of these root sets
conditional on x. Counts of labels need not equal distinct root deletions.

For d|315 and J subset{1,...,5}, write

    Z_(d,J)(u)=max_(a mod d) sum_(x in X+,x=a mod d)
                         u_x/product_(j in J)ell_j(x),
    kappa(d)=product_(p in {3:9|d;5:5|d;7:7|d}) p/(p-1)-1,
    beta_(d,J)=kappa(d)+1_(|J|>=2),
    C(u)=sum_(d,J) beta_(d,J) Z_(d,J)(u).

The positive margin sum u-C(u) pays all shallow multioutside originals
and the complete arbitrary-height core3/5/7 tails. This payment theorem
is reused from758; it is not re-established from the example alone.

## A scaled single-axis upper envelope

Choose positive scales s_j. For 1<=k<=5 define

    Y_(d,j,k)(u)=max_(a mod d) sum_(x in X+,x=a mod d) u_x/ell_j(x)^k,
    A_(j,k)(s)=s_j^(k-1)/k * e_(k-1)((1/s_i)_(i!=j)),

where e_t is the elementary symmetric polynomial, e_0=1. Then

    C(u)<=Ctilde_s(u)
      :=sum_d kappa(d) Z_(d,empty)(u)
        +sum_(j=1..5,k=1..5) A_(j,k)(s)
             sum_d [kappa(d)+1_(k>=2)] Y_(d,j,k)(u).       (1)

To prove this, fix a nonempty J with k=|J|. AM-GM gives, pointwise,

    1/product_(i in J)ell_i(x)
      <=sum_(j in J) s_j^k/[k*product_(i in J)s_i] /ell_j(x)^k.

Multiply by u_x, sum in a fixed d-cylinder, then bound the maximum of
the sum by the sum of the corresponding maxima. All coefficients are
nonnegative. Finally sum over the subsets J containing j. Their
coefficients collect to A_(j,k)(s), proving(1). The empty subset remains
unchanged. No maximizing phases are claimed to coexist; these are upper
bounds on queries of the same law.

For s=(10,12,16,18,22), the coefficient matrix, with k across columns, is

| Axis | k=1 | k=2 | k=3 | k=4 | k=5 |
|---|---:|---:|---:|---:|---:|
|11|1|1955/1584|10675/14256|2125/9504|125/4752|
|13|1|2087/1320|133/110|9/20|18/275|
|17|1|1126/495|11168/4455|1984/1485|2048/7425|
|19|1|2307/880|2943/880|729/352|2187/4400|
|23|1|2387/720|34969/6480|9317/2160|14641/10800|

There are ten d with kappa(d)>0. Hence(1) uses ten empty-subset caps,
50 first-power caps and240 caps at powers2 through5, totalling300.
Each nonempty cap involves only one singleton dictionary; every cap
still uses the SAME u. Minimizing separate laws for separate axes is
not an application of(1).

The sufficient search target is Ctilde_s(u)<sum u. Failure of this
stronger condition does not refute feasibility of C(u)<sum u, much less
actual noncoverage. The fixed scales can be replaced by positive scales
depending on d and k before the coefficient collection; no improvement
from such optimization is asserted here.

## A literal common-source certificate

Use the nonunit divisor order

    (3,5,7,9,15,21,35,45,63,105,315).

The core phases and singleton OLD phases are

    core: (1,4,0,5,0,6,23,26,20,87,276),
    11:   (0,1,4,0,6,18,11,36,60,81,186),
    13:   (2,2,2,2,2,2,2,2,2,2,2),
    17:   (0,1,4,0,6,18,11,36,18,81,81),
    19:   (0,1,4,0,6,18,11,36,18,81,81),
    23:   (0,1,4,0,6,18,11,36,18,81,81).

The full actual core survivor set has74 rows. Their minimum denominator
vector is(1,1,5,7,11), so X+=X. Put u=0 on

    {2,11,38,81,107,110,125,137,186,218,260,291},

u=1 on

    {3,12,18,33,36,47,53,80,92,152,183,197,201,207,227,
     246,261,267,278,282,290,306},

and u=2 on the remaining40 rows. Then sum u=102. Direct exact evaluation
of the complete original372 slots gives

    C(1)/74 =122673875539055231/91684362715545600 >1,
    C(product_j ell_j)/sum_x product_j ell_j
            =547112609/516754128 >1,
    C(u)/102=353776946866374881/379127229607526400 <1.

The product-rule mass is32297133. These first two inequalities refute
universal success of those TWO rules for this sufficient envelope.
They do not rule out their actual-source success with sharper root
information. In particular the displayed u certifies feasibility here.

The single-axis cost for that very same u is

    Ctilde_s(u)/102
      =47292539850937617536238835637847876462092667791983
       /49706518301412129989142768215521526478274560000000
      <119/125<1.                                      (2)

The [literal input](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_single_axis_input.json)
contains only the old phases and weight labels. The certificate is uniform
over all singleton outside roots and all remaining shallow multioutside
phases. It admits arbitrary finite core heights and larger ordered
outside primes by758. Outside exponents are still at most one.

For an explicit numerical realization, set each pure outside class to
root1, and every mixed singleton class p_j*d to the unique CRT residue
with old phase b_(j,d) and outside root0. Together with the core these
are71 pairwise-distinct odd moduli. In this realization a positive hit
count deletes just ONE additional root: actual root minima are
(9,11,15,17,21). It realizes the phase dictionary, not equality in the
conservative label-count bound. All6142 individual row/root points are
checked directly against the numerical congruences.

For a density consequence using only the conservative certificate,
the maximum point-mass cap is D0=max_x u_x/product_j ell_j(x)=1/72930.
Thus758 converts(2) into Haar survivor density at least

    [102-Ctilde_s(u)]/[315*11*13*17*19*23*D0]
      =2413978450474512452903932577673650016181892208017
       /2236062345353230965246878352518828669074145280000000.

This bound applies to this fixed old dictionary and all of the extensions
just stated. It is not a lower bound for arbitrary old dictionaries.

## An exact marked interface for the single-axis moments

Let q=P_j-1 and f(h)=(q-h)^(-k). On 0<=h<q, finite Newton expansion gives

    f(h)=sum_(m=0..h) binomial(h,m) Delta^m f(0).

Only degrees m<=min(11,q-1) can occur here. In particular at p=11 the
coefficients at m>=10 are undefined and must NOT be included, even
multiplied by a zero row weight. The needed coefficients are positive:

    Delta^m f(0)=1/(k-1)! * integral_(0..infinity)
                   t^(k-1) exp(-qt) (exp(t)-1)^m dt >0

for m<q. This follows by the Laplace integral for an inverse integer
power and a finite binomial sum; convergence uses q-m>0.

For a subset T of the eleven singleton old labels, its simultaneous
congruences are either inconsistent or exactly one CRT cylinder
(L_T,c_T), with L_T=lcm(T)|315. For T empty take(L_T,c_T)=(1,0).
Let N_j(m,L,c) count consistent subsets giving that marked cylinder.
Then on the admissible support

    sum_(x=a mod d) u_x/ell_j(x)^k
      =sum_(m=0..min(11,q-1),L,c)
         Delta^m f(0) N_j(m,L,c)
         sum_(x=a mod d,x=c mod L) u_x.                 (3)

Indeed the sum of products of exactly m incident label indicators is
binomial(h_j(x),m); substitute this in the Newton identity. All marks
come from the literal phases of one dictionary. No independently chosen
row loads are introduced. There are sum_(L|315)L=624 possible cylinder
locations. At m=1, these data recover every original old phase, so the
FULL marked interface does not itself merge distinct complete labeled
dictionaries. Equation(3) supplies a different exact query representation,
not a proved compression of the phase search.

## Verification and remaining work

The [standard-library consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_single_axis.py)
reconstructs the core, all55 incidence lists, all71 numerical originals,
all372 and300 rational query maxima, the25 scale coefficients, both
failed-rule costs, the successful common-law costs, density conversion
and290 admissible Newton-domain identities. Its explicit checks survive
Python -O. The [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_single_axis.json)
must match complete recomputation, including every cap and a maximizing
phase. An independent integer-common-denominator implementation matched
every cap and reconstructed1850 marked row/power identities for this
dictionary, with the required degree truncation.

The immediate unresolved finite target is: for every actual core and
five singleton old-phase dictionaries, find ONE law with C(u)<sum u,
or produce actual phases and an exact dual witness that refutes this
sufficient method. The300-slot condition is an alternative stronger
target. More outside axes and arbitrary outside heights remain further
requirements of the unrestricted problem.
