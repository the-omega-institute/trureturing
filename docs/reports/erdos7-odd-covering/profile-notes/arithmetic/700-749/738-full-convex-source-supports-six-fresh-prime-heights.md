# Six arbitrary-height fresh directions from the full convex-order source

Let L0=315*11*13*17*19*23. For any finite family of pairwise distinct
odd numerical moduli greater than1 dividing

    L0*q1^E1*q2^E2*q3^E3*q4^E4*q5^E5*q6^E6,

where the fresh primes are distinct, outside L0, and sorted with
q1>=29,q2>=31,q3>=37,q4>=41,q5>=43,q6>=47, the uncovered Haar density is
at least

    2699106184481030045171/53817625874009626674318000 > 1/20000.  (S1)

Every fresh height Ei is an arbitrary nonnegative integer. Original phases are
arbitrary and fixed once for the whole family. The old exponent limits
remain v3<=2 and every other exponent in L0<=1. This is an ordinary
mathematical proof with two distinct complete exact enclosure checks,
not a new Lean verification or a resolution of unrestricted Erdos #7.

## 1. The stronger source information needed here

Use the SAME actual uniform old survivor law mu from the pruned old
carrier, with Haar(E23)>=104726/6084351. The [conditioned convex-source result](736-a-common-conditioned-convex-law-sharpens-the-same-source.md) supplies ONE explicit17-atom comparator Y such that

    E_mu h(L) <= E h(Y)

for every complete old divisor query L and every increasing convex h.
The support of Y is

    {8,10,12,16,20,24,32,40,48,64,80,96,128,160,192,256,384}.

Its probability law is the already verified conditioned convex-source
law; source, phases and events are not separately reoptimized per h.
In particular,

    E Y=354870451028/26915276115,
    E Y^2=1940069387744/8971758705.

There are384 old positive divisor labels, including the unit. Hence
1<=L<=384 pointwise. The same bound also follows almost everywhere
from the full comparator via h(t)=(t-384)_+.

For each of the63 nonempty fresh supports J, group the actual originals
once by their full exponent tuple and old cofactor. Complete missing
query labels upward for an upper bound, retaining every present original
phase, and take the finite geometric average with constant-one padding:

    C_J=sum_e alpha_(J,e)L_(J,e)+(1-sum_e alpha_(J,e)),
    alpha_(J,e)=product_(j in J)(q_j-1)/q_j^e_j.

The rectangle of actual finite heights has total weight at most1.
If J includes an index whose height is zero, this sum is empty and
C_J=1. The constant-one padding is a comparison term, not an actual
additional congruence or a separately chosen phase.
Jensen on the SAME law, together with h(1)<=E h(Y), gives

    1<=C_J<=384,
    E_mu h(C_J)<=E h(Y)                                   (S2)

simultaneously for all63 fields and all the increasing convex penalties
used below. In particular, applying the transferred full convex-order
bound to h(t)=(t-384)_+ gives E_mu(C_J-384)_+=0, hence C_J<=384
mu-almost surely. This separately justifies the range required by the
restricted conjugate; it is not assumed merely from finite moments.
This is not restricted to height2 and introduces no actual
extra forbidden congruences.

## 2. A finite convex dual for the carving response

The [existing Haar-dominated fibre carving construction](728-one-common-shallow-source-supports-three-arbitrary-fresh-prime-heights.md) applies to six
coordinates. Monotonicity of its NORMALIZED response in each capacity
reduces to

    r=(28,30,36,40,42,46), m=r-1=(27,29,35,39,41,45).

Set

    A_i=C_{i}, u_i=(r_i-A_i)_+,
    P=product_i u_i,
    b_J=product_(i outside J)u_i,
    Q=sum_(|J|=2) b_J C_J,
    H=sum_(|J|>=3) b_J C_J,
    Hbar=sum_(|J|>=3) C_J product_(i outside J)m_i,
    W=(P-Q-H)_+.

Here Hbar>=H and H+W>=(P-Q)_+. Conditional actual survivor mass is at
least W/product(r_i), using a submeasure dominated by fresh Haar.

Let T={1} union support(Y), and let g be the piecewise-linear
interpolation of x^2 at the18 nodes of T. It is increasing and convex
on[1,384] and dominates x^2 there. Extending it linearly with its
endpoint slopes gives a global increasing convex function if needed
for the source theorem. Since C_J and Y have the established range,
the extension has no effect on their evaluations. Thus it satisfies

    E g(Y)=E Y^2.

Its restricted convex conjugate is the finite maximum

    g*(s)=max_(1<=c<=384)(s c-g(c))
         =max_(v in T)(s v-v^2).                         (S3)

Indeed, on each interpolation interval the maximized expression is
affine, so its maximum occurs at an endpoint. For every actual pair
field, g(C_J)>=s C_J-g*(s).

Fix kappa=1/5000. For every0<=lambda<=kappa,

    kappa W+sum_(|J|=2)g(C_J)+kappa Hbar
      >=lambda P-sum_(|J|=2)g*(lambda b_J).

This follows from kappa(H+W)>=lambda(P-Q), followed by the15 conjugate
inequalities. Therefore the left side bounds

    Psi(u)=max_(0<=lambda<=1/5000)
                [lambda P-sum_(|J|=2)g*(lambda b_J)].    (S4)

There are no quadratic-branch restrictions here. The finite conjugate
covers every u, including zero coordinates. At lambda0, every g*(0)=-1,
so Psi>=15.

## 3. Fixed nonnegative hinge penalties for the six unary fields

Define

    f_i(a)=(1/100)sum_t c_(i,t)(a-t)_+,
    f(A)=sum_i f_i(A_i).

The nonzero coefficient table is:

| i / threshold t | 8 | 10 | 12 | 16 | 20 | 24 | 32 |
|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | 12634 | 52898 | 34342 | 41801 | 0 | 0 | 0 |
| 2 | 15374 | 0 | 60271 | 58710 | 0 | 0 | 0 |
| 3 | 6885 | 0 | 24801 | 28063 | 34776 | 25472 | 0 |
| 4 | 6385 | 0 | 16214 | 19003 | 12339 | 49940 | 0 |
| 5 | 4735 | 0 | 15737 | 15922 | 7199 | 51748 | 0 |
| 6 | 0 | 5894 | 11911 | 11324 | 0 | 22024 | 52293 |

All coefficients are nonnegative. Their exact expected sum under Y is

    sum_i E f_i(Y)=72243007727020441/6055937125875.        (S5)

The complete continuous-domain enclosure proves

    f(A)+Psi(u)>=19000 for every real A_i>=1.            (S6)

This conclusion uses the full hinge budgets from(S2), not just the
first four moments. A counterexample to a selected-field four-moment
relaxation therefore does not contradict(S6).

## 4. Why the finite checks prove the all-real inequality

If any A_i>=r_i, monotonicity and nonnegativity of all f_j give

    f(A)>=min_i f_i(r_i)=1068457/50>19000.

This alone handles the complete exterior. The producer additionally
counts Psi>=15, giving1069207/50, but that extra15 is not needed.

It remains to cover the closed box product_i[1,r_i]. Both implementations
start with the full box and split boxes into two complete children.
On a box select a supporting affine function ell_i of the convex f_i,
and select any exact rational lambda in[0,1/5000]. Then

    f(A)+Psi(u)
      >=sum_i ell_i(A_i)+lambda product_i u_i
                    -sum_(|J|=2)g*(lambda b_J).          (S7)

The expression on the right is concave in EACH coordinate separately.
The affine support terms are affine; product_i u_i is affine in each
coordinate; b_J is either constant or affine in that coordinate; and
the negative of the convex g* composed with an affine function is
concave. It follows by successively choosing endpoints that the minimum
of(S7) on the box is attained at one of its64 corners. It is enough to
verify those64 rational values. Joint concavity is not asserted.

The main producer uses spatial grid denominator256, a4096-step lambda
grid, supporting lines active at each box center, and longest-side
bisection. Lambda is selected by integer comparisons; it need not be
the true continuous maximizer for(S7) to remain valid. Each conjugate
is evaluated at its exact maximizing node using the increasing secant
slopes v_j+v_(j+1). Every accepted corner inequality is checked after
clearing denominators with arbitrary-precision integers.

The main certificate contains134,159 nodes and67,080 leaves, maximum
depth36. Of these leaves,64,488 use64 corner checks and2,592 use the
simpler bound f(low)+15. The exact accepted volume equals the original
box volume1,971,926,775, and nodes=2*leaves-1 verifies the complete
binary subdivision structure.

The independent implementation also uses a valid monotone-profile lower
bound. Fix u1=u>0 and write P=a*u. For pair supports not containing1,
b_J=u*c_J; for pair supports containing1, b_J=d_J does not involve u.
Set v=lambda*u in(S4). Terms of the first kind have argument v*c_J,
and terms of the second kind have argument v*d_J/u. Each g* is
nondecreasing, since it is a maximum of affine functions of strictly
positive slopes. Increasing u therefore increases the expression for
each fixed v and enlarges its allowed interval[0,kappa*u]. Consequently
Psi is nondecreasing in u. At u=0, P=0 and every g*(lambda*b)>=-1,
while lambda0 attains15, so Psi=15. The same conclusion extends to
zero and to every coordinate. Thus f(low)+Psi(r-high) is a valid box
lower bound; a legal fixed-lambda evaluation may further lower Psi
without affecting validity.

The independent implementation uses spatial denominator512,8192 lambda
steps, left-endpoint supporting lines, and normalized-width splits
prioritizing active hinge locations. Its different tree contains63,175
nodes and31,588 leaves, maximum depth26. It independently verifies the
continuous box and the same exact budget and density. Thus the two
implementations do not merely replay the same stored leaf list.

The independent monotone-profile test also uses that Psi is nondecreasing
in each u_i. Fix u_i=u>0 and put v=lambda*u. The positive term is then
v times a fixed product. Pair terms whose pair omits i have the form
-g*(v*c); those whose pair includes i have the form -g*(v*b/u), with
b,c>=0 fixed. Since g* is nondecreasing (all its affine slopes are
positive knots), increasing u increases every fixed-v expression and
expands the allowed interval 0<=v<=kappa*u. At u=0, the maximum is15,
attained by lambda=0; all Psi values are at least15. Therefore this
boundary case also preserves monotonicity. The independent leaf bound
f(low)+Psi(r-high) is consequently valid on its whole box.

The canonical [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_six_fresh_heights.py)
embeds the rational coefficients and replays the pinned conditioned-source
arithmetic before checking every primary box. Its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_six_fresh_heights.json)
contains the fixed dual, node counts, exact budget and final density.
The inherited actual-source and carving statements remain ordinary
mathematical premises. Neither implementation is a Lean formalization.

## 5. One expectation, one carved submeasure, actual nonempty survival

The coefficients of Hbar sum to

    sum_(|K|<=3)product_(i in K)m_i=934878.

Taking one expectation under the same actual mu in(S2),(S4),(S6) yields

    (1/5000)E W
      >=19000-sum_i E f_i(Y)-15 E Y^2-(934878/5000)E Y.

The complete cost is

    2670385906653884932/151398428146875<19000,

hence

    E W>=1649473825093920544/242237485035>0.              (S8)

At every old point the actual unary carving and mixed deletion provide
a fresh-coordinate Haar-dominated surviving submeasure of mass at least
W/product(r_i). Finite summation over the uniform old survivor set gives
actual uncovered Haar density at least

    Haar(E23) E_mu W / product(r_i),

which is(S1). A positive submeasure on the finite CRT carrier has a
point in its support, and that point avoids every original congruence.
The density is an actual finite-period fraction, not a normalized live
mass silently equated with Haar probability.

For larger fresh primes, the relevant comparison uses normalized

    [product_i l_i
       -sum_(|J|>=2)(C_J/product_(j in J)r_j)
                           product_(i outside J)l_i]_+,
    l_i=(1-A_i/r_i)_+.

Holding the numerical field values fixed, this is nondecreasing in every
capacity. When all u_i>0, it factors as

    product_i(1-A_i/r_i)
      *[1-sum_(|J|>=2) C_J/product_(j in J)(r_j-A_j)]_+.

Both nonnegative factors are nondecreasing in each r_i. When any u_i=0,
the response is0; its nonnegative continuous extension gives the same
monotonicity across that boundary. Each actual family's fields satisfy
(S2), even though its finite geometric weights depend on its own primes.
Consequently the reference capacities used in(S6) give the stated bound
uniformly over all six allowed actual fresh primes and all finite heights.

## 6. Why the full convex interface has a finite exact description

Let T={1} union support(Y). For any real-valued field C>=1, the eighteen
hinge inequalities

    E(C-t)_+ <= E(Y-t)_+ for every t in T

are equivalent to increasing-convex domination by Y. Necessity follows
by choosing the hinges as test functions. Conversely, the cut at384
forces C<=384 almost surely. Interpolate any increasing convex h at
T by its secant polygon g. Convexity gives h<=g on[1,384], with equality
at each Y atom. This polygon is a constant plus a nonnegative multiple
of (x-1)_+ and nonnegative linear combinations of the internal hinges
(x-t)_+. The cuts imply

    E h(C) <= E g(C) <= E g(Y) = E h(Y).

Thus the finite hinge interface retains all increasing-convex tests;
it does not merely select a finite list of moments. Interpolating the
pair penalty at Y's own knots is especially useful: it strengthens its
pointwise value between knots while leaving its expectation on Y
unchanged. The common actual source and all63 field constraints are
still required. The finite interface does not assert independence or
realizability of an arbitrary list of marginal laws.
