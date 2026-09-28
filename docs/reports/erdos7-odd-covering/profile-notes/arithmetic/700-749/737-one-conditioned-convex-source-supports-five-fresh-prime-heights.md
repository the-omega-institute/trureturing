# Five arbitrary-height directions from the stop-loss source

This is an ordinary mathematical proof with an exact integer enclosure,
not a new Lean verification. Its source premise is the simultaneous
[same-source bounds of Report736](736-a-common-conditioned-convex-law-sharpens-the-same-source.md):

    E C_J <= G1 = 354870451028/26915276115,
    E C_J^2 <= G2 = 1940069387744/8971758705,
    E C_J^3 <= G3 = 31390970044192/6211217565.

Every C_J>=1 is a field on the SAME actual old survivor law mu.
The old carrier and exponents remain L0=315*11*13*17*19*23, v3<=2,
all other old exponents<=1, with Haar(E23)>=104726/6084351.
There is no fourth-moment premise in this bridge.

For a finite family of pairwise distinct nonunit numerical moduli dividing
L0*product_i q_i^E_i, where E_i are nonnegative integers and there are
five distinct fresh primes q1>=29,q2>=31,q3>=37,q4>=41,q5>=43,
arbitrary finite fresh heights and arbitrary globally fixed original
phases, the [existing finite-inventory carving argument](728-one-common-shallow-source-supports-three-arbitrary-fresh-prime-heights.md) gives a positive
uncovered Haar density at least

    3500552703183369329/97495699047118888902750 > 1/30000.

The old-height restrictions persist; this is not unrestricted Erdos #7.
All reductions use one source and the actual finite original inventory.

## 1. The five-direction scalar inequality

After the normalized carving response is compared monotonically in the
fresh capacities, set

    r=(28,30,36,40,42), m=r-1=(27,29,35,39,41),
    A_i=C_{i}, u_i=(r_i-A_i)_+,
    P=product_i u_i,
    Q=sum_(|J|=2) C_J product_(i outside J)u_i,
    H=sum_(|J|>=3) C_J product_(i outside J)u_i,
    W=(P-Q-H)_+.

Put

    D=sum_(|K|=3) product_(i in K)u_i^2,
    Hbar=sum_(|J|>=3) C_J product_(i outside J)m_i.

Complementation identifies the ten terms in D with the squared
coefficients of Q. Cauchy-Schwarz gives

    sum_(|J|=2) C_J^2 >= Q^2/D

when D>0. Also Hbar>=H and H+W>=(P-Q)_+. Hence, for kappa=1/250,

    sum_(|J|=2) C_J^2 + kappa Hbar + kappa W
      >= Phi_kappa(P,D),

where

    Phi_kappa(P,D)=max_(0<=t<=kappa)(tP-Dt^2/4)
                 =P^2/D,                    if2P<=kappa D,
                  kappa P-kappa^2 D/4,      if2P>=kappa D.

For D=0, P=0, so define Phi(0,0)=0. These formulas cover the full
positive-part domain, not only its quadratic branch.

Define the convex unary polynomial

    f(A)=(31/2)A1^2+(7/10)A2^2
         +(13/25)A1^3+(89/100)A2^3+(1/2)A3^3
         +(9/25)A4^3+(3/10)A5^3.

The exact enclosure establishes, for ALL real A_i>=1,

    f(A)+Phi_(1/250)(P,D) >= 19700.                 (E)

It does not assume A_i are integer, that a queried field is independent
of another field, or that extrema from different source laws coexist.

## 2. Why the finite enclosure covers the continuous domain

If any A_i>=r_i, the unary polynomial alone is at least

    min_i [w2_i r_i^2+w3_i r_i^3
                 +sum_(j!=i)(w2_j+w3_j)]
      =2224487/100>19700.

It remains to cover the closed five-dimensional box product[1,r_i].
The producer starts from that entire box and repeatedly bisects its
longest side, on the exact grid of denominator512. Every split checks
both children. There is no random sampling in the final certificate.

Two exact lower bounds certify leaves.

First, f is coordinatewise nondecreasing. Phi is coordinatewise
nondecreasing in the u_i. To see the latter, fix the other coordinates
and write P=a u,D=b u^2+c with a,b,c>=0. For u>0 substitute v=tu:

    Phi=max_(0<=v<=kappa u)
             [a v-b v^2/4-c v^2/(4u^2)].

Increasing u enlarges the maximization interval and increases each
fixed-v expression. At u=0, Phi=0. Thus on A in[lo,hi],

    f(A)+Phi(r-A) >= f(lo)+Phi(r-hi).

The exact comparison uses both branches and the D=0 case.

When that lower bound does not suffice, use a stronger local bound.
Let c be the box center and choose any rational0<=t<=1/250; the
producer uses the center maximizer rounded down to a multiple of
1/256000. Convexity gives

    f(A)>=f(c)+grad f(c).(A-c)=ell_c(A).

Also Phi(P,D)>=tP-t^2D/4 by its variational definition. The function

    ell_c(A)+t product_i(r_i-A_i)
      -(t^2/4)sum_(|K|=3)product_(i in K)(r_i-A_i)^2

is concave in each A_i separately: ell_c is affine, the product term
is affine in each coordinate, and every affected D term has a
nonpositive quadratic coefficient. Successively taking endpoints in
each coordinate shows that its minimum over the box is achieved at
one of its32 corners. Checking all32 corners therefore gives a valid
full-box lower bound. This is not a joint-concavity claim.

All polynomial coefficients, t, corners and centers are rational. The
producer clears denominators and compares arbitrary-precision integers.
Its completed tree contains24,321 nodes and12,161 accepted leaves;
10,400 leaves use the tangent/corner bound,1,711 the quadratic bound,
10 the linear bound and40 the D=0 bound. The maximum depth is23.
The exact sum of leaf volumes is43,820,595, the full box volume, and
nodes=2*leaves-1. Thus every point of the continuous box is covered.

The [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_five_fresh_heights.py)
pins and replays the Report736 source arithmetic, then recomputes the
whole continuous-domain enclosure and final rational budget. Its
[retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_five_fresh_heights.json)
contains the full tree counts and reserve. An independent implementation
uses denominator1024, a different dual mesh, left-endpoint tangents and
splitting by relative coordinate width. It certifies the same bound with
48,187 nodes and24,094 leaves, maximum depth25, and the same total box
volume. All its accepted corner slacks are strictly positive. Both
implementations use exact integer arithmetic throughout.


## 3. The single expectation and actual Haar conclusion

The sum of the quadratic weights of f is81/5; the sum of its cubic
weights is257/100. There are ten pair fields. The sum of all Hbar
coefficients is

    1+sum_i m_i+sum_(i<j)m_i m_j=11794.

Taking ONE expectation in(E) and in the scalar majorization yields

    (1/250) E W
      >=19700-(131/5)G2-(257/100)G3-(11794/250)G1.

The full expected cost on the right is exactly

    194558096999947588/10093228543125,

so

    E W >=8557010599229824/80745828345>0.

The actual carved submeasure is dominated by the fresh-coordinate Haar
law and has conditional mass at least W/product(r_i). Integrating over
the SAME uniform E23 source and multiplying by its actual Haar mass
lower bound gives the density stated above.

For larger actual primes, compare the normalized response

    [product l_i -sum_(|J|>=2)
             (C_J/product_(j in J)r_j)product_(i outside J)l_i]_+,
    l_i=(1-A_i/r_i)_+.

For a fixed coordinate it has the form(h*l_i-k)_+,k>=0, so it is
nondecreasing in l_i; increasing a capacity also decreases the relevant
negative charge coefficients. Thus the normalized response is
nondecreasing in every capacity with the numerical field values fixed.
Each actual family's fields satisfy the same moments, allowing the
fixed reference capacities above. This step compares the normalized
response, not W alone with an incorrectly fixed denominator.

At arbitrary finite heights, fields are finite geometric averages of
complete old queries with constant-one padding. Convexity transfers
all three simultaneous source moment bounds. The actual moduli and
phases are grouped once by their complete fresh support and exponent
tuple; no original is independently changed or repeatedly deleted.


The finite-height fields used above are explicitly

    C_J=sum_(1<=e_j<=E_j) alpha_(J,e)L_(J,e)
                           +(1-sum_e alpha_(J,e)),
    alpha_(J,e)=product_(j in J)(q_j-1)/q_j^e_j.

There are31 nonempty fresh supports. Each query L_(J,e) has one phase
per old numerical divisor, completed only for an upper bound. If a
coordinate height is zero, the relevant sum is empty and C_J=1; the
padding supplies no actual forbidden class. Unary survivors are carved
to exact masses l_i before mixed classes are deleted, so the displayed
complementary products multiply actual chosen masses. This preserves
the upper-bound direction of every deletion charge.

The earlier abstract selected-moment obstructions concern weaker caps.
They do not contradict this result: the new common source comparison
adds constraints that those tables fail. The all-query cylinder
structure still defines the actual source, but the numerical first-three
bounds from Report736 are sufficient for this five-direction argument.
The unresolved task remains arbitrary old core heights and unrestricted
small-prime support; this theorem settles neither.
