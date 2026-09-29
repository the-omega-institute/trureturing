# Three new full-height primes from one core source and mixed moments

Let

    L0=315*11*13*17*19*23.

Consider any finite family of distinct nonunit congruence moduli dividing

    L0*q1^E1*q2^E2*q3^E3,
    q1>=29, q2>=31, q3>=37,

where the three new primes are distinct and not inL0. Every original phase
is arbitrary but fixed once for the entire actual family. Then the actual
uncovered Haar density is at least

    3207884069503261/641174722555488632784
       >1/200000.                                      (TC1)

The new prime heightsE1,E2,E3 are arbitrary finite integers. The OLD core
restriction remainsv3<=2 andv5,v7,v11,v13,v17,v19,v23<=1. This is an ordinary
proof with an exact finite interval certificate. It is not new Lean
verification, and it does not settle unrestricted odd covering.

## 1. The square and cubic bounds are on the same actual carrier

Use the [common pruned-head construction in Report 725](725-one-common-shallow-carrier-admits-an-arbitrary-height-last-prime.md), underlying the uniform shallow23 carrier. For every actual old core family, it constructs ONE setE23 of
actual old survivors with uniform lawmu and

    Haar(E23)>=d=104726/6084351.                        (TC2)

We require two simultaneous complete-query moment bounds on THISmu:

    E_mu L^2<=G2=2607189975/7283281,
    E_mu L^3<=G3=94428228722435/16149165669.             (TC3)

Here a complete old query has one freely chosen phase at every numerical
divisord|L0, including the unit term1. The phases of different query labels
need not be coherent.

The first bound is the already established six-shape square extension.
The second follows from the SAME head source, as follows. In
[Report 1, A single improved full comparator](../../001-064/01-survivor-reduction.md#a-single-improved-full-comparator) gives increasing-convex domination, under the
one uniform pruned315 law, by the probabilityX with atoms

|x|1|2|3|4|5|6|8|12|
|---|---:|---:|---:|---:|---:|---:|---:|---:|
|P(X=x)|581/6966|3031/6966|146/1053|425/2106|10/1443|45/481|1/37|1/74|

Becausex^3 is increasing and convex on the nonnegative range,

    E L^3 <=E X^3=87660407/1116882                     (TC4)

on that very same uniform pruned head law. The source explicitly permits
its direct square bound and full comparison profile to be used together.
No cubic-optimized source is substituted.

The punctured-product moment step works for every integerk>=1. Append a
primep on itsp-1 pure-live first roots. Write an enlarged complete query as
A(x)+B_z(x), withA andB=sum_z B_z bounded above by legitimate old complete
query loads. For nonnegative increments,

    sum_z [(A+B_z)^k-A^k] <=(A+sum_z B_z)^k-A^k.

This follows by expanding the polynomial: for eachj>=1,
sum_z B_z^j<=(sum_z B_z)^j. Thus if both old queryk-moments are at mostH,

    E (A+B_z)^k
       <=(1-1/(p-1))E A^k+(1/(p-1))E(A+B)^k
       <=H[1+(2^k-1)/(p-1)],                          (TC5)

using(A+B)^k<=2^(k-1)(A^k+B^k). For k=3 andp=11,13,17,19,23, the product
factor is

    product_p [1+7/(p-1)]=1077205/152064.              (TC6)

The common source BEFORE mixed shallow deletion is the uniform pruned head
times these five pure-live root laws. Its remaining actualE23 mass is at
leastdelta_i for shapei. The six simultaneous relative-mass bounds are

    1243487/13077504,
    7609619/64627200, 7609619/64627200,
    39317/253440,
    123881/887040, 123881/887040.

Their minimum isdelta0=1243487/13077504. Restricting by all actual mixed
shallow originals decreases each unnormalized nonnegativeL^k integral.
After normalizing that ONE restricted law, (TC4)–(TC6) therefore give

    G3=(87660407/1116882)*(1077205/152064)/delta0.

The corresponding shape-specific square computation gives the statedG2
uniform ceiling. These numerical maxima are bounds on moments of the
same lawmu for each actual family; they do not select separate sources.

The exact checker reconstructs this arithmetic and the inherited comparison
law's probability table. It does not claim to reprove the earlier universal
head domination theorem or its complete finite profile certificate.

## 2. Seven complete height inventories on that one old source

For every nonempty new-prime supportJ subset{1,2,3}, group actual numerical
labels by their exponent tuplee_j>=1 and old cofactor d|L0. At each fixed
tuple, all old phases define a complete old queryL_(J,e), includingd=1 for
the pure new-prime cofactor slot. Missing labels may be filled for an upper
bound; every present original retains its one globally fixed phase.

Putr_j=q_j-1 and define the finite geometric weights

    alpha_(J,e)=product_(j in J) r_j/q_j^e_j.

Their sum over the finite exponent rectangle is at most1. Define the ONE
height-averaged query field

    C_J=sum_e alpha_(J,e) L_(J,e)
                          +(1-sum_e alpha_(J,e)).     (TC7)

The last term pads with the constant1. It is a conservative numerical
upper bound, not an added original congruence. All sevenC_J are functions
of the same old stateu and are allowed to be correlated. They satisfyC_J>=1
and, by Jensen's inequality on(TC7),

    E C_J^2<=G2,      E C_J^3<=G3.                    (TC8)

For unary supports writeA=C_{1}, B=C_{2}, D=C_{3}; use their cubic bounds.
For the other four supports writeC12,C13,C23,C123; use their square bounds.
No product assumption on these seven old query fields is made.

## 3. Carve actual unary submeasures before charging cross constraints

Condition on one old stateu and put independent Haar coordinates on the
three new prime powers. LetR_i(u) be the ACTUAL surviving Haar mass of the
i-th coordinate after all unary-support originals are removed. The complete
height charge from(TC7) gives

    R_1>=(1-A/r_1)_+,
    R_2>=(1-B/r_2)_+,
    R_3>=(1-D/r_3)_+.                                (TC9)

Letl_i be the corresponding right-hand side of(TC9). It is NOT valid simply
to replaceR_3 by its lower boundl_3 in an upper bound for a pair deletion.
Instead first carve a dominated measure of exactly the desired mass.
IfU_i is the actual unary surviving set andH_i is its coordinate Haar law,
define

    nu_i=(l_i/R_i) H_i restricted toU_i    ifR_i>0,
    nu_i=0                               ifR_i=0.

Since0<=l_i<=R_i, this has total massl_i, is supported on actual unary
survivors, and obeysnu_i<=H_i. This is valid even on a finite atomic space:
the weights may be fractional; no exact subset cardinality is assumed.

Take the productnu_1 timesnu_2 timesnu_3 at this same old stateu. Its mass
isl_1 l_2 l_3 and it is dominated by the new-coordinate product Haar law.
For a12-support original, the third coordinate is free, so its mass on this
carved product is at most its unrestricted12 Haar mass TIMESl_3. Summing
the complete actual12 height inventory therefore charges at most

    [C12/(r_1 r_2)] l_3.

Likewise charge13 and23 withl_2 andl_1. The full123-support inventory costs
at mostC123/(r_1 r_2 r_3), since the whole carved product is Haar-dominated.
Restrict this ONE carved product by all actual pair/triple originals. The
remaining submeasure is still Haar-dominated, is supported on all actual
avoidance, and has mass at least the positive part of

    F(l)=l_1 l_2 l_3
        -[C12/(r_1 r_2)]l_3
        -[C13/(r_1 r_3)]l_2
        -[C23/(r_2 r_3)]l_1
        -C123/(r_1 r_2 r_3).                         (TC10)

For comparison across new primes, F_+ is nondecreasing in eachl_i>=0.
Fix the other two variables. ThenF is an affine functionh l_i-k withk>=0.
Ifh>=0 its positive part is nondecreasing; ifh<0 it is identically zero on
l_i>=0. This supplies the needed monotonicity despite the negative terms.

The normalized lower bound is also nondecreasing as anyr_i grows: its
arguments(1-C_i/r_i)_+ increase, while every negative coefficient containing
r_i decreases. The preceding coordinate monotonicity then applies.
This comparison holds the seven numerical field values fixed. The actual
geometric weights in(TC7) depend on the chosen primes, but for each fixed
actual family its resulting seven fields satisfy the same moment bounds;
one may apply this pointwise capacity comparison to those field values.
No claim is made that the actual fields stay unchanged when primes change.
Therefore allq1>=29,q2>=31,q3>=37 reduce to the baseline capacities

    (r_1,r_2,r_3)=(28,30,36).

Set

    u=(28-A)_+, v=(30-B)_+, w=(36-D)_+,
    W=[uvw-C12*w-C13*v-C23*u-C123]_+.                 (TC11)

The constructed Haar-dominated conditional submeasure has mass at least
W/(28*30*36). Product structure has only been used for the three carved
unary measures before pair/triple deletion, conditionally on the same old
state. The final restricted measure need not be a product.

### The same carving interface for any finite number of new primes

The construction is not specific to three axes. For any finite new-prime
index setI, define all nonempty-supportC_J by the finite geometric averaging
and constant1 padding of(TC7). Putr_i=q_i-1 and

    l_i=(1-C_{i}/r_i)_+.

Carve each actual unary survivor coordinate to massl_i as above, and take
their one product. For an original whose new-prime support is exactlyJ,
all coordinates outsideJ are free. Its aggregate full-height charge on this
carved product is bounded by

    [C_J/product_(j in J)r_j] product_(i notin J)l_i.

Consequently the one actual supported, Haar-dominated submeasure retains
at least

    Psi=[product_(i in I)l_i
          -sum_(J subset I, |J|>=2)
             (C_J/product_(j in J)r_j)
             product_(i notin J)l_i]_+.              (TC11a)

AllC_J are functions on the SAME old source, one field per complete
numerical cofactor/height inventory. Fixing the otherl variables makes the
expression inside the positive part affinehl_i-k withk>=0, soPsi is
nondecreasing in everyl_i. It also increases when a nonnegative deletion
coefficient decreases. Thus the normalized lower response is monotone in
each new prime capacityr_i, with the original joint fields held fixed.

Equation(TC11a) is a general finite interface, not a universal positivity
claim. Its higher-support fields and shared-source relations must still be
bounded sufficiently to prove a positive expected response; a collection
of separately optimized fields or source laws cannot replace them.

## 4. Reduce four quadratic variables to three continuous variables

Write

    P=uvw, R=u^2+v^2+w^2+1,
    Q=C12*w+C13*v+C23*u+C123.

Cauchy–Schwarz gives

    C12^2+C13^2+C23^2+C123^2>=Q^2/R.

SinceQ>=0, minimizingQ^2/R+3(P-Q)_+ gives

    phi(P,R)=P^2/R          if2P<=3R,
             3P-9R/4       if2P>=3R.                 (TC12)

Indeed its minimizer isQ=P in the first regime andQ=3R/2 in the second.
Thus, pointwise,

    A^3+B^3+D^3
      +C12^2+C13^2+C23^2+C123^2+3W
      >=A^3+B^3+D^3+phi(P,R).                        (TC13)

This relaxation ignores the lower boundsCij,C123>=1, which can only make
the bound weaker. It does not assume that a minimizing quadratic vector
comes from an actual original family.

## 5. Exact interval certificate for the real-variable lower envelope

IfA>=28 orB>=30 orD>=36, the unary cubes alone are at least
28^3+1+1=21954. On the remaining rectangle

    A∈[1,28], B∈[1,30], D∈[1,36],

an exact finite interval calculation establishes

    A^3+B^3+D^3+phi(P,R)>=19000.                     (TC14)

Here is the complete enclosure rule. A dyadic cell has denominatorh=2^k
and lower numeratorsa,b,c:

    A∈[a/h,(a+1)/h], and similarly forB,D.

Set

    U=28h-a, V=30h-b, Z=36h-c,
    n=(U-1)(V-1)(Z-1),
    m=U^2+V^2+Z^2+h^2,
    s=a^3+b^3+c^3.

Within the cell, P>=n/h^3, R<=m/h^2, and the unary cube sum is at leasts/h^3.
The variational definition in(TC12) shows thatphi is nondecreasing inP and
nonincreasing inR. Consequently valid rational cell lower bounds are

    [m*h*s+n^2]/[m*h^4]       if2n<=3mh,
    [4s+12n-9mh]/[4h^3]      otherwise.               (TC15)

The checker starts with all27*29*35=27405 unit cells. A cell whose lower
bound is at least19000 is accepted; every other cell is split into all
eight dyadic children. Every comparison clears denominators and uses only
integers. The complete calculation finishes after446637 processed nodes,
at maximum depth5, with no unfinished cell. The accepted leaf counts by
depth are

    (25071,11701,39579,108426,162864,46592).

Their exact volumes sum to27405. Each refinement replaces its parent by
all eight children, and the checker verifies the corresponding node-count
identity as well. These facts plus(TC15) establish the whole closed domain,
not just isolated sample points. The exterior bound completes(TC14).

## 6. One expectation and the final density

Integrate(TC13)–(TC14) on the same old source using(TC8):

    3E W>=19000-3G3-4G2.

The exact moment budget is

    3G3+4G2=4187580088869535/220705264143
             <18973.631<19000.

Hence

    E W>=5819929847465/662115792429>0.                (TC16)

The new-coordinate carved and restricted submeasure is dominated by Haar
at each old state. The old source is uniform onE23, of density at most1/d.
The combined final submeasure therefore has density at most1/d relative
to global Haar and is supported on actual avoidance. Multiplying that
submeasure byd produces a measure dominated by Haar, still supported on
actual avoidance. The actual uncovered Haar mass is consequently at least

    d*(E W)/(28*30*36),

which is exactly(TC1). Every exponent, original phase, and query field has
remained on that one actual family and source throughout.

The earlier abstract three-axis second-moment obstruction does not contradict
this result. That abstraction used only separate first and second moments;
the present certificate additionally uses an inherited cubic bound and
keeps the actual pair-deletion charges multiplied by the opposite unary
survivor mass. No actual covering counterexample is inferred from the
failure of a weaker relaxation.

The [standard-library consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_three_fresh_heights.py)
pins and replays Report725's actual-carrier construction, reconstructs the
inherited comparator's moment arithmetic, and verifies the complete interval
cover using exact integers and fractions. Its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_three_fresh_heights.json)
is reproducible with `python3 -I -S -B -O`.

An independent breadth-first implementation evaluates each rational box
through the variational minimizer in(TC12), without importing this integer
formula or its output. It obtains the same node and leaf counts, full volume,
moment bounds and density. The minimum accepted interval margin is
452731/398051328, strictly positive.

The inherited head-profile theorem, complete moment transport(TC5), height
averaging(TC7), and actual-fibre argument(TC9)–(TC11a) are the ordinary
mathematical inputs detailed above. The checks are not new Lean verification.
The existing seven/eight-prime full-height noncoverage results remain prior
results as attributed in Report725; no literature-priority claim is made.
This larger-support conclusion retains the old core exponent restriction.
