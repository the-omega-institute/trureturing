# Four new primes at arbitrary finite heights from one mixed-moment carrier

Let

    L0 = 315 * 11 * 13 * 17 * 19 * 23.

Consider any finite family of distinct nonunit numerical congruence moduli
that divide

    L0 * q1^E1 * q2^E2 * q3^E3 * q4^E4,

where the four new primes are distinct, do not divide L0, and are ordered
so that q1 >= 29, q2 >= 31, q3 >= 37, q4 >= 41. All original phases are
arbitrary, but each is fixed once for the entire family. The actual
uncovered Haar density is at least

    1110198785825664533 / 18010359497054150553600 > 1/17000.     (FC1)

The heights E1,...,E4 are arbitrary finite nonnegative integers. The OLD
core restrictions remain v3 <= 2 and all other core exponents <= 1. This
is an ordinary mathematical proof with finite exact integer certificates
and independent implementations; it is not a new Lean verification or a
solution of unrestricted odd covering.

## 1. An improved cubic bound on the same actual head law

The [uniform pruned-head construction of Report725](725-one-common-shallow-carrier-admits-an-arbitrary-height-last-prime.md) produces one actual survivor set
E23 with its uniform law mu and

    Haar(E23) >= d = 104726/6084351,
    E_mu L^2 <= G2 = 2607189975/7283281                  (FC2)

for every complete old query L on the divisors of L0, including its unit
term. Query phases are freely chosen per numerical label and need not be
coherent. They are not identified with the actual original phases.

We improve the cubic query bound while retaining this SAME source. This
uses [the deletion-sensitive inequality (D2)](../../001-064/01-survivor-reduction.md#coupling-the-original-deletions-to-the-load-numerator), specialized to h(t)=t^3. Here is its input and proof.

Let S be one of the six canonical pruned survivor sets modulo 45 and
n = |S| in {16,17}. Set D0 = {3,5,9,15,45}. For an arbitrary complete
315 query, A and B denote its old and 7-containing complete 45 query
loads. Both have unit term and one cylinder per d in D0. Pure modulus 7
leaves six digits. At old point x, the actual original 7d classes delete
b(x) distinct remaining digits, so 0 <= b(x) <= 5. The head survivor
count is N = 6n - sum_x b(x), and its uniform law is the same actual
pruned315 law used for the square estimate.

Concentrating all nonnegative query increments at one live digit bounds
any increasing convex h by

    N E h(L) <= 5 sum_x h(A(x)) + sum_x h(A(x)+B(x))
                                      - sum_x b(x)h(A(x)).

Write A^up and B^up for the values sorted increasingly. Cubic rearrangement
implies

    sum_x (A(x)+B(x))^3 <= sum_j (A^up_j+B^up_j)^3.

For completeness, if a <= a' and b <= b', the difference between the
ordered and crossed pairings is

    (a+b)^3+(a'+b')^3-(a+b')^3-(a'+b)^3
      = 3(a'-a)(b'-b)(a+a'+b+b') >= 0.

Successively removing inversions proves the sorting bound. Define

    J3(A) = max_(old query B) sum_j (A^up_j+B^up_j)^3.

This bounds every actual paired query, without claiming that the sorted
pairing is itself an admissible query arrangement. To establish E L^3 <= g,
it therefore suffices to verify, for every old query A,

    5 sum_x A(x)^3 + J3(A)
      + sum_(d in D0) max_(cylinder C mod d)
                      sum_(x in S intersect C) (g-A(x)^3)_+
      <= 6n g.                                           (FC3)

Indeed, subtracting gN from the concentration numerator produces
sum_x b(x)(g-A(x)^3). Discard its negative summands, then use
b(x) <= sum_(d in D0) 1_(actual original d-cylinder)(x). The five
cylinder maxima in (FC3) bound the resulting positive terms. There is no
independence hypothesis on the original deletions or the two query blocks.

Enumerating every effective old query and every sorted query histogram
establishes the following six sufficient constants:

| Canonical shape | n | Old query layouts | Sorted histograms | Cubic upper g |
|---|---:|---:|---:|---:|
| Short root, same root / other column | 17 | 4760 | 170 | 19573/256 |
| Short root, other root / same column | 17 | 4760 | 135 | 19063/256 |
| Short root, other root / other column | 17 | 4760 | 179 | 19063/256 |
| Long root, same root / other column | 16 | 4480 | 139 | 9643/128 |
| Long root, other root / same column | 16 | 4480 | 131 | 9671/128 |
| Long root, other root / other column | 16 | 4480 | 162 | 9671/128 |

There are 27,720 actual old query layouts and 141,892 ordered pairs of
sorted histograms. Missing, inactive or empty-cylinder query slots can
first be completed upward to nonempty old cylinders; this increases the
actual nonnegative query load on S, so a bound for completed queries also
bounds the originals. The constant 19573/256 is thus a uniform cubic
upper bound on the existing pruned315 source. It is a sufficient bound,
not an assertion of sharpness for actual original families.

The producer checks (FC3) after clearing denominator 256, with minimum
scaled slacks (27,48,48,50,40,40). The independent checker uses histogram
counts and quantile coupling rather than sorted-value zipping, and direct
positive-cylinder sums rather than the producer's piecewise linear caps.
Its reduced-denominator slacks agree after rescaling. Both exit 0.

Now apply the same pure-prime product extension through 11,13,17,19,23.
The general kth-moment multiplier for a new prime p is

    1 + (2^k-1)/(p-1).

To verify it, split an enlarged query as A+B_z on the p-1 pure-live roots,
with sum_z B_z <= B for an old complete query B. For integer k >= 1,
nonnegative binomial terms give

    sum_z [(A+B_z)^k-A^k] <= (A+B)^k-A^k.

Together with (A+B)^k <= 2^(k-1)(A^k+B^k), the old kth-moment bound H
then gives H[1+(2^k-1)/(p-1)] after averaging the roots. For k=3 the
product multiplier through 23 is

    1077205/152064.

The relative mass retained by the one common actual mixed-deletion step
is at least

    delta0 = 1243487/13077504

for all six shapes. Restriction decreases every unnormalized nonnegative
query moment. Normalizing this SAME restricted source therefore gives

    E_mu L^3 <= G3
       = (19573/256)(1077205/152064)/delta0
       = 906617738995/159166336.                         (FC4)

The previously established square bound (FC2) remains valid on that exact
source. Cauchy-Schwarz and G2 < 19^2 also imply E_mu L <= 19. Thus all
mean, square and cubic estimates below apply simultaneously to ONE law mu.

## 2. Fifteen full-height fields and the actual carving interface

This specializes the [general finite-interface carving rule in Report728](728-one-common-shallow-source-supports-three-arbitrary-fresh-prime-heights.md) to four new coordinates.

For each nonempty new-prime support J subset I={1,2,3,4}, group all actual
numerical labels by exponent tuple e_j >= 1 and old cofactor d | L0.
At each exponent tuple, the old phases give a complete query L_(J,e).
Fill missing labels only for an upper bound; every present original
keeps its globally fixed phase. Put r_j=q_j-1 and define

    alpha_(J,e) = product_(j in J) r_j/q_j^e_j,
    C_J = sum_e alpha_(J,e) L_(J,e)
                        + (1-sum_e alpha_(J,e)).          (FC5)

The finite exponent rectangle has total geometric weight at most one.
The last term is constant-1 padding of this bound, not a new original
congruence. Jensen on the same mu yields, for each of the fifteen fields,

    C_J >= 1,
    E C_J <= 19,  E C_J^2 <= G2,  E C_J^3 <= G3.          (FC6)

All fifteen fields are allowed to be correlated. No separate extremizing
source, product of old query fields, or independent phase choice is used.

Write A_i=C_{i}. Conditional on an old point, let U_i be the ACTUAL unary
survivor set in the i-th new coordinate and let R_i be its Haar mass.
The unary geometric charge gives R_i >= l_i=(1-A_i/r_i)_+. Define

    nu_i = (l_i/R_i) Haar restricted to U_i, if R_i>0;
    nu_i = 0,                              if R_i=0.

This is a Haar-dominated submeasure of exact mass l_i. Fractional weights
are permitted on finite atoms; no subset of a prescribed cardinality is
asserted. Take their product at the same old point. A mixed original with
new support J sees all complementary coordinates as free, so its complete
height inventory costs at most

    [C_J / product_(j in J) r_j] product_(i notin J) l_i.

After deleting all actual mixed originals, this ONE carved and restricted
submeasure has mass at least

    Psi = [product_i l_i
           - sum_(J subset I, |J|>=2)
               [C_J/product_(j in J)r_j]
               product_(i notin J)l_i]_+.                (FC7)

It is supported on actual total avoidance and still dominated by the
new-coordinate Haar law. Carving is essential: a lower bound for unary
survivor mass could not otherwise be multiplied into an upper deletion
charge.

For fixed other coordinates, the bracket in (FC7) is h*l_i-k with k>=0.
Its positive part is nondecreasing in l_i: if h>=0 this is direct, and
if h<0 it vanishes on l_i>=0. Decreasing a negative charge coefficient
also increases Psi. Consequently (FC7) is nondecreasing in every capacity
r_i, with the numerical fields C_J fixed. Each actual family's fields
satisfy (FC6), even though their defining weights depend on its primes.
Thus a pointwise comparison at those fixed numerical field values reduces
all the allowed primes to

    (r_1,r_2,r_3,r_4) = (28,30,36,40).

Set m_i=r_i-1, so m=(27,29,35,39), and

    u_i=(r_i-A_i)_+,  P=product_i u_i,
    Q=sum_(i<j) C_ij product_(k notin {i,j})u_k,
    H=sum_i C_(I minus {i}) u_i + C_I,
    W=[P-Q-H]_+.                                         (FC8)

The constructed conditional submeasure has mass at least
W/(28*30*36*40). Note 0<=u_i<=m_i by A_i>=1.

## 3. Quadratic pair costs and linear higher-support costs

Put

    Dpair = sum_(i<j) u_i^2 u_j^2,
    Hbar = sum_i m_i C_(I minus {i}) + C_I.

The coefficient squares of the six pair charges in Q are precisely the
six summands of Dpair, with complementary-pair indexing. Cauchy-Schwarz
therefore gives sum_(i<j) C_ij^2 >= Q^2/Dpair when Dpair>0. Also Hbar>=H
and H+W>=max(P-Q,0).

For any kappa>0 define the complete scalar envelope

    Phi_kappa(P,D) = min_(q>=0) [q^2/D + kappa(P-q)_+]
                  = max_(0<=t<=kappa) [tP-D*t^2/4]
                  = P^2/D,                 if 2P<=kappa*D,
                    kappa*P-kappa^2*D/4,   if 2P>=kappa*D.

For D>0 the minimum is attained at q=min(P,kappa*D/2); the dual maximum
is attained at t=min(kappa,2P/D). These direct optimizations prove the
displayed formulas without a minimax assumption. In our application D=0
implies P=0; set Phi_kappa(0,0)=0. Choose kappa=1/8. Then

    sum_(i<j) C_ij^2 + (1/8)Hbar + (1/8)W
       >= Phi_(1/8)(P,Dpair),                            (FC9)

where the two branches are P^2/Dpair when 16P<=Dpair and
(32P-Dpair)/256 otherwise. This covers all zero-coordinate boundary cases.
The proof deliberately relaxes actual constraints on the higher-support
fields, so it does not claim an extremizing relaxed field collection is
jointly realizable.

## 4. An exact inequality over all real unary loads

For all real A_i>=1, the exact interval certificate proves

    A1^3+(4/5)A2^3+(1/2)A3^3+(1/3)A4^3
       + Phi_(1/8)(P,Dpair) >= 18000.                    (FC10)

If any A_i>=r_i, the weighted cubic sum alone is at least
640069/30 > 18000. It suffices to cover the closed rectangle
[1,28] x [1,30] x [1,36] x [1,40].

The crucial enclosure property is coordinatewise monotonicity in u_i of
the COMPLETE envelope, including both branches. Fix the other coordinates
and write P=a*u and Dpair=b*u^2+c, with a,b,c>=0. The dual formula above,
after the substitution v=t*u when u>0, gives

    Phi_kappa(a*u,b*u^2+c)
      = max_(0<=v<=kappa*u)
            [a*v-b*v^2/4-c*v^2/(4u^2)].

As u increases, the feasible interval expands, while each fixed feasible
v has a nondecreasing objective. Therefore the maximum is nondecreasing.
At u=0 the envelope equals zero, and it is nonnegative for u>0; this proves
coordinatewise monotonicity on the full nonnegative orthant. No derivative
or omission of the linear branch is needed.

For a dyadic cell of denominator h=2^depth, with lower unary numerators
(a,b,c,e), write

    A1 in [a/h,(a+1)/h], ..., A4 in [e/h,(e+1)/h],
    U=(28h-a-1,30h-b-1,36h-c-1,40h-e-1),
    n=product_i U_i,
    m=sum_(i<j) U_i^2 U_j^2,
    Q0=30a^3+24b^3+15c^3+10e^3.

The unary cubic terms are bounded below at the lower unary corner. The
envelope is bounded below by evaluating P and Dpair at the SAME lower
u-corner. At that corner P=n/h^4 and Dpair=m/h^4, so the regime comparison
is exactly 16n<=m. A certified lower bound for the entire cell is

    [m*h*Q0 + 30n^2]/[30m*h^4],      if m>0 and 16n<=m,
    [256h*Q0+30(32n-m)]/[7680h^4],   if m>0 and 16n>m,
    Q0/(30h^3),                     if m=0.             (FC11)

The initial 27*29*35*39 = 1,068,795 unit cells cover the whole rectangle.
Accept a cell if (FC11)>=18000 by exact integer cross multiplication;
otherwise replace it by all sixteen dyadic children. Both implementations
finish at maximum depth 3 with 14,576,283 processed nodes. Their counts
by depth agree exactly:

| Depth | Visited cells | Accepted leaves |
|---:|---:|---:|
| 0 | 1068795 | 981096 |
| 1 | 1403184 | 1119276 |
| 2 | 4542528 | 4069917 |
| 3 | 7561776 | 7561776 |

There are 844,218 refinements. The exact checks verify

    sum_depth leaves_depth / 16^depth = 1068795,
    nodes = 1068795 + 16*844218.

Every refinement processes all sixteen children, and there are no pending
cells. These facts and the proved enclosure (FC11) establish (FC10) on
all real points of the closed rectangle, not merely sampled points.
Together with the exterior lower bound they prove the full assertion.

## 5. One expectation and the actual Haar bound

Add the weighted unary cubes to (FC9) and apply (FC10). Taking ONE
expectation on mu and using (FC6) gives

    (1/8) E W >= 18000 - (79/30)G3 - 6G2 - (131/8)*19,

because the cubic weights sum to 79/30 and sum_i m_i+1=131. The exact
upper cost is

    (79/30)G3 + 6G2 + (131/8)*19
       = 683586565221409/39154918656
       < 18000.

Consequently

    E W >= 21201970586591/4894364832 > 0.                (FC12)

The conditional carved survivor submeasure is dominated by the new
coordinate Haar law at every old point. The uniform old survivor law mu
has density at most 1/d relative to old Haar by (FC2). Combining the two
therefore gives an actual survivor measure of density at most 1/d relative
to global Haar. Multiplying it by d makes it Haar-dominated without
changing its actual support. Hence the true uncovered Haar density is at
least

    d * E W / (28*30*36*40)
      = 1110198785825664533/18010359497054150553600,

which proves (FC1). All exponents, actual phases, numerical labels and
fifteen query fields stayed on the same actual family and source.

### The inherited cubic bound already suffices for positivity

For comparison, the existing same-source increasing-convex comparator
gives G3old=94428228722435/16149165669. Using this in the SAME certified
envelope, without the new head cubic calculation, yields

    (79/30)G3old + 6G2 + (131/8)*19
      = 283756897702608515/15890779018296 < 18000,
    E W >= 2277124626719485/1986347377287,
    Haar(avoidance)
      >= 23847415365782478611/1461878367426514082747520 > 0.

Thus the complete pair envelope already proves four-prime positivity in
the old fifteen-field moment model. The new same-source cubic estimate
strengthens the quantitative density from about 0.0000163129 to about
0.0000616422; it is not necessary for the existence claim. Both variants
retain the same shallow old-core restrictions and arbitrary finite new
prime heights.

## Certificate scope

The [cubic consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_head_cubic.py)
checks the six fixed sufficient bounds against all effective old queries
and all sorted histogram pairs; its [result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_head_cubic.json)
records the exact integer slacks. An independent implementation uses
histogram-count quantile coupling and direct positive-cylinder sums.

The [four-dimensional consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_four_fresh_heights.py)
pins and replays both the actual-carrier construction and this cubic
calculation. It checks the complete real-domain enclosure with both
branches of Phi_(1/8), then reconstructs both rational budgets and density
bounds. Its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_four_fresh_heights.json)
is reproduced under `python3 -I -S -B -O`. A second integer implementation
has independently reproduced all node counts, leaves, volume and the
inherited-cubic budget and density.

Canonical six-shape pruning and the uniform shallow23 carrier are inherited
ordinary mathematical inputs. Rearrangement, moment transport, finite-height
averaging, carving, pair-cost minimization, enclosure monotonicity and Haar
domination are justified above. These checks are not Lean verification.
No optimum, literature-priority, unrestricted old-core height or unrestricted
odd-covering conclusion is claimed. The earlier seven/eight-prime full-height
results remain prior results, as attributed in Report725.
