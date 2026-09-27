# Complete weighted inventories do not realize one selector family

For four tested points,101 directions exactly describe every nonnegative
weighted Boolean-selector inventory budget. This completes the pointwise
inequalities, extending the three-point description in
[report498](498-ten-directions-completely-describe-three-point-weighted-budgets.md).
It still does not make a feasible budget vector realizable by one original
arithmetic family.

A finite original-label example makes this failure quantitative. For
every prime p>=7 and integer J>=1, consider exactly the distinct odd
moduli3p^j and5p^j,1<=j<=J, with one independently selected old residue0
or1 per complete numerical label and an arbitrary new-prime phase.
At four fixed old points, write t_i=(p-1) times the actual pure-p union
deletion fraction. Then

    max_(actual families) min_i t_i = 2/p-2/p^J,            (R1)

whereas the complete weighted finite-inventory relaxation gives

    max_(budget vectors) min_i t_i = 1-1/p^J.               (R2)

The exact gap1-2/p+1/p^J is positive. The relaxed optimum is even the
average of four actual family responses. This is an ordinary general
proof and an exact finite arithmetic countermodel to budget sufficiency;
it is not a covering counterexample, a new full-chart mass bound, or
Lean certification. The convex and polyhedral tools used below are
standard finite-dimensional mathematics.

## All four-point directions from a finite comparison arrangement

Let D be finite, A_d,B_d in{0,1}^4, and kappa_d>=0. Define

    N(w)=sum_d kappa_d max(w dot A_d,w dot B_d), w>=0.

Every comparison A_d-B_d belongs to{-1,0,1}^4. There are40 nonzero
normal vectors modulo multiplication by-1. Include all of them; the
four coordinate boundary planes are among these normals. For every
three linearly independent normals, compute their one-dimensional
kernel. If one orientation of that kernel is nonnegative, normalize
its integer generator to a primitive ray.

The9880 normal triples have9584 rank-three and296 dependent cases.
The3530 nonnegative kernel occurrences deduplicate to101 rays, grouped
by all distinct permutations of the following representatives:

| Representative | Number of rays |
| --- | ---: |
| 0001 | 4 |
| 0011 | 6 |
| 0111 | 4 |
| 0112 | 12 |
| 1111 | 1 |
| 1112 | 4 |
| 1113 | 4 |
| 1122 | 6 |
| 1123 | 12 |
| 1124 | 12 |
| 1223 | 12 |
| 1234 | 24 |

Call this set R4. For any real vector v,

    [w dot v<=N(w) for every w>=0]
      iff [r dot v<=N(r) for every r in R4].               (R3)

To prove the nontrivial direction, take a nonzero w>=0 and choose the
closed sign cone containing it, using the sign of every comparison
normal. Tied normals may be imposed as equalities. Intersect the cone
with sum_i w_i=1. This is a nonempty compact polytope. Every vertex of
the slice has three independent active homogeneous normals: otherwise
a nonzero perturbation preserving the active equations and coordinate
sum would keep both sufficiently small signed perturbations feasible,
contradicting extremality. Their common kernel is the vertex's ray,
which was included in R4. This argument also covers lower-dimensional
cones and coordinate faces.

Express w as a nonnegative combination of these vertex rays. On the
whole sign cone, each label has one common maximizing choice A_d or B_d;
ties cause no difficulty. Therefore N is linear on that cone. For
w=sum_j a_j r_j,a_j>=0,

    N(w)=sum_j a_j N(r_j),
    w dot v=sum_j a_j(r_j dot v)<=N(w).

The zero vector is immediate. This proves R3 for all nonnegative real
weights, including faces, missing labels, zero coefficients and an empty
D. Checking a sampled weight grid is not the completeness argument.
As in
[report501](501-complete-weighted-boundaries-cut-a-binary-obstruction.md),
R3 is pointwise: it does not justify minimizing each objective separately
and treating its minimizers as one common axis configuration.

## What the complete budgets actually retain

Put Z=sum_d kappa_d conv{A_d,B_d}, a Minkowski sum of segments. Its
support function is N. The full budget system is equivalent to

    v in Z-R_+^4,

or, explicitly, to the existence of beta_d in[0,1] such that

    v_i<=sum_d kappa_d[B_(d,i)+beta_d(A_(d,i)-B_(d,i))]
    for every i.                                         (R4)

One implication follows by dotting R4 with any nonnegative w. For the
other, Z-R_+^4 is closed and convex: Z is compact and the subtracted
orthant is closed. A separating linear functional for a point outside
this set must have nonnegative coordinates, since a negative coordinate
would make its supremum along a negative orthant ray infinite. Its finite
support value is then N(w), contradicting the assumed budget inequality.
Intersect with R_+^4 when nonnegative loss vectors are required.

Thus the representation retains a common continuous selector for each
label in a convex relaxation. It need not retain an actual binary
selector. Applied separately to different axis or mixed-deletion vectors,
R4 does not require their beta variables to coincide: the complete
numerical labels contributing to those sums are different. Neither
direction of R4 grants original-phase realizability.

## A literal finite arithmetic realization gap

Choose old centres A=0 and B=1 modulo15, and ordered old points

    x=(0,1,10,6) modulo15.

The two old numerical labels d=3,5 have membership vectors

    A3=(1,0,0,1), B3=(0,1,1,0),
    A5=(1,0,1,0), B5=(0,1,0,1).

For these labels,

    N(w)=max(w1+w4,w2+w3)+max(w1+w3,w2+w4).

The four binary selector pairs give activation-count vectors

    (2,0,1,1), (1,1,0,2), (1,1,2,0), (0,2,1,1).

Each misses one point. Their mean is(1,1,1,1), so that vector satisfies
all nonnegative weighted budgets. This is a literal same-source example,
not a table of independently chosen pointwise selectors.

Now fix p>=7 prime and J>=1. Include all2J original numerical moduli
3p^j,5p^j for1<=j<=J. They are pairwise distinct odd integers greater
than one. Each complete modulus has one residue whose old component is
selected from0 or1 modulo its old factor d; its residue modulo p^j is
arbitrary. These two components determine one original residue by CRT.
There are no additional old-only or other-cofactor classes in this model.

In the fibre of each old point, use uniform measure on Z/p^J Z and let
alpha_i be the union deletion fraction. Put t_i=(p-1)alpha_i. Summing
the exact finite geometric inventory gives

    c_J=(p-1)sum_(j=1..J)p^(-j)=1-p^(-J),
    w dot t<=c_J N(w), t_i<=p-1.                          (R5)

The vector v_J=c_J(1,1,1,1) satisfies every R5 inequality and the axis
cap. Conversely N(1,1,1,1)=4, so R5 implies min_i t_i<=c_J. This
proves the relaxed optimum R2. Using this finite c_J is essential:
the unscaled one-vector belongs to the full geometric envelope but not
to this finite total budget.

For any actual family, the two j=1 selectors leave one of the four old
points inactive for BOTH original labels. At that point all deletion
must come from j>=2. The union bound, irrespective of the new phases,
gives

    alpha_i<=2 sum_(j=2..J)p^(-j),
    t_i<=2/p-2p^(-J)=:tau_J.                              (R6)

For J=1 the sum is empty and tau_J=0. Missing labels can only decrease
the upper bound: assign an arbitrary virtual selector to any absent
j=1 label to choose an omitted point, without adding an actual deletion.
R6 already proves that v_J has no actual realization, since

    c_J-tau_J=1-2/p+p^(-J)>0.

## Sharpness and four actual families with the relaxed mean

Use new-prime phases p^(j-1) for3p^j and2p^(j-1) for5p^j. All2J
cylinders are disjoint. Different heights have different p-adic
valuations; at a common height the first nonzero digits1 and2 differ.
Hence union deletion is exactly the sum of activated cylinder measures.

If each d uses a fixed old selector across all heights, the four actual
families give c_J times the four activation-count vectors above. Their
mean is exactly v_J. Thus even the convex hull of actual family responses
contains the impossible target vector.

For the sharp construction, select A for both j=1 labels and B for all
j>=2 labels. With the same disjoint new phases the actual loss vector is

    (2(p-1)/p, tau_J, c_J, c_J).

Its minimum is tau_J. Together with R6 this proves the exact actual
optimum R1 for every stated p,J. The strict gap persists as J grows;
it is not solely a missing infinite tail.

The mechanism is a simultaneous integer choice at the first new-prime
level, with a finite bound on what later levels can repair. Additional
old cofactors can activate the omitted point, so R6 is not automatically
a new constraint for the full mixed chart. Connecting such joint
first-level restrictions to that chart's original labels and source
mass remains an open obligation. No conclusion about unrestricted
Erdos#7 follows from this restricted countermodel.

## Reproduction

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/four_point_weighted_inventory_realization_boundary.py

The standard-library consumer enumerates all normal triples with exact
integer determinants, retains101 ray witnesses, checks the four
three-dimensional boundary faces and all256 Boolean comparisons, and
reconstructs the literal CRT model. For p=7,J=3 it verifies the four
constant-selector families and the sharp family on the full new-coordinate
carrier, obtaining relaxed value342/343, actual sharp value96/343 and
gap246/343. The quantified p,J proof is the derivation above, not an
extrapolation from these checks. A default run checks the adjacent JSON.
