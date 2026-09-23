# 58. Adaptive initial-block recovery and an all-schedule budget obstruction

Consider the 154 distinct odd numerical moduli in the balanced-profile
head of [Chapter 57](57-balanced-depth-profile-and-degree-seven-frontier.md),
with its original twenty named prime-power coordinates and heights.
Keep every profile and every modulus, and change only four residues:

| Modulus | Old residue | New residue |
|---|---:|---:|
| 39 | 22 | 14 |
| 45 | 43 | 26 |
| 55 | 11 | 28 |
| 63 | 7 | 32 |

All other 150 residues stay fixed. The complete input is
[the complete fixed input](../frontier/source-budgets/adaptive_phase_head_input.json); its SHA-256 is
`1253b904f3f22348b304e5f45ea8478a4fd5df9885ca55ec70ef858bace35660`.
Every phase is fixed before sampling and is identical on every branch.

Let epsilon be the probability of hitting the union of these original
154 forbidden classes under a legal capped head law. Reuse the balanced
profile continuation constants

    C = 130197276585546949/250000000000000000,
    J = 617212231457700477699/62500000000000000,
    T = 326059/4.

The sufficient noncoverage score is

    S(epsilon) = epsilon + C + (J-1)/(T-1).

The denominator is T-1. Its head threshold is exactly

    eta = 29187881279576281900621/81513750000000000000000
        = 0.3580731015267520... .

## 1. Adaptive initial-block recursion

Permit adaptive coordinate selection only within the first five named
primes 3,5,7,11,13. Afterwards read all fifteen remaining head coordinates,
and then all tail primes, in numerical order. At every complete observed
transcript, conditional on choosing p, its row belongs to the original
nonempty compact polytope R_p of absolute p-adic cylinder caps.

For unread coordinates U and original labels A still compatible with the
full transcript, let V(U,A) be the least final head-union probability.
If A is empty it is zero. If a live label has no unread requirement it is
one. Otherwise

    V(U,A) = min_(p allowed next) min_(nu in R_p)
                 sum_z nu(z) V(U without p, Phi_(p,z)(A)).

The map Phi keeps precisely the unchanged original labels matching the
actual p-coordinate value z. During the initial block, every remaining
block prime is allowed next; after it, only the least remaining prime is.

Backward induction proves that this is an attained value. Compactness
attains each finite row minimum, and the conditional minimizing rows paste
into one probability law on full named tuples. Randomizing the next prime
cannot improve the minimum. Histories with equal (U,A) share the same
head objective and remaining row polytopes, which justifies caching this
value. Full sampled tuples must nevertheless be retained for later tail
kernels; the cache key is not claimed sufficient for every future query.

## 2. Exact comparison with every fixed order of this same block

For the four-change input, the adaptive five-prime value is

    epsilon_adaptive =
      37345911496927629364677605591855192391271703 /
      104396039896667873177065429687500000000000000
      = 0.3577330283207384... .

It gives

    S(epsilon_adaptive) =
      9073940023304367506173263496820691404782866391819 /
      9077026876935478236999484980468750000000000000000
      = 0.9996599267939864... < 1.

Now keep the same legal conditional-row choices but require the order of
these first five primes to be fixed before sampling. All 120 permutations
were evaluated exactly, always with the same numerical suffix. The best
prefix is 3,5,7,13,11, and its optimal head mass is

    epsilon_fixed =
      37672347347524656292537987560647626711914203 /
      104396039896667873177065429687500000000000000
      = 0.3608599271084715... .

Its score is 1.0027868255817196... > 1. Thus every fixed permutation of
this five-coordinate block fails this particular sufficient budget,
whereas an adaptive permutation of the same block passes it. The exact
advantage in both head mass and score is

    51386989468245088998092399652488677 /
    16433851223403049693359375000000000000 > 0.

This does not enumerate the fixed orders of all twenty coordinates and
makes no claim about the unrestricted twenty-coordinate adaptive optimum.
A score exceeding one is failure of this sufficient budget, not coverage.

## 3. Consequence with unrestricted large-prime tails

The four-change head, or any subset of its classes, together with any
finite family of further distinct odd numerical moduli whose largest
prime divisor is greater than 73, does not cover the integers. The tail
residues, supports and exponents are arbitrary. Numerical distinctness is
required for the entire combined family.

To apply the existing adaptive comparison and full-history continuation,
extend every head coordinate beyond its original height by independently
uniform higher digits. Keep the entire actual head tuple, and apply the
original numerical tail kernels. The resulting single joint law obeys
the same deterministic profile caps, so its charge and moment allowances
are bounded by the same C and J. Only its initial union loss changes.

A short rational certificate avoids reliance on decimal rounding:

    epsilon_adaptive < 17887/50000,
    C < 651/1250,
    J < 9876.

At the continuation cutoff B=16384, condition only on the single common
event S that avoids the charged classes. Its mass is strictly greater than
6073/50000. For each complete layout statistic L, the pointwise bound L>=1
and the same-law moment estimate give

    E[L^2 | S] <= 1 + (J-1)/mu(S).

The event and law are shared by all of these estimates.
Consequently the normalized second-moment bound is strictly less than

    Gamma < 1 + 9875/(6073/50000) = 493756073/6073,

while

    T - 493756073/6073 = 5132015/24292 > 0.

Equivalently the sufficient score is strictly below
3259523597/3260550000 < 1. The existing unrestricted-tail criterion
therefore supplies an uncovered residue. This is a fixed-phase head
result with unrestricted tails; arbitrary head phases and arbitrary
additional 73-smooth moduli remain outside this statement.

## 4. Why scheduling alone cannot recover the stronger D7 allowance

For any legal adaptive read-once head law and any named-coordinate
cylinder, the full-history caps imply

    mu(X_p=x_p for all p in A) <= product_(p in A) r_(p,H_p).

Proof is by induction on unread coordinates: reading outside A preserves
the remaining target event bound; reading p in A contributes at most its
cap. Randomized selections average these same bounds.

Use a separate numerical-order tree solely as a certificate describing
cylinders that cover the actual surviving tuples. At certificate depth k
with live original labels A, define

    U(k,A)=0                        if a live class is already satisfied;
    U(k,A)=1                        if A is empty;
    U(k,A)=min(1, r_(p_k,H_k) *
                   sum_z U(k+1,Phi_(p_k,z)(A))) otherwise.

A node either covers by its whole prefix cylinder or covers by the
recursive child cylinders. The global cap and union bound show that
U(0,all labels) bounds survivor mass for every sampling schedule. The
certificate order does not restrict that schedule.

For the four-change input the exact upper bound is

    mu(survivors) <=
      205194149227778634827603820897/306240236010156250000000000000.

Thus every admissible adaptive law has

    epsilon >=
      101046086782377615172396179103/306240236010156250000000000000
      = 0.3299569256439134... .

Let E7 be the unchanged exact balanced-profile allowance for smooth
labels outside the exponent core with each exponent at most five and
total degree at most seven. Its certified value is
0.0390094448119163... . Combining the exact fractions gives

    epsilon + E7 + C + (J-1)/(T-1)
      >= 1.0108932689290777... > 1

for every adaptive schedule. Hence scheduling alone cannot close this
stronger fixed-profile, fixed-allowance certificate. The conclusion is
about the stated bound: E7, C and J are upper allowances, not lower
bounds on actual losses. Sharper joint allowances or changed profiles
are not excluded. In particular this does not contradict the successful
baseline result in Section 3 or prove that the four-change head covers.

## 5. Reusable reduction when remaining constraints disconnect

For globally fixed labels, let W(U,A)=1-V(U,A) with arbitrary adaptive
read-once order. Suppose row polytopes are nonempty compact and depend
only on their named coordinate, with no shared budget or order constraint.
Handle a live label with empty remaining scope first: then W=0. Empty A
has W=1.

An unread coordinate absent from every remaining label scope can be
removed from this head optimization and sampled from any feasible row
later. It only supplies randomization, which cannot improve a maximum.

If the remaining nonempty label scopes split into disjoint connected
coordinate components (U_i,A_i), then

    W(U,A) = product_i W(U_i,A_i).

Induct on the number of unread relevant coordinates. Selecting p in
component i leaves all other component values unchanged. For every
outcome, the inductive hypothesis factors the continuation into the
local remaining value and those unchanged factors. Maximizing the row
and then the chosen coordinate gives at most the displayed product;
a locally optimal first coordinate attains it. The factors are
nonnegative, so zero values require no division. Sequential independent
component policies also attain the product.

This is factorization of optimal values, not independence of every
admissible law. Cross-component interleaving cannot improve it under the
stated conditions. History-dependent row constraints, shared budgets,
mandatory order constraints or cross-component objectives require their
own argument. All sampled coordinates remain available to tail queries.

## Verification and open scope

The adaptive five-axis value was independently recomputed using every
actual local leaf and every ancestor cap, without importing the candidate
row optimizer: 102,491 states and 7,851,685 leaf evaluations. A separate
integer-cap calculation verified all 120 fixed-prefix values exactly,
using the balanced-profile identity to deduce all proper ancestor caps
from terminal leaf caps. The mixed-cylinder bound was independently
replayed over 45,327 states and 3,427,615 actual local leaves. The independent
executables exit zero under `python3 -B -I -S -O`. The component factorization follows from the induction in Section 5.

These results are ordinary mathematics plus exact finite computations,
not new Lean declarations. They do not settle unrestricted Erdos #7,
a phase-uniform head bound, or the full twenty-axis adaptive optimum.


The [adaptive producer](../frontier/source-budgets/adaptive_phase_head.py)
and [actual-leaf verifier](../frontier/source-budgets/verify_adaptive_phase_head.py)
retain their [exact result](../certificates/source_norms/source-budgets/adaptive_phase_head.json)
and [independent result](../certificates/source_norms/source-budgets/adaptive_phase_head_verification.json).
The [fixed-order producer](../frontier/source-budgets/adaptive_phase_fixed_orders.py)
and [independent integer-cap verifier](../frontier/source-budgets/verify_adaptive_phase_fixed_orders.py)
retain every one of the 120 values in the
[full table](../certificates/source_norms/source-budgets/adaptive_phase_fixed_orders.json)
and [independent table](../certificates/source_norms/source-budgets/adaptive_phase_fixed_orders_verification.json).
The [mixed-cylinder producer](../frontier/source-budgets/adaptive_phase_cylinder_dual.py)
and [actual-leaf verifier](../frontier/source-budgets/verify_adaptive_phase_cylinder_dual.py)
retain the [full bound](../certificates/source_norms/source-budgets/adaptive_phase_cylinder_dual.json)
and [independent bound](../certificates/source_norms/source-budgets/adaptive_phase_cylinder_dual_verification.json).

The continuation uses the complete, source-bound
[balanced tail certificate](../certificates/source_norms/source-budgets/balanced_profile_tail_budget.json)
and [exponent-frontier certificate](../certificates/source_norms/source-budgets/balanced_profile_exponent_frontier.json).
Its common-law comparison is the result of
[Chapter 55](55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md);
the cylinder-cover weak dual is proved in
[Chapter 56](56-exponent-frontiers-and-cylinder-cover-certificates.md).
Every program above supports `--write` and `--check` under
`python3 -B -I -S -O`; the fixed-order and cylinder verifiers read complete
semantic certificates through the report's canonical IO.
