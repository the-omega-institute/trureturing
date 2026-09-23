# A mixed split/common comparison survives every positive pair exclusion

This is an ordinary method obstruction with an exact finite certificate,
not a new Lean result and not a covering counterexample. It concerns the
auxiliary comparison of [report491](491-all-split-common-patterns-force-six-shallow-classes.md),
while the two endpoint regimes have separate noncoverage proofs.

Fix the normalized worst source type(2,4,1), references(2,7,3,4), first-root
splits at3,5,7 and common paths at11,13,17,19. Preserve each complete original
numerical label's global A/B choice. Common paths mean agreement through every depth queried by original later
labels, followed by fixed common auxiliary extensions. Original finite heights
and each full label's one selector are retained. Use the literal joint
six-anchor initial Haar measure and the cap-dominated split/common auxiliary
laws from report491. The source lower mass and caps are inherited from the
complete conditional source of [report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md),
with its attributed Schroeder inputs and verification boundary; see the
[library entry](../../../../../Library/Arith/schroeder2026nine.md). Let
eta denote this comparison measure and m7=7235955529/450000000000.

The independent audit proves existence of an auxiliary profile support U
with eta(U)>m7, upward for the paired factor order at7,11,13,17,19 while
holding3/5 factors fixed, containing no Q<20 profile, and satisfying K=0
for every pair in U. This is a counterexample to sufficiency of that auxiliary
measure, monotonicity, mass threshold and all positive-K pair exclusions.
It is not a realization by an actual original covering family or its source.
Additional original source exclusions, multi-point constraints or another
comparison can still resolve the original mathematical question.

## Literal selector count

A profile s=(s3,s5,s7,f11,f13,f17,f19) has signed factors+f=(f,1),-f=(1,f),
0=(1,1) at the first three coordinates and shared pair(f,f) at the others.
Let A_x and B_x be the two labelled boxes of old exponent vectors. Write
Q_x=|A_x union B_x|. For two points the same-selector capacity is

    N_xy=sum_d max(1_Ax(d)+1_Ay(d),1_Bx(d)+1_By(d)).

The Boolean identity, checked at all16 membership patterns, gives

    N_xy=Q_x+Q_y-|Ax intersection By|-|Bx intersection Ay|
         +sum(the four triple intersections)
         -2|Ax intersection Bx intersection Ay intersection By|.

Every triple or quadruple intersection has zero exponents at each of the
three split coordinates; at the common coordinates its size is
I=product min(f_p(x),f_p(y)). Therefore

    N_xy=Q_x+Q_y-I(crossA+crossB-2),

where crossA and crossB are the products of the three opposite-labelled
split-coordinate minima. This formula counts literal original-selector
capacity. It does not relabel centres to optimize each pair.

## Exact support and mass

The initial chart is the literal complement modulo675 of

    0 mod3, 1 mod9, 4 mod27, 0 mod5, 1 mod25, 2 mod15.

Its mass is221/675. At7 the auxiliary factor law has mass1-2C7/7 at(1,1)
and C7*6/7^f at each of(f,1),(1,f), f>=2. At each common prime p the law
has mass1-Cp/p at(1,1) and Cp*(p-1)/p^f at(f,f), f>=2. Here

    (C7,C11,C13,C17,C19)=(3/2,5/3,3/2,2,9/5).

The product law is only the upper comparator; actual-source independence
is neither needed nor asserted. In each initial CRT cell the reference-shell
masses are the exact Haar masses, so the complete chart retains the3/5
joint relation. The boundary references are(2,7,3,4).

The support consists of12705 of the20076 profiles with20<=Q<=38, together
with ALL profiles Q>=39. The full finite enumeration has23408 profiles
Q<=38, including3332 SAFE profiles Q<=19. Thus the overflow mass is evaluated
as the complete initial anchor mass221/675 minus the exact mass of ALL
Q<=38 profiles. No geometric tail is discarded.

The audit independently reconstructs the joint3/5 shell masses from the
literal six cylinders modulo675 and the geometric mass inside each reference
cell. It then multiplies the declared auxiliary split/common probabilities.
The result agrees exactly, as fractions, with the submitted support:

    eta(U)=0.016460221482737878...,
    eta(U)-m7=0.00038032030718232186...>0.

Each factor at7 has immediate successors0->+2,-2 or+f->+(f+1),
-f->-(f+1). Each common factor has successor f->f+1. All other coordinates
remain fixed. The audit checks every immediate successor of every finite
support profile:8098 successors remain in the declared finite support and
58698 enter Q>=39. These immediate steps generate the complete paired
partial order, so adjoining the full overflow makes U upward. This includes
zero-weight profile points; closure is not inferred only on positive mass.

## Every pair admits a zero witness

There are80702160 unordered distinct finite support pairs. The audit groups
by the two loads q,r and scans every pair with exact integer arrays. For
each of190 unordered load pairs it records the least literal N attained.
The scan performs90447447 integer pair evaluations including diagonals and
equal-load symmetry. Each recorded minimum is independently rechecked by
explicitly constructing its two literal divisor boxes and summing the max
of membership counts above. The code imports neither the producer, saved
graph nor an optimizer. Each generated coordinate factor is at most38;
the conservative bound4*38^7+76 on the scan arithmetic is below2^63.
The NumPy int64 products and minima are therefore exact, not floating point.

For every minimum(q,r,N), the audit constructs exact rational axis allocations
(a_x,a_y),(b_x,b_y) satisfying

    0<=a_i<=min(22,q_i),  sum_i a_i<=N,
    0<=b_i<=min(28,q_i),  sum_i b_i<=N.

The remaining two unnormalized fibre areas are

    R_i=(22-a_i)(28-b_i).

Each verified witness satisfies

    0<=R_i<=q_i, R_x+R_y<=N.

Choosing the available mixed deletion equal to R_i leaves zero objective.
Since the pair relaxation is nonnegative, its value K equals0. This argument
only verifies a feasible witness, and does not require any optimizer result
or proof that its search procedure finds a global optimum. For a larger N
the very same allocations remain feasible. The minimum-N checks therefore
cover all finite pairs at those loads, not merely the190 representative
pairs.

For overflow, the common unit label always contributes two to N, whereas
each other label in either inventory contributes at least one. Thus

    N>=max(Q_x,Q_y)+1.

Any pair of BAD profiles with one Q>=39 dominates(q,r,N)=(20,39,40), after
exchanging the two points if needed. A directly checked zero witness there is

    (a_x,a_y)=(20,20),
    (b_x,b_y)=(18,22),
    (R_x,R_y)=(20,12).

The witness remains feasible as any capacity increases, so all pairs touching
overflow have K=0 too. Reference paths of infinite valuation are null under
eta; their inclusion does not change the mass result.

Consequently no graph whose edges impose positive K on pairs of this
comparison space can exclude U. Adding more such edges, exact pair-clique
constraints or a sharper optimizer for this unchanged relaxation cannot
make the supremum of permitted support mass less than m7. This does not
apply to genuine three-point constraints, source-exclusion information, or
changes to the auxiliary measure.

## Reproduction and boundary

Run from the repository root, with NumPy available:

    python3 -I -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_split_pair_support_barrier.py

The consumer checks the adjacent certificate and compares its full generated
result with the retained JSON. It uses NumPy only for bounded exact integer
pair scans; all masses and feasible witnesses use Fraction. Unlike the
standard-library-only consumers, this command intentionally does not use-S.

The certificate stores the references, profile schema, finite support indices
and exact masses. Profile order is reconstructed by the consumer's explicit
Cartesian recursion, including zero-weight points. The result retains all190
minimum-N pairs, representative indices, rational zero witnesses, exact
support and overflow masses, and all upward-closure counts. Source mass/cap
inputs are content-pinned and checked against the same worst-source vertices.
No original source producer or Lean build is rerun by this consumer.

This obstruction does not supply jointly realizable23/29 phases or an actual
source support. The feasible zero witnesses can differ from pair to pair;
there is no claim that they arise from a single original family. That missing
joint requirement is a concrete next target. A true multi-point capacity
would retain the same selector at every point, for example

    N123=sum_d max(sum_i 1_Ai(d),sum_i 1_Bi(d)), i=1,2,3.

Such an inventory is not a clique inequality from the pair graph. Its full
axis and mixed-class budgets, and any useful positive lower bound, remain
separate proof obligations. Retaining further actual exclusions of this same
source is another option; exclusions from a differently optimized source
cannot be charged here.
