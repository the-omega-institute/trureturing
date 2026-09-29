# Exact convex-query geometry on one pruned315 source

This result identifies a sufficient boundary for complete convex-query
readings on the actual pruned315 source: the17-vector of deleted live-root
counts. It also computes exact hinge envelopes conditional on the source's
own size and complete-query mean. It identifies the exact convex-response obstruction for six uniform
sources and the finite source groups used in subsequent source reweighting.
All statements are ordinary finite mathematics and exact computation,
not Lean verification.

## 1. The live-row argument keeps one actual source

Fix the first canonical45 survivor set

    S={x mod45: x!=0 mod3, x!=4 mod9, x!=0 mod5,
                 x!=1 mod15, x!=37 mod45}.

It has17 points. Exclude the actual or an auxiliary pure7 root, naming it0.
There are at most five remaining7-bearing original labels, with45 cofactors

    D={3,5,9,15,45}.

Every one deletes a cylinder C_d in S at ONE live7 root. If an original
is absent, has empty old cylinder, or uses the already excluded root0,
choose an auxiliary nonempty cylinder at one live root and delete it.
This merely chooses a smaller actual survivor source. It does not change
any original phase or purport to create a new distinct-modulus covering
family; auxiliary source restrictions may coexist with redundant originals.
All old comparison lemmas apply to this same additionally pruned source.

After this harmless source choice, each of the five labels uses one of
six live colors. Hence at least one live color y0 remains entirely untouched
above S. For x in S, let b(x) count its deleted live colors, and r(x)=6-b(x).
The actual source is uniform on its surviving cells, with

    N=sum_x r(x), 77<=N<=94,
    mu<=315/N Haar315.

No independence of deletion colors is assumed.

Every complete315 divisor query can be written as

    Q(x,y)=A(x)+sum_j 1_{C_j}(x)1_{y=a_j},

where A is a complete45 query with its unit term; the positive7 slots
have cofactors1,3,5,9,15,45. Their old phases and their7 phases are free
QUERY parameters. They are not the phases of the actual deleted originals.
Let B(x)=sum_j1_{C_j}(x), itself a complete45 query including its unit.
For increasing convex phi, define Delta(v)=phi(A+v)-phi(A). Convexity gives
Delta(v+w)>=Delta(v)+Delta(w) for v,w>=0, and monotonicity lets one include
query events on deleted rows. Therefore, pointwise at each fixed x,

    sum_(y survives at x) [phi(Q(x,y))-phi(A(x))]
       <=phi(A(x)+B(x))-phi(A(x)).

Place ALL positive7 query phases at the untouched row y0, keeping every
old phase unchanged. That is a legitimate query on the same actual source,
and it attains the displayed upper bound. Consequently

    max_query E_mu phi(Q)
      = (1/N) max_A [sum_x (5-b(x))phi(A(x))+J_phi(A)],
    J_phi(A)=max_B sum_x phi(A(x)+B(x)).                 (AQ1)

Here A and B range over genuine complete45 layouts on the SAME points x.
There is no reordering of B separately for different x. Equation(AQ1) is
an equality, not the sorted-histogram relaxation used in the prior D2 bound.

Thus b(x) is sufficient for this whole convex-query task. It need not be
sufficient for arbitrary future operations or other arithmetic interactions.
The untouched-row property is the condition allowing these colors to be
forgotten for the present task.

## 2. A finite exact actual-source catalogue

The effective old-cylinder inventories for D have sizes2,4,5,7,17, giving
4760 actual label choices. Equalities among five live colors have52 set
partitions; all can be realized with at most five of the six live roots.
Simultaneous permutations of those live roots preserve the source and query
problem, so these52 patterns exhaust the additionally pruned sources up to
that symmetry. There are247520 label/color configurations.

Taking their actual unions at each color produces19324 distinct vectors b.
No independent per-point b values are invented. These vectors occupy18
cardinalities N=77,...,94. Complete45 queries likewise have4760 distinct
17-vectors A. The native consumer evaluates all11331180 unordered pairs
(A,B), covering4760^2 ordered pairs by symmetry, and computes all12 integer
hinges of their same-point sums in one pass.

For the linear query, each positive7 slot is maximized at the untouched row.
Their combined numerator is the fixed number

    17+sum_(d in D) max_(a mod d)|S intersect(a mod d)|=42.

Hence the exact maximum nonunit query mean of an actual source is M/N, with

    M=42+sum_(d in D) max_(a mod d)
                     sum_(x in S, x=a mod d)(6-b(x)).    (AQ2)

Grouping actual vectors by their OWN pair(N,M) yields192 nonempty groups.
It neither chooses a new source for a query nor combines a size from one
source with a mean from another. Every actual source is assigned to its
group before any future query is considered.

For t=0,...,11, the consumer uses(AQ1) to obtain the exact uniform bound

    H_(N,M)(t)
       =max_(b in that actual group) max_query E_mu_b(Q-t)_+.

For fixed t,A its numerator is

    5 sum_x(A(x)-t)_+ +J_t(A)
       -min_(b in the actual group)sum_x b(x)(A(x)-t)_+.

Every minimization is over the enumerated joint vectors. Deletion masks
are not optimized independently across x or labels. This is the actual
source/query maximum envelope for the stated additionally pruned family.

The functions H_(N,M) are convex, nonincreasing and1-Lipschitz, since each
is the pointwise supremum of genuine hinge expectations. They have
H(0)-H(1)=1 and H(12)=H(13)=0. The exact consumer verifies that

    p_y=H(y-1)-2H(y)+H(y+1), y=1,...,12

is nonnegative, sums to1, and recovers every listed hinge. Thus every one
of the192 groups has a genuine comparison law Y_(N,M). Distinct thresholds
need not be attained by one query. The comparison law is auxiliary; the
actual source stays fixed.

The direct mean bound185/86 is attained. One actual pruned source has
N=86, non7 query numerator143 and positive7 numerator42. Therefore simply
lowering the old global first moment would be invalid. Its source group
has(N,M)=(86,185), contains6 distinct b vectors, and has the exact hinge
numerators

    (271,185,104,61,32,21,10,7,4,3,2,1)/86.             (AQ3)

## 3. The six worst uniform sources have actual convex-order maxima

For each of the six sources with(N,M)=(86,185), one genuine complete query
attains ALL twelve hinge values(AQ3) simultaneously. Its zero-seven and
positive-seven old45 query layouts can be chosen identical; put every
positive-seven slot on the untouched live row. The resulting load law is

    P(Q=1,2,3,4,6,8,12)=(5,38,14,18,8,2,1)/86.

The exact consumer produces such a layout for every source vector. Since
all complete queries are integer-valued between1 and12, integer hinge
bounds plus the mean determine increasing-convex order. Therefore this
one actual query dominates every query in that order, on the SAME source.
For every increasing convex phi, the supremum of E phi(Q) is exactly
its expectation under the displayed law.

Thus dividing these six sources further, choosing a different scalar
threshold, or retaining several hinges of one query together cannot
improve this particular uniform-source comparison. The actual source
weights or the later transport/deletion estimates must change. This
sharpness claim concerns the fixed uniform sources and their free-query
interface, not every supported probability law or every later interface.

The group(N,M)=(86,184) has22 actual vectors. Together these two groups
have28 distinct vectors. The complete catalogue retains all of them so
a later source-selection rule can verify that every exceptional source
has an assigned replacement; recognizing only a source size is insufficient.

## 4. Exact consumer and scope

The [consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_actual_source_catalogue.py),
[native enumerator](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_actual_source_catalogue.cpp)
and [result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_actual_source_catalogue.json)
recompute all247520 configurations,19324 source vectors,192 groups and2304
integer hinge bounds. The consumer compiles and runs the complete native
enumeration with undefined-behavior checks, reconstructs192 genuine laws,
checks domination by the inherited head D2 bounds, and finds all six sharp
query witnesses. It pins the inherited head result, but does not replay
its earlier D2 proof. A stale retained result is rejected.

An independent enumerator rebuilt the actual source and same-point query
inventories and matched every group hinge, all192 genuine laws and every
D2 comparison. Independent literal CRT evaluation of six families of11
distinct originals and their complete queries realizes the same sharp law.
These finite checks complement the untouched-row proof of the query
maximum; they do not constitute new Lean verification.

Auxiliary pruning is a CHOICE OF SOURCE inside the actual survivors. It
never changes or relabels the original family. The boundN<=94 relies on
this choice. Earlier constructions that do not add these auxiliary holes
may haveN=102; their statements are not retroactively changed.

The vectorb is sufficient for this complete convex-query interface because
all positive-seven query phases are free and an untouched row exists. It
is not asserted sufficient for arbitrary marked queries, future mixed
originals, or high-prefix operations. Those tasks require their own
common-source incidence boundary. All other old45 shapes retain their
previously certified source estimates.

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_actual_source_catalogue.py
```
