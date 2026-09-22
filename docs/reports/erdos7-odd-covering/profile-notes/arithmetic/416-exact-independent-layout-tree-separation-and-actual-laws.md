[Index](../../marked_head_profile.md) · [Literal phase game](400-literal-layout-mixtures-and-exact-tree-rank-duality.md) · [Concentrated sharp sources](414-same-projection-transport-controls-concentrated-sharp-sources.md)

# Exact independent-layout separation on the 5 by 7-power carrier

Ordinary proof of the recurrence and exact integer verification; no Lean
certification is claimed.

Given K>=0, distinct points (r,y) with r in {1,2,3,4}
and 0<=y<7^K, and nonnegative integer weights w of positive sum W, compute
exactly

    max_lambda sum_x w_x ell_lambda(x)^2 / W,

where each original divisor d|5*7^K has its own independently selected
phase. The law is fixed. This is separation for a supplied law, not a
minimax law constructor and not an E7 result. Exact rational weights may
be scaled by a common denominator.

The implementation [`independent_layout_tree_dp.py`](../../frontier/cover-geometry/independent_layout_tree_dp.py) exposes

    oracle=IndependentLayoutTreeDP(K, points)
    result=oracle.separate(integer_weights,
                          max_states=None, max_operations=None)

The result includes an exact Fraction `value`, integer `numerator` and
`denominator`, a literal `layout` dictionary (original divisor -> residue),
and `point_costs` in the supplied input order for direct use as a generated
optimization cut. It also returns state/operation counts and elapsed time.
`max_states` counts created memo entries; `max_operations` counts subset
convolution candidates, including witness reconstruction. Exceeding either
specified count raises ResourceLimitError; no partial maximum or certificate
is returned. Neither option bounds total arithmetic work or memory. In
particular a one-child tree can create many states with zero subset candidates. The code uses the Python
standard library and unbounded integer arithmetic. No repository files
are modified by importing or calling it.

The existing `height_two_layout_second_moment.py` separates the different
nine-label p^2 q^2 game. The seven-bit support-cost DP solves a different
support-selection problem. The present interface instead keeps all
2(K+1) separately named original divisors of 5*7^K at arbitrary height.

## Exact sufficient boundary

Build the lowest-digit-first seven-adic trie of points of positive mass.
At a node u of depth d, each ancestor phase either contributes to no point
below u, adds one to every row below u (a pure label), or adds one to just
one row below u (a mixed label). Consequently its entire effect is a vector

    v=(v_1,v_2,v_3,v_4)

of nonnegative inherited loads. No other ancestor history is needed to
compute the final square on any descendant. In particular, the square is
not replaced by its separate marginal maxima.

There are two distinct original labels at each future depth j:
P_j=7^j and M_j=5*7^j. A bit mask S records exactly which individual labels
at depths d,...,K are assigned to the subtree u. Each assigned label must
select exactly one descendant node at its own depth; a mixed label also
selects one row. Other labels act in other subtrees. P_j and M_j are separate
bits and may be assigned to different root columns, at every j independently.

Let F_u(v,S) be the maximum weighted squared load below u under this
contract. Masks use two bits per depth, pure first, with the current depth
in the two least significant bits.

## Node recurrence and child allocation

Let e be the pure current-depth bit of S, f its mixed current-depth bit,
and S' the remaining mask after dropping these two bits. Set

    v'=v+e*(1,1,1,1)+f*e_a,

where row a is maximized over {1,2,3,4} when f=1 (there is no choice when
f=0). A current-depth pure phase is the node prefix itself. The mixed
phase is the CRT class consisting of this prefix and row a.

For children u_1,...,u_t, define the exact combination

    C_u(v',S') = max_(S_1 disjoint-union ... disjoint-union S_t=S')
                    sum_i F_(u_i)(v',S_i).

Then F_u(v,S)=max_a C_u(v',S'). At depth K, no future bits remain and the
value is simply sum_r w_(r,u) (v'_r)^2. In code the leaf's four masks are
computed by four exact formulas, with the mixed contribution maximized
over its four possible rows.

All mask values for one node and one inherited vector are computed
together. Combine two child tables by max-plus subset convolution:

    (A star B)[S] = max_(T subset S) (A[S\T]+B[T]).

Sequentially combining at most seven children gives C_u. The root fixes
the divisor-one contribution and maximizes the independent divisor-five
row. For each a, start with v_r=1+[r=a] and allocate all bits at depths
1,...,K across the root children. At K=0 the direct value is W+3 max_r w_r.

Reconstruction backtracks the winning child allocations and mixed row
choices. Every original label is recovered exactly once. A mixed phase at
node prefix z of depth j and row r is the canonical integer

    z+7^j*((r-z)*(7^j)^(-1) mod 5).

The output is independently evaluated by the literal divisor conditions;
its weighted square must equal the stored optimum before return.

## Why the maximum is exact

Every layout whose phases meet positive-mass source points determines one
unique node for each pure label and one node/row for each mixed label.
Below any node, its deeper labels split disjointly by child. Its ancestor
contributions are exactly v. Thus the layout provides a feasible choice
at every recurrence and its score is at most the computed value.

Conversely, each maximizing current-row choice and mask partition fixes
legal phases of the original, separately named labels. Child subcarriers
are disjoint, so their weighted scores add. Induction reconstructs a full
actual layout attaining the computed value. No compatible-phase or common
path requirement has been added.

It is harmless to omit trie nodes of zero mass and phases whose events
miss all positive-mass points: replacing such an empty indicator by any
nonempty legal indicator for that same original label can only increase
the nonnegative pointwise load and its square. There is always such a
phase because W>0. Root row zero is similarly dominated by an active row.
The DP therefore covers the maximum over all original phases, including
inactive ones, without wasting states on them.

## Complexity, including inherited row loads

At depth d the inherited vector is a*1+b, where a counts at most d+1
pure ancestors/current labels and b has four nonnegative coordinates
whose sum is at most d+1. Hence the number of vectors, including the
locally incremented combination states, is bounded by

    (d+2) * binomial(d+5,4) = O((d+2)^5).

There are at most 7^d trie nodes at depth d. A child convolution handles
2(K-d) remaining bits and uses O(3^(2(K-d)))=O(9^(K-d)) arithmetic
operations; the at most seven children and at most ten local increment
options are constant factors. Summing over nodes, masks, and inherited
vectors gives the safe worst-case upper bounds

    O((K+2)^5 * 9^K) exact arithmetic operations,
    O((K+2)^5 * 7^K) stored integers.

The sums account for the inherited vector states, not just mask work.
Sparse support reduces actual trie size. All scores lie between zero and
4(K+1)^2 W, so integer bit complexity also depends on log W+log(K+1).
By contrast full literal enumeration has 5^(K+1)*7^(K(K+1)) layouts;
even discarding inactive phases can still leave a much larger product.
The algorithm is exponential in K, not claimed polynomial-time in K.

## Controls and measured scope

Twelve seeded tiny laws at K=0,1,2,3 agreed with independent direct
enumeration of all active original phases. The K=2 concentrated sharp
law reproduces the value 10483/1755 and the literal lower witness in 414.

An explicit non-common-path control uses row 1 only, mass units one at
y=0,7,...,42 and mass units three at y=1. Its exact maximum is 16, attained
by phases

    a_1=0, a_5=1, a_7=0, a_35=21, a_49=1, a_245=1.

These phases deliberately select different root columns at different
depths. Restricting every selected seven-adic phase to one common path
has exact maximum 72/5. This control would detect accidentally replacing
original independent phases by a coherent-path subproblem.

On the fixed actual four-component family law from report 414:

| Height | Exact maximum | Cached states | Subset operations |
|---|---|---:|---:|
| 2 | 10483/1755 | 864 | 6712 |
| 3 | 160507/26325 | 16164 | 152212 |
| 4 | 12043/2025 | 223164 | 2611544 |

The height-four support has 1,793,538,398,437,500 active phase combinations.
These are measured controls of the general recurrence, not a proof of
an all-source energy inequality. The particular fixed 414 recipe fails
at these three heights; this does not refute existence of another
successful law on the same source.

The independent check runs as:

    python3 docs/reports/erdos7-odd-covering/frontier/cover-geometry/independent_layout_tree_dp_check.py
    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/independent_layout_tree_dp_check.py

It performs CRT integer remainder enumeration without calling the DP's
literal-cost routine, checks the known K2 family value, and tests the
full 1372-point height-three carrier with uniform weights. That dense
case has exact value 19/7, agreeing with the independent original-LCM
shell expression, and used 41584 cached states and 387882 subset operations
in this deterministic control. Eight malformed inputs and two requested resource
exhaustions are explicitly rejected; a subsequent unrestricted solve
on the same oracle succeeds. Both successful and interrupted solves
clear their internal memo tables. Operation counters include witness
subset-convolution reconstruction.

## Different actual laws succeed at heights three and four

The fixed-recipe failures above do not obstruct the underlying sources.
On the very same R_K of report 414, two explicit rational probabilities
satisfy the finite target against **every independent original layout**:

| K | Source points | Positive law atoms | Probability denominator | Exact Gamma_K | Target 2t_K | Strict margin |
|---|---:|---:|---:|---|---|---|
| 3 | 127 | 31 | 100 | 559/100 | 152/27 | 107/2700 |
| 4 | 627 | 71 | 1000 | 2843/500 | 158/27 | 2239/13500 |

The complete positive supports, integer masses and attaining original
layouts are in
[`concentrated_sharp_small_height_laws.json`](../../frontier/cover-geometry/concentrated_sharp_small_height_laws.json).
Every positive point is in the actual source; omitted source points have
zero mass. Each probability is selected before the independent phases.
The exact separation recurrence proves the upper bound, while the
recorded literal layout gives equality by ordinary CRT remainders.
These values are maxima for the **supplied laws**, not source minimax
optima or claims about all admissible sources.

The reusable data checker
[`concentrated_sharp_small_height_laws.py`](../../frontier/cover-geometry/concentrated_sharp_small_height_laws.py)
checks support membership, exact normalization, the target, the computed
full maximum and the literal witness. It accepts an optional JSON path
with the same schema. From the repository root:

    python3 docs/reports/erdos7-odd-covering/frontier/cover-geometry/concentrated_sharp_small_height_laws.py
    python3 -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/concentrated_sharp_small_height_laws.py

Together with 412 at K=2 and 414 for every K>=10, these certificates
supply successful source laws for this explicit family at K=2,3,4 and
all K>=10. [Prefix-local transport](417-prefix-local-disagreement-extends-the-same-law-to-height-seven.md)
further extends the same fixed law to every K>=7. The
[finite completion](418-concentrated-sharp-sources-admit-a-common-law-at-every-height.md)
closes heights 5,6 and gives one actual law at every K>=2 for this family.
No change is made to the independent-phase quantifiers, and no claim is
made about unrestricted Erdős #7.
