[Index](../../marked_head_profile.md) · [All-height ceiling](427-shared-row-cap-mixtures-break-the-six-barrier.md) · [Cap architecture](425-full-six-pair-cap-mixtures-have-an-exact-laminar-dual.md) · [Literal-layout game](400-literal-layout-mixtures-and-exact-tree-rank-duality.md)

# Original phase conflicts close the sharp height-two component bound

Let `S subset {1,2,3,4} x Z/49`. Choose any full five-cap probability
on `S` and any six pair three-cap probabilities on their actual row
pairs, in the sense of report 425, PC1. These seven probabilities may
be fixed arbitrarily. There are convex weights, fixed before every
independent original phase, whose common law satisfies

    max_(a_d mod d, d|245) E (sum_(d|245) 1_(x=a_d mod d))^2
       <= 46/9 = 2t_2.                                      (PH1)

Divisor one and all six original labels `1,5,7,35,49,245` are
retained. No common-path condition is imposed. The constant is sharp
for arbitrary prescribed seven components: Section 6 gives one
actual seven-component game with value exactly `46/9`. Sharpness of
the unrestricted source optimum is not asserted.

Together with report 427, PH1 proves the finite target for these
arbitrary fixed components at every `K>=2`. For an admissible source
as defined in report 400, the depth-zero direct law and report 390's
root theorem supply the remaining source-level heights. Thus

    every admissible S at every finite seven-height K admits
    one supported law with Gamma_(1,K) <= 2t_K.               (PH2)

The low-height source laws are not identified with mixtures of
arbitrary prescribed components. All statements retain five-height
one. Deeper powers of five and general prime supports are outside
PH1--PH2; unrestricted Erdős #7 remains unresolved.

This is an ordinary proof using exact integral flows and a complete
rational case split. It is not Lean certification.

## 1. The new information: actual shared prefix capacity

Report 427, JC15, shows that separately bounding each row prefix,
even with a pair law's root row masses retained, does not settle
height two. The missing relation connects different depths and
rows. If a depth-two mixed label uses a row different from the
shallower mixed label, its mass inside a shared root prefix consumes
part of that root's **total** capacity. The two row contributions
cannot both receive the same full root budget.

The present proof retains every original phase intersection inside
a finite prefix-flow problem. In particular:

- When the depth-two pure and mixed phases agree, they share the
  same leaf capacity across all rows.
- When they disagree, their two ordered cross terms vanish.
- Whether the two leaves have the same root controls how their
  mass competes with both depth-one labels.

These are constraints on one actual measure, including ancestor
and descendant capacities. They are not adjustments of report
427's scalar coefficients.

## 2. A finite integral domain for the seven row masses

Fix a probability `theta` on **complete original layouts** and let
`f_theta` be their averaged squared cost. First replace every mixed
phase in absent row zero by a phase in an actual row with the same
seven-adic prefix. This only increases every component's cost. It
therefore suffices to bound the resulting layout distributions; make
this replacement before the row ordering PH4 below. For the moment
this resulting `theta` is fixed.
Extend each component's allowable support to the full carrier

    X={1,2,3,4} x Z/49.

For each of the seven cap polytopes, maximize `E_eta f_theta` over
that full-carrier polytope. This can only increase each of the seven
prices. The maximizations are separate, so all seven replacements
can be made at once. They occur after fixing the same `theta`; no
replacement is claimed to work simultaneously for every `theta`.
This is a dual upper-bound step.

For branching `b` equal to five or three, multiply a cap law by
`b^2`. Its total mass becomes `b^2`; every root-prefix capacity is
`b`; every leaf capacity is one, shared by all its allowed rows.
These are the integral laminar-flow constraints of report 425,
PC5. A flow first chooses roots, then leaves, then actual row-labelled
points. The integral-flow theorem implies that every cap-polytope
vertex is a uniform law on `b^2` distinct leaves, with one allowed
row selected at each leaf. Parallel row choices at one leaf share
its capacity; they do not create extra capacity.

A linear maximum occurs at such a vertex. Hence its row masses have
one of the following forms:

    full law: beta=(n_1,n_2,n_3,n_4)/25,
              n_r>=0 integers, sum_r n_r=25;
    pair {r,s}: (gamma,1-gamma)=(k,9-k)/9,
                k in {0,...,9}.                             (PH3)

There are exactly `binomial(28,3)=3276` full row-quota vectors,
including zero coordinates, and ten choices for each pair. This
reduction follows from maximizing the actual linear prices before
relaxing them. It does not assert that arbitrary mixtures of vertex
row masses are themselves vertices.

For the fixed `theta`, simultaneously relabel the four rows so that
its mixed-root frequencies satisfy

    rho_1<=rho_2<=rho_3<=rho_4,
    rho_r=P_theta(the divisor-five label selects row r).     (PH4)

The full law, all six pairs, their quota directions and every
layout are relabelled by this one permutation. All 3276 full quotas
and all ten pair quotas remain available. No second ordering of
`beta` is imposed.

## 3. Twenty complete original-phase types

After a mixed phase in absent row zero is replaced by any actual
row at the same seven-adic phase, its load only increases. We may
therefore write the three mixed rows as a word
`w=(r_0,r_1,r_2)` in `{1,2,3,4}^3`.

The four positive-depth labels are denoted `P1,M1,P2,M2`, with
moduli `7,35,49,245`. Their first seven-adic digits form the ordered
four-tuple

    (P1, M1, parent(P2), parent(M2)).                         (PH5)

Up to permutation of the seven root digits, its equality relation
is one of the fifteen set partitions of four labelled positions.
If the last two positions differ, their leaves are already distinct.
If they agree, the depth-two leaves can agree or differ. Exactly
five of the fifteen partitions identify those last positions:
identifying them gives the five partitions of three positions.
There are therefore exactly

    15+5=20                                                 (PH6)

phase types. A root permutation and independent permutations of
its seven child digits carry every literal phase tuple to one of
these representatives. Conversely every representative is realized
with seven root digits and seven child digits. This is a complete
classification of a **single layout's** prefix incidences, not a
common coordinate change on an arbitrary mixture of layouts.

Together with the 64 mixed-row words there are 1280 columns. For
one column `c=(w,o)` and row quota `q`, let

    Q_b(q;c)=max_eta E_eta f_c,                              (PH7)

where the maximum is over full-carrier cap laws in the specified
rows with that row quota, and `f_c` is the squared original-label
load of the representative. Transporting an original component
by a layout's tree automorphism preserves every prefix cap and its
row quota. Thus its cost on that layout is at most PH7.

This allows the transported maximizing law to differ from column
to column. It enlarges the upper bound. The proof never identifies
these column maxima with one jointly realized component law.
The original whole-layout distribution induces one common
probability on the 1280 columns, used for every component.

## 4. Exact cap prices by a small network, with equal dual values

Scale the law by `b^2` as in PH3. The price network has edges

    source -> row -> leaf -> root -> sink.                  (PH8)

Source-to-row capacities equal the integer row quotas; all must
be filled since their sum is `b^2`. A row-to-leaf edge has cost
the exact squared load of that row-labelled point. Leaf-to-root
capacity is one, and root-to-sink capacity is `b`. This network
retains all cross-row leaf and root restrictions simultaneously.
Its maximum profit divided by `b^2` is exactly PH7.

To evaluate it efficiently, leaves with the same cost vector and
the same selected-label incidences can be grouped. Each root has
at most two distinguished depth-two leaves. Its remaining leaves
form one group; roots hit by none of PH5 form one further group.
A group representing `m` roots and `h` identical leaves per root
has leaf capacity `mh` and root capacity `mb`. A grouped flow
splits back by dividing it equally among those `m` roots and then
among the `h` leaves. The original capacities follow, all costs
are preserved, and row totals do not change. There is no additional
row-by-root quota to preserve. The reverse map just sums flows.
Thus this aggregation preserves the exact maximum, even when the
unpacked maximizing measure is fractional.

Rows not selected by the mixed word have the same cost vector and
may also be combined. Their combined flow can be split among the
original unused rows in proportion to their quotas, preserving all
leaf and root totals. This explains the reusable cache indexed by
mixed-row equality type and active row quotas; it is not a source
symmetry assumption.

The checker uses only integer augmenting flows. It additionally
constructs a residual potential `pi` with

    pi_v>=pi_u+c_e

on every residual edge of positive capacity. For each original
edge let `U_e` be its capacity and `c_e` its cost. Every feasible
flow of value `b^2` has profit at most

    b^2(pi_sink-pi_source)
       +sum_e U_e max(0,c_e-pi_v+pi_u).                      (PH9)

This follows by summing the potential differences using flow
conservation, then bounding each remaining edge profit by its
capacity times its positive part. The program verifies every edge
capacity, every vertex balance, the literal flow profit, and equality
with PH9. Its cap prices are therefore exact upper bounds as well
as attained lower bounds. Numerical optimization is not used by
the retained checker.

## 5. Complete rational upper certificates for the common distribution

For a pair `{r,s}`, `r<s`, define the existing row coefficients
from report 427,

    W_(r,j)=(2j+3+2n_j)1_(r_j=r)+2#{i<j:r_i=r},
    n_j=#{i<j:r_i=r_j}.

The checker also reconstructs them from the original ordered label
pairs, including divisor one. Put

    A_rs(c)=3 1_(r_0=s)
               +sum_(j=1)^2 (W_(r,j)+W_(s,j))3^-j.

The root ordering PH4 gives the existing quota-independent bound

    E_theta cost_rs <= 23/9+E_theta A_rs(c).                 (PH10)

For a pair whose quota `k` has been fixed, replace this by the
stronger price `E_theta Q_3((k,9-k);c)`. For the full component use
`E_theta Q_5(n;c)` throughout. Each branch therefore bounds the
minimum actual component price by the minimum of seven averages.

Here is the exact dual certificate format. For each pair choose
one of its current bounds, written `d_rs+E_theta g_rs(c)`, where
`d_rs=23/9, g_rs=A_rs` for PH10 and `d_rs=0, g_rs=Q_3` for a fixed
quota. Supply nonnegative multipliers `p_rs`, three nonnegative
order multipliers `a_r`, and a nonnegative full multiplier `b`, with

    sum_(r<s) p_rs+b=1,
    tau=46/9-sum_(r<s) p_rs d_rs.                            (PH11)

For every one of the 1280 columns check

    tau+sum_(r=1)^3 a_r(1_(r_0=r)-1_(r_0=r+1))
       >= sum_(r<s) p_rs g_rs(c)+b Q_5(n;c).                 (PH12)

Averaging PH12 under the same `theta`, the order term is
`sum a_r(rho_r-rho_(r+1))<=0`. Adding the weighted constants in
PH11 proves that the convex average of these seven upper prices
is at most `46/9`. Their minimum is no larger. This proves the
required bound on that quota branch for every common `theta`.

All full quotas are listed by the exhaustive integer generator in
PH3. At a decision node, choose one not-yet-fixed pair and branch
on **all ten** values `k=0,...,9`. Each leaf supplies PH11--PH12;
unbranched pairs retain PH10. The checker verifies that no pair is
branched twice on a path and that every used quota agrees with its
branch. Hence each full quota covers all `10^6` six-pair quota
assignments. Shared subtrees only compress this finite exhaustive
argument.

The retained decision certificates have the following exact scope:

| Item | Count |
| --- | ---: |
| Full row-quota vectors | 3276 |
| Possible quotas for each pair | 10 |
| Complete mixed-word/phase columns | 1280 |
| Independently certified integral cap prices | 92500 |
| Distinct rational duals | 7109 |
| Retained decision-DAG nodes | 7558 |
| Expanded decision nodes across the full domain | 7766 |
| Expanded certificate leaves | 7317 |
| Exact layout/value-column checks | 9373077 |

All prices have denominators dividing 25 or 9. The checker multiplies
PH12 by `225` and by the least common multiple of the dual
denominators, then checks integer inequalities. The normalization
column is checked exactly as well. Every retained node and dual is
used; the data file contains no optimizer transcript or snapshots.

We have proved, for every original `theta`, that the minimum price
of the seven original fixed components is at most `46/9`: replacing
by extremal full-carrier components and then by column prices only
increased the relevant upper bound. Finite minimax, exactly as in
report 427, JC3, now supplies convex weights on the **original seven
components**, fixed before all layouts. Their support remains in
`S`. This completes PH1.

## 6. A real fixed-component game attains equality

Use the full carrier `X` and the following three original layouts,
each with probability `1/3`. Tuple order is
`1,5,7,35,49,245`:

    (0,1,0,21,0,196),
    (0,2,1,22,1,197),
    (0,3,2,23,2,198).                                       (PH13)

Each has a constant mixed row, respectively one, two or three,
and compatible seven-adic phases along root zero, one or two.
These particular layouts are permitted within the larger independent
phase game.

For the resulting `f_theta`, choose a maximum-price cap basis for
each component. To fix all ties, scan points by decreasing price,
then increasing row and increasing leaf; accept a point whenever
its leaf has not yet been used and its root count is below `b`.
Stop after `b^2` acceptances and assign each point mass `b^-2`.
This is report 425's laminar greedy rule with prices negated and
specifies seven actual probabilities once and for all.

Their exact expected prices, with the full component first and
then pairs `12,13,14,23,24,34`, are

    26/5, 20/3, 20/3, 46/9, 20/3, 46/9, 46/9.              (PH14)

Thus PH13 gives a lower bound `46/9` on this prescribed-component
game. PH1 supplies the matching upper bound. There is also a direct
successful mixture: the three components for pairs `14,24,34` are
uniform on their active row and the nine leaves

    {a+7d: a,d in {0,1,2}}.

Their equal mixture is uniform on three rows times this complete
ternary depth-two tree. Row mass is `1/3`, each pure depth-`j`
prefix has mass at most `3^-j`, and each row-prefix intersection
has mass at most `3^(-j-1)`. Expanding the original square and using
`sum_r W_(r,j)<=6j+3` gives

    E load^2 <= sum_(j=0)^2
       [(2j+1)3^-j+(6j+3)3^(-j-1)]
      =2S_3(2)=46/9.                                       (PH15)

One of PH13's layouts attains equality. The checker evaluates all
original CRT predicates, constructs all seven cap bases, verifies
PH14 and this attaining product-law layout. The example concerns
prescribed component choices; it does not claim that every law on
the full carrier must have value `46/9`.

## 7. The first five-layer source comparison at every seven-height

For an admissible source, the full five-tree and six pair ternary
trees supply the seven cap probabilities. PH1 handles `K=2`.
Report 427 handles all `K>=3`, including its sharper height-three
bound and its uniform ceiling below the targets for `K>=4`.

At `K=0`, admissibility means every pair of the four rows meets the
source, so at least three rows are present. Uniform mass on three
of them gives `1+3*(1/3)=2=2t_0` for the original labels `1,5`.
At `K=1`, the source has at least five projected columns, and every
row pair has at least three columns in its union. With row zero
empty, these imply that every three rows of `Z/5` meet every set
of five columns. Report 390, TB1, therefore gives one supported
law with maximum at most `4=2t_1`. These are source-level
constructions, not statements about arbitrary prescribed seven
component mixtures at `K=0,1`.

This proves PH2 for every finite `K`. It closes report 400's
LD11 within its stated admissible first-five-layer source class.
The original load still has only the two five-levels `1` and `5`;
extra five-power labels and their cross terms require separate
arguments. No unrestricted covering conclusion follows here.

## 8. Exact artifacts and verification

The reusable standard-library checker is
[`height_two_phase_orbit_common_law.py`](../../frontier/cover-geometry/height_two_phase_orbit_common_law.py).
It exposes phase-orbit generation, the exact quota-conditioned cap
price, and certificate verification. Its necessary exact data are
[`height_two_phase_orbit_certificates.json`](../../frontier/cover-geometry/height_two_phase_orbit_certificates.json),
containing only rational duals and their finite decision DAG.
The compact data file is 1055639 bytes. The code regenerates the
mathematical domains and all 92500 cap prices; the data do not
supply a table of trusted price outputs.

```sh
python3 docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_phase_orbit_common_law.py --compact
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_phase_orbit_common_law.py --compact
```

Both modes return the same exact certificate counts and sharp-game
prices. No numerical solver is imported or executed. The optional
`--certificates` argument accepts the same explicit certificate
schema for independent verification; malformed or incomplete
coverage is rejected rather than reported as a bound.

The mathematical ingredients reused here are finite minimax and
the integral laminar-cap representation established in reports 400
and 425. The additional result is the universal phase-sensitive
height-two inequality certified by PH3--PH12, not a new general
minimax or flow-integrality theorem.
