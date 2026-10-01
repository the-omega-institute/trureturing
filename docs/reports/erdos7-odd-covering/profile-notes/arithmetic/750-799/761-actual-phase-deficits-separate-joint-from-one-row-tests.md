# Short load cuts from actual label phases, and the failure of all one-row tests

Let X be any finite actual old carrier. For each numerical label d in a
finite set D, the available phases partition X into cells C_(d,a), with
empty cells permitted. Each label has a finite nonempty phase set,
and its phase can be chosen independently of the other labels.
One actual phase dictionary chooses ONE phase a_d
for every label. Its load is

    h_x=sum_d 1_(x in C_(d,a_d)),
    H=sum_x h_x=sum_d |C_(d,a_d)|.

This definition keeps all row hits of the same numerical label tied to
one common phase. Arbitrary integer loads, separate choices for different
rows, and mixtures of phase dictionaries are not identified with an
actual dictionary.

## 1. A general phase-deficit lift

Write

    n_d(a)=|C_(d,a)|,
    M_d=max_a n_d(a), M=sum_d M_d,
    delta_d(a)=M_d-n_d(a), Delta=M-H.

Then Delta=sum_d delta_d(a_d). Because each label can independently select
a largest cell, M is an attainable maximum total, not merely an upper
bound.

Fix any real row weights w_x and put

    q_d(a)=sum_(x in C_(d,a)) w_x,
    b_d=max_(a:n_d(a)=M_d) q_d(a), B=sum_d b_d.

Thus B is the exact maximum of q(h)=sum_x w_x h_x among dictionaries with
H=M. Define the smallest nonnegative multiplier

    theta=max_(d,a:delta_d(a)>0)
                (q_d(a)-b_d)_+ / delta_d(a),                    (C1)

with maximum of an empty set interpreted as zero. Every phase satisfies
q_d(a)<=b_d+theta delta_d(a), so every ACTUAL dictionary satisfies

    q(h)<=B+theta(M-H),
    theta H+q(h)<=theta M+B.                                   (C2)

The multiplier(C1) is optimal for retaining this exposed-face intercept B.
If theta is decreased below(C1), one offending phase exceeds its proposed
bound. Choose it for that label and, for every other label, a largest cell
attaining b_d. This is one actual phase dictionary violating the decreased
bound. This sharpness claim concerns the affine family with the fixed B;
it does not claim every such affine bound is the exact conditional support
at every lower value of H.

Equation(C2) is a useful restricted support-function calculation. It
produces short inequalities by selecting w supported on one or two rows,
while measuring how much total load must be sacrificed to escape the
maximum-total face. The derivation is valid for every X and every finite
family of labelled partitions, not only the following75-row example.

When all w_x are integers, the complete scalar conditional support can
also be computed without mixing dictionaries. Initialize F_0(0)=0 and
F_0(t)=-infinity for t!=0. Process each original label once:

    F_(j+1)(Delta)=max_a
          [F_j(Delta-delta_d(a))+q_d(a)].                       (C3)

At the end F(Delta) is the exact maximum of q(h) over actual dictionaries
with H=M-Delta. An unattained deficit remains -infinity. Induction on the
labels proves this recurrence, and storing an attaining option recovers
one actual phase dictionary. It is an exact DP for the declared scalar
query; it does not recover every joint load vector from its marginals.

## 2. Two short cuts on the actual75-row core

The [aggregate-load obstruction](760-aggregate-load-bounds-lose-actual-label-compatibility.md)
already separates a relaxed load table from actual phases by a support
cut. The following cuts retain more information about the cost of changing
those phases.


Take the actual core

    (3,0),(5,0),(7,0),(9,4),(15,11),(21,8),
    (35,9),(45,1),(63,1),(105,59),(315,179),

and its75 survivor rows X modulo315. Let

    D=(3,5,7,9,15,21,35,45,63,105,315).

The maximum cell sizes, in this order, are

    (38,26,16,23,15,9,5,6,4,3,1),

so M=146. All phases and all these counts are recomputed from the literal
core in the consumer.

For w=-1_{16},(C1) gives theta=1/9 and B=-1, yielding the integer cut

    H-9h16<=137.                                               (C4)

The source of the factor9 is concrete: the unique largest mod9 phase is7
with23 surviving rows, while the largest other mod9 cell has14. This
largest phase contains row16. To avoid the hit from this label costs at
least9 total load. Every other label has a largest phase avoiding row16.
Thus H>=138 forces h16>=1, and at H=137 an actual phase dictionary can
first attain h16=0. The exact deficit DP verifies this threshold.

The same argument forces all23 rows congruent7 modulo9 to have positive
load whenever H>=138. At H=146, the unique largest mod3 phase also forces
all38 rows congruent2 modulo3. These two row sets are disjoint, so61 rows
are necessarily hit at maximum total. This describes the lower and middle
load layers, where the [phase-uniform high-load bounds](759-one-actual-label-dictionary-localizes-thin-fibres.md) give no constraint.

For w=1_{16}-1_{61},(C1) gives theta=1 and B=1:

    H+h16-h61<=147.                                            (C5)

This has a direct integer verification. For every label other than315,
the quantity

    n_d(a)+1_(16=a mod d)-1_(61=a mod d)

is at most M_d; for315 it is at most2=M_315+1. Summing gives(C5). In
particular, at H=146, one must have h16-h61<=1. The exact deficit DP gives
the stronger conditional maxima as follows:

| Delta=M-H | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| max(h16-h61) |1|2|2|3|3|3|3|4|4|4|4|5|5|

The affine(C5) is shorter than this exact conditional table. Both come
from fixed numerical phases, not independent row assignments.

## 3. Every single-row test can pass while a two-row cut fails

Use the following actual phase vector, indexed by D above:

    a=(2,2,6,7,2,5,2,16,25,2,2).                              (C6)

Every phase in(C6) is a largest cell for its label. Let h be its actual
load. Direct exact reconstruction gives

    H=146, max_x h_x=6, h16=h61=2.

Define the INTEGER relaxed load

    h_hat=h+e16-e61.                                          (C7)

It is nonnegative, has total146, and still has maximum6. In particular
the heavy-row bounds at levels7,8,9,10 all hold with zero high rows.

For EACH row x, the complete pair(146,h_hat_x) has an actual dictionary:

- For x other than16 or61, use(C6) itself.
- For x=16, replace only the315 phase2 by16. This keeps total146 because
  every occupied315 cell has size1, and makes the row16 load equal3.
- For x=61, replace only the45 phase16 by7. Both are size6 maximum cells;
  the total stays146 and the row61 load becomes1.

These are three actual fixed phase vectors. The consumer reconstructs all
three and checks all75 one-row claims individually. No convex combination
is used. Hence h_hat passes EVERY valid inequality

    alpha H+beta h_x<=constant

for every row x and all real alpha,beta, because the relevant pair has an
actual witness. More generally it passes every sound test depending on
only(H,h_x). The witnesses can differ across x, which is precisely the
information this kind of summary omits.

Yet(C7) violates the joint cut(C5):

    H+h_hat16-h_hat61=146+3-1=148>147.                         (C8)

Therefore h_hat is outside even the convex hull of actual load vectors.
Exact single-row conditional feasibility, the total load, and all earlier
high-layer bounds still do not establish one common actual phase source.
This is a statement about the sufficiency of load constraints. No claim
is made that(C7) gives a negative372-query row-law certificate; unlike the
separate relaxed dual example, no such cost computation is needed here.

## 4. Consequence for the universal-source problem

The deficit method supplies short certified cuts and an exact scalar DP
for generating them. It can prune a proposed load table before attempting
the row-law inequality, and(C5) shows that pair information can be needed
even after every single-row condition has been imposed.

It does not prove that all pair cuts are sufficient. Complete support
inequalities characterize the convex hull of sums of phase masks; that
convex hull still permits mixtures. A uniform argument for actual phase
dictionaries must either establish that its row-law property survives
this relaxation or retain enough phase-choice data to use one actual
dictionary throughout. Neither assertion is supplied by(C1)--(C8).

## Exact verification and remaining boundary

The [standard-library consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_phase_deficit_cuts.py)
uses only literal core phases and actual per-label phase vectors. It
reconstructs the core, evaluates every numerical phase for both cuts,
computes exact conditional-deficit DPs, and checks all75 actual projection
witnesses. Its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_phase_deficit_cuts.json)
contains the three actual dictionaries and all witness assignments, and
must equal fresh full recomputation.

An independent implementation retains all reachable (deficit,reward)
pairs, instead of only the best reward at each deficit; all26 stated
conditional values agree. Independent complete phase histograms verify
the137 and147 cut bounds, and literal reconstruction verifies all75
projection witnesses and the61 forced rows at maximum total.

The universal lifting statement follows from (C1)--(C3); the finite checks
verify the specific cuts and counterexample. Neither is new Lean
verification. In particular, this new relaxed load has no claimed
372-slot dual obstruction. It proves only that all one-row tests do not
ensure one jointly realizable phase dictionary. The
[all-colour row-envelope problem](758-one-row-mass-law-handles-all-outside-colours.md)
for arbitrary old phases and unrestricted Erdős #7 remain unresolved.
