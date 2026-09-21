# 67. Shared-root prefix bounds for the actual survivor law

For the unchanged actual law of
[Chapter 64](64-adaptive-core-policy-and-continuous-stoploss-optima.md),
retaining one first3 root for each of the66 original labels divisible
by3 adds credit2.7869612896236187... to the proved mixed credit of
[Chapter 65](65-independent-survivor-marginal-ceiling-at-the-fixed-cutoff.md).
The new lower credit is16.867154438168644.... A refinement that retains
first9 prefixes where the original label permits them raises it to
16.8681002893431.... The baseline B16384, tau1 score remains
1.0087465995478049...>1.

The first3 binary relaxation is solved exactly by a feasible integer
flow and a cut of the same value. The first9 bound is certified by
nonnegative rational endpoint charges. The maximum of the first9 relaxation lies in an exact
interval of width less than0.000001276, using a feasible assignment
of this relaxed state problem as the lower control. That lower control
is not asserted to be a true survivor integral of an actual layout.

| Retained selected upper bound | Value | Full certified credit |
|---|---:|---:|
| Chapter65 separate scalar marginals | 30.108996611942683... | 14.080193148545026... |
| Exact first3-root binary optimum | 27.322035322319064... | 16.867154438168644... |
| First9-prefix rational charge bound | 27.32108947114461... | 16.8681002893431... |

Both replacements start from the same Chapter65 mixed certificate.
The first3 gain is included in the first9 gain; neither is added to
the overlapping triangle correction of
[Chapter 66](66-shared-phase-triangles-and-common-center-obstruction.md).
All154 original labels and phases, twenty balanced profiles, actual
policy rows, full event H and directed tail constants remain unchanged.

## Restricted queries under the same complete survivor law

Fix the exact Chapter64 actual policy and nu(A)=mu(H intersect A), where
H avoids all154 original classes after all20 head coordinates. Original
labels, original phases, full heights, leaf allocation order and terminal
kernels remain unchanged. At the initial node the retained policy reads
prime3. The original modulus3 class is0, so nu is supported on first3
roots1 and2. The law is not conditioned or re-optimized below.

For every query modulus m divisible by3, write m=3^e n, (n,3)=1. For
r=1,2 define

 M_m(r)=max_{a mod m: a mod3=r} nu([a mod m]).

Let x denote the full initial3-coordinate value, w(x) its actual integer
row allocation, and s_x its next retained boundary. Let V_s(n) be the
existing Chapter65 history-relaxed query numerator, in its corresponding
remaining-coordinate denominator. All children of this actual first row
have the same remaining coordinate set and denominator D_child; the
initial denominator is D=U_3 D_child. Then

 B_m(r)=max_{b mod3^e: b mod3=r}
          [sum_{x mod3^H: x mod3^e=b} w(x) V_(s_x)(n)]/D

is an upper bound for M_m(r). For a fixed globally chosen a, its3^e
component selects one b, and its remaining n component is the same in
every history. Applying the old child upper bound separately and then
maximizing over b enlarges that fixed-residue value. Future phases remain
relaxed across child histories exactly as in Chapter65, but the first3
root stays fixed. No future conditioning of a row cap is introduced.

Root0 gives zero. The maximum over r=1,2 is exactly the previous scalar
relaxed query, so this computation refines that same bound. For m=3,9,15,21
the independent literal certificate gives all residues exactly; taking
its largest mass among a mod3=r supplies the exact M_m(r), and replaces
the relaxed value. Its maximum over r is the same exact M_m used in the
Chapter65 hybrid certificate. All2662 affected query moduli are retained.
No other query or marginal maximum is changed.

## One binary variable for each original numerical label

Let V={d in E154:3 divides d}, |V|=66, and W=E154 minus V, |W|=88.
Each complete test layout chooses one independent fixed residue c_d for
each divisor. If d in V has c_d mod3=0, every term involving its cylinder
has zero nu-mass. Replacing its root by1 cannot decrease the following
nonnegative upper relaxation, so only roots1,2 are needed for its maximum.
This does not require all labels to share a root.

Select exactly the66 coefficient3 unaries in V and every coefficient2
unordered pair with at least one endpoint in V. All remaining terms keep
their old hybrid upper bounds. For i representing d_i in V put

 U_i(r)=3 B_(d_i)(r)+2 sum_{e in W} B_lcm(d_i,e)(r),
 w_ij(r)=2 B_lcm(d_i,d_j)(r), i<j.

The old selected upper is obtained by maximizing each of these underlying
unary and pair terms separately, before summing. Denote it by S_old.
For fixed roots r_i, a pair of V-label cylinders with different roots is
empty. With equal root r its intersection is empty or a cylinder modulo
the lcm whose first3 root is r. A V/W pair likewise uses its V-label's
root. Consequently the selected part of every complete layout is at most

 F(r)=sum_i U_i(r_i)+sum_{i<j:r_i=r_j} w_ij(r_i).

There are66 unary terms,66*88 mixed pairs and66*65/2 V-pairs. Each original
unordered pair occurs once, with coefficient2; each selected unary occurs
once, with coefficient3. Labels with the same root remain distinct. Their
higher digits and other prime residues need not be mutually compatible,
so this is still an upper relaxation of the complete original layout.

## Exact finite cut certificate

Clear the common actual denominator D and write x_i=0 for root1, x_i=1
for root2. In these integer units define

 C=sum_i U_i(1)+sum_{i<j} w_ij(1),
 k_ij=(w_ij(1)+w_ij(2))/2,
 a_i=U_i(2)-U_i(1)+sum_{j!=i}(w_ij(2)-w_ij(1))/2.

The pair weights have a factor2, so k_ij and a_i are integers. Direct
binary expansion gives

 F(x)=C+sum_i a_i x_i-sum_{i<j} k_ij |x_i-x_j|.

Since all B_m(r) are nonnegative, k_ij>=0. Set
K=C+sum_i max(a_i,0). Introduce source s and sink t, arcs
s->i of capacity max(-a_i,0), i->t of capacity max(a_i,0), and both
arcs i->j and j->i of capacity k_ij. For the cut whose source side is
{x_i=0}, its capacity is exactly K-F(x). Thus any feasible s-t flow
of value v proves F(x)<=K-v for every binary assignment. If one cut
has capacity v, this upper bound is attained in the binary relaxation.
This is the finite shared-root transport principle already used in
profile339e; no new general max-flow theorem is claimed.

The certificate checks every integer arc flow against its capacity,
flow conservation at all66 internal vertices, equal source/sink value,
and equality of that flow value to the displayed cut capacity. It also
evaluates F on that cut directly. Its chosen maximizing assignment puts
all66 labels on root1. This is a conclusion of unrestricted binary
optimization, not an imposed common-root premise. No statement of
uniqueness, full-residue centering, or attainability in the true original
layout problem follows from this binary optimum.

## Same-law credit and continuation

The exact rational certificate gives

 S_old=30.108996611942683...,
 max F=27.322035322319064...,
 kappa=S_old-max F=2.7869612896236187... .

Replacing exactly this selected old contribution by max F improves the
Chapter65 mixed lower credit to

 Delta_new=14.080193148545026...+kappa
          =16.867154438168644... .

The earlier three-triangle credit uses overlapping selected terms and is
NOT added. The unchanged complete-head envelope therefore obeys
integral_H L_c^2<=J_head-epsilon-Delta_new uniformly over all complete
head layouts. Independent added higher head digits preserve all selected
old cylinder marginals; the old full-height envelope pays for every other
term. The existing head-to-tail transport then applies to the same H and
actual probability law, with its positive product and common final event.

At B16384 and tau1 the resulting baseline score is
1.0087471657527378...>1; with the named D7-complement allowance it is
1.047756610564654...>1. Neither criterion closes. These decimals merely
abbreviate the retained full rational comparisons. This result does
not optimize the actual head law, rephase the original family, solve the
full joint-layout maximum, or resolve unrestricted Erdos7.

## Refinement to first9 prefixes

Keep the actual64 law and full survivor H of the first3-root construction.
For any query m divisible by9, define M_m(b) as the largest H-cylinder
mass over globally fixed residues a mod m satisfying a mod9=b. At the
actual initial3-coordinate row, use the same child query bounds as before,
but maximize the initial3^v3(m) bin only among those with first9 prefix b.
The old induction proves an upper bound B_m(b). Prefixes0,3,6 are killed
by the original0mod3 class and prefix4 by4mod9. Thus the five possibilities
are1,2,5,7,8. For m=9 the literal all-residue data give the exact values.
Taking the maximum over these prefixes with each fixed first3 root agrees
exactly with every previously retained first3 query. All1337 affected
query moduli are checked. No later policy choice is altered.

The same66 original labels now have their correct distinct state spaces:
38 labels divisible by3 but not9 have states1,2 modulo3; the28 labels
divisible by9 have states1,2,5,7,8 modulo9. Each label chooses one fixed
state. Its unary includes3 times its own query bound and2 times every
intersection with the88 original labels not divisible by3. For a pair
of the66 labels, two states are compatible exactly when they agree modulo
the smaller of their state moduli3 or9. Incompatible states receive zero.
Compatible states receive2 times the lcm query at the finer state. This
still relaxes all further digits and all other prime phases, so its
maximum is an upper bound on the actual selected layout contribution.

## A rational dual that needs no numerical optimizer for verification

Denote these nonnegative unaries by u_i(a) and pair payoffs by w_ij(a,b).
For each unordered edge choose nonnegative charges alpha_ij(a) and
beta_ij(b), satisfying, for every compatible state pair,

 alpha_ij(a)+beta_ij(b)>=w_ij(a,b).

For incompatible pairs the right side is zero, so nonnegativity suffices.
Set the site price

 theta_i=max_a [u_i(a)+sum of charges incident at state a of i].

For any single global assignment, charge each edge to its two endpoints,
then bound each endpoint's resulting cost by theta_i. Consequently

 selected actual contribution <= max F <= sum_i theta_i.

The retained certificate consists only of rational edge charges and these
derived site prices. Its inequalities and final sum are exact finite
arithmetic. A numerical linear program was used solely to propose charges;
upward rational rounding, explicit shortfall repair if needed, and exact
verification establish feasibility independently of numerical optimality.
For this certificate no shortfall repair was required. The ordinary proof
also covers any other feasible charges, with no change of the actual law.

## Near-tightness of this particular relaxation

The rational certificate gives

 U_9=27.32108947114461... .

Assign prefix1 modulo3 to all38 shallow labels, and prefix7 modulo9 to
all28 deeper labels. This is one legal assignment in the relaxed state
problem. Evaluating the same unary and pair tables gives exactly

 L_9=27.321088195401146... <= max F <= U_9.

The gap U_9-L_9 is less than0.000001276. This feasible-assignment value
is a LOWER bound on the RELAXED table objective only. The query entries
are upper estimates, and their other-prime maximizing phases can differ;
L_9 is not asserted to be attained by a complete actual layout or its
true survivor integral.

Relative to the same old selected upper30.108996611942683..., the feasible
dual supplies credit2.787907140798074..., of which0.000945851174455... is
new beyond the first3-root cut. Even the exact optimum of this unchanged
prefix relaxation can improve the first3-root bound by at most

 27.322035322319064...-L_9 <0.000947127.

This rules out a larger gain from optimizing this same prefix relaxation
more accurately, and therefore also from merely improving the feasible
dual of its marginal LP. It does not rule out additional higher-digit relations or a
different relaxation.

The full certified credit is16.8681002893431..., and the B16384 tau1
baseline score remains1.0087465995478049...>1. The D7-complement score remains
1.0477560443597211...>1. The first3 and three-triangle gains are not added
again: this replaces the same selected part of the old Chapter65 bound.
The full-height extension and same-H positive-product tail transport are
unchanged. Unrestricted Erdos7 remains open.

## Complete certificates and reusable programs

The first3 query certificate retains all2662 affected moduli, all three
root entries including root0, the recovered old scalar bound and the
four exact literal overrides at3,9,15,21. The first9 query certificate
retains all1337 affected moduli and all nine prefix entries. Each
first9 record projects back to the previously certified first3 record.
The query recursions use the same actual row reconstruction and child
upper bounds as Chapter65. Their120-second and2,000,000-state guards
require complete output; a guard failure does not produce a completed
certificate.

The binary model includes66 unaries,5808 mixed pairs and2145 pairs
between the selected labels. Its retained graph contains all4356
nonzero directed arcs, their integer capacities and flows, the cut and every
chosen root. The independent verifier reconstructs every coefficient
and arc without calling a flow optimizer. It also reconstructs the
initial row and checks its exact root masses and pure3-power bins.

The prefix model has38 two-state labels and28 five-state labels.
All2145 unordered edges retain complete charge arrays for both
endpoints. The exact checker verifies8616 compatible-pair inequalities;
nonnegativity covers all incompatible pairs. It derives all66 site
prices and all five displayed constant-prefix controls. The numerical
proposal LP has14106 variables,8832 constraints and31488 nonzero matrix
entries. These dimensions do not certify numerical optimality.

| Program | Complete canonical artifact |
|---|---|
| [shared_first3_root_queries.py](../frontier/source-budgets/shared_first3_root_queries.py) | [All root queries](../certificates/source_norms/source-budgets/shared_first3_root_queries.json) |
| [shared_first3_root_cut.py](../frontier/source-budgets/shared_first3_root_cut.py) | [Integer flow and cut](../certificates/source_norms/source-budgets/shared_first3_root_cut.json) |
| [verify_shared_first3_root_cut.py](../frontier/source-budgets/verify_shared_first3_root_cut.py) | [Independent binary certificate verification](../certificates/source_norms/source-budgets/shared_first3_root_verification.json) |
| [shared_first9_prefix_queries.py](../frontier/source-budgets/shared_first9_prefix_queries.py) | [All prefix queries](../certificates/source_norms/source-budgets/shared_first9_prefix_queries.json) |
| [shared_first9_prefix_bound.py](../frontier/source-budgets/shared_first9_prefix_bound.py) | [Rational bound and lower controls](../certificates/source_norms/source-budgets/shared_first9_prefix_bound.json) |
| [verify_shared_first9_prefix_bound.py](../frontier/source-budgets/verify_shared_first9_prefix_bound.py) | [Independent prefix certificate verification](../certificates/source_norms/source-budgets/shared_first9_prefix_verification.json) |

These six programs support `--write` and `--check` under
`python3 -B -I -S -O`. Their checks remain active under optimization,
and their exact certificate paths bind all consumed logical sources,
including the earlier scalar queries, literal masses and restricted
query records. Timings do not participate in certificate equality.

The [rational charge input](../frontier/source-budgets/first9_prefix_edge_charges_input.json)
is sufficient for the standard-library exact checks. The optional
[proposal program](../frontier/source-budgets/propose_first9_prefix_charges.py)
uses NumPy and SciPy to produce candidate charge inputs for this same
model; it is not invoked by any canonical writer or checker. Numerical
output receives no mathematical authority until the exact charge
inequalities and derived site bounds pass.

The ordinary query induction, elementary binary identity and endpoint
charge inequality explain the general implications. The finite
certificates establish these particular same-law values. No new Lean
declaration or unrestricted max-flow theorem is introduced. The full
joint-layout maximum, stronger relations and unrestricted odd covering
remain unresolved.
