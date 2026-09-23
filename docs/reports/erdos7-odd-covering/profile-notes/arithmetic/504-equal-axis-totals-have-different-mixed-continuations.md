# Equal axis totals have different mixed continuations

Two actual finite families can have identical pure-axis deletion counts and
identical combined survivor counts at every tested old point, yet respond
differently to the same next original congruence class. In the example below,
adding0 mod667 deletes weighted mass46/667 from one family and33/667 from
the other. Even the best choice of a common residue modulo667 has these
different values.

Thus per-point axis totals are not a sufficient boundary for subsequent
mixed-label operations. The missing relation is the alignment of phases
across old points. This is a finite arithmetic counterexample to summary
sufficiency, not an upper-bound improvement for all original families or a
resolution of Erdos#7. The proof is ordinary mathematics, with exact integer
checks and no new Lean verification.

## Same original labels, references and tested old points

Use the three profiles and51 old numerical labels from
[report503](503-integer-selectors-strengthen-capped-budgets-but-axis-limits-survive.md):

    (4,2,-4,1,2,1,1),
    (5,-2,4,1,1,1,1),
    (-5,-3,-2,1,1,1,1).

Retain its single pair of old CRT centres and its three simultaneous old
points. Both families contain exactly the102 original moduli

    {23d : d in D} union {29d : d in D}.

These moduli are distinct, odd and greater than one. Every label has one
fixed old selector and one new-prime phase. Only first new-prime levels
are used. There is no independently chosen selector for each tested point.

Family F uses report503's certified phases. Family G changes only two
23-axis phases, preserving their old selectors:

| Old label d | Activated old points | Modulus | Phase change | Original residue change |
| ---: | --- | ---: | --- | --- |
| 35 | third point only | 805 | 3 to0 modulo23 | 141 to736 modulo805 |
| 13 | first point only | 299 | 18 to22 modulo23 | 156 to91 modulo299 |

The other old-point memberships are unchanged. Other labels still occupy
phases3 and18; the new phases0 and22 were previously unused by every old
point. Each point's active labels therefore still have distinct phases.
The29-axis family is identical in F and G.

Write P_i and Q_i for the deleted first phases in F23 and F29 over old
point i. For both families,

    (|P_1|,|P_2|,|P_3|)=(18,21,18),
    (|Q_1|,|Q_2|,|Q_3|)=(21,13,24).                     (P1)

Thus the axis deletion fractions agree exactly, not merely asymptotically.
On the full uniform23-by29 fibre, the pure families leave

    ((23-|P_i|)(29-|Q_i|))_(i=1..3)=(40,32,25)           (P2)

of the667 points. Even these combined per-fibre survivor totals agree.

## One fixed mixed continuation distinguishes the families

The numerical modulus667=23*29 has not been used by either family. Its old
cofactor is1, so it activates all three old points and has no old-selector
ambiguity. For a common new phase(a,b), its newly deleted weighted mass is

    L(a,b)=(1/667)*sum_i w_i
                    1_(a notin P_i)*1_(b notin Q_i),
    w=(17,16,13).                                      (P3)

This is one actual original residue modulo667, shared by all three fibres.
The weights are a declared task readout, not a probability distribution on
the completed old source.

For F, phase0 is undeleted in both axes at all three points. The fixed
continuation0 mod667 therefore deletes one additional point from each fibre,
with

    L_F(0,0)=(17+16+13)/667=46/667.                      (P4)

This is also the maximum over every common mixed phase, since46 is the
total available weight.

For G, the union P_1 union P_2 union P_3 is all of F23: all21 old used
phases remain occupied somewhere, and the two modifications add0 and22.
Every a is consequently already deleted at at least one old point. Since
the smallest weight is13,

    L_G(a,b)<=33/667 for all(a,b).                       (P5)

At a=0 only the third point is already deleted on the23 axis. The29 phase
b=0 remains undeleted at all three points. Hence the same fixed continuation
0 mod667 gives

    L_G(0,0)=(17+16)/667=33/667,                         (P6)

attaining the upper bound. The exact response difference is13/667. After
this fixed continuation, the three survivor counts become(39,31,24) for F
and(39,31,25) for G.

The future operation here is fixed and legal in both families. No optimal
controller or inaccessible choice is needed to distinguish them. The
additional all-phase maximum calculation shows that freely choosing a
common mixed phase does not remove the discrepancy either.

## What a boundary must retain for this task

For a fixed pure-axis pair, keep the phase-indexed surviving-point sets

    R_p(a)={i:a notin P_i}, R_q(b)={i:b notin Q_i}.

If a mixed label has selected old activation mask C_d, its incremental
response is read from

    R_p(a) intersect R_q(b) intersect C_d.               (P7)

The totals in P1 and P2 cannot reconstruct this common intersection. The
example preserves those totals and changes both a specified response and
the best possible response.

At these fixed first levels and fixed old interfaces, an exact representation
for continuing mixed deletions consists of the current survivor table
H_i(a,b) together with the set U of already used original numerical moduli.
Here every permitted old cofactor d divides the fixed old carrier M, so its
selected mask is constant on each old fibre; otherwise that interface must
also be refined before applying the update.
The label d*23*29 must satisfy d*23*29 notin U before it can be added.
Adding that class with the single selected old mask C_d and common phase
(a0,b0) updates

    H'_i(a,b)=H_i(a,b)*
       [1-1_(i in C_d)*1_(a=a0)*1_(b=b0)],
    U'=U union {d*23*29}.                               (P8)

Initially H_i(a,b)=1_(a notin P_i)*1_(b notin Q_i). After mixed deletions,
that product representation need not persist. The table computes the response
of a specified legal operation; U preserves the distinct-modulus legality
test. Together they suffice for this restricted finite task, without a
minimal-state claim or an efficient solution for arbitrary prime powers.
Deeper moduli require the corresponding phase resolution; original-label
restrictions must be retained at every level.

The common CRT realization does not imply that a particular completed
conditional source places positive mass on these points. The pair supplies
no uniform discount below the old mixed budget: F itself permits the full
single-label response. The remaining research obligation is a bound on
joint phase arrangements valid for every relevant original family and
connected to the actual-source estimate.

## Reproduction

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/equal_axis_totals_distinct_mixed_responses.py

The standard-library consumer reads the fixed report503 certificate and
arithmetic data, constructs every original residue in F and G, and checks
numerical-modulus distinctness. It enumerates all667 integers in each of
the three old fibres for each family, testing the original congruences
directly. It then checks the fixed continuation and all667 common mixed
phases. The adjacent JSON retains both complete families, phase sets,
response counts and exact maxima; no exploratory search is needed.
