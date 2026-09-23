# Complete weighted boundaries cut a binary obstruction

Combining weighted axis and mixed budgets excludes a triple contained
in the binary support of
[report500](500-a-binary-support-survives-1608-triple-exclusions.md):

    17s1+16s2+13s3>=4/77.                                 (C1)

For this triple, each of the ten basic mixed objectives separately has
nonpositive minimum, even on the complete weighted axis domain. A fixed
nonnegative combination has minimum32>0 because the objectives must use
the same axis pair. Thus ten-direction completeness of the pointwise
budgets does not justify replacing their joint use by ten separate minima.

The full symmetry orbit gives48 new edges. They cut the old binary
support, but deleting two points repairs it with exact mass still above
m7. This establishes a new local relation and the remaining limitation
of the specified1656-edge system. It does not give a global upper-bound
improvement, an arithmetic realization or unrestricted noncoverage.
The proof and certificates are ordinary mathematics and exact rational
computation, not new Lean verification.

## One original family and complete weighted axis domains

Retain the fixed chart, labels and common-selector convention of
[report499](499-weighted-mixed-budgets-exclude-old-zero-triples.md).
Every full numerical label d*23^j*29^k has one fixed A/B old-centre
selector shared among all tested old points. Define

    N(w)=sum_d max(sum_i w_i 1_Ai(d),sum_i w_i 1_Bi(d)).

Use all ten directions from
[report498](498-ten-directions-completely-describe-three-point-weighted-budgets.md):
the seven nonzero0/1 directions and112,121,211. With this set R, let

    P_h={v:0<=v_i<=h, r dot v<=N(r) for every r in R}.

For the actual pure-axis deletions t_i=22alpha_i,u_i=28beta_i,
t belongs to P22 and u belongs to P28. If s_i is the actual fraction
of full23/29 Haar surviving the later classes in that old fibre, then
for every fixed w>=0 report499's common mixed budget proves

    616*sum_i w_i*s_i>=g_w(t,u),
    g_w(t,u)=sum_i w_i(22-t_i)(28-u_i)-N(w).               (C2)

Old-only survival is an additional requirement before s_i represents
full-family survival. Independent old-point sources or independently
chosen selectors for the three fibres are not substituted in C2.

## Exact local certificate

The ordered profiles and their declared indices are

    v1=(4,2,-4,1,2,1,1)       index4407,
    v2=(5,-2,4,1,1,1,1)       index5640,
    v3=(-5,-3,-2,1,1,1,1)     index16010.

Their boxes have51 literal old exponent labels. The seven subset
capacities, in binary-mask order, are

    (22,21,39,30,45,42,58),

and N112=85,N121=78,N211=79. For w=(17,16,13), N(w)=892.
The complete P22 and P28 have17 and22 vertices. Exact evaluation of
all374 pairs gives

    min g_w=32,
    t=(18,21,18), u=(21,13,24)

as a minimizing pair. Its residual areas are(28,15,16), so
17*28+16*15+13*16-892=32. The fixed-weight objective is affine in
either axis argument separately; report499's successive-vertex proof
therefore makes this finite calculation a bound on the whole domain.
C2 proves C1. Three strictly bad fibres are impossible whenever

    0<theta<=32/(616*46)=2/1771,

in particular at the common theta=1/3696.

For this same weight, using only the seven subset axis directions gives
minimum-59 on14*16 vertex pairs, attained at
t=(22,17,19),u=(0,21,21). This verifies that the selected certificate
cannot discard the extra axis constraints. It does not claim that each
of the three extra directions is necessary, or that every possible
weight fails on the old domain.

## Complete basic budgets do not mean separate minima suffice

On the complete axis domain, the basic mixed objective minima are:

| Mixed direction | Minimum of g_r |
| --- | ---: |
| 100 | -22 |
| 010 | -14 |
| 110 | -4 |
| 001 | -30 |
| 101 | -45 |
| 011 | -28 |
| 111 | 0 |
| 112 | -27 |
| 121 | -4 |
| 211 | -16 |

No row alone supplies a positive lower bound. Nevertheless the
same-cone decomposition

    (17,16,13)=12(111)+(211)+3(110)

has additive capacities

    892=12*58+79+3*39.

Thus at EVERY common axis pair,

    g_w=12g111+g211+3g110.

Minimizing the three terms independently retains only
12*0-16+3*(-4)=-28. Minimizing their sum on a common axis pair gives32.
The strict difference is not an extra inventory direction: report498's
ten directions already describe every pointwise weighted budget.
It is a loss caused by allowing each term a different minimizing pair.
All values and minimizers in the table are retained in the exact result.

## Forty-eight edges and a precise remaining binary obstruction

There are288 simultaneous split-coordinate/common-coordinate/global-flip
transformations of the seed. All remain in the chart because each split
entry of every seed profile is nonzero. Literal A/B membership-pattern
checks transport the same bound, giving48 distinct edges with no overlap
with the1608 in report500. The point weights follow the ordered images.
Report499's box-inclusion argument makes these valid constraints on the
upward closure of actual bad profiles.

The report500 support violates exactly

    {4405,5640,16010}, {4407,5640,16010}.

Removing4405 and4407 preserves upward closure; all old pair and triple
upper constraints persist under taking a subset. The consumer separately
checks every order arrow and all1656 triple edges. The repaired support
retains15797 middle points and the entire Q>=39 overflow, with

    loss=25797248/11816768588625
        =0.000002183105119349872...,
    eta(U_repaired)=0.01615007258449842...,
    eta(U_repaired)-m7=0.00007017140894286592...>0.          (C3)

This loss is optimal only among upward subsets of that fixed baseline.
Indeed every repair must remove an endpoint of each violated edge.
Deleting an endpoint forces deletion of all its selected ancestors.
The3*3 endpoint choices give nine such unions. Each union is itself a
valid repair; any repair contains one of these unions. Nonnegative
comparison weights therefore reduce the exact minimum removal cost to
the nine retained rational sums. The displayed two-point deletion attains
their minimum. Adding points outside the baseline is outside this claim.

The report495 half-integral support satisfies all48 new edges as well:
40 doubled-cover sums are2 and eight are3. No stronger fractional or
binary global optimum is asserted. In particular C3 shows that the
specified1656-edge system still cannot yield an auxiliary upper bound
below m7. More complete joint relations or a different source estimate
are needed to use the existing positive-survival bridge.

## Reproduction

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_split_complete_weighted_boundary.py

The standard-library consumer reconstructs the literal profiles,
capacities, complete rational vertices, basic minima, orbit and nine
deletion choices. It pins the already verified report500 support and
result to inherit all pair constraints, recomputes the relevant literal
shell weights, and checks order directly. A default run compares the
whole result with the adjacent JSON. No solver output, proposed graph,
NumPy dependency or transient search file is an input.
