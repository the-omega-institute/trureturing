# Genuine triples and upward order leave a fractional obstruction

The mixed two-centre comparison still admits a fractional bad-support
function of mass

    0.016545212156457986... > m7 =7235955529/450000000000.     (F1)

It obeys every positive pair exclusion, all432 genuine three-point
constraints in a specified symmetry family, and the complete upward order
with the3/5 coordinates fixed. Its excess over m7 is

    0.00046531098090242957... .                              (F2)

These values are rounded displays of exact rational calculations. This
is an obstruction to obtaining a sufficiently small upper bound from the
stated fractional relaxation. It is not a binary support, an actual source,
or an original congruence covering. Integrality and further genuine joint
constraints remain available. The result does not settle unrestricted
Erdos#7 or even all mixed two-centre configurations.

## Fixed source and the relaxation being tested

Use the same completed actual source as
[report494](494-three-fibre-inventories-exclude-a-pair-admissible-triple.md):
the worst shallow type(2,4,1), reference values(2,7,3,4), first-root splits
at3,5,7 and common queried paths at11,13,17,19. Its source lower mass is m7
and its density with respect to old-coordinate Haar is at most27/2.
The auxiliary comparison law eta retains the literal six exclusions

    0 mod3, 1 mod9, 4 mod27, 0 mod5, 1 mod25, 2 mod15.

Their complement modulo675 has221 cells. The conditional comparison caps
at7,11,13,17,19 are(3/2,5/3,3/2,2,9/5). No averaged replacement source,
new selector per point, or reference chosen separately for a bound is used.
The exact consumer checks the pinned source data and all these constants.

Write a profile as

    v=(signed3,signed5,signed7,common11,common13,common17,common19).

At each split coordinate,+f denotes factors(f,1),-f denotes(1,f), and0
denotes(1,1). The3-coordinate cannot be0 on this shallow chart. Write A_v
and B_v for the two labelled old-cofactor boxes, including the unit label.
If C_v is the product of the four common factors and a_v,b_v are the
products of the three split factors for A,B, then

    Q_v=|A_v union B_v|=C_v(a_v+b_v-1).

There are3332 profiles with Q<=19 and20076 with20<=Q<=38. The remaining
Q>=39 profiles form the infinite overflow. Their total eta mass is computed
exactly by subtracting the finite masses from221/675. This accounts for all
finite valuation depths; any infinite-depth reference singleton has zero
mass under the geometric comparison law.

At theta=1/3696, the earlier source argument bounds the bad set by an
upward profile support, with the3/5 factors held fixed. Its indicator z is
binary and satisfies

    z_v=0                    for Q_v<=19,
    z_u<=z_v                 for each allowed enlargement u<=v,
    z_u+z_v<=1               for every valid pair edge,
    z_u+z_v+z_w<=2           for every declared triple edge.  (F3)

The fractional relaxation replaces z in{0,1} by0<=z<=1. For the common
threshold, pair edges require K2>=1/3 and triple edges require K3>=1/2.
The witness below satisfies even every pair with K2>0. It therefore also
satisfies all pair edges valid at the stated threshold, without a claim
that an arbitrarily small positive bound suffices for that threshold.

## An explicit half-integral witness

The adjacent certificate stores20076 integers c_v in{0,1,2} in the fully
reconstructed profile order. Define

    z_v=0                    if Q_v<=19,
    z_v=1-c_v/2              if20<=Q_v<=38,
    z_v=1                    if Q_v>=39.                    (F4)

The finite middle contains11420 entries with z=1,7557 with z=1/2, and1099
with z=0. Exact summation of eta(v)z_v plus the overflow gives F1/F2.
Every profile weight uses the literal3/5 anchor cells and the stated
geometric comparison shells; no rounded optimization weights enter F1.

The consumer checks all16858 immediate middle-to-middle order arrows
and88764 immediate middle-to-overflow arrows. Each fixes3/5 and enlarges
one of7,11,13,17,19. At7, zero may grow to either sign; a nonzero sign may
only increase its absolute factor. These arrows generate the required
order. Arrows from Q<=19 preserve F3 because z=0 there; all arrows within
the overflow preserve it because z=1 there.

## Every potentially violated pair has an exact zero witness

A pair inequality can fail only when c_u+c_v<2, meaning z=1 against z=1
or z=1/2. There are151503430 such unordered distinct pairs in the finite
middle. For each, reconstruct the literal capacity

    N_uv=sum_d max(1_Au(d)+1_Av(d),1_Bu(d)+1_Bv(d)).          (F5)

For the split/common profiles, Boolean expansion gives

    N_uv=Q_u+Q_v-I_uv(crossA+crossB-2),                      (F6)

where I_uv is the product of the four common-coordinate minima, crossA
is the product of the three split-coordinate minima between A_u and B_v,
and crossB uses B_u and A_v. This identity is checked on all16 membership
patterns. Direct labelled-set enumeration independently checks the minimum
capacity in each cover/load group.

Group the deficient pairs by loads Q_u,Q_v and their cover values. There
are371 group pairs, collapsing to175 load pairs. An exact integer scan
finds the least N in each. The scan also includes repeated-profile pairs;
its161537537 elementary computations include those diagonals and the
extra symmetry within equal groups. Its census is checked separately from
the witness inequalities. All integer intermediates are bounded by
4*38^7+76, below the signed64-bit limit.

For each minimum(q,r,N), the consumer supplies rational axis allocations
t,u and mixed deletions d satisfying

    0<=t_i<=min(22,Q_i), 0<=u_i<=min(28,Q_i),
    sum_i t_i<=N, sum_i u_i<=N,
    d_i=(22-t_i)(28-u_i)<=Q_i, sum_i d_i<=N.                 (F7)

Thus the older pair relaxation permits zero surviving area. Larger N only
relaxes these budgets, so no deficient pair has a positive pair bound.
All remaining middle pairs already obey their inequality numerically.

Every pair involving overflow and another Q>=20 profile has, after
swapping points if necessary,

    Q_1>=20, Q_2>=39, N>=max(Q_1,Q_2)+1>=40.

The last inequality follows from the shared unit label: it contributes2
to N, while every other union label of either point contributes at least1.
The single rational witness

    t=(20,20), u=(18,22), d=(20,12)

satisfies F7 at(20,39,40), hence at every such larger capacity triple.
Pairs touching Q<=19 automatically obey F3 because their z is0. This
proves the complete pair claim without reading a producer's pair graph or
trusting its completeness.

## The declared genuine triple family

The certificate specifies these nine ordered seed triples by their indices
in the reconstructed20076-profile order:

    (108,98,931), (108,110,931), (110,98,931),
    (108,14353,3256), (108,14353,3307),
    (2780,14353,3307), (2784,14353,3307),
    (98,1007,12715), (110,8038,14062).

For each seed, compute all seven literal capacities

    N_I=sum_d max(sum_(i in I)1_Ai(d),sum_(i in I)1_Bi(d)).

Then enumerate all rational vertices of the two axis polytopes P22,P28
from report494 and minimize its bilinear expression over every vertex
pair. There are six ordered capacity types, or five up to point permutation:

| Representative(N1,N2,N12,N3,N13,N23,N123) | K3 |
| --- | ---: |
| (20,20,40,24,40,40,58) | 6 |
| (20,22,40,24,40,42,58) | 2 |
| (20,24,40,28,40,32,48) | 16 |
| (20,24,40,24,40,40,56) | 16 |
| (24,24,38,24,42,40,54) | 10 |

Every value exceeds1/2, so every seed excludes simultaneous bad fibres
at the same theta. Generate all simultaneous permutations of the three
split axes, permutations of the four common axes, and global A/B swaps.
Among2592 images,960 leave the chart because signed3 becomes0. The1632
eligible images deduplicate to432 triples. Literal set counts verify the
preserved capacities; the witness satisfies sum c_v>=2 on every triple.
Coordinate permutations preserve these capacities, not the profile weights;
all transformed weights are recomputed on the original chart.

The family is precisely this symmetry closure. It is not asserted to
contain every genuine three-point constraint, and no claim is made that
triples meeting overflow always have zero bounds.

## Consequence for the actual-source proof and reproduction

For any upper bound U on every actual upward bad support, the existing
same-source comparison would yield

    Haar(original survivors)>=(m7-U)/49896                  (F8)

when U<m7. A fractional feasible point with F1 prevents these F3 constraints
alone from proving such a U for their whole fractional feasible set.
It does not prevent a smaller bound for binary supports or for actual
sources satisfying additional arithmetic relations. The7557 half entries
mark information lost by this particular relaxation; they do not describe
half-present points in an original family.

Reproduce the complete result with:

    python3 -I -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_split_fractional_support_barrier.py

NumPy is required only for bounded exact integer pair scans; all masses,
vertices and zero witnesses use rational arithmetic. The consumer reads
the compact witness and pinned existing source results, reconstructs all
other data, and compares its result with the adjacent JSON. It imports no
solver, producer graph, search log or floating optimization certificate.
The result is an ordinary proof with exact finite checks, not Lean
certification. Original source construction, all mixed charts and
unrestricted noncoverage are not newly verified by this consumer.
