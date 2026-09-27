# Integer triangle cuts give a strict relaxation gap

For the same fixed mixed comparison as
[report495](495-genuine-triples-and-order-leave-a-fractional-obstruction.md),
every binary upward bad support has auxiliary mass at most

    U=0.01642282793189944... <4105707/250000000.              (I1)

The exact rational certificate uses pair exclusions, genuine three-point
constraints, upward order, and triangle inequalities that follow from the
pair constraints for binary variables. The bound remains above

    m7=7235955529/450000000000=0.01607990117555555...,
    U-m7=0.00034292675634388614... .                         (I2)

Thus this is a stronger upper bound, not a noncoverage proof. It also
gives a strict quantitative distinction between the previous fractional
relaxation and its binary feasible set. If OPT_frac and OPT_bin denote
their respective supremal masses, report495's explicit feasible mass L
and this universal upper bound imply

    OPT_frac-OPT_bin >= L-U
                     =0.00012238422455854343... >0.         (I3)

Neither optimum needs to be known or attained to prove I3. All displayed
decimals are rounded from exact rational values in the adjacent result.

## The same domain and source throughout

Keep the six original shallow exclusions, reference values(2,7,3,4), first
splits at3,5,7, common queried paths at11,13,17,19, and theta=1/3696 from
report495. The profile domain, weights eta, conditional caps and completed
actual source are identical. The finite middle has20076 profiles with
20<=Q<=38; profiles with Q<=19 have support indicator0. Count all Q>=39
mass on the upper side. The3/5 coordinates stay fixed under upward closure.

The system defining OPT_frac and OPT_bin contains the common valid pair
constraints K2>=1/3, the432 declared genuine triples with K3>=1/2, and the
complete later-coordinate upward order. One may instead include every
positive pair inequality in both systems: report495's witness satisfies
all of them, and this upper bound uses only those valid at the common
threshold. The same gap conclusion follows for that stronger pair system.

All original full numerical labels and their single fixed selectors remain
unchanged. Source lower mass m7 is used only through the existing same-source
bridge. No positive comparison weight is promoted to a lower bound on
actual-source occupation.

## Where binary information strengthens a pair constraint

Suppose three profiles i,j,k have pair exclusions

    z_i+z_j<=1, z_i+z_k<=1, z_j+z_k<=1.

Adding gives2(z_i+z_j+z_k)<=3. For binary z the sum is an integer, so

    z_i+z_j+z_k<=1.                                        (I4)

This triangle cut is valid without any new arithmetic assumption. It is
different from a genuine three-point inventory constraint, which may hold
even when all three pair bounds are zero and gives a right side of2.
Both kinds are used here with their respective right sides.

A concrete active triangle has profiles

    (2,-2,-2,1,2,2,1),
    (3, 2, 2,1,2,1,1),
    (-5,2,-2,1,2,1,1),

at indices1077,2782,15563. Their three literal pair capacities and bounds are

| Pair | Q_i,Q_j,N_ij | K2 |
| --- | --- | ---: |
| 1,2 | 20,24,38 | 7 |
| 1,3 | 20,22,38 | 10 |
| 2,3 | 24,22,36 | 5 |

Every bound exceeds the required1/3. The fractional witness from report495
assigns1/2 to each of these profiles, satisfying the three pair inequalities
but violating I4. This displays the lost integer information directly.

## An exact upper certificate with all rounding residuals paid

Collect the selected valid inequalities into A z<=b and let w_v=eta(v)
for the finite middle. Choose any nonnegative rational row multipliers y.
Set

    r_v=w_v-(A^T y)_v.

For every feasible0<=z<=1,

    sum_v w_v z_v
      =y^T A z+sum_v r_v z_v
      <=y^T b+sum_v max(r_v,0).                            (I5)

Add the full overflow mass to the right side. This is an exact upper bound
even when the proposed multipliers were obtained approximately. Every
positive residual is recomputed from the exact profile weight and paid.
No solver status, floating objective, or optimality assertion enters I5.

The certificate uses positive integer row numerators with common denominator
10^13. There are

| Active row kind | Count | Right side |
| --- | ---: | ---: |
| Pair exclusion | 8960 | 1 |
| Genuine triple | 8 | 2 |
| Integer triangle cut | 484 | 1 |
| Upward order z_i-z_j<=0 | 706 | 0 |

Order rows have one negative coefficient. Their multipliers remain
nonnegative, and their signed column contributions are retained before
computing the residuals. Dropping that negative contribution would invalidate
I5. The exact row-price numerator is85242794419. The consumer sums all20076
residual terms and the same full overflow mass, obtaining I1.

Only the actually used rows require certification. The8960 pair rows and
the constituent edges of the484 triangles involve10204 distinct pair edges
and340 ordered capacity types. Each is reconstructed from its original
labelled divisor boxes; the least active K2 is exactly1/3. The exact pair
bound uses the rectangle-boundary minimum proved in
[report481](481-individual-mixed-budgets-strengthen-two-fibre-certificates.md)
and applied to the labelled inventories in report489.
It evaluates all endpoints and intersections of the four affine residual
pieces on each rectangle edge using rational arithmetic.

Each of the eight genuine triples is separately verified from its seven
literal capacities and complete rational axis-vertex sets, using the
bilinear minimum from report494. The consumer also verifies membership in
report495's declared432-triple family. Every order row is checked to be a
single allowed enlargement at7,11,13,17 or19 with3/5 unchanged. Thus the
upper bound depends on no unverified edge-list completeness claim.

## What the bound settles and what it leaves open

I3 proves that integrality can lower the bound by a strictly positive
amount in this exact arithmetic model. This is stronger than observing
that one fractional assignment violates one cut: the universal binary
upper bound lies below a certified fractional feasible mass.

The same-source noncoverage criterion still requires U<m7, since it would
give original survivor Haar mass at least(m7-U)/49896. I2 does not meet
that criterion. It is neither a feasible-support construction of mass U
nor a proof that further cuts cannot cross m7. Additional genuine joint
constraints, stronger integer deductions and other actual-source information
can still improve it. Other reference charts and unrestricted Erdos#7
remain open.

Reproduce with the standard-library consumer:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_split_integer_cut_bound.py

The compact input contains only the row indices and exact multipliers.
The consumer regenerates the profile space and all exact weights, checks
every active arithmetic row and integer cut, recomputes the entire residual
bound, and checks the pinned prior fractional result for I3. Its output is
compared to the adjacent JSON. It imports neither a solver nor a producer
graph. These are ordinary proofs and exact rational certificates; no new
Lean verification is claimed.
