# A phase-block deficit consumed by the adaptive triple survivor bound

Keep exactly the three old profiles, fifty-one old numerical labels, common
old CRT centres and points, and complete ten-direction axis polytopes used in
[report508](508-adaptive-triple-gain-without-a-uniform-mixed-inventory-rebate.md). Pure and mixed classes have their actual original selectors and
phases: there is at most one class per complete numerical modulus, shared
across all three tested old points. The new coordinates carry full uniform
product Haar measure. Finite pure and mixed families are allowed to omit
labels. This is an ordinary proof supported by exact rational arithmetic;
it is not a Lean verification.

Write t_i and u_i for 22 and 28 times the respective pure-axis deletion
fractions, and s_i for the later-fibre survivor fractions after the mixed
classes. Thus s_i is nonnegative. Let

    w=(17,16,13), v=(17,9,8), v2=(9,16,9).

The established mixed-capacity sums are N(v)=671 and N(v2)=662. The old
relaxed objectives and their branch minima remain unchanged:

    g_v(t,u)=sum_i v_i(22-t_i)(28-u_i)-671,
    min_{t_1<=20} g_v=41,
    min_{t_1>=20} g_v2=92.                              (1)

The new conclusion is

    616 w dot s >= C := 41+616/667 = 27963/667,         (2)
    w dot s >= 27963/410872,
    max_i s_i >= 27963/13969648.                        (3)

The denominator in the final inequality uses the selected branch weight,
whose coordinate sum is 34; w itself has coordinate sum 46. No arithmetic
sharpness or improved global source-mass bound is asserted.

## The seventeen-label block and its exact selector regret

Consider only the first-mixed complete labels d*23*29 for

    d=1,3,9,21,27,63,81,147,189,441,567,1029,1323,
      3087,3969,9261,27783.

For weight v, the sums of their individual maximum activation scores total
229. For each of these labels, every maximizing old selector activates the
second old point. Every nonmaximizing selector loses at least one unit of
score. An absent label loses at least one as well. These statements are
checked from the literal old CRT residues, independently agreeing with the
profile-box masks. The old label 5 is deliberately excluded: its masks 100
and 011 both have score 17, so a maximizing selector need not activate point 2.

Let c count block labels that are absent or use a nonmaximizing selector.
The chosen geometric score of the block is at most 229-c, and at least
17-c labels activate the second point. This counts choices in one actual
family and makes no pointwise selector reassignment.

## Packed root cells on the good region

Define the good part of the first branch by

    t_1<=20,  t_2>=4180/207,  u_2>=3052/261.            (4)

Let a_r and b_s be conditional pure-survivor fractions in the 23 and 29
first-digit cells of the second old fibre. They lie in [0,1] and satisfy

    sum_r a_r=23(1-t_2/22)<=17/9=1+8/9,
    sum_s b_s=29(1-u_2/28)<=152/9=16+8/9.              (5)

Pure classes on the two axes act independently on their respective
coordinates. Consequently the pure-surviving mass in phase cell (r,s) is
a_r*b_s/667. This equality uses the declared product Haar measure.

For 0<=k<=17, let T_k be the sum of the k largest root-cell products a_r*b_s.
Apply the separately convex packed-cell inequality P3 of
[report511](511-pure-axis-totals-force-a-phase-deficit-without-fixed-phases.md)
to the two caps in (5). Up to row and column permutations, the maximizing
relaxed vectors are

    a*=(1,8/9,0,...,0),
    b*=(1 repeated 16,8/9,0,...,0).

Independent row and column permutations leave the product multiset
unchanged. Its positive terms are 16 copies of 1, 17 copies of 8/9, and
one copy of 64/81. Therefore

    T_k <= k-(1/9)(k-16)_+,  0<=k<=17.                (6)

This is a relaxed upper bound; the packed vectors need not be claimed to
arise simultaneously at all old points from a legal pure family.

If k block labels activate point 2, their union uses at most k root cells,
so its mass is at most T_k/667. Relative to their chosen geometric capacity
k/667, (6) saves at least (1/9)(k-16)_+/667 in that fibre. The fibre weight
is 9. Since k>=17-c, the weighted block union U_block obeys

    667 U_block
      <=229-c-(k-16)_+
      <=229-c-(1-c)_+
      <=228.                                           (7)

For c=0 the phase packing saves one; for c>=1 the selector regret already
saves at least one. Repeated phases only reduce the union. Losses in the
other two fibres are nonnegative, so ignoring them preserves the upper
bound. This proof controls the actual block union relative to the fixed
geometric ceiling 229/667, not a separately optimized individual-envelope
quantity under changed pure families.

## Subtract this block once from the whole mixed bound

For every old label d and positive heights j,k, the ordinary geometric
capacity is max(v dot A_d,v dot B_d)/(23^j*29^k). Summing over all potential
complete mixed labels gives

    sum_{d,j>=1,k>=1} capacity(d,j,k)=671/(22*28)=671/616.

This infinite sum is only an upper bound on any actual finite inventory;
it does not assert that an infinite family is a covering system.

The seventeen block labels are distinct members of this potential
inventory, all with j=k=1. Their geometric capacities sum to 229/667.
Replace only their combined contribution by (7), and leave all other
complete numerical labels at their ordinary geometric capacities. The
whole actual mixed union inside the pure survivors is then at most

    (671/616-229/667)+228/667 =671/616-1/667.           (8)

This is valid even if some block or other labels are absent. The bound
uses subadditivity between the block and the rest; no overlap loss is
subtracted twice. The exact weighted pure-survivor product is

    sum_i v_i(22-t_i)(28-u_i)/616.

Subtracting (8), and then using (1), proves throughout (4)

    616 v dot s >= g_v(t,u)+616/667 >= C.              (9)

## The complementary regions retain stronger old objective bounds

For each h in {22,28}, P_h has coordinate bounds 0<=x_i<=h and inequalities
w_d dot x<=n_d, in direction and capacity order

    directions: 100,010,110,001,101,011,111,112,121,211;
    capacities: 22,21,39,30,45,42,58,85,78,79.

Within t_1<=20, the complement of (4) is covered by the following closed
regions; overlap at a threshold causes no difficulty:

| Added inequality | t vertices | u vertices | Pairs | Minimum g_v |
| --- | ---: | ---: | ---: | ---: |
| t_2<=4180/207 | 15 | 22 | 330 | 8821/207 |
| u_2<=3052/261 | 15 | 10 | 150 | 1269/29 |

The respective unique minimizing vertex pairs are

    t=(3893/207,4180/207,3893/207), u=(22,12,23);
    t=(18,21,18), u=(22,3052/261,23).

Both exact minima are greater than C=27963/667. All vertices were obtained
by enumerating all triples of independent active constraint normals,
solving them by Cramer's rule with rational arithmetic, and retaining
exactly feasible points. The polytopes are compact and full dimensional.
Every vertex appears in that list. For either variable fixed, g_v is
affine in the other; successive linear minimization therefore attains a
minimum at a vertex pair. The reported values are exact polytope minima,
not sample estimates or claims that the minimizing budgets are arithmetic
families. The ordinary old mixed bound proves 616 v dot s>=C on both regions.

## Exhaustion and transport

The good and two bad regions exhaust t_1<=20. Therefore 616 v dot s>=C
throughout that first branch. The other branch t_1>=20 retains
616 v2 dot s>=92>C from (1). Both weights are coordinatewise at most w,
and s is nonnegative, proving (2). In either branch, the weight used is
nonnegative and sums to 34. Thus its dot product with s is at most
34 max_i s_i, proving (3) without incorrectly assigning sum 34 to w.

The actual full-family survival interpretation still requires the old
points to avoid all old-only classes. The result strengthens the existing
triple survivor inequality; it does not produce a new Boolean triple edge
or improve a completed-source mass bound. It is a conditional phase loss
consumed with exhaustive complementary bounds, not a uniform inventory
rebate for all pure families.

## Reproduction

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/phase_deficit_triple_survival.py

The standard-library consumer reconstructs all51 literal old-label masks,
the17 forced labels and their selector regret, and the packed-cell bound.
It regenerates all vertices and checks1074 rational objective values:
594 for the two original branches and480 for the complementary regions.
It compares the regenerated certificate and result to their adjacent JSON
files by default. Source hashes bind the old CRT configuration and report508.
The arbitrary-family phase proof is (5)–(8), not an extrapolation from finite
phase samples.

The old first-branch minimum41, N(v)=671, second-branch minimum92 and fixed
objective minimum32 remain unchanged. The improvement comes from applying
the additional same-family phase constraint and covering its complement.
