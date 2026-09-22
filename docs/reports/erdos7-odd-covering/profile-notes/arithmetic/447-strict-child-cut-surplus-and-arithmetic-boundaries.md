[Index](../../marked_head_profile.md) · [Direct child flow](446-direct-child-flow-and-incidence-caps.md)

# Strict direct flow at occupancy (4,5,5,5)

This is an ordinary finite-network proof. It constructs a supported law; it does not assert that every law satisfying the earlier non-strict caps has moment below nine. No Lean certification or realization by an actual covering system is claimed.

At height(2,2) and occupancy4555, the projected-law and standalone-tree premises below force every actual network cut to have capacity at least65/63. If every root/first-seven cylinder meets at most two children, one supported law then has original-label second-moment bound569/65<9. Together with the other occupied-child cases, the common bound is79/9 whenever at least one child is missing and the same incidence and tree premises hold.

Let F be a finite actual source on four occupied first-five roots, literal second-five children, and seven-prefix leaves of height two. After permuting the roots, let the occupied-child counts be n=(4,5,5,5), and put q_r=n_r-2, so q=(2,3,3,3). Assume:

* For each pair of roots and each choice of q_r actual children at the first and q_s actual children at the second, the combined seven projection supports a probability with every depth-B prefix bounded by kappa_B=3^(-B), B=1,2.
* The complete seven projection of F contains a full five-ary tree of height two.

The first premise follows from full ternary-five times five-ary-seven product blocking by adjoining the empty children and the empty first-five root. More generally it can be checked directly as a projected-law premise. The second premise is separate: feasibility of fractional prefix caps alone must not be substituted for literal tree existence.

Use the actual-child network: source-to-root capacity1/3, root-to-actual-child capacity1/9, private downward seven-prefix edges of capacity gamma*kappa_B, actual child/leaf bridges of capacity2, and a common upward seven-prefix tree of capacity kappa_B, with gamma=2/7. Each child retains its own private tree until its actual bridge. The sink is the root of the common tree.

## All cuts have cost at least65/63

A cut crossing an actual bridge has cost at least2. Otherwise let a_r be its number of source-side actual children at root r, and define

    T = sum_r min(1/3,(n_r-a_r)/9),
    I = {r : a_r>=q_r}.

The top edges cost at least T. Let R be the cut cost in the common seven tree, and let L_rc be the cut cost in a private child tree before multiplication by gamma. Thus R and every L_rc are nonnegative integer multiples of1/9. Private costs at sink-side children, if any, only increase the cut.

For R<1 set t=1-R. The projected-law premise and the union bound give, for any r,s in I and any selected active-child subsets A,B of sizes q_r,q_s,

    sum_(c in A) L_rc + sum_(c in B) L_sc >= t.             (S1)

Indeed every actual point in that restricted projection has a path from its source-side child node to the sink; since its actual bridge does not cross, some private or common prefix edge on the path must cross. A projected witness law bounds the union of these prefix events by the displayed cut sums.

Averaging (S1) gives x_r+x_s>=1, where

    x_r = q_r sum_(active c) L_rc / (a_r t),
    w_r = a_r gamma/q_r.

For nonnegative x satisfying these pair inequalities,

    sum_I w_r x_r >= min(W/2, W-max_I w_r),
    W=sum_I w_r.

Indeed, if every x_r>=1/2, use the bound W/2. Otherwise take a smallest x_j=z<1/2. The other coordinates are at least1-z, so the weighted sum is at least (W-w_j)+(2w_j-W)z. This affine function on0<=z<=1/2 is at least min(W-w_j,W/2), hence at least the claimed bound.

Consequently the total cut is at least

    T+min(1,W/2,W-max_I w_r)                               (S2)

when |I|>=2. When |I|<=1, every ineligible root contributes exactly1/3 to T.

For |I|=0, T=4/3=84/63. For |I|=1, T>=1, and at least one active actual child has a nonempty set of bridges. Its path to the sink crosses a private or common prefix edge, since no bridge crosses. The least positive capacity of these edges is2/63, so the total cost is at least65/63.

For |I|=2,3, the minimum of (S2) is respectively8/7 and22/21. These bounds follow from the endpoint values

    u_r=min(2/9+gamma/2,n_r gamma/(2q_r)),
    v_r=min(2/9+gamma,n_r gamma/q_r),

which here are

    u=(2/7,5/21,5/21,5/21),
    v=(32/63,10/21,10/21,10/21).

For a fixed eligible set of size j, the half-sum and exclusion branches minimize to

    (4-j)/3 + sum_I u_r,
    (4-j)/3 + sum_(I except h) v_r.

For j=2 their minima are8/7,8/7; for j=3 they are22/21,9/7. The T+1 branch is at least1+(4-j)/3. Thus the minima of S2 are72/63 for j=2 and66/63 for j=3. If R>=1, the top contribution gives at least1+(4-j)/3, also greater than65/63.

Suppose |I|=4. If not all a_r=n_r, then T>=1/9. In the half-sum branch each coefficient of a_r is gamma/(2q_r)-1/9: it is-5/126 at the four-child root and-4/63 at each full root. The unique minimum at full activity is1, so a non-full profile has half-sum branch at least1+5/126. Every actual cut lies on the1/63 lattice; hence this branch rounds up to66/63. Each exclusion branch is at least10/7=90/63, and T+1>=70/63. If R>=1, the top contribution gives at least70/63 directly.

It remains to treat a=n=(4,5,5,5). Here T=0. If R>1, then R>=10/9=70/63 because R lies on the1/9 lattice. For R<1 write

    R=k/9,  u=9-k,  k in{0,...,8},
    z_rc=9 L_rc.

Every z_rc is a nonnegative integer. Let p_r be the minimum sum of q_r of these integers under root r. Equation S1 implies p_r+p_s>=u for every two roots. Sorting a root's child costs shows that a total of n nonnegative integers whose least q sum is p is at least

    f_(n,q)(p)=p+(n-q)ceil(p/q).

Indeed the q-th smallest integer is at least ceil(p/q), and the other n-q integers are at least that large. The lower bound is attained by dividing p as evenly as possible between the first q integers and setting all others to ceil(p/q). In the present case write

    f2(p)=p+2ceil(p/2),  f3(p)=p+2ceil(p/3).

For the minimum possible total Z=sum_rc z_rc under the pair constraints, select a root attaining the smallest p. Each other root is at least z=max(p,u-p). Their mutual constraints are then satisfied by setting all three equal to z. Since both functions are increasing, this minimizes the cost for that choice. It suffices to consider0<=p<=ceil(u/2): if the smallest p exceeds this endpoint, reducing all four coordinates to ceil(u/2) preserves feasibility and lowers the cost. The exact integer minimum is therefore

    Z_min(u)=min_(0<=p<=ceil(u/2))
               min(f2(p)+3f3(z), f3(p)+f2(z)+2f3(z)),
    z=max(p,u-p).

The two expressions correspond to whether the smallest p occurs at the four-child root or at a full root. The finite values are:

| k | u | Z_min(u) | Minimum numerator 7k+2Z_min(u) |
| ---: | ---: | ---: | ---: |
| 0 | 9 | 35 | 70 |
| 1 | 8 | 32 | 71 |
| 2 | 7 | 29 | 72 |
| 3 | 6 | 22 | 65 |
| 4 | 5 | 19 | 66 |
| 5 | 4 | 16 | 67 |
| 6 | 3 | 15 | 72 |
| 7 | 2 | 12 | 73 |
| 8 | 1 | 9 | 74 |

The actual cut cost is at least R+gamma*sum L_rc=(7k+2Z)/63, so these values give at least65/63. The control program checks the displayed one-dimensional formula against all four-coordinate candidates0<=p_r<=u (clipping a larger coordinate to u preserves every pair constraint); the formula itself follows from the sorting and minimum-coordinate argument above.

Finally suppose R=1. If any private edge crosses, it adds at least2/63 and the desired bound follows. Otherwise every private cut cost is zero. A crossing top edge would itself add at least7/63, so it too can be excluded when proving the lower bound. All actual child nodes are source-side. Every actual child/leaf path must therefore cross a common-prefix edge: no positive private edge or bridge can cross. The common cut covers the full actual seven projection. Put the uniform branching measure mu on its assumed complete five-ary tree. For a depth-B prefix, mu(v) is either0 or5^(-B), and

    kappa_B=3^(-B)>=(5/3)mu(v),  B=1,2.

Since the cut-prefix events cover that tree, their mu-masses sum to at least1, even if events overlap. Consequently

    R=sum_(common cut edges v) kappa(v)
      >=(5/3)sum_v mu(v)>=5/3,

contradicting R=1. This exhausts all cuts and proves the lower bound65/63.

## A quantitative margin and the original-label moment

Every network capacity is an integer multiple of1/63:

    1/3=21/63, 1/9=7/63,
    gamma/3=6/63, gamma/9=2/63, 2=126/63.

The preceding classification shows that every cut is at least65/63. Finite max-flow/min-cut supplies a flow of value at least65/63; scaling down if necessary gives exactly65/63. Normalize its masses on actual bridges by this value. The result is ONE probability nu on the original source whose root, child, pure-seven and child/seven caps are all the earlier caps multiplied by alpha=63/65.

If every root/first-seven cylinder meets at most two actual children, the SAME law also has root/seven cap alpha*(4/7)3^(-B). With all nine original divisor labels of L=25*49 retained, their unscaled caps are

    q_1=1,
    q_5=q_7=1/3, q_25=q_49=1/9,
    q_35=4/21, q_175=2/21,
    q_245=4/63, q_1225=2/63.

The unscaled complete LCM sum over all81 ordered label pairs is9. The sole pair whose LCM is1 is(1,1); its contribution remains1. Every other pair is bounded by alpha times its previous cap, for every independent choice of the original phases. Therefore

    Gamma_1225(nu) <= 1+alpha*(9-1)=569/65<9.

The law is chosen before the phases. This construction uses the actual source and its projected witnesses, together with the strict cut argument; it is not a consequence of the old nine caps alone. The proof is stated for height two and occupancy (4,5,5,5), and asserts no compatibility between laws constructed on different sources or heights.

## Combining the occupied-child cases

Let F subset Z/25 x Z/49 have exactly four occupied first-five roots, block every product of a complete ternary five-tree and complete five-ary seven-tree (both height two), and have a standalone seven projection containing a complete five-ary tree. Assume at least one actual second-five child is missing under an occupied root and every root/first-seven cylinder meets at most two children. Then there is ONE supported probability with Gamma_1225 at most79/9<9, for every independently phased layout on all nine original divisor labels.

Indeed, occupancy4555 is the strict theorem above. With at least two missing children and each root having at least three, [446](446-direct-child-flow-and-incidence-caps.md)'s occupancy theorem gives at most79/9. Since569/65<79/9, this is the common upper bound over the two cases. If a root has at most two children, the three-empty-child test makes the other three roots individually robust, so the existing three-robust-root bound from [444](444-uniform-subtree-restrictions-couple-two-prefix-trees.md) applies. Its value at K=2 is65/9<79/9. This last branch does not require the incidence hypothesis. No new original modulus is introduced to account for missing children.

## Old caps can all be sharp on the same source

The strengthened construction is necessary: the nine earlier caps alone do not force every feasible law to be strict. The [exact saturation source and law](../../frontier/cover-geometry/child_cut_saturation.py) provide a121-point source with occupancy4555, incidence exactly two at every root, all600 literal pair/triple product-blocking checks, a standalone complete five-ary projection, and four individually nonrobust roots. It misses the first-five and first-seven zero digits, the complete mod25 class21, and the complete mod49 class37.

In coordinates(r,c,g,h), where x5=r+5c and x7=g+7h, its first root has child incidences

    c0->{1,6}, c1->{1,6}, c2->{2,3}, c3->{4,5}, c4->empty,

with every h=0,...,4 at each listed incidence. At r=2,3,4 start with c->g=c+1; at g=1 use h in{0,r-1}, and at the other columns use h=0,...,4. Add g=2 with all five h-values at child c2. There are40 points in root1 and27 in each other root.

For two full roots, distinct column triples give at least three full columns, while equal triples containing column1 have two full columns and a union of at least three second digits in column1. At root1, every triple except{c0,c1,c4} already contains at least three full columns; that exceptional triple has columns1,6, and any triple at another root supplies at least two further full columns. Thus every restricted pair contains a ternary seven-tree, proving product blocking. Root1's exceptional triple and each full root's triple{c0,c1,c2} give the nonrobust witnesses: exclude their two full columns, and at a remaining two-leaf column choose the five complementary second digits.

A supported39-atom law of denominator63 attains all nine old caps at the same CRT center1. Its literal masses are retained in [the data](../../frontier/cover-geometry/child_cut_saturation.controls.json). The global cylinder maxima, in units1/63, are

| Five depth / seven depth | 0 | 1 | 2 |
| --- | ---: | ---: | ---: |
| 0 | 63 | 21 | 7 |
| 1 | 21 | 12 | 4 |
| 2 | 7 | 6 | 2 |

Choosing phase1 for every original divisor makes all81 pair bounds equalities. The load takes values1,2,3,4,6,9 with respective masses(33,14,4,4,6,2)/63. Hence its second moment is exactly9. This is a valid joint choice from the independently allowed phases and uses one fixed law.

Applying the strict constructor to this SAME121-point source instead produces a37-atom law with the new caps and full LCM upper569/65. Thus the counterexample excludes an inference about every old-cap-feasible law; it does not exclude existence of a better law, prescribe the chosen law, or establish arithmetic realization by an odd cover.

## Original arithmetic exclusions do not imply the incidence hypothesis

There is also a separate exact boundary on what the current residual premises supply. Take one AP at each nonunit divisor of1225:

| Modulus | Residue | Private witness relative to this partial family |
| ---: | ---: | ---: |
| 5 | 0 | 5 |
| 7 | 0 | 7 |
| 25 | 21 | 46 |
| 35 | 34 | 34 |
| 49 | 48 | 48 |
| 175 | 173 | 173 |
| 245 | 242 | 242 |
| 1225 | 241 | 241 |

The [independent exact program](../../frontier/cover-geometry/original_head_exclusions.py) computes its common avoid-set F of736 points. The family is divisor-closed, all19 comparable class pairs are disjoint, and the displayed witnesses establish local irredundancy. Its source has occupancy4555 and incidence maxima(4,5,5,5). It passes all600 literal product-blocking checks and both standalone tree conditions. All phases and the full avoid-set are retained in [the data](../../frontier/cover-geometry/original_head_exclusions.controls.json).

Therefore these original exclusions, divisor closure, local irredundancy and tree conditions do not imply incidence at most two or a second missing child. This is the avoid-set of a PARTIAL AP family, not a full covering system, a globally minimum cover, or a realized residual of such a cover. It also does not rule out a useful lower-incidence subsource inside this avoid-set.

For the actual 3-free residual R3 with remaining-digit and outside-cofactor states, a child belongs to the incidence set at(r,g) exactly when SOME such state survives over that child. Consequently an incidence bound of two requires at least three children at every(r,g) whose ENTIRE remaining fibres are covered by actual 3-free originals: for every tail/cofactor state there must exist an original covering it. Individual cylinder exclusions do not supply this universal fibre-coverage assertion. Whole-cover constraints, paired original classes and compatible cofactor transport remain possible extra inputs; this counterexample has not supplied or refuted them.

## Exact construction controls and remaining scope

The direct constructor's explicit `strict_one_gap=True` option requires actual occupancies4555, depth two, gamma2/7, ternary prefix caps and the literal standalone five-ary projection, then checks every pair of actual-child subset projections. It uses bridge capacity2 before scaling the ENTIRE network by63/65 and calls the existing exact unit-flow primitive. It checks support, normalization and every scaled cap on the one resulting law. The divisor1 cap stays1. The default general interface and its previous data remain unchanged.

The [strict controls](../../frontier/cover-geometry/strict_child_cut_surplus.py) retain [three constructed laws](../../frontier/cover-geometry/strict_child_cut_surplus.controls.json):

| Actual source | Points | Positive law atoms | Denominator | Theorem upper | Law's LCM upper |
| --- | ---: | ---: | ---: | ---: | ---: |
| One-gap control from446 | 116 | 36 | 65 | 569/65 | 542/65 |
| Old-cap saturation source | 121 | 37 | 65 | 569/65 | 569/65 |
| Common CRT translation of that source | 121 | 35 | 65 | 569/65 | 111/13 |

The translation adds3 modulo25 and8 modulo49 to every point. These are compatible components of one translation modulo1225; no branch obtains an independent phase choice. Each control checks480 actual-subset projection premises, all600 original pair/triple tree predicates,1080 numerical cut profiles, all9 original cylinder caps and the full81-pair sum. The shared profile audit finds only81 one-eligible-root equality profiles and the one all-active profile; the mathematical proof bounds all those actual cuts by at least65/63. The integer reduction also checks all25332 clipped four-coordinate candidates against its one-dimensional formula. Eight rejection controls cover the mode, height, occupancy, coefficient, prefix caps, standalone tree, projected-law and incidence premises.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/strict_child_cut_surplus.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/child_cut_saturation.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original_head_exclusions.py
```

These rational controls do not optimize Gamma or replace the general cut proof. The result removes the one-missing-child equality obstruction under the stated incidence and standalone assumptions. It does not prove a general incidence theorem or a suitable subsource-selection theorem, handle arbitrary prime heights, supply simultaneous full cofactor transport, or resolve unrestricted Erdős #7. The retained proof is ordinary mathematics with exact construction controls, not a new Lean-certified declaration.
