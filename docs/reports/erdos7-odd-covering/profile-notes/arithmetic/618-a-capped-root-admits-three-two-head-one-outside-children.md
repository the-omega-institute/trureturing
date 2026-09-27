# A capped root admits three two-head/one-outside children

Keep the actual ten-head restrictions, ordinary private domains and global
two-parent network of [Report614](614-one-global-two-parent-network-preserves-a-common-survivor.md).
Replace its first four outside network entries by one fixed two-head root
and three fixed children, each with those same two head parents and that
root. All subsequent owners retain Report614's arbitrary global two-parent
crossings. The proportion of complete head configurations admitting one
common avoiding extension is greater than 1/220000.

The three children admit actual four-prime originals with TWO head parents
and only ONE outside parent. That case is excluded from Report616. This
extension does not admit Report616's general three-parent networks with two
outside parents; the two extensions have different, non-nested scopes.
This is an ordinary proof with exact rational checks, not new Lean
verification or a resolution of unrestricted Erdős #7.

## The actual family and its fixed choices

First use the reference ten-prime head

    P0={3,5,7,11,13,17,19}, P1={23,29,31}.

Head originals satisfy Report598: pure originals and originals touching P1
are unrestricted; mixed originals within P0 have an exponent at least three,
exponents at most one at both 3 and 5, or at least five distinct prime divisors.
All actual numerical original moduli are distinct and carry one globally
fixed phase each. Heights are arbitrary finite quantities.

Let q0<q1<q2<q3 be the first FOUR outside NETWORK entries, so they are at
least 37,41,43,47. Ordinary private interior primes are not network entries.
The fixed parent pair of q0 is (3,5). The fixed parent triple of each qj,
1<=j<=3, is (3,5,q0). It may own any subset of the actual originals

    3^i 5^j q0^k qv^e,
    i,j,k>=0, i+j+k>0, e>=1.                    (CR1)

Here qv is that child's owner. Zero parent exponents are permitted; there
is still ONE declared inventory at each owner. All later network entries
are numerically greater than q3 and have exactly Report614's fixed pair of
distinct smaller parents. They may connect across roots and head pairs and
may use any of the four special entries as parents. Network size, depth,
width and co-occurrence treewidth are not bounded.

Every network entry retains its actual Report599 ordinary private extension
domain, including pure owner powers. Private interiors remain disjoint from
network entries and from each other away from the declared attachment roots.
Ordinary Type I head branches and separate ordinary components are unchanged.
Every original is assigned once to a head, an owner inventory or an ordinary
block. No additional crossing through private interiors is granted.

The choices below are made together on this ONE actual family. At q0 select
the exponent patterns of the 15 smallest nonunit 3,5-smooth labels and use
threshold 1/5. At each of q1,q2,q3 select the patterns of the 20 smallest
nonunit 3,5,37-smooth labels, with the 37 direction transported to q0, and use
threshold 1/2. No root cap is optimized separately from its downstream fee.

## A capped root preserves the normalized joint-law construction

Use the actual seven-coordinate submeasure eta from Reports598/614:

    eta<=rho=product_(p in P0)rho_p, eta(1)<=1,
    eta(1)-c_head Gamma(eta)>=K,
    K=26345885990886052732242307711
         /9055182074115772514304000000000,
    rho_3<=2H_3, rho_5<=(5/3)H_5.               (CR2)

Other P0 factors retain their p/(p-2) caps. The actual normalized head-only
kernels at 23,29,31 have original-Haar caps 5/3,20/11,2. Consequently the full
head marginal mu has the same density and smaller marginal bounds as in
Report616:

    mu<=C H_P, C=138320/2673, alpha=1/C,
    each one-head marginal<=2H,
    each two-head marginal<=4(H times H).       (CR3)

For the specific first two head coordinates the stronger support-sensitive
bound is available: a queried positive 3-exponent costs factor 2, a queried
positive 5-exponent costs factor 5/3, and an absent query costs no factor.
This follows from eta<=rho and normalized elimination of the other factors;
it is not multiplication of unrelated marginal laws.

For an entry v and a selected set of N nonunit parent patterns, let R_v be
its actual ordinary private domain after deleting all selected-pattern
original towers. Since each tower has at most one actual original per owner
height,

    H_v(R_v)>=D_v/(v-1), D_v=v-3-N.             (CR4)

Let t be the remaining forbidden-fibre mass in the normalized base
H_v(.|R_v). At threshold 0<delta<1, use the existing capped row: if t<=delta,
condition on the allowed part; if t>delta, use relative densities

    (t-delta)/(t(1-delta)) on the forbidden part,
    1/(1-delta) on its complement.              (CR5)

Every row is normalized, including t=1. Its original-Haar density is at
most (v-1)/(D_v(1-delta)), and its violation probability is exactly
(t-delta)_+/(1-delta). In particular,

    violation probability<=t^2/[4delta(1-delta)]. (CR6)

The root q0 now uses CR5 as well. Preload it and all other early roots before
the normalized head-only kernels. Each early-root row depends only on x0 in
P0. Their exact joint law is therefore

    eta(dx0) K_head(dx1|x0)
                     product_(early roots q)nu_q(dz_q|x0).      (CR7)

The head kernels ignore the outside coordinates. Thus the head marginal is
exactly the same mu, and conditioned on the full head, early roots retain
their product kernel. This identity uses normalization of the rows, not the
old root's uniform formula. All remaining entries are sampled in increasing
order after the full head is present. Denote the resulting unnormalized law
by Pi. It is never conditioned on final survival.

## One root cap feeds all three child moments

For q0, N=15 gives D=q0-18 and delta=1/5. Hence

    A(q0)=5(q0-1)/[4(q0-18)]<=45/19.            (CR8)

The quotient (q-1)/(q-18) decreases for q>=37; equality in CR8 occurs at37.
In particular A(q0)<q0/4, so every old outside-prefix comparison survives:

    A(q0)/q0^j<=(r/4)r^(-j) for q0>=r>=37,
    A(q0)/q0^j<=3^(-j), j>=1.                  (CR9)

For a child v, N=20 and delta=1/2 give

    original-Haar cap<=2(v-1)/(v-23)<=40/9<6
                                            for v>=41.       (CR10)

Thus all later two-parent owners can use exactly Report614's reference
kernel and its old conditional cap six. No extra descendant amplification
is omitted. Untouched roots retain their old D>=4 choices.

For reference primes p_i and caps c_i define

    k(e,f)=product_i p_i^(-max(e_i,f_i))
                  *[c_i if max(e_i,f_i)>0, otherwise1].       (CR11)

If S_N is the unit and the N selected nonunit patterns, put

    M(N)=sum_(e notin S_N,f notin S_N)k(e,f).

These are all-height sums. Set

    T_p=1+c[3/(p-1)+2/(p-1)^2],
    R_p(0)=1+c/(p-1),
    R_p(i)=c p^(-i)[i+1+1/(p-1)] for i>=1.

Then the finite complement identity gives

    M(N)=product T_p-2 sum_(e in S_N)product R_p(e_p)
                         +sum_(e,f in S_N)k(e,f).              (CR12)

For q0 use (p_i)=(3,5), (c_i)=(2,5/3) and N=15. Exact evaluation gives

    M_root=1043/9720,
    Pi(E_q0)<=M_root/[4(1/5)(4/5)19^2]
             =5215/11228544.                   (CR13)

For each child use (p_i)=(3,5,37), (c_i)=(2,5/3,45/19) and N=20. Query the
outside root using its conditional cap CR8 and then integrate the joint
head query by CR2. The same Pi therefore gives

    M_child=1248323/4432320,
    Pi(E_qv)<=M_child/(qv-23)^2.                (CR14)

The factor 45/19 is the actual root bound from the SAME root choice used in
CR13. Repeated queries on one coordinate pay their cap only once at the
maximum exponent. Incompatible original phases contribute zero. Expanding
the square and summing the geometric owner-height pair gives CR13--CR14;
no independence between head and root is assumed.

Using q1>=41,q2>=43,q3>=47, the four new entry fees sum to at most

    S=5215/11228544
       +1248323/1436071680+1248323/1772928000
       +1248323/2553016320
     =27577492013/10914144768000.               (CR15)

## Replace the four old rows in the complete global budget

Use the complete, retained old series

    S_E=sum G_E(q)<1/2600,
    S_L=sum G_L(q)<1/125000,
    W_2=sum J_2(v)<1/250000.                    (CR16)

Their exact finite rows and entire prime tails are unchanged. By CR3 and
the original conditional comparison, untouched early roots cost
(10/3)G_E, untouched late roots cost4G_L, and untouched two-parent nonroots
cost2J_2. Ordinary Type I head blockers cost at most2^-16.

The special entries are not charged their old rows as well. Every untouched
network entry is greater than q3>=47. Thus from the old complete series one
may remove all root rows at the reference primes37,41,43,47 and all nonroot
rows at41,43,47. This remains valid when the actual qj are larger: the retained
series then merely includes additional unused nonnegative reference terms.
The exact recovered amount is

    R=sum_(q in {37,41,43,47})[(10/3)G_E(q)+4G_L(q)]
                           +2 sum_(v in {41,43,47})J_2(v)
     =166863257555290507129/139748489904627489600000. (CR17)

All events are now removed from ONE Pi. Equations CR2 and CR13--CR17 give

    Pi(good)>=K-(10/3)S_E-4S_L-2^-16-2W_2+R-S
             >K-1/780-4/125000-1/65536-2/250000+R-S>0. (CR18)

Project the good set using the FULL head density C from CR3. The proportion
of extendible head configurations is strictly greater than

    alpha[K-1/780-4/125000-1/65536-2/250000+R-S]
      =5260468727593499468839527169104406487
          /1136921153757303339735127550853120000000000
      >1/220000.                               (CR19)

The one- and two-head caps pay particular events; they do not replace C in
this projection. A good configuration already supplies all shared network
coordinates. Its actual private ordinary witnesses and the remaining
ordinary components glue without adding a new network assignment. CRT then
gives an integer avoiding every original class. If Q_off is the product of
all outside resolving prime powers, full survivor density exceeds
1/(220000 Q_off); the uniform head fraction is not a height-independent full
density bound.

For any ten ordered odd head primes, transfer the first two head positions
and every full exponent/support vector by Report614's shifted injections
and padded pullbacks. Outside coordinates qj and their order stay fixed.
Each original retains its numerical ownership and fixed parent tuple, with
an injective label correspondence and one phase per transformed label.
A padded-source extension gives a target extension with the same outside
witness, and averaging the head injections transfers CR19. The source
marginal constants are not asserted unchanged for an arbitrary target law.

## A genuinely new actual family, and remaining restrictions

At the reference primes take the originals

    3*5*37,
    3*5*37*41, 3*5*37*43, 3*5*37*47,

all with phase zero, and include the other eight head primes by pure-prime
originals. The first original forces37 to have its two head interfaces.
The later four-prime originals require a fixed inventory containing both
head directions and37. They cannot be represented by Report614's fixed
pairs or Report616's triples with at least two outside parents. Absorbing37
into a private interior would violate the required interfaces and
disjointness, and the fixed ten-smallest-prime head cannot absorb it.

Conversely, this result grants no other three-parent owner. In particular
it does not cover Report616's arbitrary later triples with two outside
parents. The present result keeps only three prescribed two-head/one-outside
children attached to the first root. Arbitrary numbers of these children,
other head-pair triples, multiple inventories at an owner, extra private
crossings and unrestricted head labels remain outside the proof.

The improvement comes from changing one normalized root row while keeping
its actual downstream cap in the same budget. Merely optimizing the root's
own fee and the child fees under separate best laws would not establish
CR18.

## Retained exact certificate

The [producer](../../frontier/cover-geometry/capped_root_three_child_forward_kernels.py)
and [data](../../frontier/cover-geometry/capped_root_three_child_forward_kernels.json)
check 59 named conditions: checked input fingerprints, literal selected
patterns, complete moment identities, normalized cap inequalities, exact
recovered rows and the final positive rational budget. The common-law
identity CR7, conditional comparisons and witness gluing are ordinary
proof obligations supplied above, not consequences of finite arithmetic
checks. No new Lean verification is claimed.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/capped_root_three_child_forward_kernels.py
