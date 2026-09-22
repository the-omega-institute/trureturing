[Index](../../marked_head_profile.md) · [Common prefix laws](376-complete-prime-chain-transport-and-joint-prefix-laws.md) · [Actual fibre lifts](442-minimum-coarse-sources-lift-through-actual-fibres.md)

# One supported law couples row caps to all tree-prefix caps

These are ordinary finite-flow deductions using the tree interfaces of reports376 and442. No new Lean certification or literature priority is claimed.

Let a finite rooted tree have leaf set Y. For each proper node v, let
Y_v be its descendant leaves and let kappa(v) be a nonnegative rational
capacity. Let F be an actual subset of {1,...,m} x Y, and fix
1 <= q <= m. Assume that, for every q-element row set U, the projection
of F restricted to U supports a probability eta_U with

    eta_U(Y_v) <= kappa(v) for every proper node v.

Then there is ONE probability nu supported on F satisfying simultaneously

    nu(row r) <= 1/(m-q+1),
    nu(Y_v) <= kappa(v),
    nu(row r, Y_v) <= (q/m) kappa(v).

All capacities and a resulting law can be rational. No independence or
compatibility of the separate witness laws eta_U is required.

## Proof by one finite flow network

Use a private copy of the prefix tree for every row r. Send an edge of
capacity 1/(m-q+1) from the source to its private root. Every private
parent-to-child edge ending at v has capacity (q/m) kappa(v). Use a
second, common copy of the tree, with edges directed from each proper
node v to its parent and capacity kappa(v); its root is the sink.
For each actual point (r,y) in F, join its private leaf to the common
leaf y by an edge of capacity one. There are no other such bridges.

A unit flow produces the desired law: the flow on the actual bridge
(r,y) is nu(r,y). Private tree edges bound joint row-prefix masses,
the common tree edges bound pure prefix masses, and the source edges
bound row masses. Conversely, any law obeying the caps induces this flow.

Consider an arbitrary source-sink cut. If it cuts an actual bridge,
its capacity is already at least one. Otherwise let A be the private
row roots on the source side and let a=|A|. The top edges alone cost
(m-a)/(m-q+1), which is at least one when a<q.

Suppose a>=q. Let P be the proper common-tree prefixes whose upward
edges cross the cut, and for r in A let L_r be the private prefixes
whose downward edges cross it. Write

    R = sum_(v in P) kappa(v),
    L = sum_(r in A) sum_(v in L_r) kappa(v).

For each U subset A of size q, P together with the L_r for r in U
covers the projected actual support F|U: follow the full source-sink
path of any actual point in that projection. Its top edge does not
cross the cut and no bridge crosses; hence a listed prefix edge must.
Apply the projected law eta_U and the union bound to obtain

    1 <= R + sum_(r in U) sum_(v in L_r) kappa(v).

Averaging over all q-subsets of A gives

    1 <= R + (q/a)L.

Thus the non-top cost retained in this argument obeys

    R + (q/m)L >= (a/m)[R+(q/a)L] >= a/m.

Unlisted cut edges have nonnegative capacity. Consequently the complete
cut costs at least

    (m-a)/(m-q+1) + a/m
      = 1 + (m-a)(1/(m-q+1)-1/m) >= 1.

Finite max-flow/min-cut supplies a flow of value at least one; truncate
or scale it to value one. This proves all three cap families under one
law chosen solely from the source and capacities.

The coefficient q/m cannot be decreased in this general theorem. Take
a one-level tree with m leaves, kappa(y)=1/q, and the m-point diagonal
source F={(r,r)}. Every q-row projection admits its uniform law. Every
law on F has an atom of mass at least 1/m, so a common joint coefficient
beta must satisfy beta/q>=1/m, or beta>=q/m. The uniform diagonal law
also meets the stated row and pure-prefix caps.

## Five-by-seven specialization

Let F subset Z/5 x Z/7^K, K>=1, meet every product of a three-element
five-row set and a complete five-ary depth-K seven-tree. For each three
rows, the seven projection meets every five-ary tree. The seven-tree
complement duality gives a complete ternary tree in that projection.
Its uniform leaf law has every length-b prefix mass at most 3^(-b).
The theorem with m=5,q=3 therefore supplies one actual law with

    row <= 1/3,
    seven-prefix(b) <= 3^(-b),
    joint(row,seven-prefix(b)) <= (3/5)3^(-b),  b>=1.

The factor 3/5 is already sharp in the five-point diagonal matching
at K=1. This statement uses full five-row input; no missing row or
standalone five-ary projection hypothesis is required.

## Consumer: an isolated ternary five-prefix skeleton

Let H>=1,K>=1, and let R subset Z/5^H x Z/7^K meet every product of a
complete ternary five-tree and a complete five-ary seven-tree at the
full respective heights. Assume its projection onto the first H-1
five digits is exactly the leaf set of one complete ternary tree.
For H=1 this is the sole empty prefix and imposes no extra restriction.

Every one of the 3^(H-1) occupied five-prefixes s is isolated by a
legal five-tree: at each step along s choose the desired occupied child
and the two unoccupied children, completing empty branches arbitrarily.
Therefore its actual last-five-digit/whole-seven fibre meets every
three-row set times every five-ary seven-tree. Choose the specialized
joint-prefix law above in each actual fibre, and mix all these laws
with weight 3^(-(H-1)). The resulting single law on R has cylinder caps

    cap(A,B) = 3^(-A-B),                     0<=A<=H-1, 0<=B<=K,
    cap(H,0) = 3^(-H),
    cap(H,B) = (9/5)3^(-H-B),               1<=B<=K.

For all the original divisor labels 5^A 7^B, keep their residue phases
independent. Expanding their load square into ordered indicator pairs
uses the cap at the pair's LCM. The number of exponent pairs with
maximum (A,B) is (2A+1)(2B+1), whether or not their phases agree. Hence,
with S_J=sum_(j=0)^J (2j+1)3^(-j)=3-(J+2)3^(-J), the SAME law satisfies

    Gamma_(5^H 7^K)
      <= S_H S_K + (4/5)(2H+1)3^(-H)(S_K-1).

The coefficient of S_K is positive. As K tends to infinity this bound
increases to

    9 + (H-22)/(5*3^H).

Thus every H<=21 has a positive gap below nine uniformly in finite K.
At H=22 every finite K still has a strict gap, while the limit equals
nine. For H>=23 this certificate alone does not give a uniform gap.

At H=2 the skeleton condition is exactly three occupied first-five roots; the second-five digits may have arbitrary actual support. Every finite seven-height K then has the uniform bound77/9<9. This closes that source class without assuming a minimum mod175 projection.

At H=3 the general bound is

    (23/9)S_K + 7/27 + (7/15)(S_K-1),

whose limiting value is 1196/135=9-19/135. At K=2 its value is
3044/405, improving the same-source marginal-only certificate eight.
Here all twelve numerical divisor labels and all 144 ordered pairs
are retained. The hypotheses permit every mod175 fine fibre to have
matching number two; the selected coarse fibres retain the entire
seven coordinate.

The law is chosen once for each fixed finite R,H,K before testing any
layout. The construction does not assert projective compatibility of
the choices for different finite sources or heights.

These are ordinary finite-flow and tree deductions, not Lean-certified
statements. They neither establish the two-sided joint-cap template
for arbitrary height-(2,2) local blockers nor settle the arbitrary
three-first-five-root source at height-(3,2). No source realization as
an odd-cover residual follows from the abstract blocking hypotheses.

## At most four occupied terminal rows remove the height restriction

Retain the exact ternary five-prefix skeleton of depth H-1. In a local
last-five/whole-seven fibre let n be the number of occupied last-five
rows. The blocking condition forces n>=3, since otherwise three empty
rows would miss the source. Adjoin all 5-n empty rows to any n-2 occupied
rows. This is a three-row set, so its seven projection meets every
complete five-ary seven-tree and supports the required ternary law.

Apply the general coupling theorem with m=n,q=n-2. The row cap remains
1/3, while the joint coefficient becomes

    beta_n=(n-2)/n = 1/3, 1/2, 3/5 for n=3,4,5.

If EVERY local fibre has at most four occupied last-five rows, take
beta=1/2 uniformly; the number and identities of occupied rows may
differ between fibres. The same equal mixture along the actual ternary
skeleton then has final-five positive-seven cap (3/2)3^(-H-B). Thus

    Gamma_(5^H 7^K)
      <= S_H S_K + (1/2)(2H+1)3^(-H)(S_K-1)
      < 9-(H+5)/3^H < 9.

The middle quantity is the limit as K tends to infinity. This gives a
positive gap for each fixed H and every finite K, for all H>=1. The
gap tends to zero with H; no constant below nine uniform in both
heights is asserted.

The row restriction is not supplied by divisor closure. Report350's
EB2 does force every pure 5^j, j<=H, when an original modulus contains
5^H. But a pure 5^H class deletes just one terminal digit in one
mod5^(H-1) fibre. It does not supply a missing terminal digit in every
occupied fibre. The stated additional support hypothesis remains
necessary for this application of the theorem.

## Full blocking does not guarantee either existing local selector

At heights H=3,K=2, use literal coordinates

    x5=r+5a+25u mod125,   x7=y+7v mod49.

Let r range over {1,2,3}, and a,v each over {0,1,2,3,4}. Set

    Y_0=(1,2,3), Y_1=(1,4,5), Y_2=(2,4,6),
    Y_3=(3,5,6), Y_4=(1,2,6).

At the first, second and third column y of each ordered triple Y_a,
respectively allow u in {0,1}, {1,2}, {0,2}. These are 450 distinct
CRT residues, occupying 45 mod175 cells and 15 mod25 prefixes. They
avoid first-five roots 0,4 and first-seven root 0, including every
mod25 class inside first-five root4. Both prime projections also meet
every complete ternary tree at their respective full depths.

Fix any complete ternary depth-three five-tree and complete five-ary
depth-two seven-tree before choosing a witness. The first-five roots
meet {1,2,3}; choose such an r. Let D be the five roots of the given
seven-tree. Every unordered pair of seven roots lies in at most two
of the five Y_a. Hence at most two a have |Y_a intersect D|=1, and
at least three have |Y_a intersect D|>=2. The three second-five digits
under r meet these good a; choose one. Any two of the displayed u-pairs
have union {0,1,2}, which meets the given three last-five digits.
Choose a compatible u and then y in the SAME given seven-tree. Its
five children below y meet {0,...,4}, supplying v. This is one actual
point of the source and both fixed trees, proving full product-tree
blocking with root/tail dependence retained.

Nevertheless every occupied mod175 fibre is exactly a two-row by
five-column rectangle in (u,v), so its maximum matching has size two.
The matching-three selector of report442 is empty. For any occupied
mod25 prefix (r,a), choose the seven-tree roots by deleting the first
two columns of Y_a. Its only remaining source column permits u in
{0,2}; choose the last-five set {1,3,4}. Any completion of those seven
roots misses the whole fibre. Thus all fifteen mod25 fibres fail the
local blocking premise used by this report's skeleton construction.
The three-row seven projection has tree-capacity exactly2/3 under
the caps3^(-b), so it also fails the common-law premise directly.

These failures persist under deleting source points. No mixture of
subsources each required to pass either fixed fibre test can repair
this example. Global blocking here lets the helpful second-five child
depend on the tested seven-tree; it does not supply a fixed good fibre.

This is an obstruction to the two selectors, not to the desired law.
The uniform probability on the 450 points has exact cylinder maxima
indexed by A=0,...,3 and B=0,...,2:

    [ 1,     1/5,   1/25  ]
    [ 1/3,   1/15,  1/75  ]
    [ 1/15,  1/45,  1/225 ]
    [ 1/45,  1/90,  1/450 ].

All twelve original phases remain independent. Their full 144-term
LCM bound gives Gamma_6125<=218/45<9 for this one law. No optimality
or odd-cover realization is claimed. Neither fixed selector settles
the general three-first-root height-(3,2) problem. Coupling across
second-five children or additional arithmetic hypotheses remain
possible routes; this example does not make either route necessary.

## Exact construction and controls

The standard-library companion [tree_cap_coupling.py](../../frontier/cover-geometry/tree_cap_coupling.py)
implements `couple_tree_caps(m, q, radix, depth, source, caps)` for
positive-depth, lowest-digit-first radix trees. The proof above permits
arbitrary finite rooted trees; that broader interface is not implemented.
The program checks every q-row projected capacity, constructs an exact
rational unit flow, and recomputes normalization, actual support, row
caps, pure-prefix caps and joint-prefix caps from the same output law.

From the repository root, run:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/tree_cap_coupling.py
```

The controls include the sharp diagonal, nonuniform rational capacities,
five rejected malformed or unsupported inputs, and 900 exact finite-height
identities. They support the implementation; the general statements use
the cut and tree proofs above, not these finite checks.

The consumer reuses report442's existing 540-point source. The flow selects
153 actual points, with 17 per occupied mod25 fibre and local denominator45.
For this particular output law, the original-label LCM upper bound and an
attained centered-layout lower bound both equal3044/405, so its Gamma is
exactly3044/405. This construction does not optimize Gamma for each source:
on the same 540-point source the earlier uniform law has Gamma265/54 and
the earlier reweighted law has Gamma394/81, both smaller. The improvement
here is the uniform guarantee for the entire stated source class and its
extension to higher trees, not a better law for this particular source.

The same companion constructs the 450-point selector obstruction from
its literal triples, verifies all 45 matching failures and all 15 missing
local product trees, and checks the uniform law's twelve caps and
144-term bound. Its 44,100 checks cover the local choices used in the
full-tree witness proof; they do not enumerate all pairs of full trees.
It also checks 4,800 finite algebra identities for the n=3,4,5 terminal-row
corollaries. The unrestricted height statements follow from the formulas
and monotonicity, rather than these bounded checks.
