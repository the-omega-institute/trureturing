[Index](../../marked_head_profile.md) · [Synchronized matching](354-synchronized-prime-private-cofactor-matching.md) · [Extremal source](350-extremal-paired-branch-and-source-support.md)

# A cofactor-height statistic controls synchronized matching

Fix a support prime p and the finite local model of 354: H>=1,
p-1 non-prime-class roots,
and original labels (r,J,C) of modulus p^e m, 1<=e<=H. For each
cofactor m and exponent e there is at most one label. The pure color
m=1 is absent at tail depth zero. At every x in the actual base R_p,
each root's compatible prefixes cover the entire tail T_p.

For a fixed x, let

    h_m(x) = max{e : an original p^e m label has x in C_(p^e m)},
    m>1, p not dividing m,

omitting colors with an empty set. There are at least p-1 such colors
by 354. Let L(x) be the (p-1)-st largest member of this finite list,
with distinct colors counted once. Multiplicities of equal heights
are retained. Thus 1<=L(x)<=H.

## 1. The stronger stopping theorem

There is a synchronized matching whose witnesses all have e<=L(x).
Consequently, a whole tail cylinder of depth at most L(x)-1 admits
that fixed matching, and

    H_T(G_x) >= p^(1-L(x)).                         (CH1)

Proof. Run 354's matching-preserving path construction only through
depth L(x)-1. If it has not completed, some root has no label on
any node of the constructed path. Every compatible nonpure label
at later depth has exponent >L(x), hence belongs to

    C_x = {m : h_m(x)>L(x)},      |C_x|<=p-2.

Starting at the current node, at each remaining depth avoid every
label whose color lies in C_x or is pure. There are at most p-1
such colors, each with at most one label at that depth across all
roots and nodes. At most p-1 children are forbidden, so a clean
child remains. The final leaf has no later label at all and the
unmatched root had no earlier label. This contradicts full-tail
coverage. Thus the matching was already complete by depth L(x)-1.

Equivalently, the late labels of these at most p-1 colors have total
relative prefix weight at most

    (p-1) sum_(j=L(x)..H-1) p^(L(x)-1-j)
        = 1-p^(L(x)-H) < 1

inside that node; they cannot cover its unmatched root. This is an
argument about the intermediate node, not an assumption that the
globally maximal height can be discarded in advance. It also covers
L(x)=H, when the late inventory is empty. For H=1 or p=2 the same
proof applies without modification.

## 2. Original modulus sets and the actual source

Let h_m=max{e:p^e m is an original modulus}, without conditioning on
x. Let L_* be its (p-1)-st largest height. Then L(x)<=L_*<=H. For
any finite nonnegative base measure nu supported on R_p, with the
explicit product tail Haar law,

    (nu x H_T)(G)
       >= integral_(R_p) p^(1-L(x)) dnu(x)
       >= p^(1-L_*) nu(R_p).                       (CH2)

All these functions are defined on the same finite original base.
An arbitrary law correlated with the tail does not inherit CH2.
At the largest prime this is the actual live endpoint source as
identified in 354. The original label witnesses have matching tails and the same cofactor
state. Different roots still correspond to different original points
in the full CRT carrier.

The fixed-tuple consequence can also retain the improved height. Let
T_low contain the root-indexed original tuples with distinct nontrivial
cofactors and every witness exponent at most L_*. At every x the
constructed good cylinder uses such a tuple. Thus some fixed tuple
has cofactor--tail product mass at least

    [integral_(R_p) p^(1-L(x)) dnu(x)] / |T_low|
      >= p^(1-L_*) nu(R_p) / |T_low|.              (CH2a)

For raw killed cofactor Haar, the nonempty original finite source has
nu(R_p)>=1/B=p^H/Q. CH2a gives a fixed synchronized tuple of mass at
least p^(H+1-L_*)/(Q |T_low|) on this carrier. Lifting to a specified
first-p-digit root multiplies the mass by 1/p. An unconditioned
reciprocal-lcm value must not replace the killed source intersection.

Now assume the original modulus set is divisor-downward closed above
one and has size n. Choose p-1 distinct cofactors realizing the largest
heights h_(1)>=...>=h_(p-1)=L_*. Each contributes all the distinct
moduli p^e m for 0<=e<=h_m. In addition the pure column contributes
p,p^2,...,p^H. The columns are disjoint because their p-free parts
are different. Therefore

    n >= H + sum_(i=1..p-1) (h_(i)+1)
      >= H + (p-1)(L_*+1)
      >= p L_* + p-1.                             (CH3)

In particular define

    L_(n,H)=min(H, floor((n-H)/(p-1))-1),
    L_n=floor((n-p+1)/p).

The nonempty-source hypotheses ensure these upper bounds are at least
one. Also L_(n,H)<=L_n: if both terms in its minimum were at least
L_n+1, then n>=H+(p-1)(L_n+2)>=p(L_n+1)+p-1, contradicting the
specified floor in L_n. CH1--CH3 imply

    H_T(G_x) >= p^(1-L(x)) >= p^(1-L_*)
             >= p^(1-L_(n,H)) >= p^(1-L_n).        (CH4)

CH3 uses divisor closure. The stopping theorem CH1 does not. Local
compatible label sets need not contain all their lower-exponent
parents at x; only the actual modulus set supplies those parents.

## 3. Near the old minimum forces long original columns

If at some x the good-tail mass satisfies

    H_T(G_x) <= C p^(1-H),       C>=1,

then CH1 gives

    L(x) >= H-floor(log_p C).

When this lower bound is positive, at least p-1 distinct cofactors
have compatible labels with heights at least that number. Divisor
closure then forces all their original modulus columns through
that height. In particular

    n >= H+(p-1)(H-floor(log_p C)+1).               (CH5)

For C=1 this requires p-1 distinct cofactors reaching the full height
H and n>=pH+p-1. More generally, if the good mass is strictly less
than p times the old bound, then all p-1 of these columns must reach
H. The conclusion forces multiple distinct exponent levels in each
original cofactor column; it does not say every lower-exponent parent
label is also live at x.

## 4. Local sharpness, including the parent count

Take the sharp local family from 354 with its nonpure depth parameter
L rather than H: p-2 roots have distinct nonpure depth-zero colors;
on the remaining root these colors and the pure color fill p-1
branches at each depth 1..L-1, leaving one continuing branch; a new
nonpure color covers its terminal prefix. The good set is exactly
one cylinder of mass p^(1-L). Extra pure powers may extend the
original height to any H>=L without adding any nonpure matching
outside that cylinder. Thus a large pure height alone cannot worsen
the bound.

Choose the p-1 nonpure colors as distinct primes other than p. The
divisor-closed modulus set

    {p^e:1<=e<=H}
       union {p^e m_i:0<=e<=L, 1<=i<=p-1}

has exactly H+(p-1)(L+1) members. The missing lower powers of the
final new color can be assigned distinct cofactor residues avoiding
the distinguished x; choose its prime larger than L+1. Original
p-free parent classes also avoid x. All prescribed live labels have
cofactor residue zero. The extra pure prefixes and off-source parent
prefixes can lie along the continuing branch. This realizes the
local covering and comparable-class disjointness conditions with
that exact modulus count. For H=L it attains n=pL+p-1 as well as
the mass bound, so the n-only estimate is sharp for this local
information together with its parent inventory.

This is not a whole odd cover, a lex-minimal covering counterexample,
or global sharpness under all extremal hypotheses. Further global
constraints can improve the estimate. The older 354 bound remains
valid; CH1 strengthens it using actual cofactor height information.

## 5. Reproducible checks and remaining obligation

The [existing exact matcher](../../frontier/whole-cover/hsw11_prime_private_matching.py)
now computes each local h_m(x), its order statistic L(x), and checks
that the returned entire good prefix has depth at most L(x)-1. It
retains the earlier full-height checks. All 1,280 selected HSW private
cofactor configurations have L(x)=22, so this particular test family
shows no improvement over its original total-height bound.

Additional local prefix examples let H reach 100 while L remains 1
or 2; their exact good masses are respectively 1 and 1/3. They show
that pure height, and even a single high nonpure column when p=3,
do not set the new threshold. Separate finite AP inventories check
the divisor-closed local sharpness construction in section 4: seven
inventories contain 75 original APs, with 168 proper-divisor membership
checks, 168 comparable-AP disjointness checks, and 176 complete tail
leaves. Each inventory supplies a CRT integer missing every one of
its original classes: take the p-coordinate to be -1 modulo p^H and
each cofactor coordinate to be L+1. These examples are explicitly
not whole odd covers. The general stopping
and counting statements follow from the arguments above; finite
checks do not replace them.

The result converts a small synchronized source fraction into a cost
in original cofactor heights and original class count. It gives no
upper bound on the unrestricted minimum cardinality, and does not
resolve the global parent-modulus replacement required after 354.
These are ordinary proofs and exact programs; no new Lean declaration,
kernel verification or resolution of unrestricted Erdős #7 is claimed.
