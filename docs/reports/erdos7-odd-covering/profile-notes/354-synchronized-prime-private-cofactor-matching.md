[Index](../marked_head_profile.md) · [Extremal source](350-extremal-paired-branch-and-source-support.md)

# Synchronized prime-private cofactor matching on the actual live source

In the hypothetical lexicographically extremal distinct odd cover of
350 (minimum cardinality, then minimum modulus sum), every point
of a prime's private cofactor region admits a **common tail coordinate**
at which all other first-prime-digit roots are covered by original
labels with pairwise distinct nontrivial cofactors. The matching uses
one cofactor state and one common tail; the original points are
`(r,t,x)` in their respective roots. It does not combine independently
attained root optima or assert intersection of APs in different roots.

A finite prefix-tree argument proves this directly. It also gives
conditional tail Haar mass at least `p^(1-H)`, where `H` is the full
original height at that prime. At the largest support prime the source
is exactly the live pre-prime survivor. This does not produce a
cover-preserving replacement or settle unrestricted Erdős #7.

## 1. The original source and local hypotheses

Use the extremal system of [350](350-extremal-paired-branch-and-source-support.md),
with original classes `A_d=a_d mod d`, `n` distinct odd nonunit moduli,
and full period

    Q = p^H B,     gcd(p,B)=1,     H>=1.

The original prime class `A_p=a_p mod p` is present. Irredundancy makes
it disjoint from every other original whose modulus is divisible by
`p`. Write the complete CRT carrier as

    F_p × T_p × X_p,
    T_p = Z/(p^(H-1)),     X_p = Z/B.

No high digits are discarded. A p-bearing original `d=p^e m`,
`p∤m`, `1<=e<=H`, has the
literal form

    A_d = {r_d} × J_d × C_d,                            (SM1)

where `J_d` is its tail prefix of depth `e-1`, of Haar mass
`p^(1-e)`, and `C_d` is its cofactor class modulo `m`. For `d!=p`,
`r_d!=a_p`. Define

    R_p = X_p minus the union of all p-free originals.   (SM2)

Then, exactly,

    Priv(A_p) = {a_p} × T_p × R_p.                      (SM3)

In particular `R_p` is nonempty. For every `x in R_p` and every
`r!=a_p`, the prefixes `J_d` of those original labels with
`r_d=r` and `x in C_d` cover **all** of `T_p`: no p-free original
can cover any of those points.

The argument below needs only this local full-tail coverage, distinct
p-bearing numerical moduli, and the absence of the pure label `p` on
these other roots. Thus it also applies to some covers whose p-free
moduli repeat. Divisor closure is used for the parent-provenance
conclusion in section 4; it is not an extra assumption in the prefix
lemma. The combinatorial lemma also holds for `p=2`. The odd-only
Simpson bound used later keeps its separate hypothesis.

## 2. Finite prefixes force a synchronized matching

Fix `x in R_p`. Regard a compatible original label `p^e m` as a
prefix label on the p-ary tail tree, attached to root `r_d`, with
color `m` and depth `e-1`. Numerical-modulus distinctness says:

    for every (color m, depth j), at most one label
    occurs anywhere among all roots and tree nodes.    (SM4)

Color `1` denotes a pure p-power and cannot be used in the matching.
It has no depth-zero label on the `p-1` roots under consideration.

We construct one descending tail path while retaining a matching of
some roots to distinct nonpure colors. Every retained label contains
the entire current tail prefix. After each level, every unmatched
root has no label on any node already visited by the path.

At depth zero, all labels have distinct colors by SM4 and none is
pure. For every root that has such a label, choose one. Their colors
are distinct, so this starts the matching and establishes the
invariant.

Suppose the current matching has `k<p-1` roots and the current depth
is less than `H-1`. At the next depth, each of the `k` used colors
and the one pure color can have at most one label. Among the `p`
children of the current node, at most

    k+1 <= p-1

therefore contain such a label. Choose a child with none of them.
All new labels on this child have unused nonpure colors, mutually
distinct by SM4. Choose one for every previously unmatched root
that now has a label, and add these pairs to the matching. Older
matched labels still contain this child. Unmatched roots still have
no label anywhere on the path.

At depth `H-1`, an unmatched root would have no label covering the
chosen leaf. This contradicts its full-tail coverage. Consequently
there is a tail `t` and a tuple of original labels

    tau=(d_r)_(r!=a_p),     d_r=p^(e_r) m_r,

such that

    r_(d_r)=r,     x in C_(d_r),     t in J_(d_r),
    m_r>1,        m_r!=m_s for r!=s.                   (SM5)

If the matching becomes complete earlier, every leaf below its
current prefix works. In all cases, the set of tails admitting such
a matching has Haar mass at least

    H_T(G_x) >= p^(1-H).                               (SM6)

This is a finite-tree proof at the full original height. It does not
replace the original labels by an infinite geometric tail.

## 3. A fixed tuple carries actual joint source mass

Let `nu` be a finite nonnegative measure supported on `R_p`, with
`nu(R_p)>0`, and use the explicit product law `nu × H_T` on cofactor
states and tails. An arbitrary correlated law need not assign positive
mass to the tails supplied by SM6; the product-law hypothesis matters.

Let `T` be the finite set of tuples whose component at each root
`r!=a_p` is a nonpure p-bearing original label in that root, with
distinct cofactors across components. The synchronized good set is

    G = union_(tau in T)
        [(R_p intersect intersection_r C_(d_r))
         × intersection_r J_(d_r)].                   (SM7)

Integrating SM6 on the same source gives

    (nu × H_T)(G) >= p^(1-H) nu(R_p).                  (SM8)

Hence one fixed tuple has

    (nu × H_T)((R_p intersect intersection_r C_(d_r))
               × intersection_r J_(d_r))
       >= p^(1-H) nu(R_p) / |T| > 0.                  (SM9)

If `n_r` is the number of nonpure p-bearing original labels in root
`r`, then `|T|<=product_r n_r`; that product can replace `|T|` in the
weaker lower bound. Labels and their residues remain the original
ones. In particular the cofactor congruences are jointly compatible.

The prefixes in a positive tuple are also compatible, so their
intersection is one prefix of depth `max_r(e_r-1)`. Its mass is
`p^(1-max_r e_r)`. The cofactor intersection is one AP of modulus
`lcm_r m_r`. Under unconditioned cofactor Haar its mass is the
reciprocal of that lcm; under the killed source the correct term is
`H_X(R_p intersect intersection_r C_(d_r))`. Dropping `R_p` would
change the measured event.

Because `R_p` is a nonempty subset of `Z/B`,

    H_X(R_p) >= 1/B = p^H/Q,
    H_Q(Priv(A_p)) >= 1/(pB) = p^(H-1)/Q.              (SM10)

For raw killed cofactor Haar `nu=1_(R_p) H_X`, SM9 therefore yields
one synchronized tuple of mass at least

    p/(Q |T|) >= p/(Q product_r n_r).                 (SM11)

This is mass on the cofactor--tail carrier. Lifting to any fixed
first-p-digit root in the full CRT carrier multiplies it by `1/p`.

The already retained Simpson bound for irredundant odd whole covers,
`Q<=3^floor((n-1)/2)`, supplies a further fixed-cardinality lower
bound by replacing `Q` with that upper bound. No uniform bound in
unrestricted `n` is claimed.

## 4. The chronological endpoint and original parents

At the largest support prime `P`, every P-free original ends before
`P`, while every original ending earlier is P-free. Thus

    R_P = complement of O_P

on the cofactor carrier. The cofactor--tail marginal of raw pre-P
killed Haar is exactly `1_(R_P) H_X × H_T`; the full original law
also has the independent uniform first-P-digit factor.
SM8--SM11 consequently concern the actual live endpoint source.
They place no positive killed mass on `Y_(P,r)`, which lies in the
already-covered region as established in 350.

For a smaller `p`, `R_p` also removes p-free originals containing
larger primes; it must not be identified with the chronological
pre-p survivor.

In the divisor-closed extremal system, every matched cofactor `m_r`
is an original modulus. Its original parent `A_(m_r)` is disjoint
from `C_(d_r)` on the cofactor carrier, since it divides `d_r` and
the original cover is irredundant. The same holds for every
nontrivial p-free divisor of `m_r`. The matched region lies in
alternate cofactor residues while avoiding these actual parents;
no independent parent law is introduced.

## 5. The height dependence is sharp for the local prefix conditions

Choose `p-2` distinct nonpure colors and give each of `p-2` roots one
depth-zero label with its own color. The remaining root must still
be covered. Starting at the tail-tree root, at each of the next
`H-1` levels put these `p-2` old colors and the pure color on `p-1`
different children of the one continuing path. Assign all those
labels to the remaining root. Continue down the last child. At the
final leaf put one new nonpure color on that remaining root.

There is at most one label for every color and depth, and each root
is covered on every leaf. Off the continuing final leaf, the last
root has only a pure label or a color already forced at another
root, so no full matching exists. The final leaf has the new color
and does have a full matching. Its mass is exactly `p^(1-H)`.

One may choose the nonpure colors as distinct primes other than `p`,
so the labels have genuine numerical forms `p^(j+1)m`; every such
numerical modulus is distinct. Same-root labels with comparable
numerical moduli in this construction are disjoint. This is still
a local prefix configuration, **not** an odd whole cover or a
lex-minimal covering counterexample. It proves sharpness under the
local hypotheses used in section 2. Additional global extremal
structure could impose a stronger bound; that question remains open.

## 6. Verification and remaining scope

The proof of SM5 is the finite prefix argument above. The retained
[exact checker](../frontier/hsw11_prime_private_matching.py) checks
literal prefix coverage, constructs the path and matching, and
independently verifies that the returned original labels all cover
the same tail with distinct nontrivial cofactors. Its HSW fixtures
retain every original 3-height from 1 through 22. They use the
complete published odd near-cover as a local example; the repeated
11 modulus is not represented as a distinct odd covering system.
Finite fixtures do not establish the general lemma by enumeration.

The HSW checks comprise 1,280 selected private cofactor configurations,
139,392 literal active 3-bearing labels, and 2,560 checks of the returned
original AP witnesses. Two independent prefix-union algorithms certify
the entire tail period `3^21=10,460,353,203` in each configuration;
7,680 small Hall-subset checks additionally verify the root graphs.
The checker rejects 12 invalid API inputs and examines all leaves of
16 sharp local configurations at `p=2,3,5,7`, `H=1,...,4`, totaling
611 leaf checks. Those finite local examples have the limited scope
stated in section 5.

The theorem resolves existence of a common tail, with the explicit
finite-height bound SM6. A legal transformation still has to preserve
coverage outside the matched region and the numerical uniqueness of
all output moduli. The existence of the common cylinder does not
remove an already occupied parent modulus or provide those global
conditions. No new Lean declaration, kernel verification, or solution
of unrestricted Erdős #7 is claimed.
