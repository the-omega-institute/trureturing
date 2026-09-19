[Index](../../marked_head_profile.md) · [Actual source](../354-synchronized-prime-private-cofactor-matching.md) · [Shallow bound](../366-shallow-tail-truncation-on-the-actual-source.md)

# Private top fans and original ancestor cuts at every height

An actual private point of the highest pure prime power forces a fan of
highest-level mixed originals. At least one of their first ancestors has
a nonempty proper cofactor trace. Consequently, either a lower cutoff
improves the original integrated source bound, or at least q distinct
nonpure top colors are required.

A further arithmetic restriction applies when q-2 original mixed classes
of exponent one are cofactor-universal. They leave just one available
first root. An original first ancestor then excludes the entire upper
cone of its top color under divisibility. A chain of top colors forces
a lower cutoff at every height H>=2. The proof uses actual comparable
APs and their common CRT points, rather than a bound on the number of
tail leaves.

These are ordinary finite proofs, not new Lean declarations or a solution
of unrestricted Erdős #7. The highest-digit mechanism is already present
in reports 336, 340 and 343. No literature-priority claim is made.

## 1. One original covering family and one probability law

Let D be a finite set of distinct integers greater than one, with one
original AP `A_d=a_d mod d` for each d. Assume that these APs cover every
integer, every AP has a private point, and D is divisor-closed above one.
Different comparable original APs are then disjoint: if they intersect,
the smaller class contains the larger, which cannot have a private point.

Put `Q=lcm(D)`. Fix a prime q, write `H=v_q(Q)>=2`, `B=Q/q^H`, and
`r_0=a_q mod q`. The carrier is the complete product
`(Z/q^H Z) x (Z/B Z)`. Let

    R_q = {x mod B : x avoids every original q-free AP}.

Every private point of a q-bearing original has cofactor in R_q. The
prime-private set consists of root r_0, all q^(H-1) tails and all of R_q.
Thus R_q is nonempty and the original uniform Haar law gives

    pi_q = q^(H-1)|R_q|/Q = |R_q|/(qB).

For each original `q^e m`, with `m>1` and q not dividing m, define

    C_e(m) = {x mod B : x = a_(q^e m) mod m},
    h_m(x) = max {e : q^e m is original and x in C_e(m)}.

Omit empty columns. Report 366 proves that the (q-1)-st largest column
height `ell_q(x)` exists, lies in [1,H], and preserves complete shallow
coverage. Define

    M_H = {m>1 : q does not divide m, q^H m in D},
    E_m = R_q intersect C_1(m),
    F_m = R_q intersect C_H(m)         (m in M_H).

Every E_m is nonempty by the actual first ancestor's private point. The
condition `ell_q(x)=H` means that at least q-1 different top traces F_m
contain x. We call its validity at every x in R_q the all-high case.
The notation never substitutes a newly chosen residue for an original
parent or truncates the original carrier.

## 2. The private top fan has an escaping first ancestor

Choose a private point z of the original pure `A_(q^H)`. Its first root
r_* differs from r_0 because H>=2. Keep its cofactor and its residue
modulo q^(H-1), and vary only the highest q-digit. No q-free or lower
q-height original can cover any of these siblings: membership in such
an AP is the same as at the private point z.

The other q-1 siblings therefore require distinct original top classes
`A_(q^H m_i)`. The colors m_i are distinct and nonpure. Their top traces
all contain the same cofactor x_0 of z.

A first-ancestor trace E_(m_i) equal to R_q cannot have root r_*: it would
cover z at x_0. Nor can it have root r_0. Two such universal first
ancestors cannot share a root, since each would cover all candidate
private points of the other. Only q-2 roots remain, so one of the q-1
fan colors satisfies

    empty != E_m != R_q.                              (PF1)

The set R_q therefore uses at least two different residues modulo m.
Both avoid the original q-free parent residue a_m. In particular,

    |R_q|>=2,             pi_q>=2q^(H-1)/Q.            (PF2)

This does not say that absence from E_m is absence from F_m: they use
different original residues. Instead, because R_q has two residues
modulo m, the single-residue top trace F_m cannot equal R_q either.
At a point outside this F_m, at most q-2 colors of the fixed fan are
active. If all-high holds, another top color outside that fan is needed.
Hence

    all-high ==> |M_H|>=q ==> |D|>=(q+1)H+q.           (PF3)

For the last count choose q distinct top colors. Divisor closure supplies
qH different mixed labels q^e m, H pure labels q^e and q distinct q-free
parents m. Their q-adic factorizations show that these three lists are
disjoint. The count is conditional on all-high; the earlier unconditional
count in 366 remains `|D|>=qH+q-1`.

## 3. An exact gain on the complete source

For the integrated bound b_q of 366 and `r_q=q-2+q^(1-H)`, subtraction
on the original Haar law gives

    b_q-r_q pi_q
       = (1/Q) sum_(x in R_q) [q^(H-ell_q(x))-1].      (PF4)

The difference vanishes exactly in the all-high case. If a nonempty
set J of actual cofactors has ell_q(x)<H, then

    b_q-r_q pi_q >= (q-1)|J|/Q >= (q-1)/Q.            (PF5)

Thus either the gain is at least (q-1)/Q, or the larger top palette and
class count in PF3 are necessary. This is a period-dependent finite
gain; it can tend to zero with growing Q. It is not a cross-prime slot
allocation or a strict gain in every later target inequality.

## 4. Saturated first roots exclude a whole divisibility upper cone

Assume that q-2 distinct original mixed classes `A_(q u_i)` have
exponent one and cofactor traces containing all of R_q. Put `U={u_i}`.
For q=2 this is the empty family. These classes occupy distinct nonprime
roots, so together with A_q they leave one root r.

Every other q-bearing original must have first root r. Otherwise a
specified universal class or A_q would cover all its possible private
points over R_q. In particular every top original has root r, because
H>=2. For m outside U the first ancestor A_(qm) has root r as well.

For m in M_H, let `Up(m)={n in M_H:m divides n}`. Then

    m in M_H minus U, n in Up(m)
        ==> E_m intersect F_n = empty.               (AC1)

Indeed, a common cofactor x and the full q-adic residue of the top
original A_(q^H n) give an actual CRT point in that AP and in A_(qm).
The first roots agree and x has the ancestor's original residue modulo
m. But qm divides q^H n, and they are different moduli since H>=2.
This contradicts disjointness of comparable originals.

No tail leaf count is used, so AC1 holds at every H>=2. The exclusion of
m in U is essential: its first ancestor has a different root.

It follows that at each x in E_m only colors in `M_H minus Up(m)` can
be active. All-high would therefore require, for every m outside U,

    sum_(n in M_H minus Up(m)) 1_(F_n)(x) >= q-1
        for every x in E_m;                          (AC2)
    |M_H minus Up(m)| >= q-1.                        (AC3)

Integrating AC2 using the original cofactor Haar law nu gives the
stronger actual-trace cut

    (q-1) nu(E_m)
       <= sum_(n in M_H minus Up(m)) nu(E_m intersect F_n).
                                                     (AC4)

The intersections in this formula are from the same original family.
Separate extremal trace sizes cannot be combined to assert AC4.

If instead `|M_H minus Up(m)|<=q-2`, all of the nonempty E_m is low.
PF5 then gives gain at least `(q-1)|E_m|/Q`. The union of several such
E_m can be used, counting every cofactor once.

If M_H is a divisibility chain, choose its least member outside U.
Such a member exists because the private fan has q-1 colors while U
has only q-2. Every top color not above m lies below m and hence in U.
AC3 fails. Therefore

    saturated first roots + chain top palette
        ==> some ell_q(x)<H, for every H>=2.         (AC5)

There is also a narrower height-two conclusion. Under all-high choose
an active top color outside U and a private point of its first ancestor.
At that cofactor, q-1 active top classes must avoid both the pure q^2
leaf and the private point's leaf. Only q-2 leaves remain, so two top
colors share a leaf. Their original APs intersect, so their colors are
incomparable. This proves a coactive antichain when H=2; AC5 alone does
not claim such a coactive pair at larger height.

## 5. What the prime 2 adds in an even cover

This section assumes q odd and 2 dividing Q. The pairwise disjoint pure
binary originals A_2,...,A_(2^k) leave one nested residue b_k modulo
2^k. Because they are q-free, every x in R_q has that residue.

If any original q^e m has v_2(m)=k, divisor closure supplies the k
first ancestors A_(q 2^j), 1<=j<=k. Disjointness from the pure binary
classes forces their binary residues to be b_j, making all k classes
cofactor-universal. They use distinct roots, excluding r_0 and the
private pure-top root r_*. Consequently

    v_2(m)<=q-2 for every original q^e m.             (BL1)

A saturated binary top ladder gives more. Suppose `q^H 2^(q-2)` is
original. For every depth e=1,...,H, its q-1 original divisors
`q^e 2^j`, j=0,...,q-2, are cofactor-universal. At depth one they occupy
q-1 different roots. Inductively every next-depth original must occupy
a child of the one uncovered prefix or it has no private point. These
q-1 children are distinct for the same reason. The whole skeleton
therefore leaves precisely one depth-H leaf P_H over every x in R_q.

Every non-skeleton q-bearing original must have a prefix containing
P_H to possess a private point. The skeleton has q-2 nonpure top
colors. All-high would supply an additional top class, at leaf P_H,
at every cofactor. Choose any such color m; it is not a binary skeleton
color. Its original first ancestor A_(qm) has no private point: the
skeleton covers all other leaves and additional top originals cover
P_H everywhere on R_q. They differ from A_(qm) because H>=2.
This contradiction proves that the saturated ladder forces a low cutoff.
Together with BL1 and divisor closure,

    all-high ==> v_2(m)<=q-3 for every m in M_H.       (BL2)

For q=3, BL1 excludes every 3-bearing original divisible by 12 when
H_3>=2, and BL2 makes all top colors odd in the all-high case. Neither
statement applies to H_3=1.

## 6. Consequences for the 3, 5, 7 part and arbitrary heights

Take q=3 and H>=2 in the same even whole-cover model.

* If the odd part of B is p^a with a<=2, all-high is impossible even
  without assuming that A_6 is original: BL2 permits only the a odd
  nonpure top colors p,...,p^a, while PF3 requires at least three.
* If A_6 is original and the odd part of B is p^a for arbitrary finite
  a, all-high is again impossible. A_6 supplies the one universal mixed
  first class; BL2 makes the top palette a chain of powers of p, and
  AC5 applies for every H>=2.
* If A_6 is original and the odd part of B is `p^a s^c` for two
  different odd primes with `min(a,c)<=1`, all-high is impossible,
  even when the other exponent is arbitrarily large.

For the last item, BL2 makes M_H odd, and divisor closure makes it a
nonunit divisor ideal. Every prime p occurring in a top color belongs
to M_H itself and is outside U={2}. AC3 requires at least two top
colors avoiding p. Writing `h_s=max_(m in M_H)v_s(m)`, their number
is at most `product_(s!=p)(h_s+1)-1`, with the product over active top
primes. Hence all-high requires

    product_(s!=p)(h_s+1)>=3 for every active top prime p.
                                                     (BL3)

One active top prime is impossible. If exactly two occur, both of
their top heights must be at least two. If only one of the two primes
in B occurs in M_H, the one-prime contradiction applies instead.

Here p,s are different from 3. Each exclusion of all-high gives at
least 2/Q gain in PF4. These statements do not exclude the whole cover.

The third item applies, with its explicit A_6 assumption, to periods
`Q=2^b 3^H 5*7`, including `5040=2^4*3^2*5*7`. It uses a structural
condition on the original class 6, not merely the numerical fact that
6 divides Q. The second item has no bound on the height of the other
odd prime. No even-cover implication is asserted for a purely odd family.

## 7. The height-one boundary and verification scope

The actual classes

    0 mod 2, 0 mod 3, 1 mod 4, 5 mod 6, 7 mod 12

form a whole irredundant, divisor-closed, comparable-disjoint cover.
Private witnesses for labels 2,3,4,6,12 are 2,3,1,11,7 respectively.
At q=3, H=1 and R_q={3 mod 4}; top colors 2 and 4 give ell_q=H.
There are only q-1 top colors, and v_2(4)=2>q-2. This refutes removing
H>=2 from PF1, PF3, BL1 or BL2.

At height one the private pure-top root is the prime root, so the fan
proof no longer excludes two different roots. In AC1 a first ancestor
can also equal the top original itself. The same-class case cannot be
used in a comparable-class disjointness contradiction.

The [exact analyzer](../../frontier/arithmetic/top_fan_ancestor_cuts.py)
accepts a JSON object with `aps` in `[residue,modulus]` order. It checks
the complete original period, all private witnesses, divisor closure,
comparable disjointness, the full cofactor/tail products, and the stated
applicable fan and ancestor restrictions. Its height-one control retains
the original period-12 cover. These finite checks verify supplied inputs;
the arbitrary-height conclusions rest on the proofs above.

The analyzer passes on 369's period-3150 cover, on the height-one
boundary above, and on the following whole period-80 cover:

    (0 mod 2), (1 mod 4), (3 mod 8), (7 mod 16), (0 mod 5),
    (1 mod 10), (7 mod 20), (23 mod 40), (79 mod 80).

The last input exercises the chain conclusion at q=2 and H=4. The
three runs check respectively 875, 6 and 36 full-tail root lifts.
Ordinary execution and detached execution from an unrelated directory
with `python3 -I -S -O -B` produce identical output for each input.
Translated copies of the period-3150 input preserve private counts,
cutoff distributions and gain. Missing divisors, noncoverage, repeated
moduli and intersecting comparable APs are rejected at their stated
input or hypothesis checks.

The remaining odd-cover obligation includes cases without saturated
first roots and top palettes satisfying the ancestor cuts. Even where
PF4 is strictly positive, the cross-prime allocation and original target
budgets of reports 363--370 remain separate obligations. All results
here retain the original residues, complete tails and single Haar law.
