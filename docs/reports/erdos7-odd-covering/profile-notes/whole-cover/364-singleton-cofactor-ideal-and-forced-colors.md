[Index](../../marked_head_profile.md) · [Private reset](357-original-private-swaps-and-prime-reset-transport.md) · [Used-height capacity](359-synchronized-parent-capacity-allocation.md) · [Prime-parent transport](362-whole-prime-private-vector-under-residue-swaps.md) · [Common source](363-common-source-antichain-capacity.md)

# Singleton cofactor ideals force height-one matching columns

A singleton first-prime root imposes a universal restriction on the
**same** prime-private cofactor region. Its actual numerical cofactors
form a relative divisor ideal. With divisor closure, a legal
prime-parent exchange forces all prime-power descendants, bounds their
height, and provides simultaneous height-one columns in every maximum
matching. These columns sharpen 363's composite-source lower bound by
using 359's actual selected heights.

These are ordinary finite proofs, with exact checks on whole even
covers. The degree-one matching argument and used-height capacity
algebra are standard or reused; no literature novelty, Lean
verification, or contradiction for unrestricted odd covers is claimed.

## 1. Actual singleton roots and a common cofactor ideal

Let D be the distinct original numerical moduli of a whole irredundant
cover, Q its complete period, and H uniform on `Z/QZ`. Every support
prime is an original label, and comparable original classes are
disjoint. Keep every prime-power height. Write `A_d=a_d mod d` and
`pi_d=H(Priv_d)`. Divisor closure is an additional hypothesis only where
stated.

Fix q and write `R_q` for the cofactor region avoiding **all** q-free
original classes. It is not a chronological survivor unless q is the
largest prime. With `T_q` the complete higher-q-digit space,

    Priv_q = {a_q mod q} x T_q x R_q,
    H_X(R_q) = q pi_q > 0.

By 357, resetting only the first q digit of any point of `Priv_d`,
`q|d`, `d!=q`, puts it in `Priv_q`, without changing its q-tail or
cofactor. In particular, every q-bearing original has an actual private
witness whose cofactor lies in this same `R_q`.

A nonprime first-q root is **singleton** when exactly one q-bearing
original class has that root; q-free originals are not counted. Define

    F_q = {m>1 : qm is the unique q-bearing original at its q-root}.

Over any cofactor in `R_q`, a singleton must cover every q-tail. Thus
its q exponent is exactly one, and `q` does not divide m. Let `C_m` be
the cofactor class `a_(qm) mod m` of the **child**, which need not be
the original parent class `A_m`. Then

    m in F_q  <=>  qm in D, q does not divide m, R_q subset C_m.
                                                               (SI1)

For the converse, another q-bearing original at that root would have
a private witness. Resetting it puts its cofactor in `R_q`; back at
the old root, the class qm already covers it, a contradiction. This
also proves the exact equality

    Priv_(qm) = {a_(qm) mod q} x T_q x R_q,
    pi_(qm) = pi_q                         for m in F_q.       (SI2)

Set `L_q=lcm(F_q)`, with empty lcm 1. Nonempty `R_q` lies in every
`C_m`, so these residues are jointly CRT-compatible. Their intersection
is one cofactor class `c_q mod L_q`. For an **actual** label qn with
`n|L_q`, its private witness forces `a_(qn)=c_q mod n`. Hence

    F_q = {n>1 : qn in D and n divides L_q}.                    (SI3)

This relative identity does not need divisor closure. It does not
assert `qL_q in D` or create missing numerical labels. With divisor
closure, every nonunit divisor of a member of `F_q` belongs to `F_q`.
Different members occupy different nonprime roots, so

    |F_q| <= q-1;
    H_q>=2  ==>  |F_q| <= q-2.                                 (SI4)

Indeed an actual label of q-height at least two needs a root which
is neither the prime root nor a singleton root. Its existence follows
from `H_q>=2`, even when the numerical q-square is absent.
Also **under divisor closure**,

    F_q intersect Lambda = supp(L_q),
    f_q := #{m in F_q : m composite} = |F_q|-omega(L_q).        (SI5)

For a nonclosed palette, f_q always means the actual composite count.
The common cylinder gives the coherent source cap

    pi_q <= 1/(q L_q) product_(p in Lambda, p not dividing q L_q)(1-1/p)
         = P0 / [(q-1) phi(L_q)].                              (SI6)

Its prescribed residues at primes dividing `L_q` avoid the original
prime classes, since the relevant original children are comparable
with and disjoint from those classes. No independence between the
different singleton constraints is assumed.

## 2. Legal prime-parent exchanges force descendants

Consider 362's no-escape swap with prime parent q and child `qP^e`,
`P!=q`. If the resulting whole cover is irredundant, legality forces
the child's first-q root to be singleton: otherwise the new prime
class contains another unchanged q-bearing original. Conversely a
singleton gives `R_q` inside the child's P-prefix, exactly the
no-escape condition, and the exchange is a whole-family root
permutation. Thus in a minimum-cardinality cover,

    legal swap with parent q and child qP^e  <=>  P^e in F_q.  (SI7)

Minimum cardinality supplies the resulting irredundancy. It cannot be
omitted when applying the forward implication to an arbitrary cover.
With divisor closure all `P,P^2,...,P^e` belong to `F_q`, at distinct
roots, and all the associated exchanges are legal. Therefore

    e <= q-1,                   f_q >= e-1;
    H_q>=2 ==> e <= q-2.                                      (SI8)

More generally a singleton qm then gives `tau(m)<=q`, or `tau(m)<=q-1`
when `H_q>=2`. Multiple prime-power branches
count their distinct cofactors in the same root budget. These are
conditional restrictions, not an existence assertion for legal moves.

## 3. Forced colors refine the same composite-target allocation

For every source `z in Priv_q`, each `m in F_q` gives a degree-one
root in the actual 354 matching graph, colored by the numerical
cofactor m, using the original height-one child qm. These roots and
colors are distinct. Every maximum matching contains all forced
colors: if a color were unused, its degree-one root would be unmatched
and its edge could be added. If its color is used elsewhere, move that
edge to the forced root. All such moves can be made simultaneously,
preserving rank and the exact selected color set. Consequently one
may choose maximum matchings satisfying

    S_(q,1,m)=Priv_q,   S_(q,e,m)=empty (e>1),   m in F_q.      (SI9)

359's containing-cylinder proof applies to the used-height set E,
giving source coefficient
`alpha_used=q sum_(e in E) q^(-e)`. For a forced column this is exactly
one, even if other original labels with larger q-height exist. Its
source lies in the cylinder of mass `rho_(q,m)/(qm)`, so

    [beta_(q,m)/rho_(q,m)] pi_q <= beta_(q,m)/(qm).

The right side is the same actual target `A_q intersect A_m` with
359's `1/k` allocation. With divisor closure, every selected parent
exists. Each ordered pair is charged once; other columns can still
use `alpha_q=q/(q-1)(1-q^(-H_q))`. For composite parents
`beta/rho>=1`. Writing C_q for the **unnormalized H-integral** of the
selected composite count, the refined composite source charge is at
least

    C_q/alpha_q + (1-1/alpha_q) f_q pi_q.                      (SI10)

This is a used-height refinement of the MP5 capacity argument. It
does **not** redefine 361's `X_comp`, whose terms all used `1/alpha_q`.

Retain 363's prime-parent bound, on that same original source:

    Fprime_q = {q^e p in D : e>=1, p!=q prime},
    u_q = sum_(d in Fprime_q) pi_d,
    epsilon_q = (q-1)pi_q-sum_(d composite:q|d) pi_d,
    Delta_F = sum_(d in Fprime_q)(cap_d-pi_d),
    U_q = min((s-1)pi_q, u_q+min(epsilon_q,Delta_F)).

Here `cap_d=P0/phi(d)`, `s=|Lambda|`. Forced relocation preserves
the color set, hence the actual prime and composite counts, so U_q
continues to apply. With `r_q=q-2+q^(1-H_q)`, the full-tail mean rank
and forced colors give both `C_q>=r_q pi_q-U_q` and `C_q>=f_q pi_q`.
Combining SI10 with 361's unchanged composite-target capacity yields

    sum_q [ f_q pi_q
          + ((r_q-f_q)pi_q-U_q)_+/alpha_q ] <= M_comp,        (SI11)

    M_comp = sum_(m composite in D) (1/m)
             [1-product_(p in Lambda:p not dividing m)(1-1/p)].

For `f_q=0`, SI11 is 363's bound. For `alpha_q>=1`, each new summand
is at least `(r_q pi_q-U_q)_+/alpha_q`. This refinement uses the full
matching structure and is not claimed independent of MP5 with that
additional information.

Forced composite edges use nonprime roots, giving
`P_q<=(q-1-f_q)pi_q`. Cutting U_q by this bound leaves SI11 unchanged,
since `r_q<=q-1`. Under divisor closure the forced prime colors also
give `P_q>=omega(L_q)pi_q`, hence `U_q>=omega(L_q)pi_q`.

## 4. What the root permutation cannot improve

A legal irredundant prime-parent exchange is a Haar-preserving
first-root permutation of the **entire labelled family**. For every
observing prime it induces a color-preserving isomorphism of the
matching graphs after transporting sources and the current prime
root. It preserves maximum rank, attainable color sets, and extrema
of prime/composite counts among maximum matchings. A transported
selection rule preserves its distribution. An arbitrary untransported
tie rule can choose a different color set, but that set was already
attainable before the exchange. This gauge alone gives no intrinsic
descent or deletion of prime colors.

Nor can a forced cofactor be used to exclude a prime-color column by
an arbitrary residue mismatch. For `p|L_q`, the private reset forces
every actual `q^e p` to have p-residue `c_q mod p`. Under divisor
closure its height-one label qp is present. A local inventory that
violates this requirement is not an irredundant whole-cover example.

## 5. Exact fixtures and scope controls

The standalone [checker](../../frontier/whole-cover/singleton_cofactor_ideal.py) uses
five whole irredundant, comparable-disjoint **even** covers from 362:
53 original APs on periods 12, 144, 960, 120 and 180, totalling 1416
base carrier points. Only the period-12 palette is divisor-closed.
It checks actual private resets, SI1--SI6, every maximum matching of
each encountered graph, simultaneous forced relocation, actual used
heights, and 29 prime-parent swap candidates. Eleven are legal;
all eleven here are whole-family transports, including matching-graph
transport for every observing prime. Period 12 verifies the complete
SI11 target chain, with every displayed budget equal to `1/12`.

Two essential negative controls use actual original APs. In period
12, points 1 and 7 share the first 2-digit and complete 3-coordinate
over `R_2`, but only 1 lies in `1 mod 4`: a first-digit shadow loses
necessary tail information. At q=3 the exact ideal modulus is 4,
not its radical 2. In period 960, `F_3={160,320}`, `L_3=320`, but
the missing original label 6 prevents insertion of cofactor 2.
Here the actual f_3 is 2, whereas `|F_3|-omega(L_3)=0`; using SI5
without divisor closure fails.

A further whole even fixture demonstrates a **strict** source gain.
In the period-960 cover, `629 mod 960` is entirely private. Replace
that AP by an affine copy of the same cover:

    (a mod d) maps to (629+960a mod 960d).

Keep the other 12 APs. The resulting 25-label cover has period 921600.
Coverage, private masses and irredundancy follow from the exact
interior/exterior membership factorization; the checker verifies all
960 interior rows and every one of the 7680 original q=5 source
points, without discarding its new second 5-digit. The relevant data
are

    F_5={2,4,8}, f_5=2, pi_5=1/120, H_5=2,
    alpha_5=6/5, r_5=16/5,
    epsilon_5=31/19200, U_5=191/19200,
    actual P_5=1/120, actual C_5=1/40.

The old 363 summand is `107/7680`; the SI11 source summand is
`77/4608`, a strict gain of `1/360`. The forced composite columns 4
and 8 have actual parents and coefficient one. This improves the
coarse alpha_5 summand by reusing the exact column-height method;
it is not new relative to 359 with these selected columns already
known. The fixture lacks other original parents, so **no full
M_comp chain is asserted for it**.

The checker completes 8345 exact checks using explicit exceptions,
including under `python3 -O`; normal and optimized relocated runs
have identical output and empty stderr. No Lean build was run.

The remaining whole-cover gaps are unchanged: no result here forces
`f_q>0` in every extremal cover, evaluates SI11 contradictorily for
all such covers, or supplies the missing general composite-parent
derivative sign. The result is the conditional cofactor/descendant
restriction and shared-source refinement, with those boundaries.
