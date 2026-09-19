[Index](../marked_head_profile.md) · [Extremal source](350-extremal-paired-branch-and-source-support.md) · [Synchronized matching](354-synchronized-prime-private-cofactor-matching.md) · [Column heights](355-column-height-matching-bound.md) · [Immediate-parent rescue](356-active-parent-private-rescue.md)

# Original private sets, legal swaps, and prime-reset transport

A hypothetical extremal distinct odd cover admits two useful operations:
a conditional swap of a child with its original prime-free parent, and
a coordinate reset taking actual private points to a prime-private set.
The first couples the actual live source to disjoint overlap regions;
the second has an explicit Haar congestion bound. Simultaneously resetting
several primes gives a direct charge to original prime-class overlaps.
These are ordinary finite deductions, not a resolution of Erdős #7 or
new Lean verification.

## 1. One original cover and its measures

Use 350's cover minimizing `(n, sum of original moduli)`. Write its
distinct original classes as `A_d`, its full period as `Q`, and uniform
probability on that period as `H`. The modulus set D is divisor-closed
above one, every support prime q occurs, and comparable original classes
are disjoint. Normalize the prime classes to `A_q=0 mod q` by one CRT
translation. All heights remain their full original heights.

Write `Priv_d` for the private set of `A_d` relative to this complete
original family, `pi_d=H(Priv_d)`, and `N(z)` for covering multiplicity.
Thus the private sets are disjoint and

    H_cov = integral (N-1) dH = sum_(d in D) 1/d - 1.

For a prime P let O_P be the union of originals ending before P, and
let B_P be the union of originals with largest prime factor P. The
original-Haar quantities from 347 are

    v_P = H(O_P intersect B_P),
    u_P = H(O_P intersect A_P) <= v_P.

Here A_P is the unique division-minimal original in its bucket. The
smaller u_P is not interchangeable with v_P in the swap argument below.

For the swap argument only, take P to be the largest support prime and
write the carrier as `(Z/P^H_P) x X_P`. Its cofactor survivor R_P avoids
every P-free original, so it equals the actual chronological pre-P
survivor on X_P. Among covers with this same fixed D choose one further
minimizing `H_X(R_P)`. There are only finitely many residue assignments;
this choice preserves the preceding minimality and all its consequences.
It is this selected cover to which 354's matching is applied.

## 2. A genuine two-label swap or an actual private escape

Fix one synchronized tuple of original children

    d_r=P^(e_r)m_r,  m_r>1,  P not dividing m_r,

one in each nonzero first-P root, with distinct m_r. Let K_r be its full
P-prefix, including the first root, and C_r its cofactor class. Then
`A_(d_r)=K_r x C_r` and `H_P(K_r)=P^(-e_r)`. Define

    B_r=A_(m_r) on X_P,
    E_r=B_r minus the union of all other P-free originals,
    Z_r=Priv_(m_r) intersect (K_r^c x X_P),
    a_r=H_X(E_r)(1-P^(-e_r)),  z_r=H(Z_r).             (PT1)

These parents are the P-free originals A_(m_r), not the immediate
parents A_(d_r/P) studied in 356. In particular m_r itself may be prime.
Comparable-class disjointness gives `B_r intersect C_r=empty`. Each
Z_r lies over E_r. The E_r are disjoint because the m_r are distinct.

The region `(K_r^c x E_r) minus Z_r` has mass exactly `a_r-z_r`.
Its sole P-free original is the parent. Since the point is not private,
it is also covered by a P-bearing original. Consequently these regions
are disjoint subsets of `O_P intersect B_P`, and

    sum_r (a_r-z_r) <= v_P <= H_cov.                  (PT2)

If Z_r is empty, replace just the following two APs:

    B_r on X_P       -> C_r on X_P,
    K_r x C_r        -> K_r x B_r.                    (PT3)

Both replacements are whole APs with the same respective moduli m_r
and P^(e_r)m_r. Old child points are covered by the new parent. Every
old private parent point lies in the new child. An old nonprivate parent
point has another *unchanged* covering class: the old child was disjoint
from the parent. Thus PT3 preserves whole coverage and modulus uniqueness.

Its new survivor is exactly

    R'_P = (R_P minus C_r) disjoint-union E_r.

The additional minimum from section 1 therefore gives

    Z_r=empty  ==>  H_X(E_r) >= H_X(C_r intersect R_P). (PT4)

These are separate comparisons of the original cover with individual
swaps. They do not establish that several swaps can be made together,
or successively after the original private sets have changed.

Let `U_tau=R_P intersect intersection_r C_r` and let J_tau be the
intersection of the selected tail prefixes. Put

    M_tau=max_r e_r,
    theta_tau=H_T(J_tau)=P^(1-M_tau),
    lambda_tau=H_X(U_tau) theta_tau.

For the exact original cofactor--tail product event, PT2--PT4 imply

    v_P >= (lambda_tau/theta_tau)
             sum_(r:Z_r=empty) (1-P^(-e_r)).          (PT5)

The same inequality holds when lambda_tau is the mass of a subevent of
`U_tau x J_tau`. This sharpens the weaker use of lambda_tau alone.
A specified first-P-root lift has mass lambda_tau/P. A transported or
normalized mass cannot replace this raw product-Haar mass. Reports 354
and 355 provide positive fixed-tuple events on precisely this source.

## 3. Resetting an actual private point has bounded congestion

For any support prime q, reset only the first q-digit to zero, keeping
the whole q-tail and every non-q coordinate. Call this map T_q. If
`q divides d` and `d!=q`, a point of Priv_d has nonzero first q-digit.
At its image every q-free original is still absent. Every q-bearing
original other than A_q is disjoint from A_q, so

    T_q(Priv_d) subset Priv_q.

T_q is injective on each fixed first-q-root slice. Different original
private sets are disjoint. Counting at most q-1 source roots gives

    sum_(d:q divides d, d!=q) pi_d <= (q-1) pi_q.      (PT6)

If d=q the map is the identity. That source occupies the additional
zero root; it must not be included for free in the q-1 bound.

In PT1 choose one prime divisor q_r of each parent m_r. Let c_q be the
number of distinct first-q roots of those actual parents assigned to q.
If `b_q=1` when one assigned parent is q itself, and zero otherwise, then

    sum_(r:q_r=q) z_r <= c_q pi_q,
    1<=c_q<=q-1+b_q                                (PT7)

for each used q. This is true even when several parents have the same
first-q root: reset is injective on that whole root slice, not merely
on each parent separately.

Set `d_q=q-1+b_q`. Weight the disjoint regions in PT2 by 1/d_(q_r), and
use PT7 for the escapes. Oddness gives d_q>=2, hence the corrected budget

    sum_r a_r/d_(q_r) <= v_P/2 + sum_(used q) pi_q.    (PT8)

One can instead use actual c_q throughout; the coefficient of v_P then
becomes `max_(used q) 1/c_q`, which can equal one. The omission of the
prime-parent root would leave PT8 without a valid proof.

## 4. Uniform tails give an explicit single-step source bridge

Write the full carrier as `F_q x T_q x X_q`. Let a finite measure lambda
be supported on disjoint subsets of actual private sets assigned to q,
using c_q first roots, and explicitly assume `lambda <= M_0 H`.
Reset the first q-digit and then sample its entire tail uniformly,
preserving every other coordinate. If mu is the X_q marginal, the output
is exactly

    lambda_bar = delta_0 x H_T x mu.

The identity from 354 is `Priv_q={0} x T_q x R_q`, with R_q avoiding
all q-free originals. The reset proof puts mu on R_q, so this output
remains private. For input density f its output density is

    f_bar(0,t,x)=sum_(r in F_q) integral f(r,s,x) dH_T(s).

Only c_q summands can be nonzero. Thus, with no height factor,

    lambda_bar <= c_q M_0 1_(Priv_q) H
               <= c_q M_0 1_(O_q^c) H.               (PT9)

The last measure is the actual raw pre-q killed Haar law: every earlier
original is q-free. For a nonlargest q this does not identify R_q with
the entire chronological survivor. Raw source restrictions have M_0=1;
normalizing a small source incurs its corresponding density cost.

All non-q coordinates, including any earlier full P-prefix exclusion,
are preserved. To use matching, let G_x be the synchronized-good q-tail
set and `g(x)=H_T(G_x)`. Report 355 gives `g(x)>=q^(1-L_q(x))`.
Simply restricting lambda_bar to these tails retains

    integral g(x) dmu(x) >= integral q^(1-L_q(x)) dmu(x) (PT10)

mass and leaves the density bound c_q M_0 unchanged. Keeping all mass
by conditioning separately on G_x instead gives density at most
`c_q M_0 q^(L_q^*-1)`. Lost mass and increased density are different
operations and have different costs.

## 5. Several resets charge disjoint prime-only overlap regions

Let Lambda be the full original prime support. For `S subset Lambda`,
`|S|>=2`, define

    U_S = union_(d composite: supp(d) intersects S) Priv_d,
    V_S = {z: the original labels covering z are exactly A_q, q in S},
    C_S = product_(q in S) (q-1).

Reset all first digits in S to zero and preserve all other digits.
Every S-free original was absent at a source point and remains absent.
Every nonprime original meeting S is absent at the image, because it is
disjoint from one of the prime classes now present. The original source
label also meets S, so it too disappears. Each A_q for q in S is present;
the other prime classes remain absent. Thus the image lies in V_S.

A private point of a composite original belongs to none of the prime
classes. Its source root at every q in S is therefore nonzero, even
when q does not divide that original modulus. At most C_S source root
vectors can map to any target. Consequently

    sum_(d composite: supp(d) intersects S) pi_d
       <= C_S H(V_S).                               (PT11)

Requiring every q in S to divide d would give a weaker statement.
The V_S for different S are disjoint and have exact multiplicity |S|.
They therefore yield the nonrepeated excess charge

    sum_(S:|S|>=2) (|S|-1)/C_S
       * sum_(d composite: supp(d) intersects S) pi_d
       <= H_cov.                                    (PT12)

Equivalently the coefficient of each composite pi_d is
`kappa(Lambda)-kappa(Lambda minus supp(d))`, where

    kappa(F)=sum_(S subset F, |S|>=2) (|S|-1)/C_S
            =1+product_(q in F) q/(q-1)
                 * (sum_(q in F) 1/q - 1).

For a particular support prime P, keep only S with largest member P.
Each corresponding V_S lies in `A_P intersect O_P`. Thus the stronger
stage account, using u_P rather than v_P, is

    sum_(S:max S=P, |S|>=2) 1/C_S
       * sum_(d composite: supp(d) intersects S) pi_d
       <= u_P <= v_P.                               (PT13)

Source moduli d may contain primes larger than P. Their private sets
are always those of the complete original family. These are lower
bounds on original overlap in terms of private mass; they are not
lower bounds on survivor mass in terms of that overlap.

## 6. A depth restriction on the swappable branch

For a parent m=m_r let kappa_m be the number of other originals whose
APs intersect A_m. All such moduli are incomparable with m. Parameterize
this parent by `z=a_m+m y`. Each nonempty intersection restricts to
one AP in y; there are at most kappa_m of them. They do not cover all y,
because A_m has a private point.

The existing Simpson bound gives the no-escape restriction. If Z_r is
empty, these restricted APs together with the one class K_r modulo
P^(e_r) cover every y. K_r is essential: the original parent has a
private point, and all such points lie in K_r. Take a minimal covering
subfamily. It retains K_r, has at most kappa_m+1 members, and its own
recomputed lcm M is divisible by P^(e_r).
[Simpson's Corollary 2](https://doi.org/10.4064/aa-45-2-145-152),
already retained in [343](343-original-prefix-sat-reductions-and-transport-obstructions.md),
gives at least `1+sum_q v_q(M)(q-1)>=1+e_r(P-1)` members. Hence

    Z_r=empty ==> kappa_m>=e_r(P-1).                 (PT14)

Simpson's definition of regular covering and Corollary 2, pages 145
and 151, require irredundancy and allow repeated moduli. Thus repeated
restricted moduli cause no problem. PT14 is a direct reuse of that
standard result.

For quantitative escape mass we use the standard
Crittenden--Vanden Eynden interval bound. It has a short verification.
For k APs `a_j mod b_j`, form

    F(y)=product_j (1-exp(2 pi i (y-a_j)/b_j)).

This vanishes exactly at covered integers. Expanding and combining equal
frequencies expresses F as a sum of at most 2^k distinct nonzero
exponentials. If it vanishes at that many consecutive integers, the
Vandermonde matrix is invertible, so every coefficient vanishes and F
vanishes at every integer. A noncovering family therefore cannot cover 2^k
consecutive integers. This also allows repeated restricted moduli.
The bound is attributed to [Crittenden--Vanden Eynden (1970)](https://doi.org/10.1090/S0002-9939-1970-0258719-2),
not claimed as a new theorem.

As a weaker consequence, Z_r empty would give P^(e_r)-1 consecutive
covered y positions and hence `P^(e_r)<=2^(kappa_m)`. The threshold
is exponential, not `2 kappa_m`. Since P is odd and P-1>log_2 P,
this does not improve PT14; its purpose here is the window count below.

The same interval bound gives quantitative private mass, not only
nonemptiness. Put `W=2^(kappa_m)` and `L=Q/m`. Every restricted modulus
is `d/gcd(d,m)`, which divides L, so the parent-private y positions form
an L-periodic set. Every W consecutive y positions include a private
one. Counting all L cyclic starting positions, with multiplicity when
W>L, counts each private residue W times. Hence `pi_m>=1/(m W)`.

For the selected child let `D=P^(e_r)`. Since P does not divide m,
D divides L and K_r becomes one residue `y=c mod D`. In each D-block,
the D-1 consecutive positions after that residue avoid K_r. Split them
into `floor((D-1)/W)` disjoint windows of length W, each containing a
private point. There are L/D disjoint blocks. Dividing the resulting
count by Q proves

    pi_m >= 1/(m 2^(kappa_m)),
    z_r >= floor((D-1)/2^(kappa_m))/(m D)
        >= [floor((D-1)/2^(kappa_m))/D]
             H_X(C_r intersect R_P).                (PT14a)

The last inequality uses the actual source subset
`H_X(C_r intersect R_P)<=H_X(C_r)=1/m`; it does not replace that
source by an unconditioned shadow. If `D>=2^(kappa_m+1)`, the integer
bound `floor((D-1)/W)>=(D-W)/W>=D/(2W)` gives

    z_r >= H_X(C_r intersect R_P)/2^(kappa_m+1).

These estimates also handle kappa_m=0, when W=1. The cyclic count does
not require W to divide L, and the block count only uses D dividing L.
They are direct counting consequences of the standard interval theorem,
with the same essential original parent and complete original period.

They also give a source-coupled escape budget. For the same fixed tuple
put `lambda_base=lambda_tau/theta_tau=H_X(U_tau)` and

    beta_r=floor((P^(e_r)-1)/2^(kappa_(m_r)))/P^(e_r).

Since U_tau is contained in every C_r intersect R_P, PT14a gives
`z_r>=beta_r lambda_base`. Using the assignments and corrected
denominators d_q from PT7--PT8 therefore gives

    lambda_base sum_r beta_r/d_(q_r)
      <= sum_(used q) (c_q/d_q) pi_q
      <= sum_(used q) pi_q.                          (PT14b)

This is a quantitative mass comparison on the original source; it is
not a transition kernel. The bound remains valid for a raw subevent
mass lambda_tau, since then lambda_tau/theta_tau<=H_X(U_tau).

There is also a positive bound at every depth, conditional only on
actual escape. Add K_r to the kappa_m restricted APs on the parent
parameter line. The uncovered set of these kappa_m+1 APs is exactly
the parameter copy of Z_r. If Z_r is nonempty, the augmented family
does not cover. Apply the same cyclic interval count with window
`W_r=2^(kappa_m+1)`. It gives

    Z_r nonempty ==> z_r >= 1/(m_r W_r)
                         >= v_r/W_r,
    v_r=H_X(C_r intersect R_P).                       (PT14c)

This includes shallow prefixes for which PT14a has zero right side.
There is no assumption that private points are uniformly distributed;
every count uses the complete original period. Nonemptiness is essential:
PT14c makes no assertion about the zero-escape branch. Unlike PT4, this
branch does not need the additional residue minimum.

The two branches give a sharper combined source budget. Let
`S={r:z_r=0}`, `T={r:z_r>0}`, `f_r=1-P^(-e_r)`, and keep the assignments
q_r and corrected d_q from PT7--PT8. Let c_q^T count only the actual
first-q roots of parents in T assigned to q, with zero for no such
parent. Set `alpha_S=max_(r in S) 1/d_(q_r)`, or zero when S is empty.
PT4 pays the S terms from disjoint original overlap regions; PT14c and
the root-reset count pay the T terms from actual private escapes:

    sum_(r in S) f_r v_r/d_(q_r)
      + sum_(r in T) v_r/(W_r d_(q_r))
      <= alpha_S v_P + sum_q (c_q^T/d_q) pi_q
      <= v_P/2 + sum_(used q) pi_q.                  (PT14d)

For odd support primes d_q>=2. Moreover f_r>=1/2>=1/W_r, and
v_r>=lambda_base. Therefore a branch-independent consequence is

    lambda_base sum_r 1/(W_r d_(q_r))
      <= v_P/2 + sum_(used q) pi_q.                  (PT14e)

Every coefficient is positive, at every original finite height. PT14d
retains the stronger branch coefficients and actual source v_r; PT14e
is only its common-source simplification. These inequalities by themselves
do not specify a transport map or give a contradictory upper bound.

## 7. The unclosed global step

PT9 controls a single transport from an *actual parent-private source*.
PT2, PT4 and PT14a--PT14e are source/target mass comparisons, not
transition kernels. A separate [bounded-displacement construction](358-local-escape-transport.md)
now maps an actual child source into its actual parent-private set at
every depth, with explicit congestion. It need not preserve previous
coordinate exclusions. The [synchronized capacity allocation](359-synchronized-parent-capacity-allocation.md)
also assigns one global surplus budget across all current primes.
Neither construction gives a contradictory upper bound on that budget.

Directly resetting another prime p at a point already private to A_q
preserves A_q membership and introduces A_p membership. Its image is
in `A_q intersect A_p`, never private to A_p. Section 5 accounts for
this overlap; it does not turn it into a private-to-private iteration.
Also `q<P` follows only when starting at the largest prime P. A later
q-cofactor may contain larger primes. No strict prime descent has been
proved.

The [mean partial-matching bound](360-mean-partial-matching-without-tail-loss.md)
removes the full-matching tail loss from a budget on raw prime-private
sources. The remaining obligation is to control accumulated transport
losses, or give a whole-cover transformation or contradictory budget.
The explicit comparison for a nonempty escape
costs 2^(kappa_m+1); no height- and label-independent comparison follows.
All statements retain actual original labels and the full finite carrier;
local examples cannot settle this global obligation.

## 8. Verification scope

The general assertions follow from the finite proofs above and independent
review. Repository searches found the prior source identities and matching
bounds in 350, 354 and 355, but not the reset inequalities. This is not a
claim of literature novelty. The [exact checker](../frontier/private_swap_reset.py)
checks actual finite AP membership, swaps, source changes, and reset
congestion. Its three full-cover fixtures contain 27 original APs and
have complete periods 12, 144 and 960, totaling 1,116 checked points.
All contain even moduli; they are not distinct odd covers. There are
seven single-prime reset cases and six multi-prime subset cases, with
literal higher-digit preservation and exact target multiplicity checked.

For fixed D=(2,3,4,6,12), all 288 normalized residue assignments give
exactly four covers, each with minimum H_X(R_3)=1/4. Their eight
parent-child swaps divide into four legal swaps and four with actual
private escapes. The period-144 tuple has tail mass 1/3, product mass
1/12, and base mass 1/4. In the period-12 cover, private points 3, 7 and
11 from original moduli 3, 12 and 6 all reset to the same prime-3 private
point; counting only two source roots would be incorrect.

The window checks cover 30 essential original classes and 406 prime
prefix/residue choices. Three of those classes belong to the explicitly
noncovering odd list `0 mod3, 0 mod5, 1 mod75`, which covers only 36 of
75 residues. For its parent 3 and the selected P=5 prefix, the actual
escape mass is 19/75 and PT14a gives 12/75. These checks include zero
kappa, windows longer than the parent period, and the stated deep range.
They test the general interval consequence without asserting a whole
odd cover. Of the 406 prefix choices, 387 have nonempty escape and pass
PT14c; 234 of those have zero in the older floor bound. The other 19
choices have empty escape. In 139 nonempty-escape prefix configurations,
the augmented window is longer than the parent period. All four exhaustively minimized
period-12 covers also check the split budget PT14d, retaining its actual
overlap coefficient rather than assuming odd support in an even fixture.
Uniform re-tail density PT9 is justified by the independently
reviewed proof, not by a numerical check in this program.

Normal and physically relocated runs from `/` with isolated, optimized
Python give byte-identical output. No Lean declaration, kernel verification
or unrestricted noncoverage proof is claimed.
