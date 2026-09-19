[Index](../../marked_head_profile.md) · [Original ancestor cuts](371-private-top-fans-and-ancestor-cuts.md)

# Original ancestor complements require more prime support

At q=3 and original height two, one actual cofactor-universal mixed first
class prevents all-high whenever the highest-level cofactor palette uses
at most two primes. This concerns the prime support of the actual top
colors; other original moduli may contain additional primes. The argument
applies to odd or even covers under the stated whole-cover hypotheses.

It sharpens 371's height-two antichain consequence by applying it after
excluding an original ancestor's entire divisibility upper cone. It does
not exclude the whole covering family or prove the existence of a
universal first class in an arbitrary odd cover. This is an ordinary
finite proof with an exact analyzer, not a new Lean theorem.

## 1. An ancestor whose remaining top colors form a chain

Use 371's original finite irredundant, distinct, divisor-closed covering
family, complete period Q, actual cofactor set R_q and original traces.
Let q>=3 be prime and `H=v_q(Q)=2`. Suppose q-2 different original
exponent-one mixed classes have cofactor traces containing all of R_q.
Let U be their q-free cofactors and M the complete nonpure top palette.
For `m in M minus U` put

    Up(m)={n in M:m divides n},       V_m=M minus Up(m).

**If V_m is a divisibility chain, some actual cofactor has ell_q<H.**

Suppose otherwise. The original A_(qm) has a private point z whose
cofactor y belongs to its nonempty first-ancestor trace E_m. The ancestor
cut AC1 of 371 excludes all top colors in Up(m) at y. All-high therefore
requires at least q-1 actual top classes from V_m active at this same y.

The universal first classes and the prime class leave one first root r.
Every top original and A_(qm) has root r. This root has exactly q leaves
because H=2. Its pure original A_(q^2) occupies one leaf. Every nonpure
top original avoids that leaf by comparable disjointness. The leaf of
z is different, since z is private to A_(qm), and every top original
also avoids that leaf at y.

Thus q-1 active top classes occupy at most q-2 leaves. Two share a leaf
and the same actual cofactor y. Their original APs intersect at the
resulting complete CRT point. Their colors belong to the chain V_m,
so their distinct original moduli are comparable. This contradicts
comparable disjointness. The empty or one-color case already contradicts
the required q-1 active colors.

More precisely, all-high requires an antichain of at least two coactive
colors in V_m at the cofactor of every private point of A_(qm). This
statement uses the actual private-point projection, which need not be
all of E_m. Nonemptiness of E_m alone is not a license to call every
point above it private.

By 371's original-Haar identity, the resulting low cofactor gives

    b_q-r_q pi_q >= (q-1)/Q,      r_q=q-2+1/q.

The proof excludes all-high, but does not assert that all of E_m is low:
without a private point above a chosen cofactor, the second forbidden
leaf in this argument is not available there.

## 2. At q=3, at least three top primes are necessary

Specialize to q=3, H=2, and one original universal first class A_(3u).
Let P(M) be the set of primes dividing any m in M. Divisor closure of
the original numerical labels makes M a nonunit divisor ideal.

If P(M) is empty, the top fan of 371 is impossible. If P(M) has one
prime, M is a chain and 371's all-height chain obstruction applies,
including when u is itself that prime.

If `P(M)={p,s}`, then both p and s belong to M. At least one, say p,
differs from u. The original A_(3p) is therefore outside the specified
universal family. Every top color not divisible by p is a power of s,
so V_p is a chain. Section 1 gives a contradiction to all-high.
Consequently,

    q=3, H=2, one universal mixed first class, all-high
        ==> |P(M)|>=3.                              (HP1)

Equivalently, top support at most two forces gain at least 2/Q on the
original source. No even-period assumption or binary ladder is used.
The universal cofactor u may be any original q-free cofactor greater
than one, and may itself be composite.

For an even original cover containing A_6, that class supplies the
universal first class. Thus, at H_3=2, any two odd cofactor primes can
have arbitrary finite heights and all-high is still impossible: under
all-high, 371's binary restriction would remove 2 from the top palette,
leaving at most those two odd primes. This extends the height-one bound
on one of the two other primes in 371 while retaining H_3=2 here.

## 3. An explicit lower ladder recovers the same obstruction at any height

There is a conditional extension to any H>=2. Keep the q-2 universal
first classes with cofactors U, and additionally require every original

    q^(H-1) u,     u in U.                           (HP2)

Divisor closure supplies q^e u at every e<=H-1. Their cofactor traces
are universal as well: R_q has one fixed residue modulo u, and the
private point of each original q^e u forces its residue to be that one.
Together with the pure q^e originals, there are q-1 universal classes
at each depth e=1,...,H-1.

These form the same kind of nested skeleton as in 371. Each level must
occupy distinct children of the one previously uncovered prefix, or
one of its classes could have no private point. The skeleton leaves
exactly one depth-(H-1) prefix P over all of R_q.

Every top original must lie in P to have a private point, and every
private point of a nonskeleton first ancestor A_(qm), m outside U,
lies in P. This prefix has precisely q highest-level children. The
pure top class occupies one, and the ancestor's private point occupies
another. AC1 still excludes Up(m). If V_m is a chain, all-high forces
q-1 top classes into at most q-2 children, giving the same contradiction
as in section 1.

Thus the chain-complement criterion, and the q=3 top-support-at-most-two
consequence, hold at any H>=2 under HP2. At H=2, HP2 is already the
declared first-class hypothesis. At H>=3 it is an additional original
label requirement, not a consequence of having only the first class.
For q=3 and u=2, it requires the original class `2*3^(H-1)`; an original
6 alone does not guarantee it.

## 4. Verification and the remaining cases

The existing [original-cover analyzer](../../frontier/arithmetic/top_fan_ancestor_cuts.py)
now reports the chain-complement conditions and the ternary top-support
condition when the complete lower ladder is present. It checks
each conclusion only after verifying its original-cover and root
saturation hypotheses. The period-3150 control from 369 has q=3,
H=2, U={2}, M={5,7,25,35}; its complement at m=5 is the chain {7}.
It supplies an actual whole-cover input for the new condition.

The period-12 boundary remains excluded at q=3 because H=1. The
period-80 input at q=2,H=4 exercises 371's all-height result without
invoking this q>=3 criterion. These checks do not prove HP1 for
arbitrary input sizes; the preceding original-AP argument does.

A height-three applicability control uses the actual whole period-1350
family

    (0 mod 2), (0 mod 3), (0 mod 5), (5 mod 6), (7 mod 9),
    (3 mod 10), (4 mod 15), (11 mod 25), (10 mod 27),
    (7 mod 30), (31 mod 45), (31 mod 50), (16 mod 75),
    (1 mod 135), (1 mod 225), (46 mod 675).

At q=3 it has the universal first cofactor 2, but no original 18.
The analyzer verifies the cover and reports the lower-ladder condition
as false; it does not apply HP1 there. Ordinary and detached optimized
runs agree. Repeated moduli, missing divisors, noncoverage and intersecting
comparable APs continue to be rejected at the input or hypothesis stage.

Without HP2 at H>=3, the first root has more than q leaves, so the same
two forbidden leaves do not force a collision among q-1 active top
classes. No unconditional all-height version of HP1 is claimed. The
remaining cases include unsaturated roots, incomplete lower ladders
and top palettes with at least three prime factors. Even a positive
source gain must still be combined with
the original target and joint-allocation budgets to address Erdős #7.
