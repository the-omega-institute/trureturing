[Index](../../marked_head_profile.md) · [Original source and ancestor cuts](371-private-top-fans-and-ancestor-cuts.md) · [Lower-ladder boundary](372-height-two-ancestor-complements-and-prime-support.md)

# Original binary first ancestors force a joint cutoff-one cylinder

Fix a prime q with H=v_q(Q)>=2 in a whole irredundant distinct
divisor-closed covering family. If the original modulus q*2^(q-2)
is present, there is a nonempty set of actual cofactors on which
ell_q=1. The number and heights of all other primes are unrestricted.
At q=3 the extra original is 6; at q=2 the hypothesis is automatic.
No complete lower q-height ladder, all-high assumption or common top
parent is required. In particular, this strengthens the A_6 case
of 371 and 372 without requiring an original 18.

The key is that a q-free original carrying a prime ancestor's residue
would be covered by other actual originals. Irredundancy forbids
such a mask. Consequently, the relevant prime coordinates can be
inserted simultaneously into the same actual source. Their complete
higher digits remain free.

This is an ordinary proof and a finite exact analyzer extension, not a
new Lean theorem or a resolution of unrestricted Erdős #7. In particular,
an all-odd family lacks the required binary structure. No literature-priority claim is
made. Positive source gain does not by itself solve the remaining joint
slot allocation or construct a cover-preserving replacement.

## 1. Original family and a first-root frame

Use the original family and full carrier of 371: one original AP
`A_d=a_d mod d` for each distinct d in a finite divisor-closed set D
above one; every integer is covered and every original has a private
point. Thus distinct comparable original APs are disjoint. Put

    Q=lcm(D), H=v_q(Q)>=2, B=Q/q^H,
    R={x mod B : x avoids every original q-free AP}.

Every q-bearing original has all its private cofactors in R. The pure
prime's private mass on the original uniform law is

    pi_q=q^(H-1)|R|/Q>0.

The cutoff ell_q(x) is the (q-1)-st largest height of the compatible
nonpure original columns. It is defined on R, and 371 gives the exact
source gain

    G_q := b_q-(q-2+q^(1-H)) pi_q
         = (1/Q) sum_(x in R) (q^(H-ell_q(x))-1).    (TI1)

Put k=q-2 and assume q*2^k is an original label. First take q odd.
The original pure binary classes A_2,...,A_(2^k) are disjoint and
leave one residue beta modulo 2^k. Every x in R has that residue.
For each j=1,...,k, comparable disjointness with A_2,...,A_(2^j)
forces the original A_(q2^j) to have binary residue beta mod 2^j.

The q-1 first classes A_(q2^j), j=0,...,k, therefore occupy q-1
different first-q roots over beta. Their roots are different because
their moduli are comparable and their binary residues compatible.
Let sigma be the one remaining root. Every other q-bearing original
must have first root sigma: otherwise a specified first class covers
every possible private point of that original over R. The resulting
restriction concerns the original fixed residues and holds globally.

At q=2, k=0, the binary modulus 2^k is 1 and there are no pure
binary classes in this argument. The frame consists only of A_2;
every other 2-bearing original has the other first root. Thus the
same statements hold with the indicated empty families. No coordinate
translation is needed in either case.

## 2. A forbidden original mask and full-coordinate insertion

Let r be an odd prime different from q with qr in D. There is no
q-free original A_d satisfying

    r divides d,       a_d = a_(qr) mod r.            (TI2)

Indeed, outside beta modulo 2^k, the pure binary originals cover
every integer of A_d. Inside beta, all roots except sigma are
covered by the first frame classes; the sigma root is covered by
A_(qr), using the r-coordinate stipulated in TI2. All these covering
labels differ from d: the first frame and qr are q-bearing, and a
pure binary label cannot contain the odd factor r. Thus

    A_d subset union_(j=1,...,k) A_(2^j)
                 union union_(j=0,...,k) A_(q2^j)
                 union A_(qr),

which contradicts the private point of A_d. This is a pointwise
covering argument on the original integers, not an assumption about
which marginal traces can be combined.

Write h_r=v_r(B). Given any y in R and any full coordinate

    u mod r^h_r with u = a_(qr) mod r,

replace only the r^h_r-coordinate of y by u. The resulting CRT point
z remains in R. Otherwise an original q-free A_d covers z. If r does
not divide d, the unchanged complementary coordinates make it cover
y as well. If r divides d, it violates TI2. Both alternatives are
impossible.

In particular, every one of the r^(h_r-1) higher-digit lifts is
allowed. Insertions at different primes preserve each other's first
digits and can be performed successively on the same original R.

## 3. Simultaneous ancestors reduce the actual cutoff to one

Define the full first-ancestor prime support

    S={r odd prime, r!=q : qr in D}.

This includes the odd primes of every q-bearing cofactor, even if
they do not occur in a top original. Put

    J={x in R : x = a_(qr) mod r for every r in S}.

The insertion argument proves J is nonempty. Also S is nonempty:
the pure top's private sibling fan requires at least q-1 distinct
nonpure top columns, whereas 371's unrestricted binary bound permits
only the q-2 colors 2^j, j=1,...,q-2, among purely binary q-bearing
cofactors for odd q. At q=2 every cofactor is odd, so there are no
binary colors. No all-high hypothesis is used.

Fix x in J and any compatible nonpure original q^e m. If m has an
odd prime factor r, divisor closure puts r in S. Apart from the
original qr itself, this class and A_(qr) have the same first root
sigma, compatible r-residues at x, and strictly comparable moduli

    qr divides q^e m.

The top or lower original's complete q-adic residue together with
x is therefore an actual CRT point in both APs, a contradiction.
The sole exception is the original qr itself, where the moduli are
equal and e=1,m=r.

If m has no odd prime factor, it is one of the q-2 binary colors. Thus at x
the only compatible nonpure columns are

    m=2^j, j=1,...,q-2, with their original compatible heights;
    m=r in S, each with height exactly one.

All q-2 binary frame first classes and every A_(qr) are active there.
There are at least q-1 columns, and at most q-2 can have height above
one. At q=2 the binary list is empty. Consequently

    ell_q(x)=1 for every x in J.                     (TI3)

In particular, all-high is impossible at every H>=2, for arbitrary
prime support and heights, whenever q*2^(q-2) is an actual original.

## 4. Exact cylinder count and relative source gain

Let

    T=B / product_(r in S) r^h_r,
    R_T={t mod T : t avoids all original q-free A_d with d dividing T}.

An original q-free modulus not dividing T contains some r in S. By
TI2 its r-residue differs from a_(qr), so it cannot meet the joint
ancestor cylinder. It follows directly that

    J = R_T x product_(r in S)
          {u mod r^h_r : u = a_(qr) mod r},
    projection_T(R)=R_T,
    |J|=|R_T| product_(r in S) r^(h_r-1)>0.          (TI4)

All products here are CRT products in the complete original carrier.
There is no independent resampling or renormalization of the source.
Equations TI1 and TI3 give

    G_q >= (q^(H-1)-1)|J|/Q.                        (TI5)

For a bound relative to pi_q, the original pure classes
A_r,...,A_(r^h_r) are disjoint and leave exactly

    N_r=r^h_r-(r^h_r-1)/(r-1)

residues modulo r^h_r. Every point of R avoids these classes. Thus

    |R| <= |R_T| product_(r in S) N_r,
    G_q/pi_q >= (1-q^(1-H))
                 product_(r in S) r^(h_r-1)/N_r.    (TI6)

This is an upper containing rectangle for the same actual R; equality
or independence of its marginal survivors is not asserted. Since
N_r<=(r-1)r^(h_r-1), a simpler consequence is

    G_q >= (1-q^(1-H)) pi_q / product_(r in S)(r-1).
                                                     (TI7)

The full pure-ladder factor in TI6 is stronger whenever h_r>1. For
fixed S, the relative factors in TI6 and TI7 do not decrease as prime
heights increase. Their product can still tend to zero as the set S
grows; this is not a positive constant uniform over arbitrary support.

## 5. The guaranteed cylinder has no extra composite-parent selections

On J the shallow graph has exactly q-2 independent frame edges,
one at each of their distinct nonprime first roots, and a star from
sigma to the prime colors r in S. Its maximum rank is q-1. Every
maximum matching selects every frame edge and one star edge.

The global singleton-root count of 364 is at most q-2. Since the
frame supplies that many singleton colors, it is the complete set.
Consequently, its forced composite-color count is

    f_q=q-3 for odd q;       f_2=0.

Every shallow maximum matching on J has exactly f_q composite
parents. It has two prime parents for odd q (color 2 and the selected
r), or one for q=2. If

    J_source={a_q mod q} x T_q x J subset Priv_q,

then, on the original full Haar law,

    integral_(J_source) (selected_composite_count-f_q) dH=0.
                                                     (TI8)

Thus the positive source gain in TI5 is not an additional
composite-parent contribution on this cylinder beyond the already
forced baseline of 366 ST5. This is an exact decomposition on
J_source, not a difference between two chosen matchings. It does
not imply that the complete global ST5 bound cannot improve: the
original prime-parent allowance and the source outside J_source
still have to be evaluated together. A proof of a global budget
contradiction cannot replace that work by TI5's positive number.

## 6. Verification and applicability boundary

The [original-cover analyzer](../../frontier/arithmetic/top_fan_ancestor_cuts.py)
checks TI2 for every applicable original mask, every full-coordinate
insertion into every point of R, the joint CRT count, and ell_q=1
at every joint point. It also checks the exact complementary residual,
pure-ladder counts, both gain bounds and the exact frame-plus-star
shallow graph in TI8. Its
preconditions still require full-period coverage, private points,
distinct original labels, divisor closure and comparable disjointness.

For q=3 in the period-3150 family of 369, S={5,7}, |R|=55 and

    J={67,137,207,277,347} mod 350.

The gain count is 98 and TI5 supplies 10 on the original period 3150.
For the period-1350 family displayed in 372, which contains A_6 but
has no original 18, S={5}, |R|=13 and

    J={9,19,29,39,49} mod 50.

All five cofactors have ell_3=1; the total gain count is 90 and TI5
supplies 40 on the original period 1350. The period-80 family in 371
also checks the q=2 empty binary-cofactor branch at H=4. These are even whole-cover
controls, not odd-cover counterexamples. Translations preserve the
counts while translating the actual witness coordinates. Ordinary
and detached optimized executions agree.

The following actual period-5040 family is an applicability control.
Its entries are `(residue, original modulus)`:

    (0,2), (0,3), (1,4), (0,5), (0,7), (3,8), (4,9),
    (7,10), (5,14), (14,15), (15,16), (11,20), (10,21),
    (11,28), (23,40), (19,45), (23,56), (43,63), (55,112).

It is a whole irredundant distinct divisor-closed cover with comparable
originals disjoint. At q=3 it has H=2 and no original 6. Instead, its
original 15 is cofactor-universal, with root 2 and cofactor residue 4
modulo 5. The exact region and cutoffs are

    R_3={199,519} mod 560,   ell_3(199)=1, ell_3(519)=2,
    pi_3=1/840,             G_3=1/2520.

The eight original classes whose moduli divide 80 leave exactly 39
modulo 80. Both actual cofactors lie over this residue. The original
21 selects 199 through its residue 3 modulo 7. Full-period enumeration
and an independent verifier check these statements; the analyzer
correctly declares the q=3 binary-frame insertion inapplicable. Thus
the complete-cover hypotheses do not force the original 6. This
even cover does not refute an all-odd claim, or the existence of a
low cofactor without 6: it has such a cofactor.

At q=3 every shallow maximum matching uses only the prime cofactor
colors 5 and 7. Over the three complete tails, their ranks sum to 6
at cofactor 199 and to 4 at cofactor 519. Thus the actual selected
parent masses satisfy C_3=0 and P_3=b_3=10/5040, even though
G_3=2/5040>0. Positive source gain therefore does not force an
improvement in this prime's composite-source term; this makes no
claim about the sum over all primes.

At q=3, the restriction to an actual A_6 is material. If it is replaced by
an arbitrary cofactor-universal A_(3u), the three first-root argument
survives, but TI2 does not follow: a 3-free original carrying an
ancestor residue may have private points outside the u-cylinder.
Here u must be prime: the divisor ideal and root count in
[364, SI4 and SI8](../364-singleton-cofactor-ideal-and-forced-colors.md)
give tau(u)<=2. This corrects 372 section 2's statement that u may
be composite under its q=3 hypotheses; that section's implication
and proof remain valid.
The A_2 parity split is what eliminates that escape at q=3. Extending
this argument to arbitrary u, or obtaining the corresponding source
gain for an all-odd family without a universal first class, remains
unresolved. The exact source gain must also still be transported
through the original joint allocation conditions.
