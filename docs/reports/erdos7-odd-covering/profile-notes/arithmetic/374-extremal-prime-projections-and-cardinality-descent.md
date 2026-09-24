[Index](../../marked_head_profile.md) · [Fresh-root transport](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md) · [Extremal original family](../321-384/350-extremal-paired-branch-and-source-support.md) · [Singleton cofactors](../321-384/364-singleton-cofactor-ideal-and-forced-colors.md)

# Minimum odd covers have large original prime-coordinate projections

Suppose a finite distinct odd covering system exists, and choose one
with globally minimum class count. For any support primes q<p, the
actual cofactor region avoiding every q-free original must use at
least p-q+1 different first-p digits. No prime-power height is bounded;
no original prime class or divisor closure is needed for this result.

In particular, in 350's divisor-closed extremal model, the prime-3
region uses at least p-2 digits at every support prime p>3. It cannot
lie in any single nontrivial cofactor congruence class. Thus the
cofactor-universal first ancestors studied in 364 cannot
occur at q=3 in this extremal odd model, at any original 3-height.

The proof transports q complete p-root branches already covered by
the q-free originals, and counts the resulting classes. It uses the
literal digit map from 348's fresh-root construction with no extra
closing classes. It is an ordinary deduction, not a new Lean theorem
or a resolution of Erdős #7. An irredundant even control demonstrates
the actual descent; global minimum cardinality supplies the
contradiction in the odd-cover argument.

## 1. Actual residual roots and complete covered branches

Let the original distinct classes be A_d=a_d mod d, d odd and d>1.
Write n for their number, Q for their complete period, and

    H=v_q(Q)>=1, B=Q/q^H=p^K M, gcd(p,M)=1,
    C0={A_d : q does not divide d}, m=|C0|<n,
    R={x mod B : x avoids every class in C0},
    S={x mod p : x in R}, s=|S|.

Here K>=1 since p is a support prime different from q. Minimum
cardinality makes R nonempty: otherwise C0 is a smaller distinct odd
cover. If a first-p root xi is absent from S, its entire full branch

    {y mod B : y=xi mod p}

is covered by C0. This statement concerns all the original higher
p digits and every other full cofactor coordinate, simultaneously.
It supplies complete branches, not independently chosen covered
points in several projections.

## 2. Too small a projection gives a strictly smaller cover

Suppose s<=p-q. Select q distinct roots xi_0,...,xi_(q-1) outside S
and match them bijectively to all q roots b=0,...,q-1. On the full
new carrier of size

    B'=q*p^(K-1)*M,

define a witness in the original cofactor carrier by

    y=xi_b+p*(z mod p^(K-1)) mod p^K,
    y=z                         mod M,
    b=z mod q.                                      (EP1)

For each fixed b this is a bijection from the new b branch to the
entire old xi_b branch. By construction y is covered by C0.

Keep every p-free class of C0 unchanged. For each original class
of C0 of the form a mod p^alpha r, alpha>=1, gcd(p,r)=1, keep it
only if xi=a mod p is among the selected roots. Replace it by the
single class of modulus q*p^(alpha-1)*r with CRT conditions

    z=b                   mod q, where xi_b=xi,
    z=(a-xi)/p            mod p^(alpha-1),
    z=a                   mod r.                    (EP2)

The high-p residue is (a-xi)/p, not a; all other prime-power heights
are retained. Membership of y in each q-free original equals
membership of z in that original's output, or is false everywhere
on the selected branches if the original was discarded. Thus the
whole q-free event vector is transported using one common witness.
Every z is covered. No pure-q closing class is added.

The modulus map d -> q*d/p is injective on transported originals.
Its images have a q factor, whereas unchanged classes are q-free.
A transported original of modulus p may become modulus q. This is
safe: at most one original has modulus p, and there is no added
closing class with which its image could collide. All output
moduli are therefore distinct, odd and greater than one.

Each class in C0 contributes at most one output class, so

    n_out<=m<n.                                     (EP3)

This contradicts global minimum cardinality. Consequently

    |projection_p(R_q)|>=p-q+1.                      (EP4)

For any whole distinct cover satisfying the small-projection
threshold, EP1--EP3 construct a strictly smaller cover. Minimum
cardinality turns this construction into EP4. The construction
needs neither original A_p nor A_q, divisor closure, comparable
disjointness, universal first ancestors or a lower-height ladder.

This is the root-and-tail map of 348 section 1 applied to q selected
complete branches. Here every new q root is used, so no repeated-prime
completion or closing family is necessary, and an original p may be
retained through its image q.

The map preserves the conditional uniform law and every event of C0
on each selected branch. It is not a measure-preserving map of the
whole original cover: q-bearing originals have been removed, most old
p branches may be unused, and the carrier has changed. No source mass
from the original Haar budget is identified with an output mass.

## 3. Consequences for the extremal original model

In 350's lexicographically extremal odd model, every support prime
is an original label and the support starts at 3. Thus for every
support prime p>3,

    p-2<=|projection_p(R_3)|<=p-1.                  (EP5)

Besides the root excluded by the original A_p, at most one first-p
root is absent from the projection. This is a statement about which
roots occur, not about their frequencies. It does not say that the
projection law is uniform or that different prime projections are
independent. The entire argument keeps the actual same R_3.

If R_3 were contained in a single class c mod u for any u>1 dividing
B, choose any prime p dividing u. Oddness and gcd(3,u)=1 give p>3,
and its projection would have size one, contradicting EP5. In
particular 364's original universal-cofactor family obeys

    F_3=empty, L_3=1, f_3=0.                        (EP6)

This includes H_3=1. More generally, if m belongs to F_q, every prime
factor p of m must be smaller than q: any p>q would again give a
singleton projection contradicting EP4. These are consequences for
the same extremal odd model, not additional assumptions that can be
imposed on arbitrary whole covers.

The earlier conditional universal-ancestor results remain valid.
For q=3, however, an extremal odd-cover proof must address the branch
without such a universal ancestor. A low-cutoff theorem conditioned
on one does not by itself control this remaining branch.

## 4. Verification and boundary

The [fresh-root constructor](../../frontier/cover-geometry/fresh_root_constructor.py)
has a `contract_small_projection` entry that computes the complete
original q-free residual and checks EP1--EP2 against every complete
q-free event vector on the common transport carrier. It checks the
original and output covers, numerical distinctness, complete heights
and the strict class-count decrease. Oddness is the default; even
control inputs require an explicit option. It does not certify
minimum cardinality from a finite run.

The constructor's complete `original5040` control has q=3, p=5,
m=13 and S={4}.
The construction gives these twelve original-provenance output
classes, written as (residue, modulus):

    (0,2), (1,4), (0,7), (3,8), (1,6), (5,14),
    (15,16), (3,12), (11,28), (23,24), (23,56), (55,112).

These are the output of selecting old roots 1,2,3. Their period is 336.
The input is an irredundant divisor-closed cover
with 19 classes; its smaller output is permitted to lose those two
properties. This demonstrates a real coverage-preserving class-count
descent: irredundancy of a general distinct cover does not itself
prohibit it. Both covers contain even moduli and are not witnesses
to the odd premise.

The constructor checks six controls, including the same cover at
q=5,p=7 where s=p-q=2, an original p transported to q, a translated
family, and a whole cover with added pure p^3 and mixed p^2 labels.
The added classes in the last control are not claimed irredundant.
There are 10368 complete conditional-source points and 151584
q-free original event coordinates in these new checks; eight invalid
inputs are rejected. The general all-height result comes from the
proof, not from the finite-period cap or these even examples.
Ordinary and isolated optimized executions agree. An independent
mutation that substitutes a for (a-xi)/p still produces a covering
output in the high-power control but corrupts 364 complete source
event vectors; the constructor rejects it. Coverage alone would not
detect that loss of original-event provenance.

No dominating extremal projection theorem was found in the searched
project reports 348, 350 and 354--373. The transport map is already
proved in 348, based on the explicitly cited HSW root construction;
the present all-root variant also retains an original p as q.
No literature-priority claim is made. Large individual projections
still do not determine their joint CRT compatibility or give the
missing all-prime budget contradiction. Unrestricted Erdős #7
remains unresolved.
