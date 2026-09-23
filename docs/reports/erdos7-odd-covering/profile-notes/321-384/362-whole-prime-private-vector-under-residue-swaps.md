[Index](../../marked_head_profile.md) · [Original private swaps](357-original-private-swaps-and-prime-reset-transport.md) · [Shared capacities](359-synchronized-parent-capacity-allocation.md) · [Full-private budget](360-mean-partial-matching-without-tail-loss.md)

# Whole prime-private vectors under legal residue swaps

A legal parent--child swap has an exact effect on every original prime's
private mass. For a prime parent, irredundancy of the resulting cover forces
a measure-preserving permutation of the entire labelled family: every
private mass is unchanged. For a composite parent, other primes can change.
An actual irredundant even cover exhibits such a cross-prime change.

These identities distinguish minimizing one survivor from minimizing a
common weighted potential. They do not strengthen 359--360's scalar surplus
budget or prove that the hypothetical extremal odd cover does not exist.
The finite counterexample below is not divisor-closed. All proofs here are
ordinary finite arguments; no Lean verification or literature novelty is
claimed.

## 1. Fixed original family and the legal exchange

Let the distinct original moduli form D, with complete period Q and uniform
Haar law H on Z/QZ. Assume the original APs cover every point and that
comparable original classes are disjoint. Every support prime is an
original label. Write A_j for the AP of modulus j, N for full original
multiplicity, and

    Priv_j={y: the original covering labels at y are exactly {j}},
    pi_j=H(Priv_j),       H_cov=sum_(j in D) 1/j-1.

Fix an original child d=P^e m, with P prime, e>=1, P not dividing m, m>1,
and with the actual original parent m present. In the CRT decomposition
into the complete P-coordinate and its complement, write

    A_m=B,                 A_d=K intersect C.

Here B and C are full lifts of cofactor APs modulo m, and K is the child's
P-prefix of depth e. In particular B and C are disjoint; K is disjoint
from the original prime class A_P. Change just these two labelled APs:

    A'_m=C,                A'_d=K intersect B.                  (SV1)

All sets below are measured on the same full original carrier. Directly,

    N'-N=1_(C intersect K^c)-1_(B intersect K^c).              (SV2)

Since the old child avoids B, the new family is a whole cover exactly when

    Priv_m intersect K^c is empty.                            (SV3)

Indeed, a point of B outside K loses only the old parent; it remains
covered precisely when it was not parent-private. Points of C outside K
gain one covering label, and no other point changes multiplicity. D and
therefore H_cov remain fixed.

Under SV3 the two exchanged labels satisfy the stronger set identities

    Priv'_m=Priv_d,          Priv'_d=Priv_m.                   (SV4)

Inside K their labels exchange. Outside K the new parent is added to an
already covered point, and the new child is absent. Thus the reverse
exchange is legal as well. SV4 needs whole coverage but not irredundancy
of the resulting family.

## 2. Exact change of every prime-private component

For each unchanged prime label q, that is q!=m, put

    G_q={y: original labels are exactly {m,q}} intersect K^c,
    L_q=Priv_q intersect C intersect K^c.

Then

    pi'_q-pi_q=H(G_q)-H(L_q).                                (SV5)

The only new private points for q occur where removing m leaves q alone;
the only lost private points occur where adding m creates a second label.
These descriptions use the actual full labelled family, not independent
extrema or projected covers.

If q divides a composite m, both B and C avoid A_q, by the original
disjointness of comparable classes. Therefore G_q and L_q are empty and

    q divides m, m composite ==> pi'_q=pi_q.                 (SV6)

If m itself is prime, its root changes from B to C. It must instead use
SV4:

    pi'_m-pi_m=pi_d-pi_m.                                   (SV7)

Keeping the old root in a survivor computation would compute a different
set. One may translate the whole new family to normalize its prime roots
again; such a common translation preserves all private masses.

For the distinguished prime P, let R_P be the cofactor set avoiding every
P-free original and let E be the cofactor portion of B avoiding all other
P-free originals. Comparable disjointness gives

    Priv_P=A_P intersect R_P,
    P(pi'_P-pi_P)=H_X(E)-H_X(C intersect R_P).                 (SV8)

This is 357's survivor identity, now part of the full vector. It holds for
any P with the stated all-P-free definition. Identifying R_P with the
chronological pre-P survivor still requires P to be the largest support
prime.

## 3. Prime-parent rigidity transports the entire family

Suppose m is prime and the swapped whole cover is irredundant. The original
comparable-disjointness hypothesis implies that every m-bearing original
other than A_m avoids its old root B. In the new family, any m-bearing
original other than the new parent and child must also avoid C: otherwise
its whole AP would lie in the new parent and be redundant. The new child
lies at B, as specified in SV1.

Let sigma exchange the two first-m roots B and C, keep every higher m-digit,
and keep every other prime coordinate. This is a Haar-preserving involution.
Every m-free original is invariant under sigma. Every unchanged m-bearing
original has its first root outside B and C and is invariant too. The two
changed labels have exactly the images in SV1. Consequently, for every
original label j,

    sigma(A_j)=A'_j,        sigma(Priv_j)=Priv'_j,
    pi'_j=pi_j.                                             (SV9)

In particular SV4 and SV9 give pi_d=pi_m, and SV8 gives

    H_X(E)=H_X(C intersect R_P).                             (SV10)

SV3 also confines the old parent-private set to B intersect K, whose
Haar mass is 1/(P^e m). In this prime-parent case,

    pi_m=pi_d<=1/(P^e m).

This applies to every prime P different from m, with no largest-P or
survivor-minimum assumption. It is an upper bound, not a contradiction
or a lower bound on the full prime-private budget.

In a globally minimum-cardinality distinct-modulus cover, every legal
same-D exchange is automatically irredundant: a redundant class could be
deleted to give a smaller admissible cover. Thus SV9 applies to all legal
prime-parent exchanges of the hypothetical extremal cover. It is not
justified for an arbitrary legal exchange without the resulting
irredundancy premise.

There is a related sufficient condition for a prime-power parent m=p^a:
if B and C agree modulo p^(a-1), the same argument exchanges only their
last low p-digit. Originals with smaller p-exponent cannot distinguish
them, and originals with exponent at least a are multiples of m and must
avoid both parent classes unless they are the two changed labels. With
irredundancy after the exchange, SV9 again holds. Merely having all lower
pure p-powers present does not assert this congruence when p is odd.

## 4. A common potential retains the cross-prime terms

Fix D in the hypothetical extremal class. Choose positive constants c_q
depending only on this fixed D, and minimize the one common potential

    Phi=sum_q c_q pi_q
       =sum_q w_q q pi_q,       c_q=w_q q.                  (SV11)

The set of residue assignments is finite. Every legal same-D exchange
stays in the extremal class, so its potential change is nonnegative. For
a composite parent the exact condition is

    sum_q c_q H(L_q) <= sum_q c_q H(G_q).                 (SV12)

For a prime parent all components are unchanged by SV9. Equivalently,
without yet invoking that rigidity, the exact derivative is

    Delta Phi = sum_(q!=m) c_q[H(G_q)-H(L_q)]
                 + 1_(m prime)c_m(pi_d-pi_m).              (SV13)

For composite m, SV8 can be isolated from SV12, but the other q terms
remain. No sign for each individual difference follows from the weighted
sum. In particular one common minimum does not authorize applying 357's
separate survivor-minimum argument to every P at once.

A descending lexicographic minimum has the same limitation. It does give
pi'_P>=pi_P when every larger-prime component is known to be unchanged;
SV6 supplies this condition, for example, if every support prime greater
than P divides the composite m. Without such an invariant-prefix
condition, an earlier positive change can mask a later negative change.

The gains G_q are genuine old double-cover regions with exact labels
{m,q}. Gains for distinct composite parents are disjoint, but the same
parent used in several comparisons can reuse the same gain region. The
pointwise reuse count is the sum of the corresponding indicators 1_(K^c).
Separately legal exchanges do not automatically form a simultaneous
exchange or a new allocation of the original surplus.

Dropping other losses and charging distinct-parent target capacities
produces a scalar inequality already supplied by 359's CRT parent
intersection argument. It is not an improvement of CA6 or the all-prime
budget in 360. The additional content here is the vector derivative and
the exact family-transport condition. A useful stronger consequence for
360 would still need control of the cross-prime terms and reused parents,
or a new extremal structural restriction forcing those terms to vanish.

## 5. Actual whole-cover cross-prime change

The following distinct even cover has complete period 180:

    (residue,modulus) =
    [(0,2),(0,3),(0,5),(1,4),(1,9),(1,10),(2,15),
     (3,20),(5,18),(7,30),(7,36),(29,45),(49,90),(179,180)].

For P=5, m=9, d=45, perform SV1:

    A_9: 1 mod 9 -> 2 mod 9,
    A_45: 29 mod 45 -> 19 mod 45.

Both families cover all 180 residues; every original class remains
essential and comparable classes remain disjoint. Their prime-private
point counts are respectively

    old: (pi_2,pi_3,pi_5)*180=(32,6,3),
    new: (pi_2,pi_3,pi_5)*180=(34,6,3).

Thus the distinguished P component is unchanged while another prime's
component changes. The reversed legal exchange changes that cross
component with the opposite sign. This refutes unconditional deletion of
the cross terms for irredundant whole covers; it is not a counterexample
to any additional consequence of divisor closure or odd extremality.
For example modulus 6, a divisor of 18, is absent. The family has even
moduli and is not an odd-cover example.

The exact gain cells in SV5 are G_2={28,46,82,118,136,172} and
G_5={55}; the loss cells are L_2={38,56,128,146} and L_5={155}.
Both cells for q=3 are empty. A CRT permutation swapping 1 and 2 modulo 9
while fixing the modulo-20 coordinate changes the other original classes
of moduli 15 and 30. Those moduli share the proper divisor 3 with m=9,
which distinguishes the two parent residues. Thus the whole-family
invariance argument of section 3 does not apply.

For contrast, a period-120 whole-cover fixture in the checker has a legal
P=3,m=8,d=24 exchange changing only pi_3, by 1/120. That fixture lacks
modulus 4, and its two parent residues 1 and 3 modulo 8 are not siblings
modulo 4. Neither prime-parent rigidity nor its stated sibling extension
applies.

## 6. Exact verification scope

The [standalone checker](../../frontier/cover-geometry/prime_private_swap_vector.py) reads no
repository state. It enumerates full original AP membership, recomputes
both changed residues by CRT, and checks the legal-swap criterion, the
full multiplicity identity, both exchanged private sets, every prime
component of SV5--SV8, and the weighted derivative for explicit positive
weight vectors. For each irredundant prime-parent exchange it constructs
the root involution and checks its action on every labelled AP and private
set. It also checks the stated sibling sufficient condition when present.

The fixtures include the three even covers of periods 12, 144 and 960 from
357 and the two whole covers of periods 120 and 180 above. The checker
explicitly verifies the nonzero distinguished-prime and cross-prime
examples, with no artificial cofactor parents. Missing divisors are
reported, not silently filled. The program uses only the standard library
and keeps checks active under optimized Python. The five fixtures contain
53 original APs and 1,416 full-period points. They give 55 candidate
exchanges, 26 legal exchanges, 11 prime-parent family transports, and
three additional composite sibling transports. One other legal exchange
creates a redundant class; it tests the general derivative but is not
used as an irredundant extremal comparison.

Normal execution and a physically relocated isolated optimized execution
from `/`, with a script path containing spaces, both exit zero with
identical output and empty standard error. A negative control that sets
every cross-prime derivative to zero is rejected by the vector identity
check. Finite execution checks
the supplied examples and identities; it does not prove a general
extremal cancellation theorem or a new lower bound for 360.
