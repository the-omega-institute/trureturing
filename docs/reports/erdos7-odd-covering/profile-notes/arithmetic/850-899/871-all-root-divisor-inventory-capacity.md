[Index](../../../marked_head_profile.md) · [Whole-class prime-cut repair](864-complete-color-covers-and-phase-product-obstruction.md#a-prime-bipartition-repairs-the-entire-deleted-union) · [Prefix repair interface](870-matroid-prefix-rounding-and-divisor-hall-repair.md)

# Averaging literal prime roots of one actual divisor inventory

This argument concerns a globally count-then-modulus-sum minimal odd
distinct covering system with maximal ternary height two. It does not
assume that every possible odd cover has these parameters. In the
q=113, height-one branch, it gives a new necessary restriction on each
actual top cofactor, not a bound on the union of all prime supports.

## Every counted divisor belongs to the same cover

Let 9qm be an actual original modulus, q>=7, with m coprime to 3.
Every nonunit divisor of an actual modulus is present in a sum-minimal
system: otherwise replacing that one original class by its projection
to the missing divisor preserves coverage and distinctness, and strictly
decreases the modulus sum. Thus every d|m supplies a unique original
with numerical modulus 9qd. Different d give different originals.

Write a_d for its literal residue and z_d=a_d modulo nine. These are
the original choices, not separately optimized phases. The same closure
supplies pure originals of moduli 3 and 9. Cardinality minimality gives
each original a private point. If two comparable moduli had compatible
phases, the larger class would be contained in the smaller class and
could have no private point. Therefore the pure 3 and 9 classes are
disjoint, and every 9qd class is disjoint from both.

Modulo nine, these two pure classes remove three plus one distinct
residues. Consequently all z_d lie in one common five-element set Z.
This conclusion includes d=1. The set is fixed by the actual guards.

## An induced prime cut retains the outside divisor stock

Write m as the product of p raised to e_p over its prime support P.
Choose disjoint nonempty S,T contained in P, and put O=P minus (S union
T). No condition is imposed on the phases of different divisors.

Choose an auxiliary root phi_p modulo p for each p in S union T.
For each old word z in Z, select exactly those 9qd originals satisfying

$$
z_d=z,\qquad
\exists p\in S:\ p\mid d,\ a_d\equiv\phi_p\pmod p,\qquad
\exists t\in T:\ t\mid d,\ a_d\equiv\phi_t\pmod t.
$$

Pick one matching prime on each side for every selected original.
The whole-class repair of PC57--PC58 bounds the selected count by its
number of used tags, hence by |S|+|T|. All five old words together
therefore select at most 5(|S|+|T|) originals for every common phi.
The repair does not require phi to come from a surviving point, a
private point, or one common point of all selected original classes.

Average over independent uniform choices of these auxiliary roots.
For one fixed d, the probability of some match on S is

$$
1-\prod_{p\in S,\ p\mid d}\left(1-\frac1p\right).
$$

The two sides use disjoint coordinates, so their probabilities multiply.
Different originals are combined only by linearity of a finite sum;
their literal phases can be arbitrarily correlated.

For A contained in P define

$$
\tau_A=\prod_{p\in A}(e_p+1),\qquad
B_A=\prod_{p\in A}\left(e_p+1-\frac{e_p}{p}\right),\qquad
R_A=\tau_A-B_A.
$$

Summing over all exponent choices in d|m gives the induced-cut constraint

$$
\boxed{\tau_O R_S R_T\le5(|S|+|T|).}
\tag{RA1}
$$

The outside factor is necessary. Changing an exponent in O gives another
actual original even though it changes neither set of tested prime
coordinates. Its literal phases and old word may change, but the
averaged count for the two sides stays the same. Dropping tau_O gives a
weaker valid estimate, not the exact inventory count.

An equivalent integer form avoids probability notation. Let

$$
P_A=\prod_{p\in A}p,\qquad
N_A=\prod_{p\in A}p(e_p+1)
-\prod_{p\in A}\bigl(p(e_p+1)-e_p\bigr).
$$

Then the number of incidences between divisor choices and matching root
assignments is tau_O N_S N_T, and pointwise capacity gives

$$
\tau_O N_S N_T\le5(|S|+|T|)P_SP_T.
\tag{RA2}
$$

For a fixed divisor, any literal root can be sent to zero by a
permutation of that coordinate's residue alphabet. The permutation may
depend on the divisor: it is a bijection on each fixed-divisor fiber.
This explains why the count is independent of the literal phases
without postulating independent phases for different originals.

## The cost comparison does not require a distinguished factor

The same fan capacity holds for actual labels $3^h m_i$, without a
common extra factor q. Keep the same global two-stage minimum, absent
next ternary level, one literal old word and disjoint prime-tag sides.
Write K for the selected count, V for the number of distinct used tags,
U for their sum, P for the sum of the two tag values over all owners,
and M for the sum of the cofactors. Thus repeated tags contribute once
to U but once per occurrence to P.

Every tag is an odd prime distinct from three, so in particular it is
at least three. For each owner, its two distinct prime tags p,t divide
its cofactor, hence $pt\le m_i$. The identity
$(p-3)(t-3)\ge0$ gives $3(p+t)\le m_i+9$. Summing, and then applying
the standard nonnegative image-sum inequality to the weights p-3 on
each side, gives

$$
3P\le M+9K,\qquad U+6K\le P+3V.
$$

Consequently

$$
M+9V\ge3U+9K.
$$

If K>V, the integer gap gives $M\ge3U+9>3(1+U)$. The fan uses V+1
fresh labels and has modulus sum $3^{h+1}(1+U)$, strictly below the
deleted sum $3^hM$. The existing fan-cover and replacement-descent
results apply, giving K<=V. No special exception for the pair 5,7 is
needed. This is a stronger application of the existing replacement
interface and standard weighted finite sums, not a new standalone
formalization module.

Suppose in addition that q does not divide m. The actual inventories
$9d$ and $9qd$, for every d dividing m, are disjoint. Apply the no-q
capacity to their combined selected originals. The pure-9 original
at d=1 is not in the five safe old words, but has no tested prime on
either side and contributes zero. Every contributing original is
strictly above nine and belongs to the same safe-word set. Root
averaging therefore gives the stronger necessary condition

$$
\boxed{2\tau_O R_SR_T\le5(|S|+|T|).}
\tag{RA5}
$$

This keeps both inventories from the same actual cover. It does not
multiply independent probabilities assigned to their literal phases.
The support-fourteen conclusion below already follows from RA1;
RA5 does not by itself establish support thirteen.

## Fifteen distinct cofactor primes violate the full-cut estimate

In the PC34 branch, all cofactor primes belong to the fixed set of 27
primes from 5 through 109. Suppose an actual top cofactor contains at
least fifteen distinct primes. Its squarefree fifteen-prime divisor
also supplies an actual top original, so apply RA1 to that divisor.

The largest possible fifteen primes, in increasing order, are

$$
47,53,59,61,67,71,73,79,83,89,97,101,103,107,109.
$$

Split these into

$$
S_* = \{47,53,67,71,83,103,107\},\qquad
T_* = \{59,61,73,79,89,97,101,109\}.
$$

For squarefree exponents the exact response product is

$$
R_{S_*}R_{T_*}
=\frac{8572171203359176348359451}
       {108602335810327006314827}
>75=5(7+8).
\tag{RA3}
$$

Any other fifteen-element subset, in increasing order, is coordinatewise
no larger than this largest subset. Assign its positions to the same
seven and eight positions used above. Decreasing any prime increases
the corresponding response: each factor 2-1/p decreases while 2 to the
side's cardinality is fixed. Both responses are nonnegative. Thus RA3
holds with at least the same left side for every permitted fifteen-prime
choice. It contradicts RA1. Under these branch hypotheses,

$$
\boxed{\omega(m)\le14\quad\text{for every actual top cofactor }m.}
\tag{RA4}
$$

This does not give omega(W)<=14: different actual cofactors may use
different supports. Nor does it give Omega(m)<=14. The previously
checked exponent relaxation m=7^13 times 11^12 still passes RA1:

$$
R_{\{7\}}R_{\{11\}}=\frac{13}{7}\frac{12}{11}
=\frac{156}{77}<10.
$$

Its total prime multiplicity is 25. All its divisor profiles pass too,
by monotonicity in the exponents. This is a numerical relaxation only;
no actual covering system or simultaneous phase realization is supplied.

## Verification boundary

The selected-prime capacity is the whole-class arithmetic theorem
`PrimeCutOwnerCapacity.selected_prime_cut_card_le`. Its single-class
replacement application has been compiled for arbitrary nonunit
divisors, including an injective embedding of a divisor inventory into
the original labels. A separate exact application obtains private
points from the existing cardinality-minimality theorem and derives
the common five-element set from the two actual pure guards.

Finite product counting has been compiled for arbitrary finite index
types, exponent caps and literal phases depending on all exponent
choices and an arbitrary outside index. It yields RA2 from pointwise
capacity, retaining the outside cardinality. The numerical RA3 and
the two-axis control are exact rational Lean checks. Sorted-subset
domination and response monotonicity also have generic Lean checks.
These reuse existing finite-set, finite-product and order results;
their applications are not new standalone formalization modules.

A composed exact Lean application now proves RA4 from one actual
9qm original with q>=7, global count-then-sum minimality, absence of every
27-divisible original, and inclusion of the tested prime divisors in
the displayed 27-prime pool. It constructs the divisor monomials using
Mathlib factorization injectivity and divisibility, obtains the actual
slots and common safe words, and supplies the capacity premise to the
support-fourteen consumer. No abstract capacity or cofactor encoding
is assumed in that final application. Its build exits zero without
warnings; all checked axiom closures are contained in the standard
three. Taking the tested set to be the full prime support gives RA4
under the stated pool assumption.

The stronger no-q application also compiles from one actual 9M
original to the complete three-set prime-power inventory bound:
all tested and outside primes are supplied explicitly, their sets
are pairwise disjoint, and each exponent cap is bounded by the
factorization of M. The monomial construction supplies every
inventory interface, including its outside cardinality. This closes
the actual-source bridge for the full outside factor in RA1.

A further exact application takes a prime q outside the cofactor
support and one q exponent in that outside set. It yields the
factor-two normalized capacity of RA5 directly from the actual
9qm original; in particular this covers the stated q=113 branch.
The more general q-not-dividing-m inventory argument above does
not require q to be prime, but that generalization is not claimed
as the compiled prime-q specialization. Pure nine contributes zero
throughout the selected-count proof. These applications reuse
existing results and stay transient, rather than introducing
standalone binding modules. None supplies an integral prefix repair
or settles unrestricted Erdős #7.
