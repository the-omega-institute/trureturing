# Eleven through fourteen-prime heads admit an unrestricted larger tail

Let C be a finite family of pairwise-distinct odd numerical moduli greater
than one, with one fixed residue per modulus. Assume at least one of
3,5,7,11 is absent from the prime support of the ENTIRE original LCM.
Each row below is a sufficient noncoverage condition:

| Maximum number of support primes at most B | B | Strict final distorted mass lower bound |
|---|---:|---:|
|11|5000|1/200|
|12|10000|1/200|
|13|20000|1/600|
|14|50000|1/7000|

The original phases, finite prime-power heights, support arities and
finite number of prime divisors above B are unrestricted. In particular,
any such family supported on at most fourteen primes is noncovering.
Equivalently, a putative odd distinct cover on at most fourteen primes
must contain all of3,5,7,11. This leaves the all-four-small-primes case
and unrestricted Erdős #7 unresolved.

These are ordinary mathematical deductions with exact rational arithmetic,
not new Lean verification or a literature-priority claim. The displayed
mass is that of a constructed distorted submeasure, not a claimed final
Haar density. No optimal cutoff or optimal clipping schedule is asserted.

## The two sources and one preserved query interface

For the first three rows use the original eight-prime source from
[763](763-a-joint-query-head-admits-an-unrestricted-prime-tail-above-1400.md)
and the half-clipped stop-loss extensions of
[771](771-stop-loss-profiles-preserve-the-ordinary-source-through-thirteen-primes.md).
At reference primes31,37,41,43,47 the same actual law successively keeps
its complete increasing-convex query comparison. Its head bounds at
sizes11,12,13 are denoted(m_k,G_k): the lower surviving mass and upper
complete-query second moment both come from that same source.

For the fourteen-prime row start instead with
[770](770-an-eight-prime-source-with-threshold-six-at-seventeen.md), whose
source threshold at17 is6. Its uniform mass and conditional caps are

    m*=89120862071/1350000000000,
    (C7,C13,C17,C19,C23,C29)=(3/2,3/2,8/5,9/5,11/7,7/4).

All32 ordinary source ledgers are recomputed for this schedule, including
the altered later multiplier distributions. The original C17=4/3 source
mass must not be mixed with this new cap list or conversely.

Apply771's full comparison proof to the new source representation:
its anchor is still contained in the product of pure3 and pure5 survivors
of masses1/2 and3/4. Only the cap17 factor of Pi0 changes, from4/3 to8/5.
Its initial second moment is the matching770 value214960187/8257536.

For q=(31,37,41,43,47,53), choose rational clipping parameters

    delta=(2/5,11/25,23/50,14/25,13/25,31/50).           (1)

All have0<delta<1 and C_delta=1/(1-delta)<=q. The general normalized
kernel and hinge loss are proved for this domain in771; the last three
parameters exceeding1/2 do not rely on a restricted half-clipping statement.
With S_i the stop-loss profile before step i, update

    m_(i+1)=m_i-S_i(delta_i(q_i-1))/[(1-delta_i)(q_i-1)],
    Pi_(i+1)=Pi_i times pi_cap(q_i,1/(1-delta_i)),
    G_(i+1)=G_i*[1+(3q_i-1)/((1-delta_i)(q_i-1)^2)].    (2)

The physical law uses a normalized kernel then actual restriction at
each head step. It is not renormalized after restriction. The complete
nonnegative query comparison survives that restriction. Different
current-exponent old layouts are combined by Jensen, as in771, not
silently replaced by one common old phase dictionary.

The exact head computation has these decimal displays:

| Reference q | Exact threshold delta(q-1) | Remaining distorted mass lower bound |
|---|---:|---:|
|31|12|0.051247992664|
|37|396/25|0.040354300115|
|41|92/5|0.030324579616|
|43|588/25|0.020657173374|
|47|598/25|0.011156294231|
|53|806/25|0.002939456938|

Every row is strictly positive. The final moment bound is exactly

    G14=581358550517953697459294131
        /9494413326475842331607040.                    (3)

The consumer retains the full rational hinge values and m14. For each
rational threshold T it uses the finite small-product identity

    S(T)=integral M dPi-T*mass(Pi)
           +sum_(integer m<T)(T-m)Pi(M=m),

with complete infinite first moments. Thus the table has no hidden
cutoff in original exponents. It does not depend on the exploratory
numerical choice procedure for(1).

## Put every small original prime inside the actual head

For a row(k,B), collect all actual support primes at most B. Pad this
head to exactly k with unused odd primes at most B, excluding a chosen
missing q* from{3,5,7,11}. The first k+1 odd primes already supply enough
choices. Artificial coordinates have positive finite heights and no
new original forbidden classes.

The ordered padded head dominates the first k entries of

    (3,5,7,13,17,19,23,29,31,37,41,43,47,53).

Source prime-injection averaging transports the relevant eight-prime
source and its entire convex comparison together. At each new actual
prime q above its reference, the fixed-cap auxiliary tails C/q^e
decrease, while the clipping threshold and loss denominator increase.
The reference recurrence(2) therefore bounds the actual continuation.

Keep complete finite old heights resolving every original, including
old exponents in classes also touching future primes. Assign each
original class to its largest exposed coordinate. Distinct numerical
labels give at most one old query per divisor at each new-prime depth;
pure powers are the unit old cofactors. All global phases remain fixed.

The head law now avoids every head-only original. All remaining primes
are greater than B. If11 occurs while q* is another small prime,11 is
inside the actual head; it is never treated as a large tail coordinate.
A final avoiding point on padded coordinates projects to an original
avoiding point.

## Pay the complete larger-prime tail on this same law

Reuse the quarter-clipped tail continuation from
[766](766-nine-and-ten-prime-heads-with-a-missing-small-prime.md) and its
analytic prime-product premise inherited from763. For B>=286,
ell>=4 and3^ell<=B, define

    tau4(B,ell)=1/B * [(2ell^2+1)/(2ell^2-1)]^4
                     * [B/(B-1)]^2
                     * sum_(h=0..4) 4!/[(4-h)!ell^h].   (4)

The total tail loss is at most(4/3)G_k tau4(B,ell). This accounts for
every actual larger prime and every finite height and old cofactor.
Its decreasing integral majorant sums over all primes above B, so
the original finite tail need not satisfy an additional cardinality bound.
The denominator is the full-coordinate B-1 appearing in the inherited
theorem; it is not replaced by a first-digit or support-only coefficient.

One may retain the tail bad sets until a final union deletion: every
later normalized kernel preserves the earlier joint marginal and hence
the earlier bad-set mass. This starts from the ALREADY RESTRICTED head
law of(2), with its paired(m_k,G_k). Its final lower mass is

    m_k-(4/3)G_k tau4(B,ell).                          (5)

The exact checks use(k,B,ell)=(11,5000,7),(12,10000,8),
(13,20000,9),(14,50000,9). The respective values of(5) are approximately

    0.00582363816054,
    0.00624362921369,
    0.00199762388713,
    0.000144494425992,

and are strictly greater than the rational lower bounds in the initial
table. In particular the final measure has positive mass outside all
original classes. Since the complete original CRT carrier is finite,
an avoiding point gives an avoiding integer.

## Exact checking and unresolved scope

The [consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fourteen_head_tail.py)
pins and freshly invokes both770 and771 suppliers and matches their
retained results. It reconstructs the new comparator, all six exact
steps at(1), all small-product atoms, complete first/second moments,
and all four tail charges. The
[retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fourteen_head_tail.json)
must match a fresh complete computation. The inherited ordinary source
geometry and analytic prime-product theorem remain explicit proof
premises, not conclusions of this arithmetic checker. Python -O is
rejected by the inherited771 source route.

An independent divisor-sum convolution reproduced every new finite
product atom, all six exact hinge losses, the full second moment(3),
and the fourteen-head tail margin. It also checked the legal cap
conditions for the parameters exceeding1/2. No original-family search
or finite-height test is used to claim the quantified theorem.

The all-four-small-primes source remains the main excluded case.
The tail condition also excludes supports with too many primes at most
the given B. Neither restriction can be removed by positivity of one
constructed head law alone. The result supplies larger quantified
noncoverage ranges while retaining the original unrestricted problem.
