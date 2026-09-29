# One eleven-label phase inventory cannot realize independent bad rows

Let C={3,5,7,9,15,21,35,45,63,105,315}, the eleven nonunit divisors of 315.
For a fixed outside prime q, each actual shallow original c*q supplies
one head phase a_c mod c. Missing labels contribute nothing. On head
residues u mod 315 define

    n_q(u)=number of present c in C withu=a_c mod c.

This counts active original labels, not distinct forbiddenq roots.
The number of distinct pure-liveq roots blocked at u is at mostn_q(u).
All phases a_c come from the SAME original family. No assumption that
a hypothetical cover exists, or that every leaf is bad, is used.

## Two-row capacity and the full three-row exclusion

For distinct u,v, a single cofactor label can be active at both only
ifc dividesu-v. Every other label contributes at most one to the two
row counts. Hence

    n_q(u)+n_q(v)
       <=11+#{c in C:c dividesu-v}
       <=18.                                         (HI1)

For a nonzero difference mod 315 the largest proper gcd is a divisor
of 315. The maximum cofactor count is 7, attained only when gcd=105,
i.e. u-v=105 or 210 mod315. Consequently:

- at most one row can have n_q>=10;
- if one row has n_q>=10, every other row has n_q<=8;
- if two rows have n_q>=9, both counts equal 9 and their difference
  is 105 or 210.

The last statement alone would still allow all three rows in one
105-fiber. To exclude that possibility, suppose u,u+105,u+210 all have
count>=9. Of the eleven cofactor slots, the seven dividing 105 can each
hit all three rows, so contribute at most 21 total incidences. The four
remaining slots 9,45,63,315 contain 3^2. Each can hit at most one of those
three rows, because the three residues are distinct modulo 9. They
contribute at most 4. Thus the total incidence count is at most 25,
whereas three rows each>=9 would require at least 27. Contradiction.
Therefore

    #{u:n_q(u)>=10}<=1,
    #{u:n_q(u)>=9}<=2.                               (HI2)

These are global consequences of the once-only original phase inventory.
They remain valid after restriction to any actual 75/85-cell head mask,
and when some originals are missing.

The bounds are sharp even on both displayed actual head masks. Setting
all eleven head phases to 4 gives n(4)=11; assigning all ten nonzero 11
roots across those labels kills the pure-live 11 fiber exactly there.
For the two-row example, set the seven low ternary-height slots to 4,
set the 9/45 slots to 4, and set the 63/315 slots to 214. Then n(4)=n(214)=9.
The common seven slots use 11 roots 1,...,7; the two high slots on each
row use roots 8,9. These are one actual set of eleven completec*11 CRT
phases, not an independently specified row table. Both 4 and 214 survive
each of the actual eleven-class heads. The exact phase lists are in
the diagnostic output.

## Consequences for one common source

Work with the fixed base law conditioned only on avoiding the pure
root 0 mod q. Itsq-1 nonzero first roots are uniform; all higher originals
are still to be paid by the established complete-height debit. Let
m_q(u) be its mass after the actual SHALLOW singleton-outside originals.
Then

    m_q(u)>=max(0,1-n_q(u)/(q-1)).                    (HI3)

In particular a completely empty shallow 11 fiber can occur on at most
one head row, and for q>=13 no such fiber can be empty: eleven labels
cannot delete all q-1 live roots. This statement concerns the declared
first-digit layer, not deletion by arbitrary higher original powers.

Given ANY nonnegative common head measure h, let its largest two atom
masses be h_(1)>=h_(2), setting h_(2)=0 if needed. The actual bad sets obey

    h{n_q>=10}<=h_(1),
    h{n_q>=9}<=h_(1)+h_(2).                         (HI4)

For the current base head weights w_l/24, every atom has mass at most
1/96. The same is true after multiplication by one 0<=f<=1, by 0<=Z<=1,
or by any 0<=H_T<=1. Thus the respective bad-row source costs are at most
1/96 and 1/48, simultaneously on that SAME chosen source.

For a concrete common restriction, discard the UNION of rows satisfying

    n11>=9 or n13>=10 or n17>=9 or n19>=10.

HI2 bounds this union by 2+1+2+1=6 rows. Restrict one source by that one
actual union, costing at most 6/96=1/16 of the base head measure. On
every retained row its four unary masses satisfy

    (m11,m13,m17,m19)>=(1/5,1/4,1/2,1/2).             (HI5)

One commonf is restricted; no different good row is chosen separately
for different queries or primes. HI5 is a correct but coarse lower
box. No claim is made that this box and loss 1/16 suffice for the final
positive gate; the current missing uniform positivity is not solved.

## Weighted joint moment and capacity interfaces

A fuller invariant avoids discarding all the finite common inventory.
For any set of head rowsS,

    sum_(u inS)n_q(u)
       <=sum_(c in C) max_(a mod c)|S intersect[a]_c|.   (HI6)

The right side is the exact total capacity of eleven one-phase slots
on that row set. HI1 and the 25-incidence three-row exclusion are its
smallest useful instances. For arbitrary nonnegative h the weighted
version is

    sum_u h(u)n_q(u)
       <=sum_(c in C) max_(a mod c) sum_(u=a mod c)h(u).  (HI7)

Each side concerns the sameh and actual original phase family. The
maxima give an upper bound, not a claim that every separate maximizing
phase realizes some different source.

More generally, for r>=1, expand the binomial moment over subsets of
DISTINCT original cofactor slots. Their common head condition is empty
or one cylinder at the lcm of those slots. Hence

    sum_u h(u) binom(n_q(u),r)
       <=sum_(J subsetC,|J|=r)
            max_(a mod lcmJ) sum_(u=a mod lcmJ)h(u).  (HI8)

The 2047 nonempty subsets can be collected into exact integer
coefficients indexed by(r,lcmJ). This gives one finite joint-moment
interface and preserves the original inventory. Its second-moment
expansion alone is a separate-cylinder bound; it is not claimed to
improve the known quadratic envelope without further joint information.

HI2 additionally yields, for this SAME h,

    sum_u h(u)n_q(u)^2
       <=8 sum_u h(u)n_q(u)+33 max_u h(u).            (HI9)

If a row has count>=10, it is the only row above 8 and its excess
n(n-8) is at most 33. Otherwise only at most two rows have count 9,
whose combined excess is at most 18 maxh<=33 maxh. All remaining
excesses are nonpositive. This proves HI 9 without a distributional
independence assumption. Its usefulness compared with existing moment
bounds must be checked on the intended source; it is not an automatic
strict improvement.

The finite checker [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_inventory.py) and its [result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_inventory.json) verifies all
314 nonzero differences, all 105 relevant three-row fibers, the complete
subset/lcm coefficient table, and explicit actual c*11 phase families
attaining the high-row bounds on both concrete heads. The proof is
ordinary finite arithmetic and combinatorics, not new Lean verification.


The two literal heads are specified in
[Report 720](720-weighted-distortion-bridge-and-all-parameter-cylinder-envelope-obstruction.md).
This inventory bound does not require either head or a hypothetical cover;
those heads provide actual sharpness examples.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_inventory.py
```
