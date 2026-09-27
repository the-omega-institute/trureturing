# A sharp phase-block deficit at a fixed pure boundary

For the actual pure-prime construction of
[report503](503-integer-selectors-strengthen-capped-budgets-but-axis-limits-survive.md),
with both pure heights at least two, a specified block of18 original mixed
moduli has independent weighted capacity382/667 but maximum simultaneous
weighted deletion exactly

    373/667.                                             (B1)

The deficit9/667 is uniform in those pure heights. One static residue per
complete numerical modulus attains B1, simultaneously at all three tested
old points. A continuous capacity model that retains the old selectors but
only measures total pure-survivor area still permits376/667. The missing
constraint is the distribution of that area among first-level phase cells.

This is conditional on a specified actual pure boundary. It supplies no
uniform discount for arbitrary pure phases: report508 already constructs
pure boundaries with no positive uniform mixed-inventory rebate. It also
does not improve the retained global source-support bound or settle
unrestricted Erdős#7. The proof here is ordinary mathematics with exact
arithmetic checks, not a new Lean verification.

## One original family and its pure boundary

Use report503's51 old numerical labels D, primes3,5,7,11,13,17,19,
two common old centres and three simultaneous old points. The profiles are

    (4,2,-4,1,2,1,1),
    (5,-2,4,1,1,1,1),
    (-5,-3,-2,1,1,1,1),

and the weights are w=(17,16,13). The new primes are23 and29. Every
complete modulus d*23^j*29^k has one old selector, A or B, and one phase
pair, shared across the tested old points. No additional old residues or
prime directions are included in this interface.

Fix the pure selectors and nonzero digits from report503. For each d,
include the prescribed class d*23^j for1<=j<=J and d*29^k for1<=k<=K,
where J,K>=2. A pure p^h phase is c_d*p^(h-1), with the same selected old
residue and nonzero digit c_d at every height. Denote the remaining product
sets in the three full uniform new-coordinate fibres by S_i^0.

At old point2, the23-axis uses digits1,...,21, and the29-axis uses
digits1,...,13. The first-level cells that survive completely are therefore

    {22} times {14,...,28},                              (B2)

exactly15 cells, each of Haar mass1/667. For a nonzero first digit, all
higher pure cylinders have first digit zero, so that digit is either
completely allowed or completely deleted. Within the zero first digit of
a p-axis using n distinct digits, the conditional deleted fraction is

    n/(p-1) * (1-p^(1-H)),                              (B3)

where H is that axis's pure cutoff. This follows by summing the disjoint
valuation layers2,...,H, conditional on the first digit being zero.

Consequently every first-level cell outside B2 has relative survivor
fraction at most1-epsilon, where

    epsilon=min(21/22*(1-23^(1-J)),
                13/28*(1-29^(1-K))) >=13/29.             (B4)

The consumer also checks B3 directly at height two on all529 and841
one-axis residues. The all-height statement is the geometric-sum proof.

## The eighteen labels and the unavoidable loss

The block consists of the complete mixed moduli667*d for

    d=1,3,5,9,21,27,63,81,147,189,441,567,
      1029,1323,3087,3969,9261,27783.                    (B5)

For each d let M_d be the maximum of w dot A_d and w dot B_d. These18
labels are exactly the labels in D for which every maximizing selector
activates old point2. Their capacities sum to

    sum_d M_d=382.                                      (B6)

Every nonmaximizing selector loses at least3 in this score. The labels
21,63,81,189,567 have alternatives010 and001, with scores16 and13;
they attain the least positive loss3. The d=1 selectors both have mask111
and score46, so neither offers a way to deactivate point2 at zero loss.

For any choice of one selector and one first-level phase pair per block
label, let c be the number of nonmaximizing selectors and n the number of
labels activating point2. Then

    selector loss >=3c,       n>=18-c.                  (B7)

At point2, suppose r different full cells from B2 are occupied. There are
at most min(n,15) such cells. The remaining labels occupy at most n-r
additional cells, each having relative survivor fraction at most1-epsilon.
Repeated phases only decrease the union. Thus its relative area is at most

    r+(1-epsilon)*(n-r)
      <= n-epsilon*(n-15)_+.                            (B8)

Compared with the sum of the chosen labels' full-cell capacities, their
union has weighted loss at least16*epsilon*(n-15)_+/667 at point2 alone.
All other losses are nonnegative. Combining B7 and B8, total loss from B6
is at least

    [3c+16*epsilon*(3-c)_+]/667 >=9/667.                 (B9)

For c>=3 the selector loss suffices; for c<=3 use16*epsilon>=208/29>3.
This proves the upper bound373/667 for all finite J,K>=2, including every
shared phase choice. The argument compares actual unions, not a sum of
separately optimized deletions.

## Simultaneous sharpness with original residues

Take maximizing selectors except for d=21,63,81, which use mask001
instead of010. The resulting activation vector is(4,15,5), with weighted
score373. Assign the five nonsingleton selected labels as follows:

| d | Selected mask | Phase modulo(23,29) |
| ---: | --- | --- |
| 1 | 111 | (22,25) |
| 3 | 110 | (22,22) |
| 5 | 011 | (22,26) |
| 9 | 110 | (22,23) |
| 27 | 110 | (22,24) |

Give d=21,63,81 the respective phases(19,25),(20,25),(21,25). Assign the
remaining ten point2 singleton labels, in increasing numerical order, to

    (22,s), s=14,15,16,17,18,19,20,21,27,28.

Every selected cell survives all pure heights at every point it activates.
At each point, the active block cells are distinct. CRT with the selected
old-centre residue supplies one original residue modulo667*d for every d.
Unique prime factorization makes these moduli distinct from each other
and from every pure modulus. All are odd and greater than one.

The weighted deletion is exactly373/667 for every J,K>=2, proving
sharpness of B1. The consumer constructs all222 original classes at J=K=2,
checks their numerical identities and residues, and checks every relevant
mixed/pure and mixed/mixed congruence incompatibility. The same nonzero
first-cell argument proves the stated all-height compatibility.

## Why total survivor area is insufficient

Instead change just d=21,63 to mask001, retaining maximizing selectors
elsewhere. The activation vector is(4,16,4), with score376. Each coordinate
of the independent full-cell deletion vector(4,16,4)/667 fits inside the
actual total pure-survivor area for every finite J,K>=2. It suffices to
compare with the smaller limiting areas

    (28,15,16)/616.

In particular,

    15/616-16/667=149/410872>0.                          (B10)

Thus a necessary model using only these three total areas and the actual
selector counts permits376/667. B1 rules out any phase realization of
that value. This is a strict separation for this block and this stated
relaxation, not a claim about every earlier joint budget or an improved
whole-family survivor constant.

## Transport to nearby pure boundaries and further mixed labels

Keep the same old points, weights, complete block labels and allowed mixed
options. For arbitrary measurable pure-survivor sets S_i in the same
uniform fibres, put

    delta_plus=sum_i w_i*mu(S_i minus S_i^0).

For each fixed mixed family F, its weighted union deletion changes by at
most delta_plus in the increasing direction. Taking the supremum over
the same allowed F therefore gives

    sup_F sum_i w_i*mu(S_i intersect union F_i)
      <=373/667+delta_plus.                             (B11)

There is no factor18: the expression compares the union once. In
particular, relative to the fixed independent ceiling382/667, the saving
is at least

    max(0,9/667-delta_plus).                            (B12)

This is not a statement about a deficit measured against newly optimized
per-label capacities at S; that would change both terms of the comparison.
More pure deletions preserve the upper bound by monotonicity, but need not
preserve the sharpness construction.

An omitted block label can be filled with any allowed virtual class for
the purpose of this upper bound. This enlarges its union, and does not
modify the actual family. Consequently the same block upper applies to
subsets, when the comparison budget still includes all18 block capacities.
It is invalid to subtract9/667 from the capacity sum of only the present
labels without separately accounting for the omitted capacities.

For additional mixed labels, apply the ordinary union bound to those
outside B5. The same saving B12 remains in the complete inventory budget;
it does not assert that particular old survivors can never be covered by
later classes. If a mixed rectangular inventory includes all d in D and
1<=j<=H,1<=k<=T, its weighted deletion from S^0 is at most

    892/616*(1-23^(-H))*(1-29^(-T))-9/667, H,T>=1.       (B13)

The original selectors and phases can be arbitrary within that inventory,
and missing labels are allowed because B13 uses the whole comparison
inventory. No mixed class is charged twice.

## The remaining source obligation

Weights(17,16,13) on these three old points are a local test functional.
The calculation gives no lower bound on how much of a completed actual
source has this pure boundary, or a boundary satisfying a useful B12.
Pure-axis totals close to the report503 limits do not by themselves bound
delta_plus; report504 already separates totals from mixed continuation.

To turn the saving into a source or distortion bound, it must be integrated
under the same actual incoming law, with the complementary histories and
the already-deleted pure mass accounted for. A joint three-point saving
does not automatically become a pointwise saving at each old history.
Nor can one subtract a single block saving again at every digit stage.
Those estimates, as well as arbitrary old phases and further prime
directions, remain unresolved here.

## Reproduction

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fixed_pure_phase_block_deficit.py

The standard-library consumer reconstructs the original old CRT masks,
the fixed pure root distributions, all24012 single-label options, B9's
finite selector-count cases and the sharp simultaneous CRT witness. Its
adjacent certificate contains the block and witness; the adjacent result
contains the derived exact counts and fractions. Default execution checks
the retained result. The quantified proofs are B3, B8 and B11, rather
than an extrapolation from a finite sweep.
