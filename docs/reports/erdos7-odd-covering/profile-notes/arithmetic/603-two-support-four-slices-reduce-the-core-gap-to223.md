# Two support-four slices reduce the core gap to223

Two complete support-four slices, containing190 numerical labels,
can be added simultaneously to
[Report598](598-high-support-central-squares-preserve-the-common-survivor-law.md),
with arbitrary globally fixed residues. Together with its800-label
augmentation, this leaves223 excluded central-square labels in the
max-exponent-two first-seven inventory, instead of413.

The enlarged ten-prime family has survivor Haar density greater than
1/1200000. A compatible extension admits arbitrarily many private
branches of Report600 when every outside prime is at least67, with
extendible-head density greater than1/3400000. The intermediate
160-label family has the stronger head bound1/360000 and permits
outside primes from53, with extendible-head density greater than
1/9000000. These are ordinary proofs with exact rational arithmetic,
not a resolution of unrestricted Erdős #7 or new Lean verification.

## The first complete slice:160 one-centre labels

Use P0={3,5,7,11,13,17,19} and V={7,11,13,17,19}. Retain every
original admitted by Report598: all pure powers, mixed P0-originals
with some exponent at least three or both central exponents at most
one, all max-exponent-two central-square labels with at least five
prime divisors, and every original touching23,29 or31.

Additionally admit every numerical label

    m=p^2 product_(q in S)q^e_q,
    p in{3,5}, S subset V, |S|=3, e_q in{1,2}.     (OC1)

There are2*10*8=160 distinct labels. Each may be absent or present
once with any residue. They have support four and a squared central
prime, so all are new relative to Report598. No other original or
query height is truncated.

Equivalently, the first-seven mixed-head condition gains the clause
"support four and exactly one of the first two primes present."
The previous clauses remain in force.

## One restriction pays the entire class

At every resolving height, Report598 supplies one actual submeasure
eta<=rho on P0 with

    eta(1)-c Gamma_Q(eta)>=K598,
    c=1084133/201247200,
    K598=26345885990886052732242307711
         /9055182074115772514304000000000,
    rho<=D H_(P0), D=3458/405.                    (OC2)

Gamma_Q includes the unit query and every numerical divisor query
at that height. Each maximization uses one globally fixed residue
layout. The product-source caps are

    kappa_3(2)=2/9, kappa_5(2)=1/15,
    kappa_q(1)=r_q=1/(q-1),
    kappa_q(2)=a_q=1/[q(q-2)] for q in V.

Let A be the union of all present new originals. Product structure
is used only for rho, before survivor restrictions. The complete
cap sum gives

    delta=eta(A)<=rho(A)<=B160,
    B160=(2/9+1/15)
         sum_(S subset V, |S|=3) product_(q in S)(r_q+a_q)
        =2261681116741/813717439920000.           (OC3)

Every original is charged once on the same source. No independently
attained cap or phasewise maximizing law is substituted for rho.

Set eta'=eta outside A. The unit-query restriction inequality gives

    Gamma_Q(eta')<=Gamma_Q(eta)-delta,
    eta'(1)-c Gamma_Q(eta')
      >=K598-(1-c)delta>=K160,
    K160=K598-(1-c)B160
       =10852138121266998757700791
        /74836215488560103424000000000>0.        (OC4)

This is one actual law restricted by all160 new classes at once.
The earlier800 classes are already avoided by eta; their cost is
included in K598. The23,29,31 continuation is reconstructed on eta'
with the unchanged controls and density multiplier200/33. Therefore

    H_P(U)>=33K160/(200D)
      =10852138121266998757700791
       /3872557174103117660160000000000
      >1/360000.                                (OC5)

Report598's digit-injection averaging transports OC1 and the retained
exponent/support conditions to any ten ordered odd primes. Distinct
numerical labels remain distinct and actual residues are pulled back
together. The result covers arbitrary finite original heights.

## The second complete slice:30 labels with both centres

Also admit every numerical label

    m=3^a 5^b q^2 r^2,
    (a,b) in{(2,1),(1,2),(2,2)}, q<r in V.       (BC1)

These3*10=30 labels have support four and are disjoint from OC1
and the800 labels of Report598. The additional source caps are
kappa_3(1)=2/3 and kappa_5(1)=1/4. Consequently their complete
union has rho-mass at most

    B30=[(2/9)(1/4)+(2/3)(1/15)+(2/9)(1/15)]
        sum_(q<r in V)a_q a_r
       =564029593/5509545166125.

Restrict the same eta' by these additional classes. The total loss
is at most B190=B160+B30, without any independence assumption on
the already restricted law. The resulting gate is

    K190=K598-(1-c)B190=K160-(1-c)B30
        =23005581948964911238467983
         /532657769065633677312000000000>0.     (BC2)

The unchanged continuation gives

    H_P(U)>=33K190/(200D)
      =23005581948964911238467983
       /27563495180381013934080000000000
      >1/1200000.                               (BC3)

All190 new labels may appear simultaneously, each with one arbitrary
fixed residue. This adds to the first-seven condition the clause
"support four, both central primes present with a central square,
and both other prime exponents equal two." The digit-injection
transport above applies to this condition as well.

## Compatible private branches from prime53

Let P be the ten smallest primes occurring in the family. Impose the
160-label head condition OC1, and require every outside prime to be
at least53. Keep exactly Report600's branch decomposition: ordinary
single-parent branches and two-parent entry branches with disjoint
private interiors, no cross-branch originals, and the same allowed
private block trees. A two-parent branch has one entry q and all its
head-touching originals are d q^e, where d>1 uses only its declared
two head parents. Their phases and finite heights remain unrestricted.

Apply [Report601](601-staged-payment-admits-every-two-parent-entry-from37.md)'s
staged-payment proof using K160. For its complete-label fees put

    S35(53)=sum_(q>=53 prime)F_(3,5)(q),
    S323(53)=sum_(q>=53 prime)F_(3,23)(q).

Remove blockers depending only on the first seven head coordinates
from eta' before continuation. Their total source mass is at most
(10/3)S35(53). Reconstruct the three continuation kernels on that
restricted source. Pay the remaining pair blockers afterward on one
Haar restriction, for total loss at most S323(53). Ordinary branches
cost at most

    sum_(q>=53 prime)2^(-(q-1)/2)
      <=sum_(odd n>=53)2^(-(n-1)/2)=2^-25.

Exact substitution yields

    Kbranch=K160-(1-c)(10/3)S35(53)>0,
    H_P(U_ext)>=33Kbranch/(200D)-S323(53)-2^-25
      >1/9000000.                               (OC6)

The certified lower bound for Kbranch is approximately
0.0000227766726509771; the certified final head lower bound is
approximately0.000000118643202908153. The producer uses exact fractions.
Both fee bounds include the inherited analytic infinite-prime tail,
in addition to the148 entry rows53,...,967.

Report601's actual-witness gluing and padded head-only digit transport
apply unchanged: empty pullbacks receive auxiliary cylinders with the
same transformed labels, retaining prime occurrences and branch supports. For Q_off the product of all original prime powers
outside P, including separate components, full survivor density is
greater than1/(9000000 Q_off). The finite number of branches, private
depth and original heights are unbounded.

The threshold53 is part of this160-label corollary. OC4 does not
retain the old budget needed for Report601's entire q>=37 attachment
conclusion; that stronger combination would require another estimate.

## All190 labels with private branches from prime67

Keep the same private branch conditions, add BC1, and require every
outside prime to be at least67. The same staged proof now gives

    Kbranch190=K190-(1-c)(10/3)S35(67)>0,
    H_P(U_ext)>=33Kbranch190/(200D)-S323(67)-2^-32
      >1/3400000.                               (BC4)

The producer sums the145 entry rows67,...,967 and the same certified
analytic tail. It obtains a gate lower bound approximately
0.0000171728264516 and an extendible-head lower bound approximately
0.000000299234032795. These are exact-rational lower bounds derived
from upper bounds on the two infinite fee series, not evaluations
of their exact infinite sums. The ordinary fee uses

    sum_(q>=67 prime)2^(-(q-1)/2)
      <=sum_(odd n>=67)2^(-(n-1)/2)=2^-32.

Full survivor density is greater than1/(3400000 Q_off). Private
depth, the number of branches and all original heights remain
arbitrary and finite. This corollary does not assert the190-label
extension for outside primes53,...,61 or for general cross-branch
constraints.

## Remaining inventory and exact verification

The previous413 excluded first-seven labels split into160 OC1 labels,
30 BC1 labels, and the following223 remaining labels:

|Support size|Remaining labels|
|---:|---:|
|2|23|
|3|110|
|4|90|

Every remaining support-four label contains both central primes;
at least one of its other two prime exponents is one. These counts
concern the finite max-exponent-two central inventory, not every
unresolved configuration or unrestricted support family.

The [producer](../../frontier/cover-geometry/central_support_four_augmentation.py)
and [data](../../frontier/cover-geometry/central_support_four_augmentation.json)
enumerate both complete slices and compare independent descriptions.
They check the190 literal identities, disjointness from the old800,
the complete223-label remainder, both cap polynomials, source
fingerprints, both head bounds and both through-infinity branch
corollaries. All221 named checks pass with optimization enabled.
The intermediate160-label result is retained separately in the data.
No previous head scan is repeated.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/central_support_four_augmentation.py

The arbitrary-residue and arbitrary-height conclusions follow from
the same-source restrictions and continuation proof. The finite
program does not enumerate all original residue choices.

[Report604](604-fixed-pair-activation-admits-ten-central-square-stars.md)
uses fixed central phases and an actual pair-activation query grid to
admit further central-square stars. Its four stronger patterns also
admit the160-label OC1 slice and separated branches from37. Those
phase restrictions are essential; this does not reduce the223-label
phase-unrestricted remainder above.
