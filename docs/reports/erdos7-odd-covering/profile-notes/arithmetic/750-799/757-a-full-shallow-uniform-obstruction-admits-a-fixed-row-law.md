# A full shallow uniform-source obstruction admits one fixed row law

There is an actual family filling all383 nonunit shallow numerical slots
on Q=315*11*13*17*19*23 for which the UNIFORM measure on its entire
actual survivor set has negative higher-core functional J. The same
fixed phases admit one explicit nonnegative row-weighted source with

    Haar(higher-core survivors)>=459911/134980560>1/294.

The phases, numerical labels and common carrier are unchanged between
these two statements. This refutes universal positivity for the uniform
source while supplying a positive source on this actual family. It does
not settle arbitrary shallow phases, exclude any family of reweighted
sources, or give a covering counterexample. All mathematics and finite
certificates here are ordinary results, not Lean verification.

## One literal full-slot family

The [literal input](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_uniform_failure_reweight_input.json)
contains all383 numerical(modulus,phase) pairs, a fixed forest and75
explicit core-row integer weights. For every d|315 and every outside
subset J, except the unit(empty) slot, there is exactly one actual class
modulo d*product_(p in J)p. No original phase is chosen separately for
a query or a different part of the proof.

The common core originals are

    (3,0),(5,0),(7,0),(9,4),(15,11),(21,8),
    (35,9),(45,1),(63,1),(105,59),(315,179).

Their old315 survivor set has75 points. The five pure outside classes
are0 mod p. There are55 other singleton-outside classes and312 classes
with at least two outside coordinates. Every live root at each outside
prime occurs among the literal phases. Let A be the complement of all
383 actual classes in Z/QZ. Direct numerical sieving gives

    |A|=27336206,    Q=334639305.

## Sixty fixed query cylinders refute the uniform-source proposal

For the counting measure F=1_A, use the saturated coefficient and
same-source functional from [Report752](752-joint-deletion-credit-distinguishes-equal-marginal-sources.md):

    kappa(d)=product_(p saturated in d)p/(p-1)-1,
    R(F)=sum_(d,J)kappa(d) max_(a,t)F(C_(d,J,a,t)),
    J(F)=mass(F)-R(F).

Saturation means9|d for3,5|d for5, and7|d for7. Choose the following ten
old phases. For each choose the empty outside query and five singleton
outside queries at root1, giving60 fixed cylinders.

|d|fixed old phase|48 kappa(d)|
|---:|---:|---:|
|5|2|12|
|7|5|8|
|9|7|24|
|15|2|12|
|21|5|8|
|35|2|22|
|45|7|42|
|63|25|36|
|105|2|22|
|315|2|57|

Their exact masses, with the listed coefficients, give

    48*selected empty-support debit=1003836400,
    48*selected singleton-support debit=381077191,
    48*mass(F)=1312137888.

Every query maximum is at least its selected fixed-phase mass, and
all omitted terms have nonnegative coefficients. Therefore

    48J(F)<=1312137888-1003836400-381077191
           =-72775703<0.

The certificate requires no maximization or solver. It applies to the
ENTIRE actual shallow survivor set; no artificial prior or omitted
survivor is responsible for the failure. A separate full joint tensor
calculation and numerical divisor-fold calculation reproduce the fixed
cylinder result and confirm negativity using all320 maxima.

## One fixed source repairs the same family

Let F0 assign weight w_x to EVERY point in the actual core-and-singleton
survivor fibre above x mod315. The75 weights are the explicit[x,w_x]
pairs in the shared literal input. Sixty are positive, all are integers
between0 and105. For example,

    w_2=43, w_16=28, w_17=35, w_19=48, w_23=95.

Restrict F0 by all312 actual multioutside classes to obtain F_w. Thus
F_w assigns w_x to every actual shallow survivor above x. It is one
supported source fixed before all free queries and future higher-core
operations. Its zero rows are permitted source selection; they do not
change the actual arithmetic family.

The [compact intersection argument](756-actual-joint-intersections-certify-a-full-shallow-family.md)
applies with these same weights in every term. Write A_p(x) for the
actual singleton-allowed roots. Initial row masses are

    w_x product_p |A_p(x)|.

For each queried outside subset J, a cylinder mass is

    sum_(x=a mod d) w_x product_(p notin J)|A_p(x)|
                         product_(p in J)1_(t_p in A_p(x)).

Common unused roots on the SINGLETON source at13,17,19,23 are verified
from the literal phases. All old phases and the11 roots are then
exhausted to calculate320 initial maxima. This shortcut is never
asserted on the source after multioutside deletion.

All48,516 original-event pairs are checked using actual CRT
compatibility and these same row weights. The fixed289-edge forest is
acyclic and gives an upper bound for the removed mass. Bonferroni gives
a lower bound for removal at each old row, hence an upper bound for each
post-deletion old-only cylinder. Maximizing over all old phases after
the bound permits the maximizing phase to change. Other cylinder
maxima can only decrease under restriction.

The resulting exact quantities are:

|Quantity on this one weighted source|Value|
|---|---:|
|Initial singleton mass|1000913915|
|48 times initial debit|35993100928|
|48 times initial margin|12050766992|
|Sum of312 event masses|222733700|
|Forest intersection saving|11017863|
|Upper bound for removed mass|211715837|
|48 times certified old-query credit|3858181129|
|Final source mass lower bound|789198078|
|48 times final debit upper bound|32134919799|
|48 times final margin lower bound|5746587945|

Indeed48*789198078-32134919799=5746587945. The weighted bare union
bound already gives48J>=1359549392>0. The forest raises this to1888406816,
and the old-query credit gives the final reserve. The changed source law
is therefore the essential repair here; overlap and credit improve it.
A tighter lower estimate for the old negative uniform J cannot change
that uniform source's sign.

## Haar domination and higher-core quantifiers

The weighted source satisfies F_w<=105*Q*Haar. Extend it uniformly in
all additional3/5/7 digits. For any finite further family of distinct
numerical originals with at least one core exponent above(2,1,1), no
other primes, and outside exponents at most1, the complete saturated
geometric tails bound the actual deleted mass by R(F_w). Each new phase
may be arbitrary but is fixed once globally. All383 shallow phases
remain as in the literal input.

The paired lower bound is therefore

    5746587945/(48*105*334639305)
      =459911/134980560>1/294.

The maximum source weight105 is part of the Haar cost and cannot be
omitted. No retention, query or domination term uses a different law.

## Exact reproduction and independent comparison

The [consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_uniform_failure_reweight.py)
reads the one literal input above. Its [native negative checker](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_uniform_failure_sieve.cpp)
sieves all334,639,305 numerical residues and evaluates only the60 fixed
cylinders. Its positive check reuses the pinned evaluator from Report756,
reconstructing every actual singleton row, initial cap, pair intersection,
forest edge and phase-credit bound with the declared75 weights. It reads
no optimized value, final tensor, or precomputed final cap. Both components
are compared against the [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_uniform_failure_reweight.json).

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_uniform_failure_reweight.py
```

An independent generalized-CRT implementation reproduces all pair
intersections,320 initial maxima and10 credit slots. Separately, an actual
joint tensor and a direct numerical weighted sieve reproduce all320 final
caps for these SAME weights; each respects the compact upper bound.
These independent calculations validate the supported-source interpretation
without becoming premises of the compact certificate. All native checks
use undefined-behavior instrumentation. No optimality is claimed.

The remaining uniform question is whether every actual shallow phase
family admits a positive supported law, and which source representation
suffices to construct one. This result proves neither that old-row
weights always suffice nor that a fixed forest/Bonferroni estimate is
complete. Failure of that estimate would not exclude other joint laws
or prove an actual covering.
