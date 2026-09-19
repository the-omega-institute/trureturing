[Index](../marked_head_profile.md) · [Actual HSW input](349-real-odd-cover-private-cylinders-and-transport-obstruction.md)

# Multiple descendants: a fresh-prime budget and a local repair

Allowing several AP descendants per original label changes the obstruction
in [349](349-real-odd-cover-private-cylinders-and-transport-obstruction.md).
Three distinct, vacant moduli suffice to repair its three private cylinders
for q=3. That repair still leaves explicit holes in the actual transformed
input. If descendants instead use only q and genuinely fresh primes,
a separate density bound requires at least 150 fresh primes for q=3,
or 509 for q=5. These are necessary conditions, not covering constructions.

The source throughout is the complete HSW seven-copy-11 cover with auxiliary
closing prime 23, every original power height 1,...,22, and the literal
parameterized family verified in 349. Its original prime support is

    P0 = {3,5,7,11,13,17,19,23}.

The statements concern the same old-q memory map, retaining all old
cofactor coordinates. They neither exclude general odd covers nor restrict
what a different transformation could accomplish. No Lean result is claimed.

## 1. Soundness and the required source region

Put W=111546435. For q=3, the private source cylinders of 1 mod3 occur
on all four old 11-roots; three roots are selected. For q=5, the private
source cylinders of 1 mod5 occur on roots 1,2,3; all four nonpure roots
are selected. In either case there are three private demands over each
point of a common old cofactor cylinder C_q. This cylinder omits the
old 11 and q coordinates and has Haar mass

    H(C_q) = 11q/W = 1/R_q,
    R_3 = 3380195,  R_5 = 2028117.

The old q digit is 1. Under the memory map it becomes the second new
q digit. Thus the complete pullback of the private label is contained in

    B_q = {q,q+1,...,2q-1} modulo q^2.

The root selection and injection may depend on every retained cofactor,
including fresh coordinates. For each fixed old q tail whose first digit
is 1, there are still three required output roots. Therefore the required
output mass conditional on C_q is exactly 3/q^2. Other original labels
cannot cover those selected points if their images are sound for their
actual source labels. Even free covering of all unselected points does
not help this requirement.

For descendants of the private original label, require the entire AP,
including any unselected points, to be contained in that label's pullback.
Every such AP has modulus divisible by q^2. Otherwise its reduction
modulo q^2 would be either all residues or all q residues of one lowest
digit, neither contained in B_q. This is whole-AP soundness; soundness
only at selected points would not imply that divisibility condition.

## 2. Capacity when descendants use only fresh cofactors

Fix a finite set F of genuinely fresh odd primes, disjoint from P0.
Allow arbitrarily many descendants of the private original label,
with arbitrary finite heights and pairwise distinct numerical moduli,
but impose the explicit prime-support restriction

    m = q^h product_(ell in F) ell^e_ell,   h>=2, e_ell>=0.

In particular, these APs cannot impose any old cofactor constraint.
This restriction is essential: the local repair below does use old
cofactors and is outside the present bound.

Conditioning on C_q does not change a descendant's Haar mass 1/m,
since its modulus uses no old cofactor prime. For a finite list D of
these descendants, the union bound gives the exact finite-list estimate

    H(output holes) >= (1/R_q) max(0, 3/q^2 - sum_(m in D) 1/m).

Global modulus distinctness can only make fewer choices available.
Even granting every numerical modulus of the allowed form, a finite
list has strictly smaller mass than the infinite geometric sum

    sum_(m in D) 1/m
      < [1/(q(q-1))] product_(ell in F) ell/(ell-1).

Consequently complete coverage requires the strict inequality

    product_(ell in F) ell/(ell-1) > 3(q-1)/q.

Equality still fails because every actual descendant list is finite.
The thresholds are 2 for q=3 and 12/5 for q=5. Arbitrarily high q
powers, or a single new-prime closing construction within this support
restriction, cannot avoid the bound. In particular, for any single
fresh prime ell>=29 the output holes satisfy

    q=3: H(holes) > 9/189290920,
    q=5: H(holes) > 191/5678727600.

These bounds allow the root choices to depend on the fresh coordinates;
they use the fixed count of three required roots on each old-tail fibre,
not a presumed fixed placement of the missing cylinders.

## 3. Exact minimum fresh-prime counts for this necessary condition

Among sets of a fixed cardinality, the first available primes maximize
the Euler product, since ell/(ell-1) decreases with ell. All fresh odd
primes are at least 29. Exact integer primality checks and rational
products give:

| q | necessary product threshold | first possible cardinality | maximizing initial set |
|---:|---:|---:|---|
| 3 | greater than 2 | 150 | the 150 primes from 29 through 937 |
| 5 | greater than 12/5 | 509 | the 509 primes from 29 through 3709 |

For q=3, the 149-prime product is between
1.999654762330740981 and 1.999654762330740982, while the 150-prime
product is between 2.001791145623829379 and 2.001791145623829380.
For q=5, the corresponding 508-prime product is between
2.399594635785381338 and 2.399594635785381339, and the 509-prime
product is between 2.400241775654794872 and 2.400241775654794873.
These are outward rational brackets, not floating-point decisions.

Reaching either cardinality does not certify adequate mass for an
arbitrary prime set, nor simultaneous coverage, nor compatibility with
the other original labels. It only stops this particular capacity test
from excluding the maximizing prime set.

## 4. Old-cofactor refinement repairs the previous cylinders locally

Take q=3, select old roots 0,1,2, and send them respectively to new
roots 0,1,2. Let G be the 11-free original labels divisible by 3.
Start with the standard memory images of all selected 11-divisible
labels, together with the unchanged 11-free, 3-free classes; discard G.
This base has distinct numerical moduli. Add these three descendants of
the same literal original class 1 mod3:

| target root | descendant | literal CRT conditions |
|---:|---|---|
| 0 | 507 mod1035 | x=3 mod9, x=2 mod5, x=1 mod23 |
| 1 | 1381 mod1449 | x=4 mod9, x=2 mod7, x=1 mod23 |
| 2 | 1328 mod1989 | x=5 mod9, x=2 mod13, x=2 mod17 |

They are sound on their entire APs. Their moduli are distinct, odd,
and nonunit. They collide with no numerical modulus in the complete
standard transport pool, even before choosing which original images
to retain. For each proposed output modulus n, a collision could only
come from an original G modulus n/3 or an original 11-divisible modulus
11n/3. The six possible original moduli are respectively

    (345,3795), (483,5313), (663,7293).

None belongs to the complete literal HSW family. Moduli involving 23
in that family have only one other prime; no normal source family
contains both 13 and 17. Higher exponents cannot create these numerical
moduli. The unchanged originals are 3-free and cannot collide either.

The original q=3 private cofactor digits were

    x5=x7=x13=x17=2,  x19=x23=1,  old x3=1.

The three APs cover the complete images of all three selected private
cylinders from 349. This is an actual local repair, so those cylinders
alone cannot exclude the enlarged interface allowing multiple
descendants and old-cofactor restrictions.

The augmented base is still not a cover. Change only the old 23 digit
from 1 to 2. On each selected source root the sole original covering
label remains 1 mod3: all power-prime first digits remain nonzero,
all high-height normal labels miss, and all closing labels miss. In
target roots 0 and 1 the new descendants also miss. Two explicit
uncovered output cylinders are

    24906702 mod30421755,
    11385922 mod30421755.

The third descendant does cover the corresponding target-root-2
cylinder. The noncoverage conclusion uses these full AP regions and
the complete original family, not an isolated point test.

## 5. Reproducible scope

The [checker](../frontier/hsw11_descendant_palette.py) uses exact prime
trial division, rational products and CRT. It verifies both sharp
cardinality crossings, the displayed rational brackets, the six absent
source moduli, all three repaired cylinders, and all three shifted
cylinders. It explicitly checks that every tested cylinder modulus is
a multiple of each descendant modulus before using a representative
to decide whole-cylinder membership. Six invalid API inputs are rejected.
The only source dependency is the sibling literal HSW family constructor.

Normal and optimized isolated Python runs produce identical JSON.
The program does not enumerate a truncated version of the source's
19,329,428 labels: parameterized support and height checks account for
the full original family. No coverage conclusion is inferred from
passing the Euler-product threshold or from the local repair.
