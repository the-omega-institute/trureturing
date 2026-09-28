# One reference source releases 132 shallow phases and every higher height

Only 59 shallow phase slots need remain matched to one of the four
reference templates. Every other 132 shallow phase may be arbitrary,
as may every nonternary higher exponent and every 23/29-bearing original.
This result uses the same actual coordinate space and one measure,
then restricts it by the target family's actual forbidden cylinders.
The reference's old multi-support forbidden cylinders need NOT occur
in the target family.

The source and complete height costs come from
[Report717](717-four-fixed-shallow-families-survive-arbitrary-nonternary-heights.md).
The refinement here permits arbitrary phases on 132 previously fixed
numerical labels, paid on the same reference measure.

## Reference-source repair lemma

Let eta be the one prefix-constant source of the common prefix-tail
construction, with massS, complete deep-loss upperA, complete nonunit
query upper K, and simultaneous shallow query capsC_(j,D). Let R be any
set of nonunit shallow numerical labels. Consider a target actual
familyF of distinct odd nonunit moduli with support in
{3,5,7,11,13,17,19,23,29} andv 3<=2.

For every shallow label outsideR which occurs in F, require that its
phase agrees with the corresponding reference phase. Labels inR may
have arbitrary actual phases or be absent. Define

    B_R=sum_(d(j,D) inR) C_(j,D).

Let E_d^F be the actual forbidden cylinder if that label occurs. Since
eta already avoids every reference original, it avoids each matching
actual shallow original. Restricteta further by avoiding the union of
E_d^F over the occurring labels inR. Its lost mass is at mostB_R,
because each actual E_d^F is bounded by the SAMEC_(j,D). This one
restriction is supported on all actual shallow avoidance, whether or
not the reference's oldR-cylinders occur in F.

Now also restrict by every actual core-only deep original. Their loss
oneta is at mostA from the prefix-tail lemma, so their loss on the
already restricted source is also at mostA. The resulting nu has

    nu(1)>=S-B_R-A,
    complete_nonunit_query_sum(nu)<=K.

No reference condition is asserted to be an actual original after its
phase is released. Avoiding additional reference cylinders only makes
nu a smaller valid source; it does not change the target family or
claim an extra arithmetic constraint in that family.

The existing 23/29 continuation thus succeeds whenever

    Delta_R=(566/49)(S-A-B_R)-K>0.

Ifeta has Haar density at mostD0=323323/73728, the final Haar survivor
density is at least 49 Delta_R/(616 D 0). All source restrictions use the
actual target phases in one family. Different query caps are never
realized by independently selected sources.

The same proof admits a sharper ACTUAL debit

    B_F=eta(union_(d inR occurring in F)E_d^F)<=B_R.

Matching phases or absent labels cost zero automatically. The uniform
sum B_R allows the stated unrestricted phase conclusion without
needing to know those phases in advance.

## Release all multi-outside-support shallow labels

PutB={11,13,17,19}. ChooseR to contain every shallow numerical label
whose support includes at least two primes ofB. There are

    3*4*(binom(4,2)+binom(4,3)+binom(4,4))=132

such labels. The other 59 slots consist of the 11 nonunit head labels,
four outside pure labels, and 44 further singleton-outside labels.
The complete literal 59(a,m) lists and their digests are in the result
JSON. For those 59 slots, a target original if present must use the
reference phase; no target family is required to include all 59.
All 132 released slots, and all deeper or 23/29-bearing slots, are free
subject only to distinctness, support andv 3<=2.

The exact same-source debits are:

| Reference head and singleton phase template | B_R | Delta_R |
| --- | --- | --- |
|opposite-root aligned|129149/1990656|29470785747941/26968451973120|
|opposite-root spread|179159/3317760|2304342223517/26968451973120|
|same-root aligned|136391/1990656|10100409786827/8989483991040|
|same-root spread|11479/207360|3989373826519/26968451973120|

All four gates are strictly positive. The resulting uniform Haar
survivor density lower bounds are:

| Reference template | Exact density lower | Decimal lower |
| --- | --- | ---: |
|opposite-root aligned|29470785747941/1486773449441280|0.01982197473261|
|opposite-root spread|2304342223517/1486773449441280|0.00154989465569|
|same-root aligned|10100409786827/495591149813760|0.02038052897155|
|same-root spread|209967043501/78251234181120|0.00268324258011|

Thus all four restricted 59-slot template classes admit arbitrary actual
multi-outside-support phases and every nonternary height. This removes
132 of the previously fixed 191 shallow phases. It does not assert that
all possible phases of the remaining 59 slots satisfy one of these
four templates.

The [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_phase_release.py)
reconstructs the actual reference sources and 192 shallow screens before
checking the retained height certificate. It verifies all 132 released
numerical labels and the complementary 59 slots, then computes the
strict gates and density fractions. Its
[result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_phase_release.json)
retains the actual fixed phase lists. Independent reconstruction from
literal integer congruences agrees with each debit and strict gate.
This is ordinary mathematics plus exact rational checking, not
additional Lean verification.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_phase_release.py
```


## The next actual-phase boundary

For a general target family, retain the same reference source and let
J_F be all occurring shallow labels whose phases differ from the
reference. The repair proof needs only

    eta(union_(d inJ_F)E_d^F) < Delta/(566/49),

whereDelta is the reference all-height gate. This is a condition on
one ACTUAL union, and can exploit overlaps and already forbidden parts.
Its sum-of-query-caps relaxation gives the table above. Replacing that
relaxation with exact shared-phase union bounds can enlarge the class
without changing the source or assuming all phase costs attain their
separate maxima together.

To prove a universal result by this route one must still show that
every actual shallow phase family has a suitable reference source or
one directly constructed common source with a positive repaired gate.
Neither the four references nor their individual margins establish
that quantifier. The reference-source lemma identifies what a future
phase-forcing result must bound: the actual uncovered discrepancy union,
not a collection of unrelated best-case phase costs.
