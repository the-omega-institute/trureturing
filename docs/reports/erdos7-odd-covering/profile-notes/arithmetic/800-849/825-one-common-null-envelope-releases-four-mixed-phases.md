# One common null envelope releases four mixed phases

The selected phases at numerical labels15,45,75,225 can vary together
inside an explicit joint relation, while the other19 mixed phases and
the3/9 anchors stay fixed. There are921600 admitted phase quadruples.
Every admitted actual family inherits the positive complete continuation
of [Report822](822-a-structural-source-atlas-covers-arbitrary-old-pure-families.md),
including arbitrary finite old pure-prime inventories and final distorted
surviving mass greater than1/2000.

One common reference must work for all four actual labels. Multiplying
their separately admissible phase counts would give1040400 quadruples
and would wrongly include118800 combinations. A concrete two-change
example below exhibits the conflicting reference requirements.

This is an application of existing common-tree transport and
selected-null source accounting. It changes neither the source tables
nor the complete-height estimates, introduces no new generic nullity
theorem, and uses no LP. The phases outside the displayed joint relation
need separate certificates. Prime support remains

    {3,5,7,11,13,17,19,23,29} union P,
    P any finite set of primes strictly above1600.

Primes31 through1600 remain excluded. No Lean verification or
unrestricted Erdős#7 conclusion is asserted.

## 1. The actual labels and the source exclusions

Keep actual anchors0 mod3 and1 mod9 and the following19 actual mixed
originals from822:

    (21,7),(33,22),(35,0),(39,13),(63,49),(51,34),
    (57,19),(55,0),(105,70),(69,46),(65,0),(99,22),
    (77,0),(85,0),(117,13),(95,0),(165,55),(91,0),(147,49).

The remaining four actual originals are a_m modm, for

    m in{15,45,75,225}, 0<=a_m<m.

All original numerical moduli are odd, nonunit and globally distinct.
The other allowed head phases and all finite heights are arbitrary.
Actual pure-q inventories, q in{5,7,11,13,17,19,23}, may have arbitrary
finite phases and heights. Higher pure ternary labels retain their
complete residual charges. The actual29 stage and every allowed finite
large-prime tail use the unchanged
[Report804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md)
contract and its inherited analytic premise.

On the common225 carrier, let[a]_m denote one cylinder. Write

    B=[0]_3 union[1]_9 union[10]_15,
    R={r mod45:r mod9 in{2,5,8}, r mod5!=0},
    D_r=B union[r]_45, r inR.                              (NE1)

There are12 choices ofr. The cylinders[10]_15 and[r]_45 inNE1 are
SOURCE/TABLE constraints. They need not be the actual originals at those
numerical labels, and they are not extra actual originals. A source may
retain these exclusions even when an actual label takes another phase.

The required relation is

    exists ONE r inR such that [a_m]_m subset D_r
    simultaneously for m=15,45,75,225.                     (NE2)

Each actual label still carries exactly one full cylinder. Inclusion in
a union does not split that original into separately chosen pieces.

## 2. Why the same positive source proof applies

The common-tree construction of
[Report823](823-common-prefix-transport-reduces-the-free45-phase-to-three-cases.md)
sendsr to11 by permuting children only under ternary root2 and permuting
the nonzero5 roots. Keep the5 root0 subtree and all other prime
coordinates unchanged. The same maps fix every one of the19 listed mixed
cylinders, both anchors, and the auxiliary10 mod15 cylinder. They send
D_r toD_11.

Extend these maps by unchanged later digits on one resolving period for
the WHOLE actual finite family, and combine by CRT. Apply them to every
actual original and the whole law. Each numerical modulus, its prime
depths, all cylinder incidences and the complete numerical query menus
are preserved. The transformed pure inventories remain arbitrary finite
pure inventories. The entire822 atlas is therefore available after
normalization. No query or individual selected label selects a different
reference map.

Every retained table used in822 is null on[0]_3 and[1]_9 because these
leaves are absent. Its selected-zero constraints make it null on
[10]_15 and[11]_45. Thus it is null onD_11. ByNE2, all four transformed
actual selected cylinders are null on that SAME table. The other19
selected cylinders are unchanged and null as before.

This reuses the proof through
[Report810 K8–K9](810-categorical-retained-kernels-give-a-finite-common-source-interface.md)
and [Report820](820-queried-colour-capacities-sharpen-complete-head-and-moment-bounds.md)'s
complete depth inventory. It does not claim that the new actual family
possesses the old literal15,45,75,225 phases. All23 selected numerical
slots are still deducted once, in their existing types:75 and225 retain
their deep5 types, and45 retains its depth1-at5 type. No auxiliary
reference cylinder receives another inventory deduction.

Use the NEW actual survivorU. Depending on the assigned822 branch, the
normalized law is lambda_w|U/lambda_w(U) or nu_u|U/nu_u(U). The same
selected-null proof supplies the same mass floor; the branch's hinge
and moment bounds use that same denominator throughout. The actual
survivor and its exact normalizer need not equal the old ones. Pulling
the entire certified construction back gives the same positive reserve
for the original actual family. ConsequentlyNE2 retains the>1/2000
distorted continuation bound and all finite heights.

## 3. The exact joint relation on the four phases

DefineB_m={a modm:[a]_m subset B}. Directly from the three cylinders inB,

    B15 ={a:a=0 mod3} union{10},                         |B15|=6;
    B75 ={a:a=0 mod3 or a=10 mod15},                     |B75|=30;
    B45 ={a:a=0 mod3 or a=1 mod9 or a=10 mod15},         |B45|=22;
    B225={a:a=0 mod3 or a=1 mod9 or a=10 mod15},         |B225|=110.
                                                               (NE3)

The last two formulas are taken in their respective residue spaces.
For45, the anchors give20 phases, and10 mod15 contributes two additional
phases25,40. For225 the anchors give100 points, and10 mod15 contributes
ten additional points. For15 and75, a first ternary root cannot be
contained in the single removed9 leaf unless the remaining leaves are
also removed by10 mod15; this gives precisely the stated formulas.

For one fixedr, exact whole-cylinder containment is

    a15 inB15;
    a75 inB75;
    a45 inB45 union{r};
    a225 inB225 union{r,r+45,r+90,r+135,r+180}.           (NE4)

The four counts are6,23,30,115. The extra root2 leaf does not contain a
whole15 or75 cylinder: both span all three9 leaves of their ternary
root. At45 it adds exactlyr. At225 it adds exactly five descendants.
This provesNE4 without assigning independent references to its clauses.

Eliminate the one existentialr inNE4. Besidesa15 inB15 anda75 inB75,
there are exactly two alternatives:

- Ifa45 inB45, thena225 can belong toB225 or havea225 mod9 in{2,5,8}
  anda225 mod5 nonzero. These are110+60=170 choices. Choose one commonr
  after inspecting the tuple; an outside-B225 value forcesr=a225 mod45.
- Ifa45 inR, thenr=a45 is forced. The225 phase must belong toB225 or
  satisfya225=a45 mod45, giving110+5=115 choices.

No other45 phase enters this envelope. Thus there are exactly

    22*170+12*115=5120                                  (NE5)

joint45/225 pairs. The15 and75 allowed sets are independent ofr, so the
total admitted phase quadruples number

    6*30*5120=921600.                                   (NE6)

These cardinalities describe this sufficient family. They do not count
all families admitting some positive source. The calculation uses the
one225 carrier and set unions, rather than enumerating the11390625
possible phase quadruples. It leaves the three45 representatives of823
outside its envelope; later certificates can supply additional cases.

## 4. Separate successful changes need not have one common reference

Start with the actual phase tuple, in order(15,45,75,225),

    (10,0,25,175).

All twelve references work. The following two changes are individually
admitted:

    change45 only:  (10,11,25,175), withr=11;
    change225 only: (10,0,25,41),   withr=41.

Combining them gives

    (10,11,25,41).                                     (NE7)

The45 cylinder lies outsideB and forcesr=11. The225 cylinder lies
outsideB and forcesr=41, because41 mod45=41. ThereforeNE7 has no common
reference, even though each label individually has one. Equivalently,
the two literals have different ternary leaves2 and5 but the same
nonzero first5 digit1. Both belong to the same actual family and cannot
be transported using independently selected child permutations.

The difference is not erased by forgetting the225 second5 digit:
replacing41 by176 changes its mod25 prefix from16 to1, but176 still
equals41 mod45 and gives the same incompatible reference requirement.
For a fixedr, all five225 descendants were already retained inNE4.

Multiplying the separate phase counts would produce

    6*34*30*170=1040400,

an overcount of118800 compared withNE6. This is a joint-realizability
failure for the declared reference method, not a covering example or
a theorem that every other source fails.

For a positive simultaneous control, the tuple

    (3,0,70,41)

changes all four old phases and satisfiesNE2 withr=41. Its75 cylinder
is inside the auxiliary10 mod15 cylinder because70=10 mod15. Its225
cylinder is inside the auxiliary41 mod45 cylinder. Neither auxiliary
phase is asserted to be the actual phase of its numerical label.

The consumer constructs one CRT integer with residue2 mod225 and1 at
all remaining prime-power coordinates. It avoids all25 originals in
each displayed finite control, includingNE7. This verifies that the
nonjoint control is not a finite covering. Arbitrary extensions may
cover that particular integer; the positive uniform statement for
admitted tuples comes from the source proof, not that witness.

## 5. Reuse boundary and the next obligation

[Report801 RC6–RC8](801-retained-core-intersections-reduce-shallow-phase-contracts-to23-labels.md)
already allows actual-cylinder containment in a reference excluded
union and explicitly allows auxiliary reference exclusions.
[Report719](../700-749/719-actual-phase-unions-and-common-affine-reference-enlarge-the-certified-families.md)
likewise distinguishes zero-cost phase changes from literal matching.
[Report802](802-same-source-leakage-budgets-admit-positive-selected-intersections.md)
supplies a same-source union-leakage repair when strict nullity fails;
its numerical budget belongs to its own law and>3000 continuation and
is not imported into822.

[Report798](../750-799/798-whole-numerical-slot-completions-retain-a-fixed-law-certificate-obstruction.md)
retains whole numerical slots and joint assignments. No original here
is fractionally allocated among references or split by numerical
cofactor. The concrete addition isNE4–NE6 and its admissible family,
obtained by composing these existing interfaces.

OutsideNE2, a next source proof can keep the actual joint union of the
four cylinders and bound its positive leakage on ONE source with ONE
reference, or construct a different source. Separate per-label minima
or separately successful transports do not supply that estimate. The
remaining intermediate-prime gap31..1600 is unchanged by this route.

## 6. Small finite consumer

The [consumer](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/common_null_envelope.py),
[certificate](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/common_null_envelope_certificate.json)
and [result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/common_null_envelope.json)
check the exact allowed cylinder sets on225, the12 common reference
maps, unchanged fixed21 cylinders, shared projection to all four
numerical slots, the joint counts and six actual-family controls.
Projection of the envelope's complement detects disallowed WHOLE
cylinders. The joint pair count uses unions over the same allowed
reference set and never multiplies independent marginal counts.

The standard-library program performs571 explicit checks with no solver
or network call. It accepts adjacent data or explicit --certificate,
--result and --write-result paths. Checks remain active under
optimization:

    python3 -I -S -B common_null_envelope.py
    python3 -I -S -B -O common_null_envelope.py

Normal and optimized replays, including optimized replay from a directory
containing spaces, pass. Ten forged input/result kinds are rejected under
optimization, including a lost depth2 carrier, duplicate actual labels,
independent-reference overcounts, an invented common reference and a
75 cylinder whose unexamined ternary leaves leave the envelope.

The common-tree proof extends the finite transport to every finite
actual resolving height. These local checks do not recompute822's
positive arithmetic or replace its complete source and tail premises.
