# Common prefix transport reduces the free45 phase to three cases

Keep the two actual anchors and the22 mixed phases other than45 from
[Report808](808-a-second-reference-colour-retains-an-actual-opposing-phase-continuation.md).
Allow the actual phase at the numerical label45 to vary. Applying the
all-pure source atlas of
[Report822](822-a-structural-source-atlas-covers-arbitrary-old-pure-families.md),
34 of the45 phases inherit its positive complete continuation. The11
remaining phases reduce to three representatives requiring separate source
certificates:

    20 mod45, 31 mod45, 16 mod45.

This is a concrete application of existing common prefix-tree transport
and selected-null inventory bounds. The common stabilizer has TEN orbits
on the45 phases; SEVEN groups suffice for organizing proof reuse. These
counts must not be identified. The argument does not establish positivity
for the remaining three classes, arbitrary mixed phases, or unrestricted
Erdős#7. The finite consumer below checks the classification and transport
controls; it does not recompute the positive atlas and performs no LP or
Lean verification.

## 1. Exact inherited contract

The fixed numerical labels and phases, written as(modulus,phase), are

    (3,0),(9,1),
    (15,10),(21,7),(33,22),(35,0),(39,13),(63,49),
    (51,34),(57,19),(55,0),(105,70),(75,25),(69,46),
    (65,0),(99,22),(77,0),(85,0),(117,13),(95,0),
    (165,55),(91,0),(147,49),(225,175).

The remaining selected original is(a mod45), with0<=a<45. Thus the
unchanged data are22 mixed originals and both anchors, or24 originals
altogether. All original numerical moduli remain odd, nonunit and
pairwise distinct. The actual old pure-q inventories, q in

    Q=(5,7,11,13,17,19,23),

have arbitrary finite phases and heights. Other allowed mixed head phases
and all higher ternary heights are arbitrary and finite. The complete
[Report804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md)
support contract remains

    {3,5,7,11,13,17,19,23,29} union {p prime:p>1600}.

Primes31 through1600 are excluded. No intermediate prime or missing
height is admitted by changing reference. The same positive lower bound
as Report822 is inherited in the34 directly reusable phases, with its
appropriate full-survivor or retained-survivor normalization.

## 2. Existing transport and the exact selected-prefix test

[Report433 §7](../400-449/433-chordal-overlap-certificates-and-their-exact-finite-limits.md)
describes the coordinatewise rooted prime-digit automorphisms preserving
every fixed-modulus divisor partition.
[Report636 §3](../600-649/636-coherent-prefix-roles-transport-the370-label-certificate.md)
constructs one family-wide alignment of shared prefix roles, and
[Report794](../750-799/794-actual-prefix-orbits-make-all-height-source-search-sparse.md)
uses actual named-prefix stabilizers for common-source queries. Their
mechanism is reused here, rather than introduced as a new general result.

For the same finite selected numerical labels m_i, write e_i=v_p(m_i).
Two phase lists a_i,b_i can be matched at prime p by ONE rooted-tree
automorphism exactly when, for every pair i,j and every shared depth
1<=r<=min(e_i,e_j),

    a_i=a_j mod p^r  iff  b_i=b_j mod p^r.                 (PC1)

Necessity is preservation of ancestors and branching. For sufficiency,
send every selected node and all its ancestors to the corresponding
target node. PC1 makes this well-defined and injective at each sibling
set. Extend each partial child bijection to a permutation of the p
children. Apply the same child permutations to every original; later
digits can remain unchanged. This is the finite shared-role extension
used in636, specialized to all named selected prefixes.

Choose a resolving period M for the WHOLE actual finite family. At each
p|M extend the selected-prefix map to depth v_p(M), and combine the
coordinate bijections through CRT. This gives one permutation of Z/MZ.
Every actual a modm cylinder maps to one cylinder with the SAME numerical
modulus m. The whole survivor, all intersections, every fixed numerical
query menu and Haar measure are transported together. Distinct numerical
labels remain distinct. No ring homomorphism or bijection of the integers
is required: covering is equivalent on this common finite period.

Push forward the entire law, including the actual pure survivors, source
weights, retained table and normalization. Equivalently, normalize the
whole family first, choose its certified source, and pull that source
back. Leaf weights follow their leaves. There is no separate source or
rephasing for each label or query.

The literal808 phase table has the following named partitions. Labels in
one cell share that prefix; different cells in one row are distinct.

| Prime and depth | Literal prefix : numerical labels |
|---|---|
|3, depth1|0:{3}; 1:{9,15,21,33,39,51,57,63,69,75,99,105,117,147,165,225}; 2:{45}|
|3, depth2|1:{9}; 2:{45}; 4:{63,99,117,225}|
|5, depth1|0:{15,35,55,65,75,85,95,105,165,225}; 1:{45}|
|5, depth2|0:{75,225}|
|7, depth1|0:{21,35,63,77,91,105,147}|
|7, depth2|0:{147}|
|11, depth1|0:{33,55,77,99,165}|
|13, depth1|0:{39,65,91,117}|
|17, depth1|0:{51,85}|
|19, depth1|0:{57,95}|
|23, depth1|0:{69}|

Depth2 at7 contains only one named node; it still must be carried to a
depth2 node under its designated root. At5 the TWO labels75 and225 must
share the same depth2 node for literal orbit matching. First-digit
agreement alone does not establish PC1.

## 3. The common stabilizer has ten actual phase orbits

Fix all24 originals other than45. At3, the anchor3 fixes root0, anchor9
fixes leaf1 and its root1, and therefore root2 is fixed. The named deep
labels63,99,117,225 fix leaf4. The remaining sibling leaf7 is consequently
fixed as well. The three leaves under root0 can permute, and the three
leaves under root2 can permute. Hence the exact leaf orbits are

    {0,3,6}, {1}, {4}, {7}, {2,5,8}.                       (PC2)

At5, the fixed originals require root0 to remain fixed, and75/225 require
its designated second child0 to remain fixed. The roots1,2,3,4 can be
permuted arbitrarily while leaving the whole root0 subtree unchanged.
Thus the45 prefix has two possible orbit types at5:

    {0}, {1,2,3,4}.                                      (PC3)

The choices in PC2 and PC3 are independent coordinate maps. CRT therefore
gives exactly5*2=10 orbits, all realizable under the same fixed24-label
stabilizer. This is a statement about the action on the45 phase, not the
size of the full all-height stabilizer group.

| Ternary leaf orbit |5 digit0: representative, size|5 digit nonzero: representative, size|
|---|---:|---:|
|{0,3,6}|0, 3|36, 12|
|{1}|10, 1|1, 4|
|{4}|40, 1|31, 4|
|{7}|25, 1|16, 4|
|{2,5,8}|20, 3|11, 12|

For the12 phases in the last cell, choose a child permutation under
ternary root2 sending a mod9 to2. Choose a first-digit permutation at5
fixing0 and sending a mod5 to1, and leave the root0 subtree unchanged.
All other prime maps may be identities. These maps fix EVERY one of the24
named cylinders, including their depth2 components, and send a mod45 to
11 mod45. Extend them and apply them to all actual unselected originals
as in §2. Arbitrary old pure families are still arbitrary old pure
families after transport, so the complete822 atlas applies.

## 4. Seven reuse groups, with34 inherited phases

Some different stabilizer orbits share a simpler nullity proof. This
permits the following seven proof-reuse groups.

| Group | Representative | Number of45 phases | Reuse or remaining obligation |
|---|---:|---:|---|
|dead ternary leaf in{0,1,3,6}|four orbits|20|Contained in0 mod3 or1 mod9|
|leaf4,5 digit0|40|1|Contained in10 mod15|
|leaf7,5 digit0|25|1|Contained in10 mod15|
|root2,5 digit nonzero|11|12|Whole-family stabilizer transport to808|
|root2,5 digit0|20|3|Remaining arbitrary-pure class|
|leaf4,5 digit nonzero|31|4|Remaining arbitrary-pure class|
|leaf7,5 digit nonzero|16|4|Remaining arbitrary-pure class|

The dead-leaf row combines FOUR strict orbits, not one. The other six
rows are each one strict orbit. The counts sum to45, and the first four
rows contain20+1+1+12=34 phases. Combining the two singleton containment
rows would give six reuse groups without changing the classification.

For the first three rows, use the same selected-null source tables as822.
All such tables vanish on the anchors and on10 mod15. Also

    40=10 mod15, 25=10 mod15.

Thus the replacement45 cylinder is null. The remaining selected cylinders
are unchanged. The numerical45 label is still subtracted exactly once
from the same height2/support{5}/depth1 inventory. This is precisely the
selected-null hypothesis of
[Report810 K8–K9](810-categorical-retained-kernels-give-a-finite-common-source-interface.md),
including the refined depth inventory of
[Report820](820-queried-colour-capacities-sharpen-complete-head-and-moment-bounds.md).
No loss coefficient, high-ternary tail or complete prime-tail allowance
changes. In particular a now-redundant45 original is not an extra credit.

The actual survivor U may change when the45 phase changes. Its normalized
law must use that NEW actual U. The reused proofs give the same valid
lower and moment bounds for the appropriate lambda_w|U/lambda_w(U) or
nu_u|U/nu_u(U); they do not identify the two survivor sets or their exact
normalizers. Report822's chosen branch retains its own normalization
through every bound. This establishes the34-phase extension from the
completed atlas without running another optimizer.

## 5. What remains, and the existing partial results

The unresolved phases for this reuse argument are exactly

    20 class: {5,20,35};
    31 class: {4,13,22,31};
    16 class: {7,16,34,43}.                               (PC4)

The representatives31 and16 cannot be exchanged while keeping the other
selected phases fixed: their ternary leaves4 and7 have different
relations to the fixed depth2 prefixes of63,99,117,225. Keeping only a
root1 label would incorrectly merge them.

A subsequent source-certificate consumer can look for further
equivalences of its constraints or objective. Such a task-level
equivalence does not identify the two actual stabilizer orbits, and the
present reduction imposes no restriction on those later certificate
methods.

[Report806 §8](806-actual-ternary-leaf-cores-give-a-finite-common-source-linear-program.md)
already supplies a complete>1600 continuation for the20 representative
when ALL old pure-q inventories are empty. Its arbitrary-pure fixed-weight
bound gives a positive head but a negative continuation gate. Neither
statement settles this class for arbitrary pure families, and a failed
gate is not a covering example or a proof that every source fails.

There is also a direct source-null subcase in each remaining class: if
the actual modulus5 original removes the same first digit as a mod45,
then that45 cylinder is contained in the pure5 cylinder and is already
null. The selected-null reuse above applies. This does not cover all
actual pure inventories for any of the three classes.

Reports803 and805 use the same actual45 phase40;805 changes the core's
star-root allocation, not the actual original. Report806 changes45 to20;
Report808 changes it to11. These are not interchangeable fixed-family
statements. The present application removes the arbitrary-pure burden in
the34 inherited phases, while retaining PC4 as the precise remaining
phase task. All other22 mixed phases are still fixed.

## 6. Controls separating transport, nullity and arbitrary phases

The prefix-tree mechanism is strictly broader than the common affine
reference of
[Report719](../700-749/719-actual-phase-unions-and-common-affine-reference-enlarge-the-certified-families.md).
At3 exchange leaves4 and7 mod9, fix every other leaf, and keep later digits
unchanged; use identity maps at other primes. Applying this ONE map to
the whole808 family changes its selected phases by

    63:49->7, 99:22->88, 117:13->52, 225:175->25.

All other selected phases are unchanged. A common affine map would have
to fix leaves1 and2 because the9 and45 originals are unchanged. It would
then have u=1,v=0 mod9 and could not move4 to7. This is a tree-orbit
extension of the literal table, but NOT an allowed move inside the
fixed-other22 task of §§3–5.

Conversely, change only225 from175 to130. All first digits and its
ternary leaf4 stay unchanged, but the75 and225 prefixes at5 now equal0
and5 mod25. They no longer lie in the literal808 tree orbit. Nevertheless
the changed225 cylinder remains null on808's SC2 core: it is on a short
leaf and has a5 zero-hit. Hence literal orbit matching is a sufficient
transport route, not a necessary condition for the selected-null method.

For a separate first-root obstruction, change15 from10 to11. Its root
now differs from the9 anchor's root. A common point with ternary leaf5
and first digit1 at every q inQ lies in808's core and hits this changed15
original. Thus this replacement is neither a tree normalization of the
old family nor null on that particular core. These controls are not
covering examples, and the latter does not rule out a different source.

## 7. Finite consumer and verification boundary

The [consumer](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/common_prefix_phase_classes.py),
[certificate](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/common_prefix_phase_classes_certificate.json)
and [result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/common_prefix_phase_classes.json)
retain the literal25-label fixture, all shared first/second-depth
partitions, the ten exact45 orbits, seven reuse groups, complete phase
lists and both nonorbit controls. The matching function returns an exact
pair/depth obstruction when a selected relation changes. Explicit
transport checks verify all12 normalized45 phases against every fixed
label, including the5-squared child constraints. The non-affine tree
control is checked through ternary height3 with unchanged later digits.

The standard-library program performs608 explicit checks, active under
optimization. Use adjacent data or explicit --certificate and --result
paths; --write-result regenerates the result.

    python3 -I -S -B common_prefix_phase_classes.py
    python3 -I -S -B -O common_prefix_phase_classes.py

Both modes and an optimized replay from a directory containing spaces
pass. Ten forged input/result kinds are rejected under optimization,
including altered depth2 sharing, a missing depth2 label, merged distinct
orbits, an inflated reusable-phase count and erased obstruction controls.

The ordinary finite-tree and CRT arguments supply arbitrary finite-height
transport. The finite checks validate this selected data and its consumer;
Report822 supplies the positive atlas, and the existing full-inventory
and tail theorems supply its quantitative continuation. The three
remaining arbitrary-pure phase classes are not resolved by this result.
