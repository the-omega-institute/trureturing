# A common pruned carrier controls shallow primes through23 and one full-height tail prime

This is ordinary mathematics with exact finite checks, not new Lean
verification. It reuses the existing six-shape head mean theorem. All
original phases are fixed globally, with one original per numerical modulus;
no phase or supported law is chosen separately for different rows or tests.

First consider shallow moduli dividing

    L_B = 315 product_(q in B) q,

where B is a finite set of distinct primes greater than7. Thus the exponent
of3 is at most2, and all other exponents are at most1. Missing moduli are
allowed. After building the shallow core through23, the same carrier also
permits one new primeq>=29 at any finite height, with every actual phase
arbitrary. The3 exponent remains at most2 and the5 through23 exponents
remain at most1. This is not the unrestricted-height nine-prime or Erdős#7
problem.

For that full-height-last-prime family the uniform Haar survivor density is

    >=52363/9464546 >0.00553254.                       (US0)

This includes every distinct original modulus of the formd*q^e, where
d dividesL_{11,...,23}, e>=0, andd*q^e>1; any finite subset is allowed.

For the separate shallow specialization with B={11,13,17,19,23,29},
where the exponent of29 is also at most one, every actual family leaves at least

    57599300 residues modulo9704539845,
    Haar density >=1047260/176446179 >0.0059352.

This covers all767 possible nonunit shallow numerical labels, with arbitrary
simultaneous phases. The proof first builds one shallow23 carrier and then
uses its complete-query second moment to append29.

For B={11,13,17,19,23}, the intermediate bound is

    5759930 residues modulo334639305,
    Haar density >=104726/6084351 >0.01721235.

For B={11,13,17,19}, the analogous bound is648934 residues modulo14549535,
or density4538/101745. A direct first-moment union bound through29 certifies
only three shapes; the same-source second-moment continuation below certifies
all six.

## 1. Existing inputs and their scope

The existing proof and finite certificate are in
[the survivor reduction](../../001-064/01-survivor-reduction.md),
especially `Survivor reduction`, `Coupling the original deletions to the load
numerator`, and the threshold-one column in `Hinge and square costs`.
[finite head geometry](../../../finite_head_geometry.md), section `Completion, pruning and symmetry`,
supplies the six-orbit reduction.

For each actual eleven-slot head at nonunit divisors of315, these results
provide ONE supported subset S of its survivors, obtained by old45 pruning.
Let N=|S|. Its uniform law satisfies, simultaneously for every complete
numerical divisor query layout,

    L_a(u)=sum_(c|315) 1_(u=a_c mod c),
    sum_(u in S)(L_a(u)-1) <= c1 N.                  (US1)

The numerical unit term is always1. The relevant bounds are:

|Pruned old45 shape|n=old45 survivors|Nmin|c1|
|---|---:|---:|---:|
|short15 root;45 same root, other column|17|77|185/86|
|short15 root;45 other root, same column|17|78|178/85|
|short15 root;45 other root, other column|17|78|178/85|
|long15 root;45 same root, other column|16|75|2|
|long15 root;45 other root, same column|16|74|157/77|
|long15 root;45 other root, other column|16|74|157/77|

In each row, Nmin<=N<=6n. Since the left side of(US1) is an integer, its
upper bound can be replaced by M(N)=floor(c1 N).

These are existing ordinary finite head results, not new sharp constants.
The new checker independently reconstructs exactly their threshold-one and
square finite inequalities on all27720 old query layouts, for55440 checked
inequalities. It does not claim to rerun the other30 shape/cost entries or
the full194040 earlier inequalities.

## 2. Why the same supported subset exists for every actual head

First fill every missing old45 slot in the order3,9,5,15,45 with an arbitrary
phase. Complete missing7-containing head slots as well. Adding auxiliary
forbidden classes can only shrink the surviving set, so a survivor of this
completion is a survivor of the original incomplete family.

Process the old45 classes in the stated order. Keep a class whenever it
contains a point surviving the already processed classes. If it is wholly
redundant, replace its phase by a class through one such surviving point.
At a replacement, the old class is already contained in the retained earlier
union. Consequently nothing formerly forbidden becomes allowed. Every old
deletion remains covered after all replacements.

In particular:

- A9 class inside the forbidden3 root is redundant. Replacing it gives a
  smaller survivor set with one other ternary root shortened by one leaf.
  This is a supported-subset reduction, not affine equivalence of the
  original nested and disjoint families.
- A15 class made effective deletes one short or long root at one live5
  column. A45 point in that same root and column is already deleted, so it
  must be relocated before the three45-position cases are classified.
- The original7-containing classes remain fixed throughout this old45
  operation. Pulling them back from the final canonical coordinates gives
  the same original head constraints on a smaller old45 support.

The ternary root/leaf partition and the five quinary points have sufficient
permutations to normalize the pure classes to0 mod3,4 mod9,0 mod5; to put
the15 column at1; and to put the effective45 point in exactly one of the
three stated positions. These are rooted-partition-preserving coordinate
permutations, not necessarily affine maps. They preserve EVERY numerical
divisor-cylinder family at once. Extend the map to the7 coordinate (or leave
that coordinate unchanged when no pure7 normalization is needed), and act
identically on the outside coordinates.

Thus one common map transports ALL head originals and ALL outside-class
head projections. Apply the existing six-shape theorem once and pull its
supported set back. The resulting S is contained in the actual original
head survivors, with(US1) for every numerical query layout simultaneously.
There is no q-specific pruning and no query-specific source.

The checker exhausts all91125=3*9*5*15*45 complete old45 original phase
assignments. At every pruning prefix it verifies inclusion of the original
forbidden union, then checks a single normalizing permutation and its action
on every3,5,9,15,45 cylinder. Missing slots are covered by the padding
argument; arbitrary original7-containing slots are covered by retaining
their same constraints over the smaller old45 support.

## 3. A uniform formula for any outside prime set

Complete any absent shallow slots. Let the actual pureq forbidden phase be
beta_q. On ONE common CRT carrier take

    E = S x product_(q in B)(Z/qZ minus{beta_q}).

Write

    P=product_(q in B)(q-1),
    Q=product_(q in B)q,
    A=sum_(q in B) P/(q-1),
    V=sum_(T subset B, |T|>=2) P/product_(q in T)(q-1)
     =Q-P-A.                                           (US2)

Before the remaining shallow originals are removed, E has NP points.

For a fixed outside primeq, the remaining singleton labels are cq with
c|315, c>1. Their actual head phases define one query layout without the
unit term. Regardless of their actual outside roots, the sum of the numbers
of points of E forbidden by these eleven classes is at most

    P/(q-1) M(N).                                      (US3)

If an outside root equals a previously forbidden pure root, its exact
contribution is zero; bounding it by(US3) is still valid.

For each fixed outside support T with at least two primes, ALL twelve
cofactors c|315 occur, including c=1. Their actual head phases define one
complete layout L_T. From(US1),

    sum_(u in S) L_T(u)<=N+M(N).

The sum of their actual forbidden cardinalities on the SAMEE is therefore
at most

    P/product_(q in T)(q-1) [N+M(N)].                  (US4)

All head phases and outside roots in(US3) and(US4) belong to the single
given original family. The theorem bounds every layout on S, so these
upper bounds hold simultaneously; it does not require the maximizing
layouts or maximum losses to be jointly realizable.

The ordinary union bound on that one carrier now gives

    Z_B >=PN-A M(N)-V[N+M(N)]
        =(P-V)N-(A+V)floor(c1 N).                     (US5)

This proves the general sufficient criterion. For a shape-independent
bound take the minimum of its right side over the six shapes and each
integer Nmin<=N<=6n. A positive minimum is a uniform lower cardinality
bound. A nonpositive value is only failure of this sufficient union bound.

Without the integer improvement, the normalized per-head-row gate is

    1-V/P-(A/P+V/P)c1
     =c1+2+s-(c1+1) product_(q in B) q/(q-1),
    s=sum_(q in B)1/(q-1).                            (US6)

Equation(US5) is stronger than separately optimizing single event caps:
each cofactor block is paid through one complete-head inventory sum. The
only union relaxation occurs after placing all actual events in the same
carrier. Intersections can improve the result further but are not assumed.

## 4. Exact values, including the integer minimum

|Outside primes B|P|A|V|All nonunit shallow labels|Period315Q|
|---|---:|---:|---:|---:|---:|
|11,13,17,19|34560|10416|1213|191|14549535|
|11,13,17,19,23|760320|263712|38315|383|334639305|
|11,13,17,19,23,29|21288960|8144256|1374847|767|9704539845|

The minimum of(US5) over each shape's permitted integerN is:

|Shape in the order of section1|Through19|Through23|Through29|
|---|---:|---:|---:|
|short, same root / other column|648934|5759930|-55195845|
|short, other root / same column|705539|7085989|-1700729|
|short, other root / other column|705539|7085989|-1700729|
|long, same root / other column|756675|8846325|65693025|
|long, other root / same column|723328|8124320|38887530|
|long, other root / other column|723328|8124320|38887530|

For through19 and through23 each minimum occurs at Nmin. This is checked
over the entire finite interval; one-step monotonicity must NOT be assumed
because of the floor. For through29 the minimizers are respectively
N=100,85,85,75,77,77. In particular substituting only Nmin=74 in the last
two cases would overstate the uniform bound.

The direct-union through29 conditional conclusion applies to an original head admitting
one valid old45 pruning into a long15-root shape. It does not assert that
every head can be so pruned. If an actual15 slot is missing or redundant,
it may be completed or moved to such a root; effective short-root originals
cannot simply be reassigned without the required forbidden-union inclusion.

There is a weaker useful decomposition for the191-label case: the59 labels
with at most one outside prime leave density at least16/247. The132 remaining
labels have total unconditional Haar fee22256/373065. Subtracting this fee
on the same original carrier gives density24832/4849845, or74496 points.
The direct block calculation(US5) improves this to648934 points. It does not
construct independent residual sets for the different blocks.

## 5. The complete-query square moment closes all767 shallow slots

On the SAME uniform pruned head law, the existing square column gives

    E L_a^2 <= g_i,
    g_i=(1091/82,1103/85,1103/85,965/76,993/77,993/77). (US7)

The ordinary finite proof of(US7) is the deletion-sensitive D4 argument in
the existing source. The checker independently reconstructs all27720 D4
integer inequalities for precisely these six constants. The moment law and
the mean law are uniform on the same S; no new source is selected for(US7).

Here is the general punctured-product moment step. Suppose one probability
nu on the current head controls every complete query square byG. Append a
new primeq uniformly on itsr=q-1 pure-live roots. For any complete query on
the enlarged numerical divisor inventory, write

    L(x,z)=A(x)+B_z(x),
    sum_(z pure-live) B_z(x)<=B(x),

whereA is its old non-q query block andB is the complete old-cofactor query
load of its q-containing block. Each is a legitimate complete old query.
Their phases can be unrelated. Since all terms are nonnegative,

    E_(z pure-live) L(x,z)^2
      <=A(x)^2+[2A(x)B(x)+B(x)^2]/r.

Indeed sum B_z^2<=(sum B_z)^2<=B^2. Integrating over the ONE oldnu and using
2AB<=A^2+B^2 gives

    E L^2<=G(1+3/r).                                  (US8)

Apply(US8) successively toq=11,13,17,19,23, always conditioning only the
pureq root at this stage. Before any remaining mixed classes are removed,
the carrier E from section3 is uniform and its every complete query obeys

    E_(uniform E) L^2 <=g_i product_(q) (1+3/(q-1))
                      =g_i*(43225/16896).              (US9)

Now remove ALL actual nonpure mixed shallow23 classes at once from E,
producing one actual carrier E23. By(US5)–(US6), its relative mass is at least
delta_i, where delta_i is the continuous gate in(US6). All six are positive.
Restricting a nonnegative L^2 decreases its unnormalized integral. Thus the
uniform law onE23 has

    Gamma23 <=g_i*(43225/16896)/delta_i.                 (US10)

No product distribution is assumed after this joint restriction. The square
bound was established before deletion and transported by restriction and
normalization, retaining every correlation inE23.

The exact resulting bounds and integer mean bounds are:

|Shape in section1 order|Gamma23 upper|t_i with E L<=sqrt(Gamma23)<=t_i|29-t_i|
|---|---:|---:|---:|
|short, same root / other column|2607189975/7283281|19|10|
|short, other root / same column|2145472875/7609619|17|12|
|short, other root / other column|2145472875/7609619|17|12|
|long, same root / other column|32930625/157268|15|14|
|long, other root / same column|643836375/2725382|16|13|
|long, other root / other column|643836375/2725382|16|13|

All inequalities Gamma23<=t_i^2 are checked as exact rational comparisons.
They hold simultaneously for every complete old query under that ONE law.

Finally append29, exclude its actual pure forbidden root, and start with
E23 times the28 remaining roots. The remaining29-bearing shallow numerical
labels are d*29 for every nonunitd dividingL_{11,...,23}: exactly383 labels.
Their globally fixed actual old phases define ONE nonunit query loadL-1.
The unit term has already paid for pure29 and is subtracted exactly once.
The sum of their actual forbidden cardinalities is at most

    |E23| E_(uniform E23)(L-1) <=(t_i-1)|E23|.

Consequently at least

    [28-(t_i-1)]|E23|=(29-t_i)|E23|                    (US11)

points survive. A queried29 root equal to the forbidden pure29 root makes
that original's deletion zero, so arbitrary actual phases do not weaken
this bound.

Combining(US11) with the six through23 cardinality bounds from section4
gives respectively

    57599300,85031868,85031868,123848550,105616160,105616160

survivors modulo9704539845. Their minimum proves the stated uniform density
1047260/176446179 for all767 shallow numerical moduli and all phases. Missing
slots only make the original surviving set larger.

## 6. The last prime can have arbitrary finite height

Keep the SAME uniformE23 law and its complete query mean boundt_i. Let
q>=29 be a new prime, and extend this law by independent Haar digits on
q^E, whereE is the largest exponent in the given finite original family.
At this stage do not pre-delete a pureq root: every pure power is included
once in its own complete numerical inventory.

For each e=1,...,E, the original classes have moduli d*q^e, d|L_{11,...,23}.
For a fixed original family their projected old phases define one complete
old query layoutL_e, including the unit term for the pureq^e class.
Their total mass on that ONE product source is at most

    q^(-e) E L_e <=t_i/q^e.

Summing all complete heights and restricting by all actual events gives

    remaining mass >=1-t_i sum_(e=1)^E q^(-e)
                    >=1-t_i/(q-1)
                    >=1-19/28=9/28.                 (US12)

No cross-height phase coherence is assumed: each numerical class has its
own fixed phase, and everyL_e is bounded on the same source. Missing labels
and unused heights only lower the actual deletion charge.

The old source is uniform onE23, so its Haar density cap is
L_{11,...,23}/|E23|. Appending Haarq digits preserves this cap. Hence(US12)
and the through23 count give, shape by shape,

|Shape in section1 order|Uniform lower density for everyq>=29 and every finitev_q|
|---|---:|
|short, same root / other column|52363/9464546|
|short, other root / same column|7085989/851809140|
|short, other root / other column|7085989/851809140|
|long, same root / other column|196585/16016924|
|long, other root / same column|1624864/156165009|
|long, other root / other column|1624864/156165009|

Their minimum is(US0). This is a density statement uniform in the last
prime's finite height; it is not a count of only767 original labels. With
last-prime heightE, the complete allowed numerical inventory has
384(E+1)-1 labels. The stronger767-label count in section5 is the separate
specializationE=1, where pre-deleting pureq improves the charge.

More generally letPnew be any finite set of new primes disjoint from the
core, extend by their independent Haar coordinates, and retain one complete
old query boundt_i. Group numerical originals by their nonunit new-prime
cofactord_new. Summing that cofactor inventory once gives the sufficient
criterion

    t_i*(product_(p in Pnew) p/(p-1)-1)<1.             (US13)

The surviving Haar density is at least the oldE23 density times
1 minus the left side. Every source and every deletion still refers to one
actual original family. For the adjacent new primes29 and31, the worst
t=19 gives gate1-19*(59/840)=-281/840; this specific sufficient bound does
not certify that case and does not supply a covering counterexample.

## 7. Relation to existing noncoverage and the unresolved height bridge

The repository already has a seven-prime, arbitrary-height noncoverage
result ([Report 22, SQ8](../../001-064/22-comparing-the-two-killed-steps.md#complete-continuations-and-the-larger-killed-frontier-allowance)). It also cites Schroeder1.0.1 Corollary C.2 for any
family on at most eight odd primes, with arbitrary finite exponents and
uncovered Haar density at least1/1002375; see [the attributed source entry](../../../../../../Library/Arith/schroeder2026nine.md)
and [the existing comparison](../../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md). That external full-height theorem is attributed and has
the local verification boundary recorded there.

Consequently, the present through19/23 statements are NOT first existence
proofs for seven or eight primes. Their contribution is a direct common
finite carrier and stronger explicit density lower bounds under the
declared shallow exponent restriction. No assertion of sharpness or
literature novelty is made.

The nine-prime result has a strict core exponent restriction, while the last
prime may have arbitrary finite height. It is not the unrestricted nine-prime
or general odd covering problem.

The remaining problem is to control the actual higher-power removals on the
core5 through23 axes (and further ternary height) together with subsequent
query/continuation costs on a single supported source. A shallow positive
Haar mass alone does not establish that gate. In particular the through23
theorem cannot be substituted for a complete core-height estimate,
and the negative direct-union short-root through29 entries are not covering
examples; the moment continuation above already overcomes that particular
bound's failure on the same actual family.

The [exact standard-library consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_uniform_shallow.py)
reconstructs these claims under `python3 -I -S -B -O`; its result is
[retained here](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_uniform_shallow.json).

The check covers all91125 original45 assignments, all55440 threshold-one
and square query inequalities, all three complete numerical shallow
inventories, every permitted integerN in each of the18 shape/B combinations,
and the six complete-query moment continuations and geometric-tail gates.
It does not enumerate all
767-label phase assignments; their quantification is handled by the
common-source proofs (US1)–(US13). An independent implementation has
reconstructed the mean and square columns, the complete inventories, and
the moment and full-height-last-prime continuations.
