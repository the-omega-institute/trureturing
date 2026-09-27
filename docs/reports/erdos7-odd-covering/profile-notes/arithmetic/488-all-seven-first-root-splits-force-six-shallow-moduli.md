# All seven first-root splits force six shallow moduli

This is an ordinary exact-comparison result, not a new Lean theorem. Consider
one finite original family of pairwise distinct odd numerical moduli greater
than one, supported on
P union{23,29}, P={3,5,7,11,13,17,19}. Each complete original later label
m=d23^j29^k, j+k>0, fixes its old residue to one of two global centres A,B.
Assume A and B differ in their first digit at every p in P. All original
old-only classes, new-coordinate phases and finite heights remain arbitrary.

If any of the six numerical moduli

    3,5,9,15,25,27

is absent from the original family, its original survivor set has normalized
Haar mass strictly greater than1/400000. In particular it cannot cover the
integers. Thus any cover in this all-seven-first-root class would have to
contain all six shallow moduli. Their presence is only a necessary condition,
not evidence that they can be extended to a cover.

More strongly, the same survivor bound holds unless a simultaneous
Haar-preserving prime-prefix relabeling takes those six original classes to

    0 mod3, 1 mod9, 4 mod27, 0 mod5, 1 mod25, 2 mod15.

Thus a possible cover in this restricted family must have this actual shallow
layout, not merely contain the six numerical labels.

The more general sufficient condition is that the old-only family admit a
legal source completion of any coarse type other than(2,4,1). For each of the
seven other types the exact scalar comparison below gives the same bound,
using that actual source's geometry and lower mass. A missing shallow modulus
allows the completion to be chosen in one of these types before the source is
constructed. The worst type(2,4,1) remains unresolved by this result.

Arbitrary original classes touching any finite set of further support primes
greater than100000000 may also be included. Only the head-only subfamily must
satisfy the centre condition and the missing-label or nonworst-completion
condition, or fail the necessary original shallow layout just displayed.
The inherited continuation retains distorted mass greater
than1/500000; this is not a Haar lower bound of that size.

The source is Michael Schroeder's *Nine Prime Divisors in Odd Distinct
Covering Systems*, edition1.0.1, with the attribution, archive identity and
arbitrary-height verification boundary retained in the
[library entry](../../../../../Library/Arith/schroeder2026nine.md).
The source mass and caps are those of
[report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md).
These are ordinary mathematical deductions with exact rational checks,
not new Lean certification, a literature-priority claim, or an unrestricted
Erdos#7 settlement. Arbitrary centre separation patterns and independently
unrelated later old residues are outside the statement.

## Source normalization and the eight different anchor measures

[Report477](477-two-arbitrary-centers-share-a-positive-original-fibre.md),
“Keep the source geometry attached to its own mass lower bound”,
specifies the eight coarse triples

    alpha in{1,2}, beta in{2,4}, gamma in{1,2}.

Alpha is the selected15 residue; beta is the selected27 residue. Gamma is
initially only the first digit of the selected25 class. A permutation of
second-digit children in that quinary root puts its second digit at0,
producing gamma mod25. This preserves the5 and15 anchors and transports
both centres, the source and every original query simultaneously.

After this same normalization, the actual source avoids

    0 mod3, 1 mod9, beta mod27,
    0 mod5, gamma mod25, alpha mod15.                          (N1)

The centres keep one global A/B labeling. For references outside the deleted
first roots, globally label A as ternary root2 and B as root1. At5 their
first digits are distinct and nonzero. Let

    R_r={x mod27:x=r mod3,x!=1 mod9,x!=beta mod27}, r=1,2,
    V_r={y mod25:y!=0 mod5,y!=gamma mod25,
                         and not(r=alpha and y=alpha mod5)}.

The exact enlarged initial anchor is

    (R_1 times V_1) union(R_2 times V_2).                      (N2)

The checker compares N2 with the literal complement of N1 at every residue
mod675. It does not reuse the worst-type rectangle masses. For example,
beta=2 deletes a cell in ternary root2, whereas beta=4 deletes one in root1.
The position of the mixed alpha cylinder and its intersection with the gamma
pure25 cylinder also remain attached to the same coarse type.

The source is report467's one fixed complete conditional process, retaining
its attribution and source-construction assumptions. It has Haar density at
most27/2 and full-history caps

    (C7,C11,C13,C17,C19)=(3/2,5/3,3/2,2,9/5).

The live lower mass for each type is its own minimum over the four retained
vertices of the continuous pure5 budget, with the existing same-budget concavity.
Across the seven nonworst types the common minimum is

    m_other=5891133457/225000000000.

The checker verifies all32 vertices and each coarse minimum. The source is
unchanged when further exclusions are released on the upper side. No finite
truncation is given a complete-source lower bound.

## Exact scalar union load under seven different first digits

Outside the union of the null sets x_p=A_p or x_p=B_p, let

    A_x=product_(p in P)(vp(x_p-A_p)+1),
    B_x=product_(p in P)(vp(x_p-B_p)+1).

Because the reference first digits differ at every old prime, their matching
old divisor inventories intersect only in the unit label. Their union has
exactly

    Q=A_x+B_x-1.                                             (N3)

The exceptional reference paths are Haar null and also nu-null by the
density bound. Assign them to BAD; they change neither mass comparison.

Every fixed new exponent pair has at most Q active old numerical labels,
whatever their original fixed centre choices. Thus Q<=19 gives actual original
23/29 fibre survivor mass at least

    (1-19/22)(1-19/28)-19/616=1/77.                            (N4)

At each p>=7 the paired Haar factor law has baseline(1,1) of mass1-2/p,
and factors(f,1),(1,f), f>=2, each of mass(p-1)/p^f. A conditional density
cap Cp gives the positive probability comparison

    Jp(1,1)=1-2Cp/p,
    Jp(f,1)=Jp(1,f)=Cp(p-1)/p^f, f>=2.                       (N5)

Every displayed baseline is nonnegative. The BAD indicator1_(A+B-1>=20)
is increasing in both loads, and reverse conditional integration preserves
that monotonicity. Hence N5 bounds the actual normalized kernels at every
complete earlier history. The auxiliary product laws assert no independence
or Markov property of the actual source.

For fixed initial loads a,b, compute the exact probability of remaining GOOD
by recursively retaining only states a+b<=20. A local A-axis factor f sends
(a,b) to(af,b), and a B-axis factor sends it to(a,bf). Every omitted larger
factor is BAD. Subtracting the resulting total GOOD mass from the full initial
anchor mass retains all infinite geometric tails. The checker also computes
the separate Q>=39 overflow by the analogous threshold39 calculation.

At3, A and B have9 prefixes each modulo27. At5, A has20 nonzero prefixes
mod25 and B has15 prefixes in a different nonzero root. Each coarse type
therefore requires24300 ordered configurations. Exact geometric distributions
inside reference cells, and constant valuations in other cells, reduce these
to the weight-class counts below. Unqueried deeper reference digits do not
change any shell mass.

| Coarse type | Exact weight classes | Largest BAD20 | Own source mass lower |
| --- | ---: | ---: | ---: |
| (1,2,1) | 30 | 0.023454302572852703... | 0.039481775677777775... |
| (1,2,2) | 66 | 0.023219951596186710... | 0.030641777132592590... |
| (1,4,1) | 20 | 0.023498356174161007... | 0.033549480819259260... |
| (1,4,2) | 44 | 0.023275018597822092... | 0.026182815364444445... |
| (2,2,1) | 66 | 0.023109817592915947... | 0.027260955396296298... |
| (2,2,2) | 30 | 0.023366195370236090... | 0.038631145244444440... |
| (2,4,2) | 20 | 0.023322141768927787... | 0.026414132397777780... |

All276 nonworst weight classes, covering170100 configurations, satisfy the
single strict rational bound

    nu(BAD20)<47/2000<m_other.                                (N6)

The largest value belongs to type(1,4,1), not the type attaining m_other.
N6 is a uniform bound for every type, so combining it with the common minimum
is legitimate. Alternatively the retained data pair each class with its own
source mass before taking any minimum.

N4, N6 and the density cap give

    H(original survivors)>(m_other-47/2000)/[(27/2)*77]
      =86233351/33412500000000 >1/400000.                      (N7)

The full fractions are retained and verified. No finite pure-tail fee is
needed here: N2 is a literal finite upper anchor, no deeper pure exclusion
is credited, and all large valuation tails are included in BAD20.

For comparison, the independently reconstructed worst type(2,4,1) has44
classes and maximum BAD20=0.023054750591280565..., exceeding its own m7.
Twenty-three of its44 scalar classes fail. Those exact44 BAD20 and overflow
values match the separate all-first-split comparison calculation. This is a
limit of the scalar argument, not a covering counterexample.

## Finite deleted-root reduction preserving all seven first-root splits

The surviving-root enumeration above does not include a centre in the selected
pure3 or pure5 first root. Those positions admit a finite reduction that retains
the seven-coordinate first-root hypothesis; the two centres must not be merged.

Work with the same fixed completed old family and its selected roots C_p,
p=3,5. If a centre lies in C_p, add C_p to the original finite family only if
the original numerical modulus p is absent. If p is already present, its
selected class is retained by completion, so no duplicate modulus is introduced.
Do this for each required one of3 and5.

Because the two centres have different first digits, at most one lies in C_p.
Delete every later class whose original selector chooses that centre and whose
old cofactor is divisible by p. Such a class is entirely contained in C_p, so
it is redundant in the augmented finite union. All remaining labels choosing
that centre are p-free.

Now replace that centre's unused p-coordinate by a first digit which is both
outside C_p and different from the other centre's first digit. Such a digit
exists: at3 the two surviving roots contain exactly one choice different from
the other centre; at5 there are at least three choices. Keep every other old
coordinate fixed through all original queried depths, and through at least
one digit even if no original cofactor queries it. Finite CRT produces fixed
integer centres satisfying these prescriptions simultaneously. At a modified
coordinate every remaining label using the changed centre is p-free, so all
its actual old residues are unchanged.

If changes are needed at both3 and5, carry out the two deletions before choosing
the final CRT representatives. Any label affected by either coordinate is
already removed; all remaining labels keep exactly their original residues and
fixed A/B choices. The two final centres still differ in the first digit at
all seven old primes. At3 and5 both now lie outside the corresponding selected
root. One global exchange of A and B can orient them as ternary root2/root1.

The augmented family is finite and has distinct numerical moduli. Its covered
union contains the original union, and removing redundant later classes does
not change that augmented union. Its survivors are therefore contained in the
original survivors.

The complete old family used to construct nu already contains every added
selected root. It remains a completion of the augmented old-only family, so
the same source, coarse type, caps and lower mass can be retained. The later
label deletions do not alter that old source. On its support the deleted classes
were already inactive. Consequently this reduction does not choose a new
favourable source type or transfer a lower bound to another law.

Thus N7 also applies to deleted3/5-root positions on any of the seven nonworst
types. The same finite reduction is available to a separately established
worst-type all-first-split theorem. It does not reduce the problem to one varying
coordinate and does not replace the finite original family by the countable
auxiliary completion.

## Choosing a nonworst completion from a missing original modulus

The pinned source's Lemma2.2 processes the selected moduli in increasing
numerical order. At modulus m, a missing class may be inserted at any residue
avoiding the already fixed selected proper-divisor classes. An existing class
is retained if disjoint from them. Otherwise it is contained in one such
smaller class and may be moved to any free residue without losing covered
points. Every smaller selected class is thereafter permanent.

Only the old-only family is completed. No later original class, its full
numerical label, residue or A/B selector is changed in this construction.
The source's selected set consists of pure powers and
15,21,35,45,63,75,105,165. Consequently the selected proper divisors relevant
to9,15,25,27 are respectively {3},{3,5},{5},{3,9}. Classes such as21 are not
additional forbidden choices when processing25 or27.

In the source's normalization, alpha=1 means that selected15 and selected9
have the same ternary first digit. Beta=2 means that selected27 has the other
surviving ternary first digit from selected9. Gamma=alpha means that selected25
and selected15 have the same quinary first digit. Each condition excludes
the worst triple(2,4,1).

If15 is missing, choose its ternary digit to match selected9 and its quinary
digit to avoid selected5. Since selected9 already avoids selected3, CRT
provides a free15 residue and alpha=1.

If27 is missing, choose its ternary first digit different from those of
selected3 and selected9. This avoids both proper-divisor classes and gives
beta=2.

If25 is missing, selected15 is already fixed and avoids selected5. Choose25
in selected15's quinary root. Then gamma=alpha: for alpha=1 the source is
already nonworst, and for alpha=2 it has gamma=2.

For the other three cases, suppose15 is present, since its absence was just
handled. If3 is missing, insert selected3 at the ternary first digit of the
original15 class. That original15 class is contained in the permanent3
class. At the later15 step it can be moved to a free class whose ternary
digit is that of selected9, giving alpha=1. If5 is missing, insert selected5
at the quinary first digit of the original15 class and make the same free
choice at15. The choice of a surviving quinary digit remains available.

If9 is missing, selected3 and selected5 are already fixed. If the original15
class is contained in either, it can later be moved, so choose any legal9
and then choose15 with alpha=1. Otherwise choose selected9 in the original15
ternary root. That root avoids selected3; every depth-two cylinder in it is
free. The original15 is retained at its later step and has alpha=1.

These choices specify one legal completed old family before constructing nu.
Continue the remaining selected moduli using Lemma2.2. Future choices cannot
alter the six already selected shallow classes. Apply the source construction
and its own nonworst lower mass, then the preceding finite deleted-root
reduction if needed. Completion preserves inclusion of the original old
covered set; prime-tree normalization transports both centres and every
original query together, preserving all seven first-root differences.
No bound is transferred from a previously chosen worst source to another law.
This proves the opening missing-modulus assertion.

## The necessary layout of the six original classes

The same free choices apply to a present shallow class when it is redundant
under the selected proper divisors: move15 to force alpha=1, move27 to force
beta=2, or move25 into selected15's quinary root to force gamma=alpha.
If original9 is contained in selected3, it too may be moved at step9. If
original15 is already contained in selected3 or5, move15 as above; otherwise
choose the replacement9 in original15's surviving ternary root, giving
alpha=1 when original15 is retained.

Consequently, if no nonworst completion is available, all six original labels
are present and their actual classes are retained:9 avoids3,15 avoids3 and5,
25 avoids5, and27 avoids3 and9. Their normalized coarse type must be(2,4,1).
The15-root differs from the9-root at3; the27-root equals the9-root at3 but
uses a different mod9 child; and the25-root differs from both the5-root and
the15-root at5. Simultaneous prefix permutations therefore carry the six
original classes to

    0 mod3, 1 mod9, 4 mod27, 0 mod5, 1 mod25, 2 mod15.

The additional second-digit permutation at5 makes the25-class exactly1 mod25
without moving the5- or15-class. Every original query and both centres move
under the same relabeling. If the actual layout cannot be put in this form,
the preceding alternatives construct a nonworst completion before choosing
its source, so N7 applies. Presence of this layout is still only a necessary
condition for a cover; the scalar comparison proves no cover exists in the
complement, not that the remaining layout covers.

## Arbitrarily many further large primes

Use unnormalized Haar restricted to the actual head survivors as seed, with
mass greater than1/400000 and density at most one. Apply
[Chapter33](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md)'s
analytic tail estimate with

    B=100000000, ell=16, c=(2ell^2+1)/(2ell^2-1)=513/511,
    M2=product_(p in P union{23,29}) p(p+1)/(p-1)^2,
    tau=c^7/B * [B/(B-3)]^2
              * sum_(j=0,...,7) 7!/[(7-j)! ell^j].

The exact rational consumer gives

    1/400000-M2*tau=0.000002055904911868467...>1/500000.       (N8)

The number of further primes, their finite exponents, phases and simultaneous
occurrences in original moduli are unrestricted. Each tail-touching numerical
label is charged once at its last exposed further prime. The head centre
condition is not imposed on these tail classes. Positive distorted mass on
the finite original CRT carrier gives an uncovered integer. Chapter33's
analytic prime-product estimate remains an ordinary input, not a consequence
of this numerical evaluation.

## Exact artifacts and remaining boundary

The [consumer](../../frontier/cover-geometry/all_first_root_source_types.py)
reconstructs all eight literal anchors and their
194400 shallow configurations, giving320 exact weight classes. It uses only
the standard library and the canonical source-identity verifier. It checks both
geometric tails in N5, every initial shell mass,32 source vertices, all276
nonworst inequalities, the strict conversion N7 and the tail reserve N8.
Default execution compares the adjacent
[result data](../../frontier/cover-geometry/all_first_root_source_types.json);
`--output` writes a reconstruction. Checks use explicit exceptions and remain
active under Python optimization; neither an optimizer nor a scratch producer
is imported.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/all_first_root_source_types.py

The source construction, coarse normalization and interpolation, full-history
conditional comparison, selectable completion, finite deleted-root reduction
and analytic tail estimate are ordinary arguments or inherited inputs.
Source producers and Lean are not rerun. The scalar bound
does not settle the worst coarse type, arbitrary later separation patterns or
unrestricted Erdős#7.
