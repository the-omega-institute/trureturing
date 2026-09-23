# Independent centre choices across ternary and quinary first roots

Let P={3,5,7,11,13,17,19}. Consider a finite original family of congruence
classes with distinct odd numerical moduli m>1 supported on P union{23,29}.
For each later modulus m=d23^j29^k, j+k>0, let d be its P-supported cofactor.
Suppose there are two fixed integer centres a,b such that:

* a and b have different first digits at both3 and5;
* they agree at7,11,13,17,19 through every exponent queried by the original
  later cofactors;
* every complete original later numerical label has old residue a mod d or
  b mod d, independently of other labels, with its choice fixed for the
  entire original family.

Old-only classes,23/29 phases, and all finite heights are arbitrary. No
original shallow anchor or missing pure-power assumption is imposed. The
original survivor set has normalized Haar mass greater than1/80000000000.
In particular the family leaves an integer uncovered.

The new case allows simultaneous disagreements in two old coordinates.
For the seven nonworst completed-source types the argument below also
allows arbitrary disagreement depths at3 and5, including coincident paths.
The remaining worst-source argument requires different first digits at
both coordinates. It does not solve unrestricted Erdős#7.

As in [report484](484-independent-centre-choices-with-one-arbitrary-old-coordinate.md),
any finite set of further support primes greater than10000000000000 may
be added, with arbitrary fixed phases and exponents on all classes touching
them. The centre restriction applies only to the head-only subfamily. The
existing Haar-seed continuation then retains distorted mass greater than
1/125000000000; this last number is not asserted as a Haar bound.

These are ordinary mathematical deductions with an exact rational
certificate. The proof does not claim new Lean certification or literature
priority.

## One complete conditional source and one fixed selector

Use [report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md)'s
fixed-completion conditional source, with completion as in
[report466](466-randomized-completion-retains-full-original-survivor-support.md).
Its external source is Michael Schroeder's *Nine Prime Divisors in Odd
Distinct Covering Systems*, edition1.0.1, with attribution and arbitrary-height
limits recorded in the [library entry](../../../../../Library/Arith/schroeder2026nine.md).
The averaged compactness law from report466 is not substituted for this
conditional process.

Fix one actual complete source nu. Completion retains legal original
selected classes and enlarges the old covered union. All original later
classes, numerical labels and centre choices stay fixed. The source obeys

    nu <= (27/2)H,
    (C7,C11,C13,C17,C19)=(3/2,5/3,3/2,2,9/5),
    m7=7235955529/450000000000,
    m_other=5891133457/225000000000.

The caps hold at every full earlier history of this one process. The mass
is at least m7 on the worst coarse type(2,4,1), and at least m_other on each
of the other seven types. The retained32 source vertices, four per coarse
type, and the inherited same-budget concavity supply these bounds. The
checker verifies their exact arithmetic; construction and interpolation
remain ordinary inherited inputs.

This auxiliary complete source may have countably many pure exclusions.
If an upper comparison retains only finite pure prefixes, the source and
its mass lower bound are unchanged. Only the upper comparison set is
enlarged, and the released mass is explicitly paid. Normalized kernels
extend to added histories by Haar because every cap is at least1; releasing
later deletion indicators is also only an upper comparison. No finite
truncation is asserted to inherit the complete source's mass lower bound.

Extend the common queried prefixes at7,11,13,17,19 to fixed common reference
paths. Extend the required3/5 prefixes of each centre separately. The
original selector for each full label is chosen before any point, fibre,
profile or support is considered. A and B below are global centre labels;
they cannot be exchanged independently at different coordinates or profiles.

## Exact union load and a safe fibre

For an old point x, put

    f3a=v3(x3-a_3)+1, f3b=v3(x3-b_3)+1,
    f5a=v5(x5-a_5)+1, f5b=v5(x5-b_5)+1,
    C=product_(p=7,11,13,17,19)(vp(xp-a_p)+1),
    L=f3a*f5a+f3b*f5b-min(f3a,f3b)*min(f5a,f5b),
    Q=L*C.                                                    (T1)

Here a_p,b_p denote the fixed reference coordinates, and vp denotes the
p-adic valuation; f3a,f3b,f5a,f5b are the four valuation factors.
Outside the null reference paths, Q is exactly the cardinality of the union
of the two matching old numerical-cofactor inventories, including the unit.
The subtraction is their intersection. It is not the product of separate
coordinatewise maxima.

For every fixed new exponent pair(j,k), at most Q old labels can be active,
regardless of their fixed original selector. The original23 and29 axis
complements have masses at least1-Q/22 and1-Q/28 when these are positive;
the cross classes cost at most Q/616. Consequently the actual original
23/29 fibre survivor mass s(x) satisfies

    Q<=19  ==>  s(x)>=(1-19/22)(1-19/28)-19/616=1/77.           (T2)

For the full family, the source support already avoids the original old-only
classes. Integration of s on that support therefore counts genuine original
survivors.

## All disagreement depths on the seven nonworst types

Let h_p be the number of initial digits shared by the two references at p.
Infinite h_p includes coincident paths. Under Haar, the exact joint tail is

    H(vp(x-ap)>=i and vp(x-bp)>=j)
      =p^(-max(i,j)) if min(i,j)<=h_p, and0 otherwise.           (T3)

Finite differences give its positive joint valuation-shell law. For fixed
reference factors at3 and5, the load T1 is increasing separately in each
factor. At each later old prime, the positive factor comparison law is

    Jp(f=1)=1-Cp/p,
    Jp(f=t)=Cp(p-1)/p^t, t>=2.                                (T4)

Reverse conditional integration at every full earlier history bounds the
increasing indicator BAD={Q>=20}. The independent Jp variables belong to
the upper comparison; they assert no independence or Markov property of
the actual source. Write f(L) for the resulting increasing BAD payoff.

At5 the full Haar joint law has mass at least3/5 at factors(1,1), the minimal
payoff pair. Remove pure5 mass1/4 entirely from that baseline. This gives a
positive comparison of total mass3/4 bounding every actual retained pure5
set: deleting mass anywhere costs at least its minimal payoff. The resulting
law is symmetric in the two centres. Let g(a,b) be the payoff after its
integration. It is increasing in each ternary factor and satisfies

    g(a,b)=g(b,a).

If h3>=1, the ternary full Haar joint law has mass2/3 at(1,1). Remove the
pure3 mass1/2 from that baseline, giving a positive comparison of mass1/2.
If h3=0, one ternary factor equals1 and the other is u>=1. Symmetry makes
the payoff g(u,1) increasing in the maximum valuation. On any retained
ternary set of mass1/2 its valuation tail is bounded by

    min(1/2,2/3^j), j>=1.

Thus its positive dominating factor measure is

    mass5/18 at u=2, and mass4/3^u at every u>=3.                (T5)

Tail expansion into nonnegative increments proves this comparison without
moving any original pure class.

For the upper comparison, retain pure3 through H3>=12 and pure5 through
H5>=8. The completed selected pure classes are disjoint, so the released
masses are

    epsilon3=1/(2*3^H3), epsilon5=1/(4*5^H5).

For a payoff in[0,1], the two releases increase the bound by at most
epsilon3+epsilon5. The actual nu lower bound stays fixed.

Saturate every valuation factor at20. This preserves the BAD payoff:
once a factor reaches20 the union inventory already has at least20 labels.
For this saturated law every h_p>=19, including infinity, is identical.
Hence the20 by20 pairs(h3,h5) in{0,...,19}² are exhaustive. Exact
convolution verifies all400 cases. The largest upper occurs at(h3,h5)=(1,0),
and, including the two released tails, is

    B_nonworst=0.024925752107812157... <1/40<m_other.             (T6)

T2 and the density cap give original survivor Haar mass strictly greater than

    (m_other-1/40)/[(27/2)*77]
      =266133457/233887500000000 >1/1000000.                    (T7)

This part covers arbitrary3/5 separation depths for every nonworst type.
Only the worst completed-source type remains below.

## Deleted-root cases reduce within the original finite family

The completed source selects a pure3 root and a pure5 root. Suppose centre a
lies in its selected pure3 root. Add that one class modulo3 to the original
finite family if the original modulus3 is absent. If modulus3 is present,
its selected class is retained by completion, so no duplicate modulus is
introduced.

Every original later class choosing a with3 dividing d is contained in this
added or retained root class and can be removed without changing the augmented
union. Choose an integer a' by finite CRT that agrees with b at3 through
all required original depths and agrees with a at5 through those depths;
at7,11,13,17,19 retain their shared prefixes. Every remaining a-labelled
class has3 not dividing d, so replacing a by a' leaves its residue unchanged.
All b-labelled classes also remain unchanged. Now a',b can differ only at5.
[Report484](484-independent-centre-choices-with-one-arbitrary-old-coordinate.md)
applies to this finite family. Its survivors are contained in the original
survivors.

If either centre lies in the selected pure5 root, exchange3 and5 in this
argument and use
[report483](483-independent-ternary-centre-choices-need-no-anchor-hypothesis.md).
Both reductions retain a strict Haar bound greater than1/80000000000.
They do not replace the finite original family by the auxiliary countable
completion.

It remains to treat the worst source with both centres outside its selected
pure3 and pure5 roots. Because their first digits differ at each coordinate,
the ternary centres then occupy the two surviving roots, and the quinary
centres occupy two distinct surviving roots.

## The normalized six-anchor joint measure

Use report477's simultaneous worst-type normalization, as in report484.
Transport the completed family, both centres and the source together.
Rooted prime-prefix bijections preserve congruence-cylinder lengths,
Haar measure, full-history caps and the fixed global centre choices. The
source avoids the six cylinders

    0 mod3, 1 mod9, 4 mod27, 0 mod5, 1 mod25, 2 mod15.           (T8)

No45 or75 phase is imposed. Release every other initial exclusion only on
the upper side. After one global centre relabeling, A is in ternary root2
and B is in root1. The enlarged initial set is exactly

    A6=(R1 times V5) union(R2 times W5),
    R1={x mod27: x=1 mod3, x!=1 mod9, x!=4 mod27},
    R2={x mod27: x=2 mod3},
    V5={y mod25: y!=0 mod5, y!=1 mod25},
    W5={y in V5: y!=2 mod5}.

The four coordinate masses are5/27,1/3,19/25,14/25, and H(A6)=221/675.
This is a joint initial measure; its3 and5 marginals are not multiplied
as if the mixed exclusion were absent.

There are9 choices for A modulo27,9 for B modulo27,20 nonzero quinary
prefixes for A, and15 prefixes in different nonzero roots for B. Thus there
are24300 ordered shallow configurations. This includes a centre in the
selected class1 mod25 or in the selected ternary classes1 mod9 or4 mod27;
only the deleted first roots were handled separately.

For each configuration, partition A6 into the six regions AA,AB,AO,BA,BB,BO.
The first letter is the matching ternary centre and the second the matching
quinary centre; O means neither quinary root. There is no surviving ternary
O region. Let u>=2 be the matching ternary valuation factor and v>=2 the
quinary factor, with v=1 in an O region. The initial union load is

    L=uv on AA,BB; L=u+v-1 on AB,BA; L=u on AO,BO.              (T9)

In every residue cell not containing a reference, the valuation is fixed.
A cell containing the reference contributes all geometric shells: at p,
factor t has mass(p-1)/p^t beyond the cell depth. The reference's unqueried
deep digits do not change these masses. Explicitly enumerating the24300
configurations produces44 complete initial weight classes.

## Same-selector pair constraints

At a profile x write its two local centre factor pairs as A_x and B_x.
For example region AB has A_x=(u,1), B_x=(1,v). Let f be its five common
later factors, and let Q_x be T9 times product(f). For a second profile y
write A_y,B_y,g,Q_y. Put

    I=product_i min(f_i,g_i),
    D=I*(product_i min((A_x)_i,(B_y)_i)
         +product_i min((B_x)_i,(A_y)_i)-2),
    N=Q_x+Q_y-D.                                              (T10)

In report481's literal notation this is exactly

    N=sum_d max(A_d(x)+A_d(y), B_d(x)+B_d(y)),

on the union of the matching numerical-cofactor inventories. The cross-centre
intersection A_x with B_y contains I compatible labels having both the3 and5
exponents zero. Every other label in that intersection demands opposite
centre choices at x and y. The other cross-centre intersection has the same
compatible core of size I; its remaining conflict labels are disjoint from
the first conflict set. These assertions use distinct first roots at both3
and5. Thus T10 subtracts the two disjoint conflict counts from Q_x+Q_y.
One full original later label cannot activate both conflicting choices.
Hence N bounds the sum of active inventories at each fixed new exponent
pair. It satisfies max(Q_x,Q_y)+1<=N<=Q_x+Q_y; the unit accounts for the extra1.

Apply [report481](481-individual-mixed-budgets-strengthen-two-fibre-certificates.md)'s
individual axis and mixed-budget optimization K(Q_x,Q_y,N). Its exact
rectangle-boundary computation has at most28 rational candidates and gives

    s(x)+s(y)>=K(Q_x,Q_y,N)/616.                               (T11)

The checker imports the existing canonical implementation and recomputes K
for every used edge. It does not trust a producer's graph or stored edge
strengths.

## Upward closure supplies the product comparison

Order profiles only by increasing their five common later valuations,
keeping the full3/5 profile fixed. This enlarges each matching cofactor
inventory and increases Q_x,Q_y,N. In its unsaturated capacity formulation,
report481's feasible set can only enlarge, while its minimized objective
is unchanged. Thus K is nonincreasing in each capacity. This antitonicity
is a property of the same optimizer used in T11.

Set kappa=1/3, theta=kappa/1232=1/3696, and let

    T={x on the actual old live set: s(x)<theta}.

T2 excludes every Q<=19 point. T11 excludes every actual pair with K>=kappa,
because their survivor masses would sum to less than K/616. This exclusion
holds for the entire theoretical threshold graph, not only the sparse
edges stored in a certificate.

Take the upward closure U of T's full profile support in the five common
coordinates. An edge between two raised profiles would imply an edge between
their ancestors by antitonicity. When those ancestors are the same profile,
the matching inventories agree and N=2Q, while K(Q,Q,2Q)=0 for Q>=20, so
this case also creates no edge. The diagonal identity has a direct zero
witness at Q=20 and follows at larger Q by capacity monotonicity.

All Q>=39 profiles may be added freely. At either such endpoint and any
other Q>=20 endpoint, the unit-label inequality gives N>=max(Q_x,Q_y)+1.
The exact zero witness K(20,39,40)=0 and antitonicity therefore give K=0.
Call this enlarged upward support U*. It still has no threshold edge and
contains no Q<20 point. Infinite valuations are Haar-null and source-null
under the density cap.

For any bounded increasing function h of one common valuation, a normalized
conditional kernel with density at most Cp satisfies, at every full history,

    E_K h <= h(0)+Cp E_H[h-h(0)] = E_Jp h.                     (T12)

The Jp in T12 is exactly T4, whose baseline is positive. Reverse integration
against these fixed future laws preserves monotonicity, so

    nu(T) <= (H restricted to A6 tensor J7 tensor J11 tensor J13
              tensor J17 tensor J19)(U*).                    (T13)

The conditional process need not be independent or determined by its current
profile. T13 is justified by the upward envelope under the full theoretical
graph. No monotonicity of T itself, or closure property of an arbitrary
sparse graph, is assumed.

## Three finite dual certificates cover every weight class

Keep precisely the full profiles with20<=Q<=38. Reconstructing T9 and the
five later factors gives7040 profiles. For each of the44 initial weight
classes, let w_v be its exact comparison mass at profile v. Pay every omitted
Q>=39 point with payoff1, assigning

    w_overflow=221/675-comparison_mass(Q<39).                  (T14)

Every initial low-load pattern is included before later convolution. Thus
T14 includes all initial and later geometric tails; no high factor is lost.
The checker verifies

    sum_v w_v+w_overflow=comparison_mass(Q>=20).

Let nonnegative lambda_e weight any collection of certified threshold edges,
and let c_v be the sum of incident edge weights. The indicator z_v of U*
satisfies z_i+z_j<=1 on each such edge. Its vertex boxes give

    nu(T) <= w_overflow+sum_e lambda_e
               +sum_v max(0,w_v-c_v).                        (T15)

This is an upper certificate. It asserts neither optimality of the dual nor
realizability of every independent profile support.

The retained family has three certificates, with3956,1196 and3658 positive
edge occurrences respectively. There are3956 distinct used edges, and every
one has K>=1/3. Their exact minima are1/3,8/15,1/3. For each of the44 classes,
the checker recalculates all weights, its complete overflow, each dual's
unpaid vertex mass in T15, and the least of the three resulting upper bounds.
It verifies all24300 configurations are accounted for and obtains

    U=max_(44 classes) min_(three certificates)(T15)
      =0.016012094340856237... < m7.                           (T16)

The exact rational values and all class cases are retained in the result
file. A dual is only selected after its value has been recalculated for the
actual weight class. An upper bound computed with one reference's weights
is never transferred unchanged to another reference.

On the actual same-source complement of T, s>=theta. Consequently

    H(original survivors)>=(m7-U)*theta/(27/2)
      =(m7-U)/49896
      =0.0000000013589633377288445... >1/800000000.             (T17)

The seven nonworst routes have the larger bound T7. The deleted-root routes
inherit the strict1/80000000000 bound. Their minimum proves the opening
no-anchor claim for simultaneous different first digits at3 and5. Positive
Haar mass yields a nonempty residue cell in the original finite CRT period,
hence an uncovered integer.

The optional large-prime continuation uses this same1/80000000000 Haar seed
and precisely report483's retained Chapter33 arithmetic with
M2=14003665/540672, B=10000000000000 and ell=27. Every tail-touching class keeps
its original full label and is assigned once to its last exposed outside
prime. Its surviving distorted mass exceeds1/125000000000.

## Verification and remaining boundary

The [standalone checker](../../frontier/cover-geometry/two_coordinate_first_root_centres.py)
reads the [three dual certificates](../../frontier/cover-geometry/two_coordinate_first_root_centres_certificate.json)
and reconstructs the [exact result](../../frontier/cover-geometry/two_coordinate_first_root_centres.json).
Run from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_coordinate_first_root_centres.py
```

Default execution compares the adjacent retained result without writing it;
`--output PATH` writes a reconstruction. Only the standard library and the
existing canonical pair/source verifier are imported. The checks reconstruct
7040 profiles,24300 configurations and44 weight classes; certify all3956
used edges and all geometric tails; check400 nonworst depth pairs and the
32 retained source vertices; and verify the numerical Haar conversions.

The fixed complete source, its normalization and interpolation, report481's
pair theorem and antitonicity, the upward-support and full-history arguments,
the finite deleted-root reduction and inherited large-prime continuation
remain ordinary mathematical deductions or inputs. Source producers and Lean
are not rerun. Worst-source shared first roots at either3 or5, simultaneous
arbitrary splits of more old coordinates, unrelated old residues and arbitrary
growing small-prime cores are outside the theorem. Unrestricted Erdős#7
remains unresolved.
