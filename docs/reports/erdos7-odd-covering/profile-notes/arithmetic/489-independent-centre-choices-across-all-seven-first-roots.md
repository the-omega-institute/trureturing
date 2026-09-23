# Independent centre choices across all seven first roots

Let P={3,5,7,11,13,17,19}. Consider any finite original congruence family
with pairwise distinct odd numerical moduli greater than one, supported on
P union{23,29}. Fix two integer centres A,B with different first digits at
every p in P. For each complete original later label m=d23^j29^k, j+k>0,
its original old residue is A mod d or B mod d. Each full label chooses
independently, with its choice fixed for the entire family. Old-only classes,
new-coordinate phases and all finite heights are arbitrary.

The original survivor set has normalized Haar mass strictly greater than

    1/1000000000.

In particular the family leaves an integer uncovered. No shallow original
anchor, missing-modulus assumption or agreement at any of the seven old
coordinates is required. The first digits must differ at all seven; arbitrary
separation depths and unrelated old residues remain outside this statement.

Any finite set of further support primes greater than100000000000 may also
be included. Only the head-only subfamily must satisfy the centre condition.
Every tail-touching original class has arbitrary phases, finite heights and
joint support. The continuation retains distorted mass greater
than1/2000000000, not a Haar lower bound of that size.

These are ordinary mathematical deductions with exact rational certificates,
not new Lean certification, a literature-priority claim or a resolution of
unrestricted Erdős#7. The external source is Michael Schroeder's *Nine Prime
Divisors in Odd Distinct Covering Systems*, edition1.0.1; its attribution,
archive identity and arbitrary-height verification boundary are retained in
the [library entry](../../../../../Library/Arith/schroeder2026nine.md).

## The same actual source and the remaining worst chart

Use the fixed-completion conditional source of
[report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md).
Completion enlarges only the old covered union; every original later label,
residue and centre selector stays fixed. The source is not the averaged
full-support compactness law. Its normalized conditional kernels satisfy the
full-history density caps

    (C7,C11,C13,C17,C19)=(3/2,5/3,3/2,2,9/5),
    nu <= (27/2)H_old.

The eight coarse types and their own mass lower bounds are those checked in
[report488](488-all-seven-first-root-splits-force-six-shallow-moduli.md).
Its seven nonworst types already retain original Haar mass greater
than1/400000. It also supplies a finite deleted-root reduction preserving
all seven first-root differences: add an already source-excluded3/5 class
if its numerical label is absent, remove contained later classes, and move
only the now-unused centre coordinate to the other surviving root. All
remaining original full-label residues and selectors are unchanged, the
same completed source is retained, and the repaired survivors are contained
in the original survivors.

It remains to consider the worst source type(2,4,1), with both centres outside
the selected deleted3/5 roots. Its live mass lower bound is

    m7=7235955529/450000000000.

Simultaneously normalize the actual source, original family and both centres.
One global A/B exchange puts A in ternary root2 and B in root1. The source
avoids

    0 mod3, 1 mod9, 4 mod27, 0 mod5, 1 mod25, 2 mod15.

The enlarged initial joint Haar chart A6 is their literal complement modulo675:

    A6=(R1 times V5) union(R2 times W5),
    R1={x mod27:x=1 mod3,x!=1 mod9,x!=4 mod27},
    R2={x mod27:x=2 mod3},
    V5={y mod25:y!=0 mod5,y!=1 mod25},
    W5={y in V5:y!=2 mod5},
    H(A6)=221/675.                                             (F1)

This is one joint3/5 measure; multiplying its separate marginals would be
incorrect. Releasing further exclusions only enlarges the upper comparison.
The complete source and its lower mass are unchanged. On newly admitted
histories normalized kernels can be extended by Haar since every Cp>=1.
No finite truncation is given the complete source's lower bound.

## Complete inventories and the fixed original selector

Extend the two centres to fixed reference paths. Away from the Haar-null
reference equalities, the local valuation-factor pair is

    (1,1), (f,1), or(1,f), f>=2.

The null sets are also nu-null by the density bound and may be assigned to
the upper exceptional set. At an old point x let A_x,B_x be the two boxes
of matching old numerical cofactors. Their coordinate lengths are
vp(x_p-A_p)+1 and vp(x_p-B_p)+1. Because the first digits differ everywhere,
their intersection consists only of the unit label. Put

    Q_x=|A_x|+|B_x|-1.                                        (F2)

For each fixed new exponent pair(j,k), at most Q_x old labels can be active.
The actual original23/29 fibre survivor mass s(x) therefore satisfies

    Q_x<=19 ==> s(x)>=(1-19/22)(1-19/28)-19/616=1/77.          (F3)

For two points let c_xy=|A_x intersection B_y| and
d_xy=|B_x intersection A_y|. Each is a product of coordinatewise minima of
the corresponding box lengths. The common-selector capacity is

    N_xy=sum_d max(1_Ax(d)+1_Ay(d),1_Bx(d)+1_By(d))
        =Q_x+Q_y+2-c_xy-d_xy,
    max(Q_x,Q_y)+1<=N_xy<=Q_x+Q_y.                            (F4)

Indeed, every nonunit label in either cross-centre intersection would need
opposite selectors to be active at both points. These two conflict sets are
disjoint; belonging to both would put a nonunit in A_x intersection B_x.
The unit contributes no conflict. One fixed original full label cannot
choose differently at x and y. This proves F4 without changing any selector.

[Report481](481-individual-mixed-budgets-strengthen-two-fibre-certificates.md)'s
individual axis and mixed-budget optimization consequently gives

    s(x)+s(y)>=K(Q_x,Q_y,N_xy)/616.                            (F5)

The same rectangle-boundary minimization has at most28 rational candidates.
Increasing any capacity enlarges its unsaturated feasible set while leaving
the minimized objective unchanged; hence K is antitone in all capacities.
The consumer recomputes this exact K for every used edge. The ordinary
pair-fibre theorem and its boundary-minimum proof are inherited inputs.

## Full theoretical closure before sparse certification

Set kappa=1/3, theta=kappa/1232=1/3696, and let

    T={x on the actual live old set:s(x)<theta}.

F3 excludes Q<20 from T. F5 excludes every pair with K>=kappa. These are
constraints under the complete theoretical relation, before any sparse
certificate is selected.

Keep the full3/5 profile fixed. At each other old prime, order the feasible
paired factors componentwise: the A and B branches are incomparable and
both lie above(1,1). Raising a profile enlarges both labelled boxes, so its
Q and every literal N are nondecreasing. Take the upward closure of T's
attained profile support in these five coordinates. A threshold edge between
two raised profiles would, by antitonicity, imply an edge between ancestors
in T. Equal ancestors are no exception: identical inventories give N=2Q
and K(Q,Q,2Q)=0 for Q>=20, starting from K(20,20,40)=0.

Add all Q>=39 profiles. F4 and the zero witness K(20,39,40)=0 show that
they have K=0 against every Q>=20 profile. The resulting U* is upward,
contains T's profiles and all overflow, contains no Q<20 profile, and is
independent for every theoretical edge K>=kappa. Both base zero witnesses
are checked exactly. T itself need not be upward, and no closure property
of a sparse graph is asserted.

For p>=7 define the positive auxiliary probability law

    Jp(1,1)=1-2Cp/p,
    Jp(f,1)=Jp(1,f)=Cp(p-1)/p^f, f>=2.                       (F6)

Its five baselines are4/7,23/33,10/13,13/17,77/95. For an increasing
bounded local payoff h, h0=h(1,1) is minimal, so every actual normalized
full-history kernel satisfies

    E_actual h <= h0+Cp E_H(h-h0)=E_Jp h.

Reverse conditional integration against these fixed future laws preserves
monotonicity in remaining paired coordinates. Release the extra deletion
indicators only on the upper side and enlarge the initial set to F1. Thus

    nu(T)<=eta(U*),
    eta=(H restricted to A6) tensor J7 tensor J11 tensor J13
          tensor J17 tensor J19.                            (F7)

Independence belongs only to this auxiliary comparison measure. Neither
independence of the actual source nor realizability of arbitrary independent
profile supports is assumed.

## Four rational certificates cover all44 reference weight classes

The ternary centres have9 prefixes each modulo27; at5 they have20 and15
prefixes modulo25 in distinct nonzero roots. The24300 ordered configurations
give44 exact joint-shell weight classes. Report488's literal anchor and
complete shell reconstruction supply the representatives and multiplicities.
Deeper digits inside a reference cell have the same geometric shell law.

A signed profile entry0 denotes(1,1), +f denotes(f,1), and -f denotes(1,f).
The ternary entry is nonzero. Retain every full profile with20<=Q<=38:
there are577578. The consumer reconstructs all of them, including profiles
of zero weight in a particular certificate's original class.

For any reference class let w_i be its exact eta weight and
BAD20=eta(Q>=20). This is computed as221/675 minus the full mass with Q<20.
All omitted Q>=39 mass is thereby paid in full, including both initial
and later infinite geometric tails.

Take any nonnegative rational weights lambda_e on certified edges K>=kappa.
Write B=sum_e lambda_e and c_i=sum_(e incident i)lambda_e. Every independent
profile indicator t satisfies sum_i c_i t_i<=B. Therefore

    eta(U*) <= BAD20-B+sum_i(c_i-w_i)_+.                      (F8)

This follows by w_i<=c_i+(w_i-c_i)_+ and
B+sum_i(w_i-c_i)_+=sum_i w_i-B+sum_i(c_i-w_i)_+.
The deficit pays for transferring a certificate to another reference class;
no transferred capacity-feasibility assumption is needed.

With D=10^13, edge units u_e have denominator2D. Replacing each w_i by
floor(D*w_i)/D only increases the deficit, yielding the rational upper bound

    Uhat=BAD20-[sum_e u_e
             -sum_i max(sum_(e incident i)u_e-2floor(D*w_i),0)]/(2D). (F9)

Four fixed certificates suffice:

| Original reference(A3,B3,A5,B5) | Positive edge rows | Sum of integer edge units |
| --- | ---: | ---: |
| (2,7,3,4) | 390215 | 143214996271 |
| (2,7,3,2) | 251397 | 125584078184 |
| (2,7,6,2) | 262766 | 122423306024 |
| (2,13,3,2) | 236498 | 108538255236 |

All used edges have literal K>=1/3. Each certificate also satisfies exact
vertex capacities in its original reference class. For each of the44 classes,
recompute all four F9 bounds with that class's own weights and take the least.
The selected certificate counts are21,4,8,11. This selection is made for the
whole reference class after evaluating its full comparison law; it does not
vary the original centres, residues or selectors at individual points.

Every class passes. The greatest selected upper, at reference(2,13,3,4), is

    Umax=0.01602145846104644...<m7,
    m7-Umax=0.00005844271450911529... .                       (F10)

The retained result stores all176 exact bounds, all44 multiplicities and
the full rational Umax. There is no floating tolerance or claimed optimality
of the sparse graph. A larger graph or a different valid certificate may
improve the bound without changing its proof obligation.

## Original survivors and the unrestricted large-prime tail

At least m7-Umax actual old live mass has s>=theta. Since the source support
avoids every original old-only class and nu<=(27/2)H_old, integration gives

    H(original survivors)>=(m7-Umax)*theta/(27/2)
      =(m7-Umax)/49896
      =1.171290574577427e-9... >1/1000000000.                 (F11)

The seven nonworst types in report488 have the larger bound1/400000. Its
same-source third-root reduction preserves the present all-seven hypothesis
and sends survivors into the original survivor set. F11 therefore holds
without a shallow-label or deleted-root restriction. The original family is
finite, so positive Haar mass gives a nonempty cell in its finite CRT period
and hence an uncovered integer.

For further primes use Haar restricted to the complete original head survivor
set as a seed, of mass greater than10^-9 and density at most one. Uniformly
resolve head heights queried by tail originals; do not add their head
projections as forbidden head classes. Apply
[Chapter33](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md)
with

    B=100000000000, ell=23, 3^ell=94143178827<=B,
    c=(2ell^2+1)/(2ell^2-1)=1059/1057,
    M2=product_(p in P union{23,29})p(p+1)/(p-1)^2=14003665/540672,
    tau7=c^7/B * [B/(B-3)]^2
          * sum_(j=0,...,7)7!/[(7-j)!ell^j].

The exact arithmetic gives

    M2*tau7=3.6859988519294195e-10...,
    1/1000000000-M2*tau7=6.314001148070581e-10...
      >1/2000000000.                                        (F12)

Every original tail-touching label is assigned once to its last exposed
outside prime, retaining its complete earlier cofactor and fixed residue.
The count of further primes, their finite exponents and their joint support
are unrestricted. F12 is a distorted-mass bound. The analytic prime-product
estimate remains Chapter33's ordinary inherited input.

## Verification and remaining scope

The [consumer](../../frontier/cover-geometry/all_first_root_centres.py)
uses the [four certificates](../../frontier/cover-geometry/all_first_root_centres_certificate.json)
and reconstructs the [exact result](../../frontier/cover-geometry/all_first_root_centres.json).
Only the standard library and adjacent canonical source/scalar/pair helpers
are loaded; no optimizer, saved graph or scratch producer is imported.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/all_first_root_centres.py

Default execution compares the adjacent result without writing it; --output
writes a reconstruction. Explicit exceptions keep checks active under -O.
The consumer verifies source identities and32 source vertices, the eight
literal anchors and their320 weight classes, all577578 worst profiles, every
used edge and its own-reference capacity, all176 transferred bounds, and the
strict Haar/tail conversions. An independent standard-library calculation
using literal CRT cells and cylinder-intersection differences agrees with
the44-class partition and all176 bounds; it also checks the used pair edges
independently of the canonical minimizer.

The fixed completed source, coarse normalization and interpolation,
report481's pair theorem and antitonicity, full-theoretical-graph upward
closure, full-history comparison, finite deleted-root transport and analytic
tail estimate remain ordinary deductions or inherited inputs. Source
producers and Lean are not rerun. Arbitrary centre separation patterns,
independently unrelated later old residues and arbitrary growing small-prime
cores are not settled. Unrestricted Erdős#7 remains open.
