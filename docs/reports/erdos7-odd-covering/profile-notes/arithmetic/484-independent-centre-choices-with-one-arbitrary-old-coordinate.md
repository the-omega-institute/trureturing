# Independent centre choices with one arbitrary old coordinate

Let P={3,5,7,11,13,17,19}. Consider a finite original family of classes c mod m
with pairwise distinct odd numerical moduli m>1 supported on P union{23,29}.
For m=d23^j29^k with j+k>0, d denotes its old P-supported cofactor.
Suppose there are two fixed integer centres a,b and one q in P such that:

* at every p in P other than q, the centres agree through every p-exponent
  used by the original later cofactors d;
* each complete original later numerical label independently has old residue
  a mod d or b mod d, with that choice fixed for the whole family.

The centres may disagree at any depth at q, including the first digit.
Old-only classes, original23/29 residues and all finite heights are arbitrary.
No shallow-anchor or missing-pure-power assumption is imposed. The original
survivor set has normalized Haar mass greater than1/80000000000.

Any finite set of further support primes greater than10000000000000 may be
added. The centre condition concerns only the head-only subfamily; all
classes touching these further primes have arbitrary fixed residues,
finite exponents and joint support. The continuation retains distorted mass
greater than1/125000000000, not a Haar bound of that size.

The new step is the unrestricted quinary disagreement case q=5, for which
we prove the stronger original Haar bound1/8000000000 below. Ternary
disagreement is supplied by [report483](483-independent-ternary-centre-choices-need-no-anchor-hypothesis.md);
q=7,11,13,17,19 is already covered by
[report478](478-independent-center-choices-with-one-varying-old-coordinate.md).
This removes the first-digit restriction remaining in report478 for both
3 and5. It does not permit arbitrary simultaneous disagreements in several
old coordinates or arbitrary unrelated old residues.

These are ordinary mathematical deductions with exact rational checks.
The source construction and report481's pair inequality retain their existing
attribution and verification limits; no new Lean certification or literature
priority is claimed.

## Keep one completed source

Use the fixed-completion conditional process of
[report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md),
with the completion rules explained in
[report466](466-randomized-completion-retains-full-original-survivor-support.md).
Its source is Michael Schroeder's *Nine Prime Divisors in Odd Distinct Covering
Systems*, edition1.0.1; the source identity and arbitrary-height boundary
remain in the [library entry](../../../../../Library/Arith/schroeder2026nine.md).
This argument does not use the averaged compactness law from report466 as a
substitute for the conditional process.

Completion retains legal original selected classes and may add missing
selected labels or move redundant selected classes. Its covered union
contains the original old covered union. All later original classes and
all of their fixed centre choices remain unchanged.

Fix one actual completed source nu with its existing complete pure-prime
exclusions. It has

    nu <= (27/2)H,
    (C7,C11,C13,C17,C19)=(3/2,5/3,3/2,2,9/5).

Every cap applies at every complete earlier history of this very process.
Its same-process mass bound is

    m_other=5891133457/225000000000

on seven coarse types, and

    m7=7235955529/450000000000

on the worst type(2,4,1). These follow from the retained32 vertices, four
per type, and the inherited reserve/loss concavity in the same continuous
budget. The checker verifies the vertex arithmetic; the source construction
and interpolation remain ordinary inputs.

Whenever the upper comparison keeps only a finite pure prefix, nu and its
lower bound remain unchanged. Only the upper initial set is enlarged, with
the released pure-tail mass paid explicitly. Its normalized kernels can be
extended to added histories by Haar, since all caps are at least1, and its
later deletion indicators may be released on this upper side. Positivity
makes the resulting process an upper comparison. No finite truncation is
asserted to inherit the completed source's lower bound. The original family
is finite, while this auxiliary completed source may have countably many
pure exclusions.

## The quinary union inventory and a safe original fibre

For q=5 extend the shared finite nonquinary centre prefixes to one fixed
common path at every p!=5. At an old point x let

    V5=max(v5(x5-a5),v5(x5-b5)),
    Q=(V5+1) product_(p in P,p!=5)(vp(xp-ap)+1).

Outside the null reference paths, Q counts the union of numerical old
cofactors matching at least one centre. At5 the two matching exponent sets
are initial intervals whose union is their longer interval; at every other
coordinate the matching intervals agree. The unit is included.

For each fixed new exponent pair(j,k), at most Q old cofactors can be active,
regardless of the original label's fixed centre choice. If Q<=19, the two
original axis complements have masses at least1-19/22 and1-19/28, and their
conjunction is a product. All original cross classes cost at most19/616.
Thus the actual original23/29 fibre survivor mass s(x) obeys

    s(x)>=(1-19/22)(1-19/28)-19/616=1/77.         (Q1)

No original residue is chosen after x or a support branch is known.

## Shared quinary roots and the seven nonworst source types

For a single reference coordinate, the valuation tail is p^(-j). For the
maximum of two quinary reference valuations it is at most2/5^j. If both
centres share their first quinary digit, the tail at j=1 is exactly1/5,
while the bound2/5^j remains valid for j>=2. These statements include
arbitrarily late separation and coincident reference paths.

On a pure-coordinate retained set of mass alpha, its restricted valuation
tail is at most the minimum of alpha and the full Haar tail. For the ideal
pure masses alpha3=1/2 and alpha5=3/4, these minima define positive comparison
measures of those masses. Every bounded increasing payoff is controlled by
these tail inequalities: expand it into its baseline and nonnegative
increments times tail indicators.

In the fixed completed source, keep only pure3 depths through H3>=12 and
pure5 depths through H5>=8 on the upper side. The selected pure classes are
disjoint. The enlarged coordinate masses are therefore

    1/2+epsilon3, 3/4+epsilon5,
    epsilon3=1/(2*3^H3), epsilon5=1/(4*5^H5).

Here the ternary coordinate has only one common path. Adding epsilon3 and
epsilon5 to the respective zero-valuation atoms dominates these enlarged
sets. For any payoff in[0,1], the product comparison increases by at most

    (3/4)epsilon3+(1/2)epsilon5+epsilon3 epsilon5
      <=epsilon3+epsilon5
      <=1312691/830376562500.                    (Q2)

At each later old prime p, the actual normalized conditional tail at every
full earlier history is at most Cp/p^j. The positive comparison probability
has mass1-Cp/p at valuation0 and Cp(p-1)/p^(j+1) at valuation j>=1. Reverse
conditional integration applies to the increasing BAD indicator1_(Q>=20).
It does not assume independence of actual histories; the independent
variables belong only to the comparison.

Exact convolution, retaining all larger factors in an absorbing BAD state,
gives these finite-prefix upper bounds, including Q2:

| Quinary positions | BAD upper, decimal for orientation | Applicable source mass |
| --- | ---: | ---: |
| Same first digit | 0.013928133894312779... | m7 |
| Arbitrary first digits | 0.019161546749357692... | m_other |

Both comparisons have a positive GOOD margin, and their original Haar
bounds after Q1 and the density cap exceed the eventual uniform quinary
bound. Thus only the worst source type with distinct quinary first digits
requires the joint calculation below.

## Normalize the worst source and enumerate all its shallow references

Use the simultaneous worst-type normalization from
[report477](477-two-arbitrary-centers-share-a-positive-original-fibre.md).
It transports the completed family, both reference paths and source together.
Rooted prime-prefix bijections preserve Haar measure, full-history caps,
fixed centre choices and every numerical modulus. The source avoids

    0 mod3, 1 mod9, 4 mod27, 0 mod5, 1 mod25, 2 mod15.       (Q3)

No45/75 phase is prescribed or used. Release every further initial exclusion
only on the upper side. The enlarged six-cylinder anchor is

    A6=(R1 times V5) union(R2 times W5),
    R1={x3 mod27: x3=1 mod3, x3!=1 mod9, x3!=4 mod27},
    R2={x3 mod27: x3=2 mod3},
    V5={x5 mod25: x5!=0 mod5, x5!=1 mod25},
    W5={x5 in V5: x5!=2 mod5}.

Their coordinate masses are5/27,1/3,19/25,14/25. This releases rather than
relocates all deeper original pure classes.

There are27 common ternary prefixes modulo27. There are250 unordered pairs
of quinary prefixes modulo25 with distinct first digits, giving6750 complete
shallow configurations. This enumeration includes centres in the deleted
pure5 root and centres inside the selected25 class. Such centres are not
silently excluded.

For each configuration, compute the exact valuation distribution in each
of the four regions. A cell containing a reference has the complete
geometric shell law; every other cell has a fixed valuation. Deeper digits
of a fixed reference do not change these shell masses. Integrating the
five-coordinate BAD payoff gives a direct single-fibre upper bound.

The checker verifies all6750 configurations, with6165 satisfying

    nu(BAD)<313/20000=0.01565<m7.                 (Q4)

Their largest exact comparison value is0.015643325771407163.... The585
remaining configurations are precisely those where the common ternary
reference is in root2 and both quinary references belong to W5, with
different first digits. Failure of this scalar bound does not imply a
covering or absence of actual survivors.

## Only two initial weight patterns remain

For the585 remaining configurations, the common ternary profile measure is

    factor k=1:5/27,
    factor k>=2:2/3^k.

A quinary matching root3 or4 has factor-u mass4/5^u for u>=2. A matching
root1 whose reference avoids1 mod25 has mass3/25 at u=2 and4/5^u for u>=3.
These are exact weights for every corresponding shallow reference, without
moving any original phase.

Consequently the585 configurations have only two complete initial weight
patterns, including the other quinary roots:

* 225 configurations have the same pattern as common3=2 mod27 and quinary
 references3,4 mod25;
* 360 configurations have the same pattern as common3=2 mod27 and quinary
 references3,6 mod25, after one global relabeling of the two centres if
 needed.

The checker compares every individual configuration's two matching-root
profile measures and remaining-root measure against its representative.
The reduction uses equality of explicit finite weights and their exact
geometric tails; it does not require a new orbit or family normalization
claim. All later row caps and pair constraints depend only on these
profiles, so this equality supplies the required comparison.

Outside the two matching quinary roots, both valuations are zero. This
part is retained. Its initial mass is3/25 in the3/4 pattern and19/135 in the
3/6 pattern. Integrating the increasing BAD payoff under the same
full-history conditional domination gives upper contributions

    B_other(3,4)=0.0010197594106602906...,
    B_other(3,6)=0.0012690217676639773....           (Q5)

Each exact rational value is added to every support branch. This counts
all remaining-root BAD mass without choosing another source or requiring
pair constraints on those roots.

## Fixed-label cross-root pair constraints

A profile in a matching quinary root is(branch,u,f), with u=v5+1>=2 and
f=(f3,f7,f11,f13,f17,f19). Put Q=u product(f). For opposite-root profiles
(u,f),(v,g), define

    Qx=u product(f), Qy=v product(g),
    N=Qx+Qy-min(u-1,v-1) product_i min(f_i,g_i).   (Q6)

At each fixed new exponent pair, a numerical old cofactor with positive5
exponent matching both nonquinary profiles would require opposite centre
choices at the two points. One fixed original full label cannot make both
choices. The subtracted term counts exactly these conflicts. Cofactors with
zero5 exponent can be active at both points and are not subtracted. Thus N
bounds the sum of active inventories for the same original selector.

Apply [report481](481-individual-mixed-budgets-strengthen-two-fibre-certificates.md)'s
individual mixed-budget inequality. Set

    ax=min(22,Qx), ay=min(22,Qy),
    bx=min(28,Qx), by=min(28,Qy),
    A=min(N,ax+ay), B=min(N,bx+by),
    t in[max(0,A-ay),min(ax,A)],
    z in[max(0,B-by),min(bx,B)],
    rx=(22-t)(28-z), ry=(22-A+t)(28-B+z),
    K=min_(t,z) max(0,rx-Qx,ry-Qy,rx+ry-N).

Here N<=Qx+Qy. Report481 proves that this minimum is attained on the
rectangle boundary and can be checked among at most28 rational candidates.
For actual original fibre masses it gives

    s(x)+s(y)>=K/616.                            (Q7)

The calculation applies to distinct nonquinary profiles as well as equal
ones. Every used edge has its own exact K recomputed.

## An exact support certificate for both patterns

Keep exceptional factors2<=u<=10 and initial common ternary factors while
u*k<=38. Pay the complete omitted initial mass with upper payoff1. At later
primes keep factors while the current load is<=38 and pay the complete
remaining geometric tail with payoff1. Terminal loads<20 have payoff0;
loads20--38 retain a profile support indicator. No high-valuation mass is
dropped.

At each actual complete earlier history the factor-bin probabilities obey

    r_f<=min(1,Cp(p-1)/p^f),
    r_tail<=min(1,Cp/p^J),
    r_f,r_tail>=0 and sum r=1.

For fixed child upper payoffs, their maximum is computed by sorting the
payoffs downward and filling capacities until mass1 is allocated. An
exchange of mass proves the rule. Applying it backwards at every history
bounds every adaptive kernel under these caps, without claiming that a
profile determines the hidden history.

For any two profile groups whose complete bipartite set of pairs has
K>0, a support avoiding all such pairs must omit one whole group. The
certificate keeps both possibilities and computes each branch upper by
this exact normalized-row rule, adding Q5 in every branch.

One certificate serves both weight patterns. Its verifier reconstructs
all profiles and rows, checks every pair and branch, and verifies complete
coverage with no pending or unreachable nodes. It checks

    2234 profiles,
    4352 normalized conditional rows,
    707 disjunction nodes,
    354 accepted leaves,
    8944 checked cross-edge occurrences,
    minimum used K=4/3.                           (Q8)

The worst exact leaf values are

    U_(3,4)=0.01607832345663344...,
    U_(3,6)=0.015378612997073483... .

The first is larger. Exact arithmetic verifies both satisfy

    U < U_star=16078324/1000000000 < m7.           (Q9)

The verifier explicitly requires every used pair to support K>=4/3;
positivity alone would not justify the following quantitative threshold.
These are certified upper bounds, with no assertion of exact optimality.
No numerical optimizer or producer is imported by the verifier.

## Original quinary survivors and the single-coordinate conclusion

On the actual old live set let T={x:s(x)<1/924}. No point in T has Q<=19 by
Q1. Two points in T cannot occupy a used edge, since their masses would sum
to less than1/462, contradicting Q7--Q8. Its matching-root support therefore
follows a certified branch. Its remaining-root part is included in BAD and
is covered by Q5 for that same actual source.

For the585 configurations, nu(T)<U_star follows from Q9. For the6165 scalar
configurations it follows from T contained in BAD and Q4. Hence the density
cap and actual original fibre give

    H(full original survivors)>(m7-U_star)/12474
      =709729/5613300000000000 >1/8000000000.      (Q10)

The earlier same-root and nonworst-source margins are larger; the checker
compares each against Q10 exactly. This covers every original q=5 family,
without imposing an original shallow-anchor assumption, a bound on heights,
or a particular45/75 phase. Positive Haar mass yields an uncovered cell in
the original finite CRT period and therefore an uncovered integer.

For q=3, report483 supplies the weaker uniform bound1/80000000000. For
q=7,11,13,17,19, report478 already gives a bound greater than1/15592500
without a first-digit condition. Its full-pure comparison and q=7 deep
pure credit concern the complete source's actual disjoint selected pure
classes; no finite truncated source lower bound is needed or asserted.
All three routes preserve independent fixed choices at each complete
original label. Taking their minimum proves the opening bound for every
single exceptional old coordinate.

The large-prime continuation is exactly report483's Haar-seed argument:
switch to Haar restricted to the full original head survivor set, of mass
greater than1/80000000000 and density at most1, and apply Chapter33 with

    M2=14003665/540672,
    B=10000000000000, ell=27.

The inherited analytic estimate and retained exact arithmetic give remaining
distorted mass greater than1/125000000000. Every tail-touching original class
keeps its complete label and fixed residue, and is assigned once to its last
exposed outside prime. No centre restriction is imposed on that tail.

## Verification and remaining boundary

The [standalone checker](../../frontier/cover-geometry/all_quinary_two_fibre.py)
reads the [support certificate](../../frontier/cover-geometry/all_quinary_two_fibre_certificate.json)
and reconstructs the [exact result](../../frontier/cover-geometry/all_quinary_two_fibre.json).
Run from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/all_quinary_two_fibre.py
```

Default execution compares the retained result without writing it;
`--output PATH` writes the exact reconstruction. Its two source input hashes
are the same retained identities used in report483. The finite checks cover
all6750 different-root shallow reference configurations, both complete pair
weight patterns, all used edge capacities, normalized rows, support branches,
released pure-tail arithmetic,32 source vertices and the uniform Haar bound.

The fixed completed source, its normalization and interpolation, the
arbitrary-height conditional-kernel bridge, report481's pair inequality,
and the inherited analytic large-prime continuation remain ordinary
mathematical inputs. Source producers and Lean are not rerun. Simultaneous
arbitrary disagreements in several old coordinates, completely unrelated
old phases, and arbitrary growing small-prime cores remain outside the
statement. Unrestricted Erdős#7 is unresolved.
