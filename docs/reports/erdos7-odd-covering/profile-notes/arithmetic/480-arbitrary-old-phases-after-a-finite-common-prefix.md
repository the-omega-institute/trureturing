# Arbitrarily many old phases after one finite common prefix

For a fixed finite prefix at each of the first seven odd primes, the later original classes may choose all deeper digits independently, with no bound on the number of old reference residues. The resulting first-nine-prime family is noncovering, as is its continuation by arbitrary original classes on sufficiently large new primes. The shallow prefix condition is explicit below.

This is an ordinary mathematical deduction with exact rational arithmetic. It uses the attributed Schroeder source construction retained in [report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md), not a new Lean certification or a resolution of unrestricted Erdős #7.

## Statement

Let P={3,5,7,11,13,17,19} and

    (h3,h5,h7,h11,h13,h17,h19)=(5,4,3,3,3,3,3),
    D=product_p p^hp=5133293432417701175625.

Consider any finite original family of residue classes c mod m, with pairwise distinct odd numerical moduli m>1 supported on P union{23,29}. Each later modulus is m=d23^j29^k with j+k>0 and d P-supported. Suppose one integer a satisfies, separately for every such original label,

    c=a mod gcd(d,D).                         (FC1)

There is no restriction on the rest of c mod d. Thus the deeper original phases can be independently arbitrary for all full numerical labels, with no fixed bound on the number of different old residues. Old-only original classes, every23/29-coordinate residue, and all finite exponent heights are arbitrary.

Then the actual original survivor set U has

    H(U)>485955529/467775000000000>1/1000000.   (FC2)

Additional support primes may be any finite set above100000000, and every class touching them may have arbitrary original phases, heights and joint support. Only the head-only family is subject to FC1. The full family still cannot cover; the tail construction retains distorted mass greater than1/2000000, not a Haar-density claim of that size.

## Original-label inventory outside the deep columns

Choose fixed P-adic paths representing a, and define

    Q(x)=product_p(vp(x_p-a_p)+1),
    T_p={x:vp(x_p-a_p)>=hp},
    SAFE={Q<=19} intersect complement(union_p T_p).

Reference points at infinite valuation belong to T_p and cause no ambiguity. Resolve all original depths and the finite prefixes in one common carrier.

Suppose an original later class is active at the old point x: x=c mod d. Write e=vp(d). By FC1,

    x=a mod p^min(e,hp).

For x outside T_p, e>=hp is impossible. Hence every active cofactor has

    e<hp and e<=vp(x-a).

Once e<hp, FC1 fixes the entire relevant p^e residue to a. Therefore at every SAFE x, every active original old cofactor is among the at most Q(x)<=19 numerical divisors matched by the single reference. Classes having any deeper cofactor exponent cannot be active there, regardless of their arbitrary higher digits. This conclusion is about the actual fixed original phases; no branch chooses new residues.

For each fixed(j,k), at most nineteen distinct original old cofactors can thus be active. Original numerical distinctness is essential. Summing the original23-only and29-only inventories gives axis deletion bounds19/22 and19/28. Cross classes delete at most19/(22*28), including d=1. Their actual common surviving fibre has Haar mass at least

    (1-19/22)(1-19/28)-19/(22*28)=1/77.        (FC3)

The only remaining obligation is positive same-source mass of SAFE.

## Charge the union of bad load and deep columns once

Use the one charged completed old source nu from report467, as in [report479](479-independent-center-choices-with-simultaneous-coordinate-splits.md). Completion enlarges only the old-only excluded family and keeps every later original residue fixed. The source avoids every original old-only class and satisfies

    nu(1)>=m7=7235955529/450000000000,
    nu<=(27/2)H,
    (C7,C11,C13,C17,C19)=(3/2,5/3,3/2,2,9/5).

The source also has its stronger lower bound for each of eight coarse anchor types, with all four pure5-budget vertices kept attached to that type. Concavity of mass lower bounds in the continuous pure5 budget gives their vertex minima for each actual source. It does not permit selecting different laws for different queries.

The unsafe event is

    UNSAFE={Q>=20} union(union_p T_p).         (FC4)

It is coordinatewise increasing in the seven reference valuations. This permits one direct stochastic comparison for the union, avoiding any duplicate payment for points that are both high-load and in a deep column.

For one coordinate p>=7, any normalized actual conditional kernel with Haar density at most Cp is bounded on increasing payoffs f by

    E_actual f <= f(0)+Cp E_H(f-f(0)).         (FC5)

The comparison law has atom1-Cp/p at valuation0 and Cp(p-1)/p^(v+1) at each v>=1. It is positive and is applied uniformly at each actual complete earlier history. Drop actual deletion indicators only on the upper UNSAFE side, and integrate the actual kernels backwards. The auxiliary product law is not a claim of independence for the physical source.

An atom with v>=hp is already UNSAFE. A profile with product(v+1)>=20 is also UNSAFE. Consequently the entire infinite calculation reduces exactly to positive factors with

    0<=v<min(hp,19), product(v+1)<=19.

Everything omitted is absorbing UNSAFE mass. This is an exact event reduction for arbitrary original heights, not a truncation of the family or an approximation to a probability tail.

## The full pure anchor handles seven source types

For the common reference, valuation zero has Haar mass2/3 at3 and4/5 at5. Completed pure3 and pure5 exclusions have masses1/2 and1/4. Every excluded point has payoff at least the valuation-zero payoff. Subtracting each total exclusion mass from its baseline atom therefore gives positive upper comparison measures of total masses1/2 and3/4, whatever the positions of the exclusions. Positive integration preserves the increasing-payoff comparison. Other anchor exclusions can be omitted on the upper-bound side.

Exact convolution retaining only SAFE factors gives

    nu(UNSAFE)<=3383355836309703271531
                   /205331737296708047025000
               =0.01647751039782366...<17/1000. (FC6)

Every coarse source type except(2,4,1) has mass at least5891133457/225000000000. Subtracting17/1000 leaves more than the final uniform SAFE margin.

## Worst source: finite-prefix event in the actual six-cylinder anchor

For source type(2,4,1), normalize the whole original family and the reference path together. As in reports477-479, including the second-digit permutation of the selected25 class, the anchor avoids

    0 mod3,1 mod9,4 mod27,0 mod5,1 mod25,2 mod15.

Tree automorphisms preserve Haar, cylinder depths, numerical exponent labels and equality of prefixes through every hp. FC1 means exactly that the original class and the reference share the indicated prefix; it is therefore preserved even though a tree automorphism need not be one global additive translation.

The six-cylinder enlargement is the disjoint union

    A0=(R1 times V5) union(R2 times W5),

where R1={x3=1 mod3,x3!=1 mod9,x3!=4 mod27}, R2={x3=2 mod3}, V5={x5!=0 mod5,x5!=1 mod25}, and W5=V5 minus{x5=2 mod5}. Their masses are5/27,1/3,19/25,14/25.

After integrating the later conditional comparisons, the SAFE product weights define the increasing unsafe payoff

    f(t)=1-sum_(d:t*d<=19) Pr(later product=d
                              and every later valuation<hp).

If an anchor valuation already reaches its hp, the checker uses one absorbing UNSAFE symbol. Otherwise t is the product of its valuation-plus-one factors. This combines deep columns and high load in the same event.

Enumerate all27 ternary reference prefixes and25 quinary prefixes. A cell not containing the reference has an exact fixed valuation. Its containing cell has the exact geometric shells until the unsafe threshold, with the remaining mass placed in the absorbing symbol. Every cell and region mass is checked. Exact signatures reduce to6 ternary and6 quinary distributions, hence36 joint expectations.

The maximum is attained at reference prefixes2 mod27 and3 mod25 and equals

    372486651515592800987/25666467162088505878125
    =0.014512579747078959...<3/200.             (FC7)

All calculations use rational numbers. No optimization package or floating-point decision is involved.

## Positive source mass, original integers and the large-prime tail

The worst source therefore has

    nu(SAFE)>m7-3/200
            =485955529/450000000000.           (FC8)

The seven other coarse sources have larger margins using FC6. The two unsafe bounds are uniform in the actual continuous source budget. All32 retained source vertices are checked in their proper coarse groups.

Divide FC8 by the joint density cap27/2 and integrate the actual original fibre floor1/77 from FC3. This gives FC2. The actual family is finite, so its positive Haar survivor set projects to an uncovered residue in its finite CRT period and hence to an integer.

For outside primes explicitly switch to Haar restricted to the full original head survivor set. It has density at most1 and mass greater than1/1000000. Resolve all head digits used by tail originals; do not insert projected tail classes into the head forbidden family. The [Chapter33](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md) SH11-SH13 continuation, with its inherited analytic prime-product premise, uses

    M2=product_(p in P union{23,29})p(p+1)/(p-1)^2
      =14003665/540672,
    B=100000000, ell=16,
    c=(2ell^2+1)/(2ell^2-1)=513/511,
    tau7=(c^7/B)(B/(B-3))^2
             sum_(j=0,...,7)7!/((7-j)!ell^j).

The integer premises B>=286, ell>=4 and3^ell<=B all hold. Exact arithmetic gives

    M2*tau7=0.0000004440950881315332...,
    1/1000000-M2*tau7>1/2000000.                (FC9)

Every original tail class retains its fixed phase, numerical label and full earlier cofactor and is assigned once to its last outside prime. Thus no restriction is placed on the number of outside primes or their joint occurrence in a modulus.

## The new phase scope and its boundary

This family exceeds any fixed bound on the number of old reference centers. For every positive n, take d=3^(5+n) and old residues r*3^5 for r=0,...,3^n-1, attached to the distinct original labels d*23^(r+1). Choose any23-coordinate residue and form each fixed original class by CRT. All satisfy FC1 with a=0 but give3^n different residues at the same old cofactor. No list of fewer than3^n centers can supply all these phases. The verifier records the n=1 literal CRT control with three different old residues and three distinct numerical labels. It illustrates the scope, not a covering counterexample.

[Report457](457-finitely-many-early-phases-control-all-core-heights.md) is a different finite-frontier result: it fixes57 old numerical cofactor patterns on the four-prime core{5,7,11,13} at the old and first ternary layers, releasing all phases outside that numerical frontier and all deeper ternary layers. Here the old seven-prime family is arbitrary and there is no limit on later phase multiplicity, but FC1 still restricts the shallow digits of every later label. Its five-prime base families are included here as old-only inputs for noncoverage; its stronger completion-load margin is not a consequence of FC2. No general comparison of the two large-prime continuation scopes is asserted. The present theorem does not say that all sufficiently large cofactors have completely unrestricted phases. It also does not contain all of report479: two centers satisfying that result's shallower common prefixes need not satisfy FC1 here.

The common prefix condition remains a real hypothesis. This proof releases every higher digit independently, but does not settle arbitrary shallow phases, arbitrary growing small-prime cores or unrestricted Erdős #7.

## Verification boundary

The [standalone verifier](../../frontier/cover-geometry/arbitrary_phases_finite_prefix.py) and [exact result data](../../frontier/cover-geometry/arbitrary_phases_finite_prefix.json) check positive laws, SAFE convolutions, all27 by25 reference-position cases through36 distinct joint signatures, all32 coarse-source vertices, literal original CRT scope control, density conversion and tail constants. Conditional domination, the original inventory implication, source interpolation, simultaneous normalization and the analytic tail estimate are ordinary mathematical inputs. Source producers and Lean are not rerun.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/arbitrary_phases_finite_prefix.py
```

Optional `--input-dir DIR` relocates the two hash-pinned source inputs; `--output PATH` writes exact result JSON. The program uses only the standard library and explicit checks which remain active under optimization. Its finite calculations verify the comparison bounds, not an enumeration of every original family.
